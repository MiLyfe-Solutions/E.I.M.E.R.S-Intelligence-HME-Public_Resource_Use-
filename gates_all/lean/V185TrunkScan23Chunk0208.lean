import V185TrunkScan23Chunk0207

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1230023 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 6, 4]
def baseStart_1230023 : Nat := 118140960795 + 1230023 * 2 ^ 59
def prefixEnd_1230023 : Nat := 4983230072969 + 3 ^ 40 * 1230023 * 2
def baseEnd_1230023 : Nat := 210531005028448754351911

theorem tailTrace_1230023 : CollatzResearch.WordTrace tailWord_1230023 prefixEnd_1230023 210531005028448754351911 := by
  unfold tailWord_1230023
  simp only [CollatzResearch.WordTrace]
  refine ⟨44862624422844217048886723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29908416281896144699257815 44862624422844217048886723)
  ·
    refine ⟨67293936634266325573330085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44862624422844217048886723 67293936634266325573330085)
    ·
      refine ⟨12617613118924936044999391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67293936634266325573330085 12617613118924936044999391)
      ·
        refine ⟨18926419678387404067499087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12617613118924936044999391 18926419678387404067499087)
        ·
          refine ⟨28389629517581106101248631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18926419678387404067499087 28389629517581106101248631)
          ·
            refine ⟨42584444276371659151872947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28389629517581106101248631 42584444276371659151872947)
            ·
              refine ⟨63876666414557488727809421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42584444276371659151872947 63876666414557488727809421)
              ·
                refine ⟨23953749905459058272928533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63876666414557488727809421 23953749905459058272928533)
                ·
                  refine ⟨1122832026818393356543525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23953749905459058272928533 1122832026818393356543525)
                  ·
                    refine ⟨210531005028448754351911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1122832026818393356543525 210531005028448754351911)
                    ·
                      rfl

theorem cell23_1230023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_1230023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230023 prefixEnd_1230023 := by exact prefixLift 1230023
  have htrace : WordTrace (prefixWord ++ tailWord_1230023) baseStart_1230023 baseEnd_1230023 := by
    simpa [prefixWord, tailWord_1230023, baseEnd_1230023] using wordTrace_append hprefix tailTrace_1230023
  have hstable : (prefixWord ++ tailWord_1230023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230023).length < 2 ^ (prefixWord ++ tailWord_1230023).sum := by decide
  have hdescent : baseEnd_1230023 < baseStart_1230023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230060 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 4]
def baseStart_1230060 : Nat := 118140960795 + 1230060 * 2 ^ 59
def prefixEnd_1230060 : Nat := 4983230072969 + 3 ^ 40 * 1230060 * 2
def baseEnd_1230060 : Nat := 631612013869562618293063

theorem tailTrace_1230060 : CollatzResearch.WordTrace tailWord_1230060 prefixEnd_1230060 631612013869562618293063 := by
  unfold tailWord_1230060
  simp only [CollatzResearch.WordTrace]
  refine ⟨22431986961855086183991817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29909315949140114911989089 22431986961855086183991817)
  ·
    refine ⟨16823990221391314637993863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22431986961855086183991817 16823990221391314637993863)
    ·
      refine ⟨25235985332086971956990795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16823990221391314637993863 25235985332086971956990795)
      ·
        refine ⟨37853977998130457935486193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25235985332086971956990795 37853977998130457935486193)
        ·
          refine ⟨28390483498597843451614645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37853977998130457935486193 28390483498597843451614645)
          ·
            refine ⟨2661607827993547823588873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28390483498597843451614645 2661607827993547823588873)
            ·
              refine ⟨1996205870995160867691655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2661607827993547823588873 1996205870995160867691655)
              ·
                refine ⟨2994308806492741301537483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1996205870995160867691655 2994308806492741301537483)
                ·
                  refine ⟨4491463209739111952306225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2994308806492741301537483 4491463209739111952306225)
                  ·
                    refine ⟨3368597407304333964229669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4491463209739111952306225 3368597407304333964229669)
                    ·
                      refine ⟨631612013869562618293063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3368597407304333964229669 631612013869562618293063)
                      ·
                        rfl

theorem cell23_1230060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_1230060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230060 prefixEnd_1230060 := by exact prefixLift 1230060
  have htrace : WordTrace (prefixWord ++ tailWord_1230060) baseStart_1230060 baseEnd_1230060 := by
    simpa [prefixWord, tailWord_1230060, baseEnd_1230060] using wordTrace_append hprefix tailTrace_1230060
  have hstable : (prefixWord ++ tailWord_1230060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230060).length < 2 ^ (prefixWord ++ tailWord_1230060).sum := by decide
  have hdescent : baseEnd_1230060 < baseStart_1230060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230080 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 4, 1, 3]
def baseStart_1230080 : Nat := 118140960795 + 1230080 * 2 ^ 59
def prefixEnd_1230080 : Nat := 4983230072969 + 3 ^ 40 * 1230080 * 2
def baseEnd_1230080 : Nat := 631622283482652540042971

theorem tailTrace_1230080 : CollatzResearch.WordTrace tailWord_1230080 prefixEnd_1230080 631622283482652540042971 := by
  unfold tailWord_1230080
  simp only [CollatzResearch.WordTrace]
  refine ⟨22432351691818857891855847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29909802255758477189141129 22432351691818857891855847)
  ·
    refine ⟨33648527537728286837783771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22432351691818857891855847 33648527537728286837783771)
    ·
      refine ⟨50472791306592430256675657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33648527537728286837783771 50472791306592430256675657)
      ·
        refine ⟨37854593479944322692506743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50472791306592430256675657 37854593479944322692506743)
        ·
          refine ⟨56781890219916484038760115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37854593479944322692506743 56781890219916484038760115)
          ·
            refine ⟨85172835329874726058140173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56781890219916484038760115 85172835329874726058140173)
            ·
              refine ⟨31939813248703022271802565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85172835329874726058140173 31939813248703022271802565)
              ·
                refine ⟨5988714984131816675962981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31939813248703022271802565 5988714984131816675962981)
                ·
                  refine ⟨1122884059524715626743059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5988714984131816675962981 1122884059524715626743059)
                  ·
                    refine ⟨1684326089287073440114589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1122884059524715626743059 1684326089287073440114589)
                    ·
                      refine ⟨631622283482652540042971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1684326089287073440114589 631622283482652540042971)
                      ·
                        rfl

theorem cell23_1230080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 4, 1, 3].length) (baseStart_1230080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230080 prefixEnd_1230080 := by exact prefixLift 1230080
  have htrace : WordTrace (prefixWord ++ tailWord_1230080) baseStart_1230080 baseEnd_1230080 := by
    simpa [prefixWord, tailWord_1230080, baseEnd_1230080] using wordTrace_append hprefix tailTrace_1230080
  have hstable : (prefixWord ++ tailWord_1230080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230080).length < 2 ^ (prefixWord ++ tailWord_1230080).sum := by decide
  have hdescent : baseEnd_1230080 < baseStart_1230080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230081 : List Nat := [1, 2, 4, 1, 1, 4, 2, 3, 1, 2, 2]
def baseStart_1230081 : Nat := 118140960795 + 1230081 * 2 ^ 59
def prefixEnd_1230081 : Nat := 4983230072969 + 3 ^ 40 * 1230081 * 2
def baseEnd_1230081 : Nat := 631622796963307036130467

theorem tailTrace_1230081 : CollatzResearch.WordTrace tailWord_1230081 prefixEnd_1230081 631622796963307036130467 := by
  unfold tailWord_1230081
  simp only [CollatzResearch.WordTrace]
  refine ⟨44864739856634092954498097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29909826571089395302998731 44864739856634092954498097)
  ·
    refine ⟨33648554892475569715873573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44864739856634092954498097 33648554892475569715873573)
    ·
      refine ⟨6309104042339169321726295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33648554892475569715873573 6309104042339169321726295)
      ·
        refine ⟨9463656063508753982589443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6309104042339169321726295 9463656063508753982589443)
        ·
          refine ⟨14195484095263130973884165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9463656063508753982589443 14195484095263130973884165)
          ·
            refine ⟨2661653267861837057603281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14195484095263130973884165 2661653267861837057603281)
            ·
              refine ⟨1996239950896377793202461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2661653267861837057603281 1996239950896377793202461)
              ·
                refine ⟨748589981586141672450923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1996239950896377793202461 748589981586141672450923)
                ·
                  refine ⟨1122884972379212508676385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748589981586141672450923 1122884972379212508676385)
                  ·
                    refine ⟨842163729284409381507289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1122884972379212508676385 842163729284409381507289)
                    ·
                      refine ⟨631622796963307036130467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 842163729284409381507289 631622796963307036130467)
                      ·
                        rfl

theorem cell23_1230081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_1230081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230081 prefixEnd_1230081 := by exact prefixLift 1230081
  have htrace : WordTrace (prefixWord ++ tailWord_1230081) baseStart_1230081 baseEnd_1230081 := by
    simpa [prefixWord, tailWord_1230081, baseEnd_1230081] using wordTrace_append hprefix tailTrace_1230081
  have hstable : (prefixWord ++ tailWord_1230081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230081).length < 2 ^ (prefixWord ++ tailWord_1230081).sum := by decide
  have hdescent : baseEnd_1230081 < baseStart_1230081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230084 : List Nat := [2, 3, 2, 2, 2, 1, 4, 1, 1, 2, 3]
def baseStart_1230084 : Nat := 118140960795 + 1230084 * 2 ^ 59
def prefixEnd_1230084 : Nat := 4983230072969 + 3 ^ 40 * 1230084 * 2
def baseEnd_1230084 : Nat := 631624337405270524392953

theorem tailTrace_1230084 : CollatzResearch.WordTrace tailWord_1230084 prefixEnd_1230084 631624337405270524392953 := by
  unfold tailWord_1230084
  simp only [CollatzResearch.WordTrace]
  refine ⟨22432424637811612233428653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29909899517082149644571537 22432424637811612233428653)
  ·
    refine ⟨8412159239179354587535745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22432424637811612233428653 8412159239179354587535745)
    ·
      refine ⟨6309119429384515940651809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8412159239179354587535745 6309119429384515940651809)
      ·
        refine ⟨4731839572038386955488857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6309119429384515940651809 4731839572038386955488857)
        ·
          refine ⟨3548879679028790216616643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4731839572038386955488857 3548879679028790216616643)
          ·
            refine ⟨5323319518543185324924965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3548879679028790216616643 5323319518543185324924965)
            ·
              refine ⟨998122409726847248423431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5323319518543185324924965 998122409726847248423431)
              ·
                refine ⟨1497183614590270872635147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998122409726847248423431 1497183614590270872635147)
                ·
                  refine ⟨2245775421885406308952721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1497183614590270872635147 2245775421885406308952721)
                  ·
                    refine ⟨1684331566414054731714541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2245775421885406308952721 1684331566414054731714541)
                    ·
                      refine ⟨631624337405270524392953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1684331566414054731714541 631624337405270524392953)
                      ·
                        rfl

theorem cell23_1230084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_1230084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230084 prefixEnd_1230084 := by exact prefixLift 1230084
  have htrace : WordTrace (prefixWord ++ tailWord_1230084) baseStart_1230084 baseEnd_1230084 := by
    simpa [prefixWord, tailWord_1230084, baseEnd_1230084] using wordTrace_append hprefix tailTrace_1230084
  have hstable : (prefixWord ++ tailWord_1230084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230084).length < 2 ^ (prefixWord ++ tailWord_1230084).sum := by decide
  have hdescent : baseEnd_1230084 < baseStart_1230084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230098 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_1230098 : Nat := 118140960795 + 1230098 * 2 ^ 59
def prefixEnd_1230098 : Nat := 4983230072969 + 3 ^ 40 * 1230098 * 2
def baseEnd_1230098 : Nat := 631631526134433469617889

theorem tailTrace_1230098 : CollatzResearch.WordTrace tailWord_1230098 prefixEnd_1230098 631631526134433469617889 := by
  unfold tailWord_1230098
  simp only [CollatzResearch.WordTrace]
  refine ⟨11216339974393126214466737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29910239931715003238577965 11216339974393126214466737)
  ·
    refine ⟨8412254980794844660850053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11216339974393126214466737 8412254980794844660850053)
    ·
      refine ⟨1577297808899033373909385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8412254980794844660850053 1577297808899033373909385)
      ·
        refine ⟨1182973356674275030432039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1577297808899033373909385 1182973356674275030432039)
        ·
          refine ⟨1774460035011412545648059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182973356674275030432039 1774460035011412545648059)
          ·
            refine ⟨2661690052517118818472089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774460035011412545648059 2661690052517118818472089)
            ·
              refine ⟨1996267539387839113854067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2661690052517118818472089 1996267539387839113854067)
              ·
                refine ⟨2994401309081758670781101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1996267539387839113854067 2994401309081758670781101)
                ·
                  refine ⟨1122900490905659501542913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2994401309081758670781101 1122900490905659501542913)
                  ·
                    refine ⟨842175368179244626157185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1122900490905659501542913 842175368179244626157185)
                    ·
                      refine ⟨631631526134433469617889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 842175368179244626157185 631631526134433469617889)
                      ·
                        rfl

theorem cell23_1230098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_1230098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230098 prefixEnd_1230098 := by exact prefixLift 1230098
  have htrace : WordTrace (prefixWord ++ tailWord_1230098) baseStart_1230098 baseEnd_1230098 := by
    simpa [prefixWord, tailWord_1230098, baseEnd_1230098] using wordTrace_append hprefix tailTrace_1230098
  have hstable : (prefixWord ++ tailWord_1230098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230098).length < 2 ^ (prefixWord ++ tailWord_1230098).sum := by decide
  have hdescent : baseEnd_1230098 < baseStart_1230098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230114 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_1230114 : Nat := 118140960795 + 1230114 * 2 ^ 59
def prefixEnd_1230114 : Nat := 4983230072969 + 3 ^ 40 * 1230114 * 2
def baseEnd_1230114 : Nat := 631639741824905407017815

theorem tailTrace_1230114 : CollatzResearch.WordTrace tailWord_1230114 prefixEnd_1230114 631639741824905407017815 := by
  unfold tailWord_1230114
  simp only [CollatzResearch.WordTrace]
  refine ⟨11216485866378634897612349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29910628977009693060299597 11216485866378634897612349)
  ·
    refine ⟨4206182199891988086604631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11216485866378634897612349 4206182199891988086604631)
    ·
      refine ⟨6309273299837982129906947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4206182199891988086604631 6309273299837982129906947)
      ·
        refine ⟨9463909949756973194860421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6309273299837982129906947 9463909949756973194860421)
        ·
          refine ⟨1774483115579432474036329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9463909949756973194860421 1774483115579432474036329)
          ·
            refine ⟨1330862336684574355527247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1774483115579432474036329 1330862336684574355527247)
            ·
              refine ⟨1996293505026861533290871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330862336684574355527247 1996293505026861533290871)
              ·
                refine ⟨2994440257540292299936307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1996293505026861533290871 2994440257540292299936307)
                ·
                  refine ⟨4491660386310438449904461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2994440257540292299936307 4491660386310438449904461)
                  ·
                    refine ⟨1684372644866414418714173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4491660386310438449904461 1684372644866414418714173)
                    ·
                      refine ⟨631639741824905407017815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1684372644866414418714173 631639741824905407017815)
                      ·
                        rfl

theorem cell23_1230114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_1230114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230114 prefixEnd_1230114 := by exact prefixLift 1230114
  have htrace : WordTrace (prefixWord ++ tailWord_1230114) baseStart_1230114 baseEnd_1230114 := by
    simpa [prefixWord, tailWord_1230114, baseEnd_1230114] using wordTrace_append hprefix tailTrace_1230114
  have hstable : (prefixWord ++ tailWord_1230114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230114).length < 2 ^ (prefixWord ++ tailWord_1230114).sum := by decide
  have hdescent : baseEnd_1230114 < baseStart_1230114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230140 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_1230140 : Nat := 118140960795 + 1230140 * 2 ^ 59
def prefixEnd_1230140 : Nat := 4983230072969 + 3 ^ 40 * 1230140 * 2
def baseEnd_1230140 : Nat := 631653092321922305292695

theorem tailTrace_1230140 : CollatzResearch.WordTrace tailWord_1230140 prefixEnd_1230140 631653092321922305292695 := by
  unfold tailWord_1230140
  simp only [CollatzResearch.WordTrace]
  refine ⟨22433445881710173015447937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29911261175613564020597249 22433445881710173015447937)
  ·
    refine ⟨16825084411282629761585953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22433445881710173015447937 16825084411282629761585953)
    ·
      refine ⟨12618813308461972321189465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16825084411282629761585953 12618813308461972321189465)
      ·
        refine ⟨9464109981346479240892099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12618813308461972321189465 9464109981346479240892099)
        ·
          refine ⟨14196164972019718861338149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9464109981346479240892099 14196164972019718861338149)
          ·
            refine ⟨2661780932253697286500903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14196164972019718861338149 2661780932253697286500903)
            ·
              refine ⟨3992671398380545929751355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2661780932253697286500903 3992671398380545929751355)
              ·
                refine ⟨5989007097570818894627033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3992671398380545929751355 5989007097570818894627033)
                ·
                  refine ⟨4491755323178114170970275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5989007097570818894627033 4491755323178114170970275)
                  ·
                    refine ⟨6737632984767171256455413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4491755323178114170970275 6737632984767171256455413)
                    ·
                      refine ⟨631653092321922305292695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6737632984767171256455413 631653092321922305292695)
                      ·
                        rfl

theorem cell23_1230140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_1230140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230140 prefixEnd_1230140 := by exact prefixLift 1230140
  have htrace : WordTrace (prefixWord ++ tailWord_1230140) baseStart_1230140 baseEnd_1230140 := by
    simpa [prefixWord, tailWord_1230140, baseEnd_1230140] using wordTrace_append hprefix tailTrace_1230140
  have hstable : (prefixWord ++ tailWord_1230140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230140).length < 2 ^ (prefixWord ++ tailWord_1230140).sum := by decide
  have hdescent : baseEnd_1230140 < baseStart_1230140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230170 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3]
def baseStart_1230170 : Nat := 118140960795 + 1230170 * 2 ^ 59
def prefixEnd_1230170 : Nat := 4983230072969 + 3 ^ 40 * 1230170 * 2
def baseEnd_1230170 : Nat := 631668496741557187917557

theorem tailTrace_1230170 : CollatzResearch.WordTrace tailWord_1230170 prefixEnd_1230170 631668496741557187917557 := by
  unfold tailWord_1230170
  simp only [CollatzResearch.WordTrace]
  refine ⟨11216996488327915288621991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29911990635541107436325309 11216996488327915288621991)
  ·
    refine ⟨16825494732491872932932987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11216996488327915288621991 16825494732491872932932987)
    ·
      refine ⟨25238242098737809399399481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16825494732491872932932987 25238242098737809399399481)
      ·
        refine ⟨18928681574053357049549611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25238242098737809399399481 18928681574053357049549611)
        ·
          refine ⟨28393022361080035574324417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18928681574053357049549611 28393022361080035574324417)
          ·
            refine ⟨21294766770810026680743313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28393022361080035574324417 21294766770810026680743313)
            ·
              refine ⟨15971075078107520010557485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21294766770810026680743313 15971075078107520010557485)
              ·
                refine ⟨5989153154290320003959057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15971075078107520010557485 5989153154290320003959057)
                ·
                  refine ⟨4491864865717740002969293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5989153154290320003959057 4491864865717740002969293)
                  ·
                    refine ⟨1684449324644152501113485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4491864865717740002969293 1684449324644152501113485)
                    ·
                      refine ⟨631668496741557187917557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1684449324644152501113485 631668496741557187917557)
                      ·
                        rfl

theorem cell23_1230170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_1230170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230170 prefixEnd_1230170 := by exact prefixLift 1230170
  have htrace : WordTrace (prefixWord ++ tailWord_1230170) baseStart_1230170 baseEnd_1230170 := by
    simpa [prefixWord, tailWord_1230170, baseEnd_1230170] using wordTrace_append hprefix tailTrace_1230170
  have hstable : (prefixWord ++ tailWord_1230170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230170).length < 2 ^ (prefixWord ++ tailWord_1230170).sum := by decide
  have hdescent : baseEnd_1230170 < baseStart_1230170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230237 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 5, 4]
def baseStart_1230237 : Nat := 118140960795 + 1230237 * 2 ^ 59
def prefixEnd_1230237 : Nat := 4983230072969 + 3 ^ 40 * 1230237 * 2
def baseEnd_1230237 : Nat := 210567633315136141926583

theorem tailTrace_1230237 : CollatzResearch.WordTrace tailWord_1230237 prefixEnd_1230237 210567633315136141926583 := by
  unfold tailWord_1230237
  simp only [CollatzResearch.WordTrace]
  refine ⟨44870429644068931597176965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29913619762712621064784643 44870429644068931597176965)
  ·
    refine ⟨8413205558262924674470681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44870429644068931597176965 8413205558262924674470681)
    ·
      refine ⟨6309904168697193505853011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8413205558262924674470681 6309904168697193505853011)
      ·
        refine ⟨9464856253045790258779517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6309904168697193505853011 9464856253045790258779517)
        ·
          refine ⟨3549321094892171347042319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9464856253045790258779517 3549321094892171347042319)
          ·
            refine ⟨5323981642338257020563479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3549321094892171347042319 5323981642338257020563479)
            ·
              refine ⟨7985972463507385530845219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5323981642338257020563479 7985972463507385530845219)
              ·
                refine ⟨11978958695261078296267829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7985972463507385530845219 11978958695261078296267829)
                ·
                  refine ⟨1123027377680726090275109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11978958695261078296267829 1123027377680726090275109)
                  ·
                    refine ⟨210567633315136141926583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1123027377680726090275109 210567633315136141926583)
                    ·
                      rfl

theorem cell23_1230237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_1230237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230237 prefixEnd_1230237 := by exact prefixLift 1230237
  have htrace : WordTrace (prefixWord ++ tailWord_1230237) baseStart_1230237 baseEnd_1230237 := by
    simpa [prefixWord, tailWord_1230237, baseEnd_1230237] using wordTrace_append hprefix tailTrace_1230237
  have hstable : (prefixWord ++ tailWord_1230237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230237).length < 2 ^ (prefixWord ++ tailWord_1230237).sum := by decide
  have hdescent : baseEnd_1230237 < baseStart_1230237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230247 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_1230247 : Nat := 118140960795 + 1230247 * 2 ^ 59
def prefixEnd_1230247 : Nat := 4983230072969 + 3 ^ 40 * 1230247 * 2
def baseEnd_1230247 : Nat := 631708034751953386654703

theorem tailTrace_1230247 : CollatzResearch.WordTrace tailWord_1230247 prefixEnd_1230247 631708034751953386654703 := by
  unfold tailWord_1230247
  simp only [CollatzResearch.WordTrace]
  refine ⟨44870794374032703305040995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29913862916021802203360663 44870794374032703305040995)
  ·
    refine ⟨67306191561049054957561493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44870794374032703305040995 67306191561049054957561493)
    ·
      refine ⟨3154977729424174451135695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67306191561049054957561493 3154977729424174451135695)
      ·
        refine ⟨4732466594136261676703543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3154977729424174451135695 4732466594136261676703543)
        ·
          refine ⟨7098699891204392515055315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4732466594136261676703543 7098699891204392515055315)
          ·
            refine ⟨10648049836806588772582973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7098699891204392515055315 10648049836806588772582973)
            ·
              refine ⟨3993018688802470789718615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10648049836806588772582973 3993018688802470789718615)
              ·
                refine ⟨5989528033203706184577923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3993018688802470789718615 5989528033203706184577923)
                ·
                  refine ⟨8984292049805559276866885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5989528033203706184577923 8984292049805559276866885)
                  ·
                    refine ⟨1684554759338542364412541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8984292049805559276866885 1684554759338542364412541)
                    ·
                      refine ⟨631708034751953386654703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1684554759338542364412541 631708034751953386654703)
                      ·
                        rfl

theorem cell23_1230247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_1230247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230247 prefixEnd_1230247 := by exact prefixLift 1230247
  have htrace : WordTrace (prefixWord ++ tailWord_1230247) baseStart_1230247 baseEnd_1230247 := by
    simpa [prefixWord, tailWord_1230247, baseEnd_1230247] using wordTrace_append hprefix tailTrace_1230247
  have hstable : (prefixWord ++ tailWord_1230247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230247).length < 2 ^ (prefixWord ++ tailWord_1230247).sum := by decide
  have hdescent : baseEnd_1230247 < baseStart_1230247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230284 : List Nat := [2, 2, 1, 4, 2, 2, 3, 1, 6]
def baseStart_1230284 : Nat := 118140960795 + 1230284 * 2 ^ 59
def prefixEnd_1230284 : Nat := 4983230072969 + 3 ^ 40 * 1230284 * 2
def baseEnd_1230284 : Nat := 70191892615129971321337

theorem tailTrace_1230284 : CollatzResearch.WordTrace tailWord_1230284 prefixEnd_1230284 70191892615129971321337 := by
  unfold tailWord_1230284
  simp only [CollatzResearch.WordTrace]
  refine ⟨22436071937449329312068953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29914762583265772416091937 22436071937449329312068953)
  ·
    refine ⟨16827053953086996984051715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22436071937449329312068953 16827053953086996984051715)
    ·
      refine ⟨25240580929630495476077573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16827053953086996984051715 25240580929630495476077573)
      ·
        refine ⟨4732608924305717901764545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25240580929630495476077573 4732608924305717901764545)
        ·
          refine ⟨3549456693229288426323409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4732608924305717901764545 3549456693229288426323409)
          ·
            refine ⟨2662092519921966319742557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3549456693229288426323409 2662092519921966319742557)
            ·
              refine ⟨998284694970737369903459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2662092519921966319742557 998284694970737369903459)
              ·
                refine ⟨1497427042456106054855189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998284694970737369903459 1497427042456106054855189)
                ·
                  refine ⟨70191892615129971321337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1497427042456106054855189 70191892615129971321337)
                  ·
                    rfl

theorem cell23_1230284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 6].length) (baseStart_1230284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230284 prefixEnd_1230284 := by exact prefixLift 1230284
  have htrace : WordTrace (prefixWord ++ tailWord_1230284) baseStart_1230284 baseEnd_1230284 := by
    simpa [prefixWord, tailWord_1230284, baseEnd_1230284] using wordTrace_append hprefix tailTrace_1230284
  have hstable : (prefixWord ++ tailWord_1230284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230284).length < 2 ^ (prefixWord ++ tailWord_1230284).sum := by decide
  have hdescent : baseEnd_1230284 < baseStart_1230284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230287 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 1, 5, 2]
def baseStart_1230287 : Nat := 118140960795 + 1230287 * 2 ^ 59
def prefixEnd_1230287 : Nat := 4983230072969 + 3 ^ 40 * 1230287 * 2
def baseEnd_1230287 : Nat := 631728573978133230154519

theorem tailTrace_1230287 : CollatzResearch.WordTrace tailWord_1230287 prefixEnd_1230287 631728573978133230154519 := by
  unfold tailWord_1230287
  simp only [CollatzResearch.WordTrace]
  refine ⟨44872253293887790136497115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29914835529258526757664743 44872253293887790136497115)
  ·
    refine ⟨67308379940831685204745673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44872253293887790136497115 67308379940831685204745673)
    ·
      refine ⟨50481284955623763903559255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67308379940831685204745673 50481284955623763903559255)
      ·
        refine ⟨75721927433435645855338883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50481284955623763903559255 75721927433435645855338883)
        ·
          refine ⟨113582891150153468783008325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75721927433435645855338883 113582891150153468783008325)
          ·
            refine ⟨21296792090653775396814061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113582891150153468783008325 21296792090653775396814061)
            ·
              refine ⟨7986297033995165773805273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21296792090653775396814061 7986297033995165773805273)
              ·
                refine ⟨5989722775496374330353955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7986297033995165773805273 5989722775496374330353955)
                ·
                  refine ⟨8984584163244561495530933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5989722775496374330353955 8984584163244561495530933)
                  ·
                    refine ⟨842304765304177640206025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8984584163244561495530933 842304765304177640206025)
                    ·
                      refine ⟨631728573978133230154519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 842304765304177640206025 631728573978133230154519)
                      ·
                        rfl

theorem cell23_1230287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 5, 2].length) (baseStart_1230287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230287 prefixEnd_1230287 := by exact prefixLift 1230287
  have htrace : WordTrace (prefixWord ++ tailWord_1230287) baseStart_1230287 baseEnd_1230287 := by
    simpa [prefixWord, tailWord_1230287, baseEnd_1230287] using wordTrace_append hprefix tailTrace_1230287
  have hstable : (prefixWord ++ tailWord_1230287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230287).length < 2 ^ (prefixWord ++ tailWord_1230287).sum := by decide
  have hdescent : baseEnd_1230287 < baseStart_1230287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230297 : List Nat := [1, 2, 1, 2, 4, 2, 1, 4, 1, 5]
def baseStart_1230297 : Nat := 118140960795 + 1230297 * 2 ^ 59
def prefixEnd_1230297 : Nat := 4983230072969 + 3 ^ 40 * 1230297 * 2
def baseEnd_1230297 : Nat := 210577902928226063676491

theorem tailTrace_1230297 : CollatzResearch.WordTrace tailWord_1230297 prefixEnd_1230297 210577902928226063676491 := by
  unfold tailWord_1230297
  simp only [CollatzResearch.WordTrace]
  refine ⟨44872618023851561844361145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29915078682567707896240763 44872618023851561844361145)
  ·
    refine ⟨33654463517888671383270859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44872618023851561844361145 33654463517888671383270859)
    ·
      refine ⟨50481695276833007074906289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33654463517888671383270859 50481695276833007074906289)
      ·
        refine ⟨37861271457624755306179717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50481695276833007074906289 37861271457624755306179717)
        ·
          refine ⟨7098988398304641619908697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37861271457624755306179717 7098988398304641619908697)
          ·
            refine ⟨5324241298728481214931523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7098988398304641619908697 5324241298728481214931523)
            ·
              refine ⟨7986361948092721822397285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5324241298728481214931523 7986361948092721822397285)
              ·
                refine ⟨1497442865267385341699491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7986361948092721822397285 1497442865267385341699491)
                ·
                  refine ⟨2246164297901078012549237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1497442865267385341699491 2246164297901078012549237)
                  ·
                    refine ⟨210577902928226063676491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2246164297901078012549237 210577902928226063676491)
                    ·
                      rfl

theorem cell23_1230297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 5].length) (baseStart_1230297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230297 prefixEnd_1230297 := by exact prefixLift 1230297
  have htrace : WordTrace (prefixWord ++ tailWord_1230297) baseStart_1230297 baseEnd_1230297 := by
    simpa [prefixWord, tailWord_1230297, baseEnd_1230297] using wordTrace_append hprefix tailTrace_1230297
  have hstable : (prefixWord ++ tailWord_1230297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230297).length < 2 ^ (prefixWord ++ tailWord_1230297).sum := by decide
  have hdescent : baseEnd_1230297 < baseStart_1230297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230328 : List Nat := [2, 1, 2, 1, 1, 6, 3, 2, 1, 1, 3]
def baseStart_1230328 : Nat := 118140960795 + 1230328 * 2 ^ 59
def prefixEnd_1230328 : Nat := 4983230072969 + 3 ^ 40 * 1230328 * 2
def baseEnd_1230328 : Nat := 631749626684967569741831

theorem tailTrace_1230328 : CollatzResearch.WordTrace tailWord_1230328 prefixEnd_1230328 631749626684967569741831 := by
  unfold tailWord_1230328
  simp only [CollatzResearch.WordTrace]
  refine ⟨22436874343369627069369819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29915832457826169425826425 22436874343369627069369819)
  ·
    refine ⟨33655311515054440604054729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22436874343369627069369819 33655311515054440604054729)
    ·
      refine ⟨25241483636290830453041047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33655311515054440604054729 25241483636290830453041047)
      ·
        refine ⟨37862225454436245679561571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25241483636290830453041047 37862225454436245679561571)
        ·
          refine ⟨56793338181654368519342357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37862225454436245679561571 56793338181654368519342357)
          ·
            refine ⟨2662187727265048524344173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56793338181654368519342357 2662187727265048524344173)
            ·
              refine ⟨998320397724393196629065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2662187727265048524344173 998320397724393196629065)
              ·
                refine ⟨748740298293294897471799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 998320397724393196629065 748740298293294897471799)
                ·
                  refine ⟨1123110447439942346207699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748740298293294897471799 1123110447439942346207699)
                  ·
                    refine ⟨1684665671159913519311549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1123110447439942346207699 1684665671159913519311549)
                    ·
                      refine ⟨631749626684967569741831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1684665671159913519311549 631749626684967569741831)
                      ·
                        rfl

theorem cell23_1230328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 1, 1, 3].length) (baseStart_1230328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230328 prefixEnd_1230328 := by exact prefixLift 1230328
  have htrace : WordTrace (prefixWord ++ tailWord_1230328) baseStart_1230328 baseEnd_1230328 := by
    simpa [prefixWord, tailWord_1230328, baseEnd_1230328] using wordTrace_append hprefix tailTrace_1230328
  have hstable : (prefixWord ++ tailWord_1230328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230328).length < 2 ^ (prefixWord ++ tailWord_1230328).sum := by decide
  have hdescent : baseEnd_1230328 < baseStart_1230328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230330 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6]
def baseStart_1230330 : Nat := 118140960795 + 1230330 * 2 ^ 59
def prefixEnd_1230330 : Nat := 4983230072969 + 3 ^ 40 * 1230330 * 2
def baseEnd_1230330 : Nat := 631750653646276561916821

theorem tailTrace_1230330 : CollatzResearch.WordTrace tailWord_1230330 prefixEnd_1230330 631750653646276561916821 := by
  unfold tailWord_1230330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11218455408183002120078111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29915881088488005653541629 11218455408183002120078111)
  ·
    refine ⟨16827683112274503180117167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11218455408183002120078111 16827683112274503180117167)
    ·
      refine ⟨25241524668411754770175751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16827683112274503180117167 25241524668411754770175751)
      ·
        refine ⟨37862287002617632155263627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25241524668411754770175751 37862287002617632155263627)
        ·
          refine ⟨56793430503926448232895441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37862287002617632155263627 56793430503926448232895441)
          ·
            refine ⟨42595072877944836174671581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56793430503926448232895441 42595072877944836174671581)
            ·
              refine ⟨15973152329229313565501843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42595072877944836174671581 15973152329229313565501843)
              ·
                refine ⟨23959728493843970348252765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15973152329229313565501843 23959728493843970348252765)
                ·
                  refine ⟨8984898185191488880594787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23959728493843970348252765 8984898185191488880594787)
                  ·
                    refine ⟨13477347277787233320892181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8984898185191488880594787 13477347277787233320892181)
                    ·
                      refine ⟨631750653646276561916821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13477347277787233320892181 631750653646276561916821)
                      ·
                        rfl

theorem cell23_1230330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_1230330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230330 prefixEnd_1230330 := by exact prefixLift 1230330
  have htrace : WordTrace (prefixWord ++ tailWord_1230330) baseStart_1230330 baseEnd_1230330 := by
    simpa [prefixWord, tailWord_1230330, baseEnd_1230330] using wordTrace_append hprefix tailTrace_1230330
  have hstable : (prefixWord ++ tailWord_1230330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230330).length < 2 ^ (prefixWord ++ tailWord_1230330).sum := by decide
  have hdescent : baseEnd_1230330 < baseStart_1230330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230367 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 3]
def baseStart_1230367 : Nat := 118140960795 + 1230367 * 2 ^ 59
def prefixEnd_1230367 : Nat := 4983230072969 + 3 ^ 40 * 1230367 * 2
def baseEnd_1230367 : Nat := 631769652430492917154151

theorem tailTrace_1230367 : CollatzResearch.WordTrace tailWord_1230367 prefixEnd_1230367 631769652430492917154151 := by
  unfold tailWord_1230367
  simp only [CollatzResearch.WordTrace]
  refine ⟨44875171133597963799409355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29916780755731975866272903 44875171133597963799409355)
  ·
    refine ⟨67312756700396945699114033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44875171133597963799409355 67312756700396945699114033)
    ·
      refine ⟨50484567525297709274335525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67312756700396945699114033 50484567525297709274335525)
      ·
        refine ⟨9465856410993320488937911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50484567525297709274335525 9465856410993320488937911)
        ·
          refine ⟨14198784616489980733406867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9465856410993320488937911 14198784616489980733406867)
          ·
            refine ⟨21298176924734971100110301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14198784616489980733406867 21298176924734971100110301)
            ·
              refine ⟨7986816346775614162541363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21298176924734971100110301 7986816346775614162541363)
              ·
                refine ⟨11980224520163421243812045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7986816346775614162541363 11980224520163421243812045)
                ·
                  refine ⟨4492584195061282966429517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11980224520163421243812045 4492584195061282966429517)
                  ·
                    refine ⟨1684719073147981112411069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4492584195061282966429517 1684719073147981112411069)
                    ·
                      refine ⟨631769652430492917154151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1684719073147981112411069 631769652430492917154151)
                      ·
                        rfl

theorem cell23_1230367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_1230367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230367 prefixEnd_1230367 := by exact prefixLift 1230367
  have htrace : WordTrace (prefixWord ++ tailWord_1230367) baseStart_1230367 baseEnd_1230367 := by
    simpa [prefixWord, tailWord_1230367, baseEnd_1230367] using wordTrace_append hprefix tailTrace_1230367
  have hstable : (prefixWord ++ tailWord_1230367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230367).length < 2 ^ (prefixWord ++ tailWord_1230367).sum := by decide
  have hdescent : baseEnd_1230367 < baseStart_1230367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230371 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 1, 1, 5]
def baseStart_1230371 : Nat := 118140960795 + 1230371 * 2 ^ 59
def prefixEnd_1230371 : Nat := 4983230072969 + 3 ^ 40 * 1230371 * 2
def baseEnd_1230371 : Nat := 631771706353110901504133

theorem tailTrace_1230371 : CollatzResearch.WordTrace tailWord_1230371 prefixEnd_1230371 631771706353110901504133 := by
  unfold tailWord_1230371
  simp only [CollatzResearch.WordTrace]
  refine ⟨44875317025583472482554967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29916878017055648321703311 44875317025583472482554967)
  ·
    refine ⟨67312975538375208723832451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44875317025583472482554967 67312975538375208723832451)
    ·
      refine ⟨100969463307562813085748677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67312975538375208723832451 100969463307562813085748677)
      ·
        refine ⟨18931774370168027453577877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100969463307562813085748677 18931774370168027453577877)
        ·
          refine ⟨887426923601626286886463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18931774370168027453577877 887426923601626286886463)
          ·
            refine ⟨1331140385402439430329695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887426923601626286886463 1331140385402439430329695)
            ·
              refine ⟨1996710578103659145494543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331140385402439430329695 1996710578103659145494543)
              ·
                refine ⟨2995065867155488718241815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1996710578103659145494543 2995065867155488718241815)
                ·
                  refine ⟨4492598800733233077362723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2995065867155488718241815 4492598800733233077362723)
                  ·
                    refine ⟨6738898201099849616044085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4492598800733233077362723 6738898201099849616044085)
                    ·
                      refine ⟨631771706353110901504133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6738898201099849616044085 631771706353110901504133)
                      ·
                        rfl

theorem cell23_1230371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_1230371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230371 prefixEnd_1230371 := by exact prefixLift 1230371
  have htrace : WordTrace (prefixWord ++ tailWord_1230371) baseStart_1230371 baseEnd_1230371 := by
    simpa [prefixWord, tailWord_1230371, baseEnd_1230371] using wordTrace_append hprefix tailTrace_1230371
  have hstable : (prefixWord ++ tailWord_1230371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230371).length < 2 ^ (prefixWord ++ tailWord_1230371).sum := by decide
  have hdescent : baseEnd_1230371 < baseStart_1230371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230380 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 7]
def baseStart_1230380 : Nat := 118140960795 + 1230380 * 2 ^ 59
def prefixEnd_1230380 : Nat := 4983230072969 + 3 ^ 40 * 1230380 * 2
def baseEnd_1230380 : Nat := 631776327679001366291591

theorem tailTrace_1230380 : CollatzResearch.WordTrace tailWord_1230380 prefixEnd_1230380 631776327679001366291591 := by
  unfold tailWord_1230380
  simp only [CollatzResearch.WordTrace]
  refine ⟨22437822641275433509816297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29917096855033911346421729 22437822641275433509816297)
  ·
    refine ⟨16828366980956575132362223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22437822641275433509816297 16828366980956575132362223)
    ·
      refine ⟨25242550471434862698543335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16828366980956575132362223 25242550471434862698543335)
      ·
        refine ⟨37863825707152294047815003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25242550471434862698543335 37863825707152294047815003)
        ·
          refine ⟨56795738560728441071722505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37863825707152294047815003 56795738560728441071722505)
          ·
            refine ⟨42596803920546330803791879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56795738560728441071722505 42596803920546330803791879)
            ·
              refine ⟨63895205880819496205687819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42596803920546330803791879 63895205880819496205687819)
              ·
                refine ⟨95842808821229244308531729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63895205880819496205687819 95842808821229244308531729)
                ·
                  refine ⟨71882106615921933231398797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95842808821229244308531729 71882106615921933231398797)
                  ·
                    refine ⟨26955789980970724961774549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71882106615921933231398797 26955789980970724961774549)
                    ·
                      refine ⟨631776327679001366291591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26955789980970724961774549 631776327679001366291591)
                      ·
                        rfl

theorem cell23_1230380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_1230380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230380 prefixEnd_1230380 := by exact prefixLift 1230380
  have htrace : WordTrace (prefixWord ++ tailWord_1230380) baseStart_1230380 baseEnd_1230380 := by
    simpa [prefixWord, tailWord_1230380, baseEnd_1230380] using wordTrace_append hprefix tailTrace_1230380
  have hstable : (prefixWord ++ tailWord_1230380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230380).length < 2 ^ (prefixWord ++ tailWord_1230380).sum := by decide
  have hdescent : baseEnd_1230380 < baseStart_1230380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230394 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2]
def baseStart_1230394 : Nat := 118140960795 + 1230394 * 2 ^ 59
def prefixEnd_1230394 : Nat := 4983230072969 + 3 ^ 40 * 1230394 * 2
def baseEnd_1230394 : Nat := 631783516408164311516527

theorem tailTrace_1230394 : CollatzResearch.WordTrace tailWord_1230394 prefixEnd_1230394 631783516408164311516527 := by
  unfold tailWord_1230394
  simp only [CollatzResearch.WordTrace]
  refine ⟨11219038976125036852660559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29917437269666764940428157 11219038976125036852660559)
  ·
    refine ⟨16828558464187555278990839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11219038976125036852660559 16828558464187555278990839)
    ·
      refine ⟨25242837696281332918486259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16828558464187555278990839 25242837696281332918486259)
      ·
        refine ⟨37864256544421999377729389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25242837696281332918486259 37864256544421999377729389)
        ·
          refine ⟨14199096204158249766648521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37864256544421999377729389 14199096204158249766648521)
          ·
            refine ⟨10649322153118687324986391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14199096204158249766648521 10649322153118687324986391)
            ·
              refine ⟨15973983229678030987479587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10649322153118687324986391 15973983229678030987479587)
              ·
                refine ⟨23960974844517046481219381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15973983229678030987479587 23960974844517046481219381)
                ·
                  refine ⟨2246341391673473107614317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23960974844517046481219381 2246341391673473107614317)
                  ·
                    refine ⟨842378021877552415355369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2246341391673473107614317 842378021877552415355369)
                    ·
                      refine ⟨631783516408164311516527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 842378021877552415355369 631783516408164311516527)
                      ·
                        rfl

theorem cell23_1230394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2].length) (baseStart_1230394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230394 prefixEnd_1230394 := by exact prefixLift 1230394
  have htrace : WordTrace (prefixWord ++ tailWord_1230394) baseStart_1230394 baseEnd_1230394 := by
    simpa [prefixWord, tailWord_1230394, baseEnd_1230394] using wordTrace_append hprefix tailTrace_1230394
  have hstable : (prefixWord ++ tailWord_1230394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230394).length < 2 ^ (prefixWord ++ tailWord_1230394).sum := by decide
  have hdescent : baseEnd_1230394 < baseStart_1230394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230401 : List Nat := [1, 2, 5, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_1230401 : Nat := 118140960795 + 1230401 * 2 ^ 59
def prefixEnd_1230401 : Nat := 4983230072969 + 3 ^ 40 * 1230401 * 2
def baseEnd_1230401 : Nat := 631787110772745784128995

theorem tailTrace_1230401 : CollatzResearch.WordTrace tailWord_1230401 prefixEnd_1230401 631787110772745784128995 := by
  unfold tailWord_1230401
  simp only [CollatzResearch.WordTrace]
  refine ⟨44876411215474787606147057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29917607476983191737431371 44876411215474787606147057)
  ·
    refine ⟨33657308411606090704610293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44876411215474787606147057 33657308411606090704610293)
    ·
      refine ⟨3155372663588071003557215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33657308411606090704610293 3155372663588071003557215)
      ·
        refine ⟨4733058995382106505335823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3155372663588071003557215 4733058995382106505335823)
        ·
          refine ⟨7099588493073159758003735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4733058995382106505335823 7099588493073159758003735)
          ·
            refine ⟨10649382739609739637005603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7099588493073159758003735 10649382739609739637005603)
            ·
              refine ⟨15974074109414609455508405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10649382739609739637005603 15974074109414609455508405)
              ·
                refine ⟨1497569447757619636453913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15974074109414609455508405 1497569447757619636453913)
                ·
                  refine ⟨1123177085818214727340435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1497569447757619636453913 1123177085818214727340435)
                  ·
                    refine ⟨1684765628727322091010653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1123177085818214727340435 1684765628727322091010653)
                    ·
                      refine ⟨631787110772745784128995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1684765628727322091010653 631787110772745784128995)
                      ·
                        rfl

theorem cell23_1230401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_1230401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230401 prefixEnd_1230401 := by exact prefixLift 1230401
  have htrace : WordTrace (prefixWord ++ tailWord_1230401) baseStart_1230401 baseEnd_1230401 := by
    simpa [prefixWord, tailWord_1230401, baseEnd_1230401] using wordTrace_append hprefix tailTrace_1230401
  have hstable : (prefixWord ++ tailWord_1230401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230401).length < 2 ^ (prefixWord ++ tailWord_1230401).sum := by decide
  have hdescent : baseEnd_1230401 < baseStart_1230401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230428 : List Nat := [2, 2, 4, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_1230428 : Nat := 118140960795 + 1230428 * 2 ^ 59
def prefixEnd_1230428 : Nat := 4983230072969 + 3 ^ 40 * 1230428 * 2
def baseEnd_1230428 : Nat := 631800974750417178491371

theorem tailTrace_1230428 : CollatzResearch.WordTrace tailWord_1230428 prefixEnd_1230428 631800974750417178491371 := by
  unfold tailWord_1230428
  simp only [CollatzResearch.WordTrace]
  refine ⟨22438697993188485608689969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29918263990917980811586625 22438697993188485608689969)
  ·
    refine ⟨16829023494891364206517477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22438697993188485608689969 16829023494891364206517477)
    ·
      refine ⟨3155441905292130788722027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16829023494891364206517477 3155441905292130788722027)
      ·
        refine ⟨4733162857938196183083041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3155441905292130788722027 4733162857938196183083041)
        ·
          refine ⟨3549872143453647137312281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4733162857938196183083041 3549872143453647137312281)
          ·
            refine ⟨2662404107590235352984211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3549872143453647137312281 2662404107590235352984211)
            ·
              refine ⟨3993606161385353029476317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2662404107590235352984211 3993606161385353029476317)
              ·
                refine ⟨1497602310519507386053619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3993606161385353029476317 1497602310519507386053619)
                ·
                  refine ⟨2246403465779261079080429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1497602310519507386053619 2246403465779261079080429)
                  ·
                    refine ⟨842401299667222904655161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2246403465779261079080429 842401299667222904655161)
                    ·
                      refine ⟨631800974750417178491371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 842401299667222904655161 631800974750417178491371)
                      ·
                        rfl

theorem cell23_1230428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_1230428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230428 prefixEnd_1230428 := by exact prefixLift 1230428
  have htrace : WordTrace (prefixWord ++ tailWord_1230428) baseStart_1230428 baseEnd_1230428 := by
    simpa [prefixWord, tailWord_1230428, baseEnd_1230428] using wordTrace_append hprefix tailTrace_1230428
  have hstable : (prefixWord ++ tailWord_1230428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230428).length < 2 ^ (prefixWord ++ tailWord_1230428).sum := by decide
  have hdescent : baseEnd_1230428 < baseStart_1230428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230498 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 7]
def baseStart_1230498 : Nat := 118140960795 + 1230498 * 2 ^ 59
def prefixEnd_1230498 : Nat := 4983230072969 + 3 ^ 40 * 1230498 * 2
def baseEnd_1230498 : Nat := 70204102044025767179561

theorem tailTrace_1230498 : CollatzResearch.WordTrace tailWord_1230498 prefixEnd_1230498 70204102044025767179561 := by
  unfold tailWord_1230498
  simp only [CollatzResearch.WordTrace]
  refine ⟨11219987274030843293107037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29919966064082248781618765 11219987274030843293107037)
  ·
    refine ⟨4207495227761566234915139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11219987274030843293107037 4207495227761566234915139)
    ·
      refine ⟨6311242841642349352372709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4207495227761566234915139 6311242841642349352372709)
      ·
        refine ⟨1183358032807940503569883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6311242841642349352372709 1183358032807940503569883)
        ·
          refine ⟨1775037049211910755354825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183358032807940503569883 1775037049211910755354825)
          ·
            refine ⟨1331277786908933066516119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1775037049211910755354825 1331277786908933066516119)
            ·
              refine ⟨1996916680363399599774179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331277786908933066516119 1996916680363399599774179)
              ·
                refine ⟨2995375020545099399661269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1996916680363399599774179 2995375020545099399661269)
                ·
                  refine ⟨70204102044025767179561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2995375020545099399661269 70204102044025767179561)
                  ·
                    rfl

theorem cell23_1230498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_1230498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230498 prefixEnd_1230498 := by exact prefixLift 1230498
  have htrace : WordTrace (prefixWord ++ tailWord_1230498) baseStart_1230498 baseEnd_1230498 := by
    simpa [prefixWord, tailWord_1230498, baseEnd_1230498] using wordTrace_append hprefix tailTrace_1230498
  have hstable : (prefixWord ++ tailWord_1230498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230498).length < 2 ^ (prefixWord ++ tailWord_1230498).sum := by decide
  have hdescent : baseEnd_1230498 < baseStart_1230498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230554 : List Nat := [3, 1, 1, 2, 2, 3, 1, 4, 6]
def baseStart_1230554 : Nat := 118140960795 + 1230554 * 2 ^ 59
def prefixEnd_1230554 : Nat := 4983230072969 + 3 ^ 40 * 1230554 * 2
def baseEnd_1230554 : Nat := 70207297034764853946199

theorem tailTrace_1230554 : CollatzResearch.WordTrace tailWord_1230554 prefixEnd_1230554 70207297034764853946199 := by
  unfold tailWord_1230554
  simp only [CollatzResearch.WordTrace]
  refine ⟨11220497895980123684116679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29921327722613663157644477 11220497895980123684116679)
  ·
    refine ⟨16830746843970185526175019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11220497895980123684116679 16830746843970185526175019)
    ·
      refine ⟨25246120265955278289262529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16830746843970185526175019 25246120265955278289262529)
      ·
        refine ⟨18934590199466458716946897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25246120265955278289262529 18934590199466458716946897)
        ·
          refine ⟨14200942649599844037710173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18934590199466458716946897 14200942649599844037710173)
          ·
            refine ⟨5325353493599941514141315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14200942649599844037710173 5325353493599941514141315)
            ·
              refine ⟨7988030240399912271211973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5325353493599941514141315 7988030240399912271211973)
              ·
                refine ⟨1497755670074983550852245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7988030240399912271211973 1497755670074983550852245)
                ·
                  refine ⟨70207297034764853946199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1497755670074983550852245 70207297034764853946199)
                  ·
                    rfl

theorem cell23_1230554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 6].length) (baseStart_1230554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230554 prefixEnd_1230554 := by exact prefixLift 1230554
  have htrace : WordTrace (prefixWord ++ tailWord_1230554) baseStart_1230554 baseEnd_1230554 := by
    simpa [prefixWord, tailWord_1230554, baseEnd_1230554] using wordTrace_append hprefix tailTrace_1230554
  have hstable : (prefixWord ++ tailWord_1230554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230554).length < 2 ^ (prefixWord ++ tailWord_1230554).sum := by decide
  have hdescent : baseEnd_1230554 < baseStart_1230554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230615 : List Nat := [1, 1, 3, 4, 2, 1, 2, 4, 1, 1, 3]
def baseStart_1230615 : Nat := 118140960795 + 1230615 * 2 ^ 59
def prefixEnd_1230615 : Nat := 4983230072969 + 3 ^ 40 * 1230615 * 2
def baseEnd_1230615 : Nat := 631896995632807946853011

theorem tailTrace_1230615 : CollatzResearch.WordTrace tailWord_1230615 prefixEnd_1230615 631896995632807946853011 := by
  unfold tailWord_1230615
  simp only [CollatzResearch.WordTrace]
  refine ⟨44884216436699502154437299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29922810957799668102958199 44884216436699502154437299)
  ·
    refine ⟨67326324655049253231655949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44884216436699502154437299 67326324655049253231655949)
    ·
      refine ⟨25247371745643469961870981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67326324655049253231655949 25247371745643469961870981)
      ·
        refine ⟨4733882202308150617850809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25247371745643469961870981 4733882202308150617850809)
        ·
          refine ⟨3550411651731112963388107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4733882202308150617850809 3550411651731112963388107)
          ·
            refine ⟨5325617477596669445082161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3550411651731112963388107 5325617477596669445082161)
            ·
              refine ⟨3994213108197502083811621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5325617477596669445082161 3994213108197502083811621)
              ·
                refine ⟨748914957787031640714679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3994213108197502083811621 748914957787031640714679)
                ·
                  refine ⟨1123372436680547461072019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748914957787031640714679 1123372436680547461072019)
                  ·
                    refine ⟨1685058655020821191608029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1123372436680547461072019 1685058655020821191608029)
                    ·
                      refine ⟨631896995632807946853011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1685058655020821191608029 631896995632807946853011)
                      ·
                        rfl

theorem cell23_1230615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_1230615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230615 prefixEnd_1230615 := by exact prefixLift 1230615
  have htrace : WordTrace (prefixWord ++ tailWord_1230615) baseStart_1230615 baseEnd_1230615 := by
    simpa [prefixWord, tailWord_1230615, baseEnd_1230615] using wordTrace_append hprefix tailTrace_1230615
  have hstable : (prefixWord ++ tailWord_1230615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230615).length < 2 ^ (prefixWord ++ tailWord_1230615).sum := by decide
  have hdescent : baseEnd_1230615 < baseStart_1230615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230622 : List Nat := [4, 3, 2, 2, 1, 1, 3, 1, 6]
def baseStart_1230622 : Nat := 118140960795 + 1230622 * 2 ^ 59
def prefixEnd_1230622 : Nat := 4983230072969 + 3 ^ 40 * 1230622 * 2
def baseEnd_1230622 : Nat := 70211176666376602162831

theorem tailTrace_1230622 : CollatzResearch.WordTrace tailWord_1230622 prefixEnd_1230622 70211176666376602162831 := by
  unfold tailWord_1230622
  simp only [CollatzResearch.WordTrace]
  refine ⟨5610558968459267793742765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29922981165116094899961413 5610558968459267793742765)
  ·
    refine ⟨2103959613172225422653537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5610558968459267793742765 2103959613172225422653537)
    ·
      refine ⟨1577969709879169066990153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2103959613172225422653537 1577969709879169066990153)
      ·
        refine ⟨1183477282409376800242615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1577969709879169066990153 1183477282409376800242615)
        ·
          refine ⟨1775215923614065200363923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183477282409376800242615 1775215923614065200363923)
          ·
            refine ⟨2662823885421097800545885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1775215923614065200363923 2662823885421097800545885)
            ·
              refine ⟨998558957032911675204707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2662823885421097800545885 998558957032911675204707)
              ·
                refine ⟨1497838435549367512807061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998558957032911675204707 1497838435549367512807061)
                ·
                  refine ⟨70211176666376602162831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1497838435549367512807061 70211176666376602162831)
                  ·
                    rfl

theorem cell23_1230622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_1230622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230622 prefixEnd_1230622 := by exact prefixLift 1230622
  have htrace : WordTrace (prefixWord ++ tailWord_1230622) baseStart_1230622 baseEnd_1230622 := by
    simpa [prefixWord, tailWord_1230622, baseEnd_1230622] using wordTrace_append hprefix tailTrace_1230622
  have hstable : (prefixWord ++ tailWord_1230622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230622).length < 2 ^ (prefixWord ++ tailWord_1230622).sum := by decide
  have hdescent : baseEnd_1230622 < baseStart_1230622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230649 : List Nat := [1, 2, 1, 7, 1, 2, 1, 3, 1, 1, 3]
def baseStart_1230649 : Nat := 118140960795 + 1230649 * 2 ^ 59
def prefixEnd_1230649 : Nat := 4983230072969 + 3 ^ 40 * 1230649 * 2
def baseEnd_1230649 : Nat := 631914453975060813827855

theorem tailTrace_1230649 : CollatzResearch.WordTrace tailWord_1230649 prefixEnd_1230649 631914453975060813827855 := by
  unfold tailWord_1230649
  simp only [CollatzResearch.WordTrace]
  refine ⟨44885456518576325961175001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29923637679050883974116667 44885456518576325961175001)
  ·
    refine ⟨33664092388932244470881251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44885456518576325961175001 33664092388932244470881251)
    ·
      refine ⟨50496138583398366706321877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33664092388932244470881251 50496138583398366706321877)
      ·
        refine ⟨1183503248048399219679419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 50496138583398366706321877 1183503248048399219679419)
        ·
          refine ⟨1775254872072598829519129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183503248048399219679419 1775254872072598829519129)
          ·
            refine ⟨1331441154054449122139347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1775254872072598829519129 1331441154054449122139347)
            ·
              refine ⟨1997161731081673683209021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331441154054449122139347 1997161731081673683209021)
              ·
                refine ⟨748935649155627631203383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1997161731081673683209021 748935649155627631203383)
                ·
                  refine ⟨1123403473733441446805075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748935649155627631203383 1123403473733441446805075)
                  ·
                    refine ⟨1685105210600162170207613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1123403473733441446805075 1685105210600162170207613)
                    ·
                      refine ⟨631914453975060813827855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1685105210600162170207613 631914453975060813827855)
                      ·
                        rfl

theorem cell23_1230649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_1230649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230649 prefixEnd_1230649 := by exact prefixLift 1230649
  have htrace : WordTrace (prefixWord ++ tailWord_1230649) baseStart_1230649 baseEnd_1230649 := by
    simpa [prefixWord, tailWord_1230649, baseEnd_1230649] using wordTrace_append hprefix tailTrace_1230649
  have hstable : (prefixWord ++ tailWord_1230649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230649).length < 2 ^ (prefixWord ++ tailWord_1230649).sum := by decide
  have hdescent : baseEnd_1230649 < baseStart_1230649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230692 : List Nat := [2, 3, 1, 1, 6, 1, 1, 2, 1, 2, 3]
def baseStart_1230692 : Nat := 118140960795 + 1230692 * 2 ^ 59
def prefixEnd_1230692 : Nat := 4983230072969 + 3 ^ 40 * 1230692 * 2
def baseEnd_1230692 : Nat := 631936533643204145590157

theorem tailTrace_1230692 : CollatzResearch.WordTrace tailWord_1230692 prefixEnd_1230692 631936533643204145590157 := by
  unfold tailWord_1230692
  simp only [CollatzResearch.WordTrace]
  refine ⟨22443512428710272152495165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29924683238280362869993553 22443512428710272152495165)
  ·
    refine ⟨8416317160766352057185687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22443512428710272152495165 8416317160766352057185687)
    ·
      refine ⟨12624475741149528085778531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8416317160766352057185687 12624475741149528085778531)
      ·
        refine ⟨18936713611724292128667797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12624475741149528085778531 18936713611724292128667797)
        ·
          refine ⟨887658450549576193531303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18936713611724292128667797 887658450549576193531303)
          ·
            refine ⟨1331487675824364290296955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887658450549576193531303 1331487675824364290296955)
            ·
              refine ⟨1997231513736546435445433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331487675824364290296955 1997231513736546435445433)
              ·
                refine ⟨1497923635302409826584075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1997231513736546435445433 1497923635302409826584075)
                ·
                  refine ⟨2246885452953614739876113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1497923635302409826584075 2246885452953614739876113)
                  ·
                    refine ⟨1685164089715211054907085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2246885452953614739876113 1685164089715211054907085)
                    ·
                      refine ⟨631936533643204145590157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1685164089715211054907085 631936533643204145590157)
                      ·
                        rfl

theorem cell23_1230692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_1230692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230692 prefixEnd_1230692 := by exact prefixLift 1230692
  have htrace : WordTrace (prefixWord ++ tailWord_1230692) baseStart_1230692 baseEnd_1230692 := by
    simpa [prefixWord, tailWord_1230692, baseEnd_1230692] using wordTrace_append hprefix tailTrace_1230692
  have hstable : (prefixWord ++ tailWord_1230692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230692).length < 2 ^ (prefixWord ++ tailWord_1230692).sum := by decide
  have hdescent : baseEnd_1230692 < baseStart_1230692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230704 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 4, 6]
def baseStart_1230704 : Nat := 118140960795 + 1230704 * 2 ^ 59
def prefixEnd_1230704 : Nat := 4983230072969 + 3 ^ 40 * 1230704 * 2
def baseEnd_1230704 : Nat := 210647565137019366213367

theorem tailTrace_1230704 : CollatzResearch.WordTrace tailWord_1230704 prefixEnd_1230704 210647565137019366213367 := by
  unfold tailWord_1230704
  simp only [CollatzResearch.WordTrace]
  refine ⟨22443731266688535177213583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29924975022251380236284777 22443731266688535177213583)
  ·
    refine ⟨33665596900032802765820375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22443731266688535177213583 33665596900032802765820375)
    ·
      refine ⟨50498395350049204148730563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33665596900032802765820375 50498395350049204148730563)
      ·
        refine ⟨75747593025073806223095845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50498395350049204148730563 75747593025073806223095845)
        ·
          refine ⟨14202673692201338666830471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75747593025073806223095845 14202673692201338666830471)
          ·
            refine ⟨21304010538302008000245707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14202673692201338666830471 21304010538302008000245707)
            ·
              refine ⟨31956015807453012000368561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21304010538302008000245707 31956015807453012000368561)
              ·
                refine ⟨23967011855589759000276421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31956015807453012000368561 23967011855589759000276421)
                ·
                  refine ⟨4493814722923079812551829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23967011855589759000276421 4493814722923079812551829)
                  ·
                    refine ⟨210647565137019366213367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4493814722923079812551829 210647565137019366213367)
                    ·
                      rfl

theorem cell23_1230704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 4, 6].length) (baseStart_1230704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230704 prefixEnd_1230704 := by exact prefixLift 1230704
  have htrace : WordTrace (prefixWord ++ tailWord_1230704) baseStart_1230704 baseEnd_1230704 := by
    simpa [prefixWord, tailWord_1230704, baseEnd_1230704] using wordTrace_append hprefix tailTrace_1230704
  have hstable : (prefixWord ++ tailWord_1230704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230704).length < 2 ^ (prefixWord ++ tailWord_1230704).sum := by decide
  have hdescent : baseEnd_1230704 < baseStart_1230704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230738 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 2, 6]
def baseStart_1230738 : Nat := 118140960795 + 1230738 * 2 ^ 59
def prefixEnd_1230738 : Nat := 4983230072969 + 3 ^ 40 * 1230738 * 2
def baseEnd_1230738 : Nat := 210653384584436988538315

theorem tailTrace_1230738 : CollatzResearch.WordTrace tailWord_1230738 prefixEnd_1230738 210653384584436988538315 := by
  unfold tailWord_1230738
  simp only [CollatzResearch.WordTrace]
  refine ⟨11222175653813473540291217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29925801743502596107443245 11222175653813473540291217)
  ·
    refine ⟨8416631740360105155218413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11222175653813473540291217 8416631740360105155218413)
    ·
      refine ⟨3156236902635039433206905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8416631740360105155218413 3156236902635039433206905)
      ·
        refine ⟨2367177676976279574905179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3156236902635039433206905 2367177676976279574905179)
        ·
          refine ⟨3550766515464419362357769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2367177676976279574905179 3550766515464419362357769)
          ·
            refine ⟨2663074886598314521768327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3550766515464419362357769 2663074886598314521768327)
            ·
              refine ⟨3994612329897471782652491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2663074886598314521768327 3994612329897471782652491)
              ·
                refine ⟨5991918494846207673978737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3994612329897471782652491 5991918494846207673978737)
                ·
                  refine ⟨4493938871134655755484053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5991918494846207673978737 4493938871134655755484053)
                  ·
                    refine ⟨210653384584436988538315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4493938871134655755484053 210653384584436988538315)
                    ·
                      rfl

theorem cell23_1230738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_1230738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230738 prefixEnd_1230738 := by exact prefixLift 1230738
  have htrace : WordTrace (prefixWord ++ tailWord_1230738) baseStart_1230738 baseEnd_1230738 := by
    simpa [prefixWord, tailWord_1230738, baseEnd_1230738] using wordTrace_append hprefix tailTrace_1230738
  have hstable : (prefixWord ++ tailWord_1230738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230738).length < 2 ^ (prefixWord ++ tailWord_1230738).sum := by decide
  have hdescent : baseEnd_1230738 < baseStart_1230738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230741 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_1230741 : Nat := 118140960795 + 1230741 * 2 ^ 59
def prefixEnd_1230741 : Nat := 4983230072969 + 3 ^ 40 * 1230741 * 2
def baseEnd_1230741 : Nat := 631961694195274453877431

theorem tailTrace_1230741 : CollatzResearch.WordTrace tailWord_1230741 prefixEnd_1230741 631961694195274453877431 := by
  unfold tailWord_1230741
  simp only [CollatzResearch.WordTrace]
  refine ⟨44888812034243025673524077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29925874689495350449016051 44888812034243025673524077)
  ·
    refine ⟨16833304512841134627571529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44888812034243025673524077 16833304512841134627571529)
    ·
      refine ⟨12624978384630850970678647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16833304512841134627571529 12624978384630850970678647)
      ·
        refine ⟨18937467576946276456017971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12624978384630850970678647 18937467576946276456017971)
        ·
          refine ⟨28406201365419414684026957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18937467576946276456017971 28406201365419414684026957)
          ·
            refine ⟨10652325512032280506510109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28406201365419414684026957 10652325512032280506510109)
            ·
              refine ⟨3994622067012105189941291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10652325512032280506510109 3994622067012105189941291)
              ·
                refine ⟨5991933100518157784911937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3994622067012105189941291 5991933100518157784911937)
                ·
                  refine ⟨4493949825388618338683953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5991933100518157784911937 4493949825388618338683953)
                  ·
                    refine ⟨3370462369041463754012965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4493949825388618338683953 3370462369041463754012965)
                    ·
                      refine ⟨631961694195274453877431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3370462369041463754012965 631961694195274453877431)
                      ·
                        rfl

theorem cell23_1230741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_1230741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230741 prefixEnd_1230741 := by exact prefixLift 1230741
  have htrace : WordTrace (prefixWord ++ tailWord_1230741) baseStart_1230741 baseEnd_1230741 := by
    simpa [prefixWord, tailWord_1230741, baseEnd_1230741] using wordTrace_append hprefix tailTrace_1230741
  have hstable : (prefixWord ++ tailWord_1230741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230741).length < 2 ^ (prefixWord ++ tailWord_1230741).sum := by decide
  have hdescent : baseEnd_1230741 < baseStart_1230741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230745 : List Nat := [1, 2, 1, 2, 1, 3, 4, 3, 2, 2, 2]
def baseStart_1230745 : Nat := 118140960795 + 1230745 * 2 ^ 59
def prefixEnd_1230745 : Nat := 4983230072969 + 3 ^ 40 * 1230745 * 2
def baseEnd_1230745 : Nat := 631963748117892438227413

theorem tailTrace_1230745 : CollatzResearch.WordTrace tailWord_1230745 prefixEnd_1230745 631963748117892438227413 := by
  unfold tailWord_1230745
  simp only [CollatzResearch.WordTrace]
  refine ⟨44888957926228534356669689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29925971950819022904446459 44888957926228534356669689)
  ·
    refine ⟨33666718444671400767502267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44888957926228534356669689 33666718444671400767502267)
    ·
      refine ⟨50500077667007101151253401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33666718444671400767502267 50500077667007101151253401)
      ·
        refine ⟨37875058250255325863440051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50500077667007101151253401 37875058250255325863440051)
        ·
          refine ⟨56812587375382988795160077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37875058250255325863440051 56812587375382988795160077)
          ·
            refine ⟨21304720265768620798185029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56812587375382988795160077 21304720265768620798185029)
            ·
              refine ⟨3994635049831616399659693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21304720265768620798185029 3994635049831616399659693)
              ·
                refine ⟨1497988143686856149872385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3994635049831616399659693 1497988143686856149872385)
                ·
                  refine ⟨1123491107765142112404289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1497988143686856149872385 1123491107765142112404289)
                  ·
                    refine ⟨842618330823856584303217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1123491107765142112404289 842618330823856584303217)
                    ·
                      refine ⟨631963748117892438227413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 842618330823856584303217 631963748117892438227413)
                      ·
                        rfl

theorem cell23_1230745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 2, 2].length) (baseStart_1230745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230745 prefixEnd_1230745 := by exact prefixLift 1230745
  have htrace : WordTrace (prefixWord ++ tailWord_1230745) baseStart_1230745 baseEnd_1230745 := by
    simpa [prefixWord, tailWord_1230745, baseEnd_1230745] using wordTrace_append hprefix tailTrace_1230745
  have hstable : (prefixWord ++ tailWord_1230745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230745).length < 2 ^ (prefixWord ++ tailWord_1230745).sum := by decide
  have hdescent : baseEnd_1230745 < baseStart_1230745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230766 : List Nat := [4, 1, 5, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_1230766 : Nat := 118140960795 + 1230766 * 2 ^ 59
def prefixEnd_1230766 : Nat := 4983230072969 + 3 ^ 40 * 1230766 * 2
def baseEnd_1230766 : Nat := 631974531211636856064817

theorem tailTrace_1230766 : CollatzResearch.WordTrace tailWord_1230766 prefixEnd_1230766 631974531211636856064817 := by
  unfold tailWord_1230766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5611215482394056867898019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29926482572768303295456101 5611215482394056867898019)
  ·
    refine ⟨8416823223591085301847029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5611215482394056867898019 8416823223591085301847029)
    ·
      refine ⟨789077177211664247048159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8416823223591085301847029 789077177211664247048159)
      ·
        refine ⟨1183615765817496370572239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789077177211664247048159 1183615765817496370572239)
        ·
          refine ⟨1775423648726244555858359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183615765817496370572239 1775423648726244555858359)
          ·
            refine ⟨2663135473089366833787539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1775423648726244555858359 2663135473089366833787539)
            ·
              refine ⟨3994703209634050250681309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2663135473089366833787539 3994703209634050250681309)
              ·
                refine ⟨1498013703612768844005491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3994703209634050250681309 1498013703612768844005491)
                ·
                  refine ⟨2247020555419153266008237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498013703612768844005491 2247020555419153266008237)
                  ·
                    refine ⟨842632708282182474753089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2247020555419153266008237 842632708282182474753089)
                    ·
                      refine ⟨631974531211636856064817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 842632708282182474753089 631974531211636856064817)
                      ·
                        rfl

theorem cell23_1230766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_1230766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230766 prefixEnd_1230766 := by exact prefixLift 1230766
  have htrace : WordTrace (prefixWord ++ tailWord_1230766) baseStart_1230766 baseEnd_1230766 := by
    simpa [prefixWord, tailWord_1230766, baseEnd_1230766] using wordTrace_append hprefix tailTrace_1230766
  have hstable : (prefixWord ++ tailWord_1230766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230766).length < 2 ^ (prefixWord ++ tailWord_1230766).sum := by decide
  have hdescent : baseEnd_1230766 < baseStart_1230766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230801 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 6, 1, 4]
def baseStart_1230801 : Nat := 118140960795 + 1230801 * 2 ^ 59
def prefixEnd_1230801 : Nat := 4983230072969 + 3 ^ 40 * 1230801 * 2
def baseEnd_1230801 : Nat := 631992503034544219127155

theorem tailTrace_1230801 : CollatzResearch.WordTrace tailWord_1230801 prefixEnd_1230801 631992503034544219127155 := by
  unfold tailWord_1230801
  simp only [CollatzResearch.WordTrace]
  refine ⟨44891000414025655920708257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29927333609350437280472171 44891000414025655920708257)
  ·
    refine ⟨33668250310519241940531193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44891000414025655920708257 33668250310519241940531193)
    ·
      refine ⟨25251187732889431455398395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33668250310519241940531193 25251187732889431455398395)
      ·
        refine ⟨37876781599334147183097593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25251187732889431455398395 37876781599334147183097593)
        ·
          refine ⟨28407586199500610387323195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37876781599334147183097593 28407586199500610387323195)
          ·
            refine ⟨42611379299250915580984793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28407586199500610387323195 42611379299250915580984793)
            ·
              refine ⟨31958534474438186685738595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42611379299250915580984793 31958534474438186685738595)
              ·
                refine ⟨47937801711657280028607893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31958534474438186685738595 47937801711657280028607893)
                ·
                  refine ⟨2247084455233935001340995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47937801711657280028607893 2247084455233935001340995)
                  ·
                    refine ⟨3370626682850902502011493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2247084455233935001340995 3370626682850902502011493)
                    ·
                      refine ⟨631992503034544219127155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3370626682850902502011493 631992503034544219127155)
                      ·
                        rfl

theorem cell23_1230801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_1230801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230801 prefixEnd_1230801 := by exact prefixLift 1230801
  have htrace : WordTrace (prefixWord ++ tailWord_1230801) baseStart_1230801 baseEnd_1230801 := by
    simpa [prefixWord, tailWord_1230801, baseEnd_1230801] using wordTrace_append hprefix tailTrace_1230801
  have hstable : (prefixWord ++ tailWord_1230801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230801).length < 2 ^ (prefixWord ++ tailWord_1230801).sum := by decide
  have hdescent : baseEnd_1230801 < baseStart_1230801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230841 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 8]
def baseStart_1230841 : Nat := 118140960795 + 1230841 * 2 ^ 59
def prefixEnd_1230841 : Nat := 4983230072969 + 3 ^ 40 * 1230841 * 2
def baseEnd_1230841 : Nat := 70223671362302673625219

theorem tailTrace_1230841 : CollatzResearch.WordTrace tailWord_1230841 prefixEnd_1230841 70223671362302673625219 := by
  unfold tailWord_1230841
  simp only [CollatzResearch.WordTrace]
  refine ⟨44892459333880742752164377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29928306222587161834776251 44892459333880742752164377)
  ·
    refine ⟨33669344500410557064123283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44892459333880742752164377 33669344500410557064123283)
    ·
      refine ⟨50504016750615835596184925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33669344500410557064123283 50504016750615835596184925)
      ·
        refine ⟨18939006281480938348569347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50504016750615835596184925 18939006281480938348569347)
        ·
          refine ⟨28408509422221407522854021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18939006281480938348569347 28408509422221407522854021)
          ·
            refine ⟨5326595516666513910535129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28408509422221407522854021 5326595516666513910535129)
            ·
              refine ⟨3994946637499885432901347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5326595516666513910535129 3994946637499885432901347)
              ·
                refine ⟨5992419956249828149352021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3994946637499885432901347 5992419956249828149352021)
                ·
                  refine ⟨70223671362302673625219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5992419956249828149352021 70223671362302673625219)
                  ·
                    rfl

theorem cell23_1230841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 8].length) (baseStart_1230841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230841 prefixEnd_1230841 := by exact prefixLift 1230841
  have htrace : WordTrace (prefixWord ++ tailWord_1230841) baseStart_1230841 baseEnd_1230841 := by
    simpa [prefixWord, tailWord_1230841, baseEnd_1230841] using wordTrace_append hprefix tailTrace_1230841
  have hstable : (prefixWord ++ tailWord_1230841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230841).length < 2 ^ (prefixWord ++ tailWord_1230841).sum := by decide
  have hdescent : baseEnd_1230841 < baseStart_1230841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230845 : List Nat := [1, 4, 1, 1, 1, 2, 2, 6, 1, 4]
def baseStart_1230845 : Nat := 118140960795 + 1230845 * 2 ^ 59
def prefixEnd_1230845 : Nat := 4983230072969 + 3 ^ 40 * 1230845 * 2
def baseEnd_1230845 : Nat := 210671698727780682325651

theorem tailTrace_1230845 : CollatzResearch.WordTrace tailWord_1230845 prefixEnd_1230845 210671698727780682325651 := by
  unfold tailWord_1230845
  simp only [CollatzResearch.WordTrace]
  refine ⟨44892605225866251435309989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29928403483910834290206659 44892605225866251435309989)
  ·
    refine ⟨8417363479849922144120623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44892605225866251435309989 8417363479849922144120623)
    ·
      refine ⟨12626045219774883216180935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8417363479849922144120623 12626045219774883216180935)
      ·
        refine ⟨18939067829662324824271403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12626045219774883216180935 18939067829662324824271403)
        ·
          refine ⟨28408601744493487236407105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18939067829662324824271403 28408601744493487236407105)
          ·
            refine ⟨21306451308370115427305329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28408601744493487236407105 21306451308370115427305329)
            ·
              refine ⟨15979838481277586570478997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21306451308370115427305329 15979838481277586570478997)
              ·
                refine ⟨749054928809886870491203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15979838481277586570478997 749054928809886870491203)
                ·
                  refine ⟨1123582393214830305736805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 749054928809886870491203 1123582393214830305736805)
                  ·
                    refine ⟨210671698727780682325651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1123582393214830305736805 210671698727780682325651)
                    ·
                      rfl

theorem cell23_1230845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_1230845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230845 prefixEnd_1230845 := by exact prefixLift 1230845
  have htrace : WordTrace (prefixWord ++ tailWord_1230845) baseStart_1230845 baseEnd_1230845 := by
    simpa [prefixWord, tailWord_1230845, baseEnd_1230845] using wordTrace_append hprefix tailTrace_1230845
  have hstable : (prefixWord ++ tailWord_1230845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230845).length < 2 ^ (prefixWord ++ tailWord_1230845).sum := by decide
  have hdescent : baseEnd_1230845 < baseStart_1230845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230902 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_1230902 : Nat := 118140960795 + 1230902 * 2 ^ 59
def prefixEnd_1230902 : Nat := 4983230072969 + 3 ^ 40 * 1230902 * 2
def baseEnd_1230902 : Nat := 632044364580648323964191

theorem tailTrace_1230902 : CollatzResearch.WordTrace tailWord_1230902 prefixEnd_1230902 632044364580648323964191 := by
  unfold tailWord_1230902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2805917761666234385633435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29929789457773166780089973 2805917761666234385633435)
  ·
    refine ⟨4208876642499351578450153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2805917761666234385633435 4208876642499351578450153)
    ·
      refine ⟨3156657481874513683837615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4208876642499351578450153 3156657481874513683837615)
      ·
        refine ⟨4734986222811770525756423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3156657481874513683837615 4734986222811770525756423)
        ·
          refine ⟨7102479334217655788634635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4734986222811770525756423 7102479334217655788634635)
          ·
            refine ⟨10653719001326483682951953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7102479334217655788634635 10653719001326483682951953)
            ·
              refine ⟨7990289250994862762213965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10653719001326483682951953 7990289250994862762213965)
              ·
                refine ⟨2996358469123073535830237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7990289250994862762213965 2996358469123073535830237)
                ·
                  refine ⟨1123634425921152575936339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2996358469123073535830237 1123634425921152575936339)
                  ·
                    refine ⟨1685451638881728863904509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1123634425921152575936339 1685451638881728863904509)
                    ·
                      refine ⟨632044364580648323964191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1685451638881728863904509 632044364580648323964191)
                      ·
                        rfl

theorem cell23_1230902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_1230902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230902 prefixEnd_1230902 := by exact prefixLift 1230902
  have htrace : WordTrace (prefixWord ++ tailWord_1230902) baseStart_1230902 baseEnd_1230902 := by
    simpa [prefixWord, tailWord_1230902, baseEnd_1230902] using wordTrace_append hprefix tailTrace_1230902
  have hstable : (prefixWord ++ tailWord_1230902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230902).length < 2 ^ (prefixWord ++ tailWord_1230902).sum := by decide
  have hdescent : baseEnd_1230902 < baseStart_1230902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230908 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_1230908 : Nat := 118140960795 + 1230908 * 2 ^ 59
def prefixEnd_1230908 : Nat := 4983230072969 + 3 ^ 40 * 1230908 * 2
def baseEnd_1230908 : Nat := 632047445464575300489163

theorem tailTrace_1230908 : CollatzResearch.WordTrace tailWord_1230908 prefixEnd_1230908 632047445464575300489163 := by
  unfold tailWord_1230908
  simp only [CollatzResearch.WordTrace]
  refine ⟨22447451512319006597426689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29929935349758675463235585 22447451512319006597426689)
  ·
    refine ⟨16835588634239254948070017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22447451512319006597426689 16835588634239254948070017)
    ·
      refine ⟨12626691475679441211052513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16835588634239254948070017 12626691475679441211052513)
      ·
        refine ⟨9470018606759580908289385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12626691475679441211052513 9470018606759580908289385)
        ·
          refine ⟨7102513955069685681217039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9470018606759580908289385 7102513955069685681217039)
          ·
            refine ⟨10653770932604528521825559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7102513955069685681217039 10653770932604528521825559)
            ·
              refine ⟨15980656398906792782738339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10653770932604528521825559 15980656398906792782738339)
              ·
                refine ⟨23970984598360189174107509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15980656398906792782738339 23970984598360189174107509)
                ·
                  refine ⟨2247279806096267735072579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23970984598360189174107509 2247279806096267735072579)
                  ·
                    refine ⟨3370919709144401602608869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2247279806096267735072579 3370919709144401602608869)
                    ·
                      refine ⟨632047445464575300489163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3370919709144401602608869 632047445464575300489163)
                      ·
                        rfl

theorem cell23_1230908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_1230908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230908 prefixEnd_1230908 := by exact prefixLift 1230908
  have htrace : WordTrace (prefixWord ++ tailWord_1230908) baseStart_1230908 baseEnd_1230908 := by
    simpa [prefixWord, tailWord_1230908, baseEnd_1230908] using wordTrace_append hprefix tailTrace_1230908
  have hstable : (prefixWord ++ tailWord_1230908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230908).length < 2 ^ (prefixWord ++ tailWord_1230908).sum := by decide
  have hdescent : baseEnd_1230908 < baseStart_1230908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230925 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1230925 : Nat := 118140960795 + 1230925 * 2 ^ 59
def prefixEnd_1230925 : Nat := 4983230072969 + 3 ^ 40 * 1230925 * 2
def baseEnd_1230925 : Nat := 632056174635701733976585

theorem tailTrace_1230925 : CollatzResearch.WordTrace tailWord_1230925 prefixEnd_1230925 632056174635701733976585 := by
  unfold tailWord_1230925
  simp only [CollatzResearch.WordTrace]
  refine ⟨44895523065576425098222229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29930348710384283398814819 44895523065576425098222229)
  ·
    refine ⟨2104477643698894926479167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44895523065576425098222229 2104477643698894926479167)
    ·
      refine ⟨3156716465548342389718751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2104477643698894926479167 3156716465548342389718751)
      ·
        refine ⟨4735074698322513584578127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3156716465548342389718751 4735074698322513584578127)
        ·
          refine ⟨7102612047483770376867191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4735074698322513584578127 7102612047483770376867191)
          ·
            refine ⟨10653918071225655565300787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7102612047483770376867191 10653918071225655565300787)
            ·
              refine ⟨15980877106838483347951181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10653918071225655565300787 15980877106838483347951181)
              ·
                refine ⟨5992828915064431255481693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15980877106838483347951181 5992828915064431255481693)
                ·
                  refine ⟨2247310843149161720805635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5992828915064431255481693 2247310843149161720805635)
                  ·
                    refine ⟨3370966264723742581208453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2247310843149161720805635 3370966264723742581208453)
                    ·
                      refine ⟨632056174635701733976585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3370966264723742581208453 632056174635701733976585)
                      ·
                        rfl

theorem cell23_1230925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1230925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230925 prefixEnd_1230925 := by exact prefixLift 1230925
  have htrace : WordTrace (prefixWord ++ tailWord_1230925) baseStart_1230925 baseEnd_1230925 := by
    simpa [prefixWord, tailWord_1230925, baseEnd_1230925] using wordTrace_append hprefix tailTrace_1230925
  have hstable : (prefixWord ++ tailWord_1230925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230925).length < 2 ^ (prefixWord ++ tailWord_1230925).sum := by decide
  have hdescent : baseEnd_1230925 < baseStart_1230925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230938 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4]
def baseStart_1230938 : Nat := 118140960795 + 1230938 * 2 ^ 59
def prefixEnd_1230938 : Nat := 4983230072969 + 3 ^ 40 * 1230938 * 2
def baseEnd_1230938 : Nat := 632062849884210183114025

theorem tailTrace_1230938 : CollatzResearch.WordTrace tailWord_1230938 prefixEnd_1230938 632062849884210183114025 := by
  unfold tailWord_1230938
  simp only [CollatzResearch.WordTrace]
  refine ⟨11223999303632332079611367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29930664809686218878963645 11223999303632332079611367)
  ·
    refine ⟨16835998955448498119417051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11223999303632332079611367 16835998955448498119417051)
    ·
      refine ⟨25253998433172747179125577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16835998955448498119417051 25253998433172747179125577)
      ·
        refine ⟨18940498824879560384344183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25253998433172747179125577 18940498824879560384344183)
        ·
          refine ⟨28410748237319340576516275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18940498824879560384344183 28410748237319340576516275)
          ·
            refine ⟨42616122355979010864774413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28410748237319340576516275 42616122355979010864774413)
            ·
              refine ⟨15981045883492129074290405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42616122355979010864774413 15981045883492129074290405)
              ·
                refine ⟨2996446103154774201429451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15981045883492129074290405 2996446103154774201429451)
                ·
                  refine ⟨4494669154732161302144177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2996446103154774201429451 4494669154732161302144177)
                  ·
                    refine ⟨3371001866049120976608133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4494669154732161302144177 3371001866049120976608133)
                    ·
                      refine ⟨632062849884210183114025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3371001866049120976608133 632062849884210183114025)
                      ·
                        rfl

theorem cell23_1230938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_1230938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230938 prefixEnd_1230938 := by exact prefixLift 1230938
  have htrace : WordTrace (prefixWord ++ tailWord_1230938) baseStart_1230938 baseEnd_1230938 := by
    simpa [prefixWord, tailWord_1230938, baseEnd_1230938] using wordTrace_append hprefix tailTrace_1230938
  have hstable : (prefixWord ++ tailWord_1230938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230938).length < 2 ^ (prefixWord ++ tailWord_1230938).sum := by decide
  have hdescent : baseEnd_1230938 < baseStart_1230938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230959 : List Nat := [1, 1, 2, 1, 3, 4, 2, 4, 1, 2, 2]
def baseStart_1230959 : Nat := 118140960795 + 1230959 * 2 ^ 59
def prefixEnd_1230959 : Nat := 4983230072969 + 3 ^ 40 * 1230959 * 2
def baseEnd_1230959 : Nat := 632073632977954600951429

theorem tailTrace_1230959 : CollatzResearch.WordTrace tailWord_1230959 prefixEnd_1230959 632073632977954600951429 := by
  unfold tailWord_1230959
  simp only [CollatzResearch.WordTrace]
  refine ⟨44896763147453248904959931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29931175431635499269973287 44896763147453248904959931)
  ·
    refine ⟨67345144721179873357439897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44896763147453248904959931 67345144721179873357439897)
    ·
      refine ⟨50508858540884905018079923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67345144721179873357439897 50508858540884905018079923)
      ·
        refine ⟨75763287811327357527119885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50508858540884905018079923 75763287811327357527119885)
        ·
          refine ⟨28411232929247759072669957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75763287811327357527119885 28411232929247759072669957)
          ·
            refine ⟨5327106174233954826125617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28411232929247759072669957 5327106174233954826125617)
            ·
              refine ⟨3995329630675466119594213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5327106174233954826125617 3995329630675466119594213)
              ·
                refine ⟨749124305751649897423915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3995329630675466119594213 749124305751649897423915)
                ·
                  refine ⟨1123686458627474846135873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 749124305751649897423915 1123686458627474846135873)
                  ·
                    refine ⟨842764843970606134601905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1123686458627474846135873 842764843970606134601905)
                    ·
                      refine ⟨632073632977954600951429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 842764843970606134601905 632073632977954600951429)
                      ·
                        rfl

theorem cell23_1230959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 1, 2, 2].length) (baseStart_1230959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1230959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1230959 prefixEnd_1230959 := by exact prefixLift 1230959
  have htrace : WordTrace (prefixWord ++ tailWord_1230959) baseStart_1230959 baseEnd_1230959 := by
    simpa [prefixWord, tailWord_1230959, baseEnd_1230959] using wordTrace_append hprefix tailTrace_1230959
  have hstable : (prefixWord ++ tailWord_1230959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230959).length < 2 ^ (prefixWord ++ tailWord_1230959).sum := by decide
  have hdescent : baseEnd_1230959 < baseStart_1230959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231036 : List Nat := [2, 2, 2, 3, 3, 2, 1, 2, 1, 3, 2]
def baseStart_1231036 : Nat := 118140960795 + 1231036 * 2 ^ 59
def prefixEnd_1231036 : Nat := 4983230072969 + 3 ^ 40 * 1231036 * 2
def baseEnd_1231036 : Nat := 632113170988350799688575

theorem tailTrace_1231036 : CollatzResearch.WordTrace tailWord_1231036 prefixEnd_1231036 632113170988350799688575 := by
  unfold tailWord_1231036
  simp only [CollatzResearch.WordTrace]
  refine ⟨22449785784087145527756481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29933047712116194037008641 22449785784087145527756481)
  ·
    refine ⟨16837339338065359145817361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22449785784087145527756481 16837339338065359145817361)
    ·
      refine ⟨12628004503549019359363021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16837339338065359145817361 12628004503549019359363021)
      ·
        refine ⟨4735501688830882259761133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12628004503549019359363021 4735501688830882259761133)
        ·
          refine ⟨1775813133311580847410425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4735501688830882259761133 1775813133311580847410425)
          ·
            refine ⟨1331859849983685635557819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1775813133311580847410425 1331859849983685635557819)
            ·
              refine ⟨1997789774975528453336729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331859849983685635557819 1997789774975528453336729)
              ·
                refine ⟨1498342331231646340002547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1997789774975528453336729 1498342331231646340002547)
                ·
                  refine ⟨2247513496847469510003821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498342331231646340002547 2247513496847469510003821)
                  ·
                    refine ⟨842817561317801066251433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2247513496847469510003821 842817561317801066251433)
                    ·
                      refine ⟨632113170988350799688575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 842817561317801066251433 632113170988350799688575)
                      ·
                        rfl

theorem cell23_1231036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_1231036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231036 prefixEnd_1231036 := by exact prefixLift 1231036
  have htrace : WordTrace (prefixWord ++ tailWord_1231036) baseStart_1231036 baseEnd_1231036 := by
    simpa [prefixWord, tailWord_1231036, baseEnd_1231036] using wordTrace_append hprefix tailTrace_1231036
  have hstable : (prefixWord ++ tailWord_1231036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231036).length < 2 ^ (prefixWord ++ tailWord_1231036).sum := by decide
  have hdescent : baseEnd_1231036 < baseStart_1231036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231055 : List Nat := [1, 1, 2, 1, 1, 3, 4, 5, 5]
def baseStart_1231055 : Nat := 118140960795 + 1231055 * 2 ^ 59
def prefixEnd_1231055 : Nat := 4983230072969 + 3 ^ 40 * 1231055 * 2
def baseEnd_1231055 : Nat := 70235880791198469483443

theorem tailTrace_1231055 : CollatzResearch.WordTrace tailWord_1231055 prefixEnd_1231055 70235880791198469483443 := by
  unfold tailWord_1231055
  simp only [CollatzResearch.WordTrace]
  refine ⟨44900264555105457300454619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29933509703403638200303079 44900264555105457300454619)
  ·
    refine ⟨67350396832658185950681929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44900264555105457300454619 67350396832658185950681929)
    ·
      refine ⟨50512797624493639463011447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67350396832658185950681929 50512797624493639463011447)
      ·
        refine ⟨75769196436740459194517171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50512797624493639463011447 75769196436740459194517171)
        ·
          refine ⟨113653794655110688791775757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75769196436740459194517171 113653794655110688791775757)
          ·
            refine ⟨42620172995666508296915909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113653794655110688791775757 42620172995666508296915909)
            ·
              refine ⟨7991282436687470305671733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42620172995666508296915909 7991282436687470305671733)
              ·
                refine ⟨749182728439450341156725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7991282436687470305671733 749182728439450341156725)
                ·
                  refine ⟨70235880791198469483443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 749182728439450341156725 70235880791198469483443)
                  ·
                    rfl

theorem cell23_1231055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 5].length) (baseStart_1231055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231055 prefixEnd_1231055 := by exact prefixLift 1231055
  have htrace : WordTrace (prefixWord ++ tailWord_1231055) baseStart_1231055 baseEnd_1231055 := by
    simpa [prefixWord, tailWord_1231055, baseEnd_1231055] using wordTrace_append hprefix tailTrace_1231055
  have hstable : (prefixWord ++ tailWord_1231055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231055).length < 2 ^ (prefixWord ++ tailWord_1231055).sum := by decide
  have hdescent : baseEnd_1231055 < baseStart_1231055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231105 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_1231105 : Nat := 118140960795 + 1231105 * 2 ^ 59
def prefixEnd_1231105 : Nat := 4983230072969 + 3 ^ 40 * 1231105 * 2
def baseEnd_1231105 : Nat := 632148601153511029725757

theorem tailTrace_1231105 : CollatzResearch.WordTrace tailWord_1231105 prefixEnd_1231105 632148601153511029725757 := by
  unfold tailWord_1231105
  simp only [CollatzResearch.WordTrace]
  refine ⟨44902088204924315839774769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29934725469949543893183179 44902088204924315839774769)
  ·
    refine ⟨33676566153693236879831077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44902088204924315839774769 33676566153693236879831077)
    ·
      refine ⟨6314356153817481914968327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33676566153693236879831077 6314356153817481914968327)
      ·
        refine ⟨9471534230726222872452491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6314356153817481914968327 9471534230726222872452491)
        ·
          refine ⟨14207301346089334308678737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9471534230726222872452491 14207301346089334308678737)
          ·
            refine ⟨10655476009567000731509053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14207301346089334308678737 10655476009567000731509053)
            ·
              refine ⟨3995803503587625274315895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10655476009567000731509053 3995803503587625274315895)
              ·
                refine ⟨5993705255381437911473843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3995803503587625274315895 5993705255381437911473843)
                ·
                  refine ⟨8990557883072156867210765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5993705255381437911473843 8990557883072156867210765)
                  ·
                    refine ⟨3371459206152058825204037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8990557883072156867210765 3371459206152058825204037)
                    ·
                      refine ⟨632148601153511029725757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3371459206152058825204037 632148601153511029725757)
                      ·
                        rfl

theorem cell23_1231105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_1231105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231105 prefixEnd_1231105 := by exact prefixLift 1231105
  have htrace : WordTrace (prefixWord ++ tailWord_1231105) baseStart_1231105 baseEnd_1231105 := by
    simpa [prefixWord, tailWord_1231105, baseEnd_1231105] using wordTrace_append hprefix tailTrace_1231105
  have hstable : (prefixWord ++ tailWord_1231105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231105).length < 2 ^ (prefixWord ++ tailWord_1231105).sum := by decide
  have hdescent : baseEnd_1231105 < baseStart_1231105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231115 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 5, 4]
def baseStart_1231115 : Nat := 118140960795 + 1231115 * 2 ^ 59
def prefixEnd_1231115 : Nat := 4983230072969 + 3 ^ 40 * 1231115 * 2
def baseEnd_1231115 : Nat := 210717911986685330200237

theorem tailTrace_1231115 : CollatzResearch.WordTrace tailWord_1231115 prefixEnd_1231115 210717911986685330200237 := by
  unfold tailWord_1231115
  simp only [CollatzResearch.WordTrace]
  refine ⟨44902452934888087547638799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29934968623258725031759199 44902452934888087547638799)
  ·
    refine ⟨67353679402332131321458199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44902452934888087547638799 67353679402332131321458199)
    ·
      refine ⟨101030519103498196982187299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67353679402332131321458199 101030519103498196982187299)
      ·
        refine ⟨151545778655247295473280949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101030519103498196982187299 151545778655247295473280949)
        ·
          refine ⟨14207416748929433950620089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151545778655247295473280949 14207416748929433950620089)
          ·
            refine ⟨10655562561697075462965067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14207416748929433950620089 10655562561697075462965067)
            ·
              refine ⟨15983343842545613194447601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10655562561697075462965067 15983343842545613194447601)
              ·
                refine ⟨11987507881909209895835701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15983343842545613194447601 11987507881909209895835701)
                ·
                  refine ⟨1123828863928988427734597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11987507881909209895835701 1123828863928988427734597)
                  ·
                    refine ⟨210717911986685330200237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1123828863928988427734597 210717911986685330200237)
                    ·
                      rfl

theorem cell23_1231115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 4].length) (baseStart_1231115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231115 prefixEnd_1231115 := by exact prefixLift 1231115
  have htrace : WordTrace (prefixWord ++ tailWord_1231115) baseStart_1231115 baseEnd_1231115 := by
    simpa [prefixWord, tailWord_1231115, baseEnd_1231115] using wordTrace_append hprefix tailTrace_1231115
  have hstable : (prefixWord ++ tailWord_1231115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231115).length < 2 ^ (prefixWord ++ tailWord_1231115).sum := by decide
  have hdescent : baseEnd_1231115 < baseStart_1231115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231155 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 3]
def baseStart_1231155 : Nat := 118140960795 + 1231155 * 2 ^ 59
def prefixEnd_1231155 : Nat := 4983230072969 + 3 ^ 40 * 1231155 * 2
def baseEnd_1231155 : Nat := 632174275186235834100527

theorem tailTrace_1231155 : CollatzResearch.WordTrace tailWord_1231155 prefixEnd_1231155 632174275186235834100527 := by
  unfold tailWord_1231155
  simp only [CollatzResearch.WordTrace]
  refine ⟨44903911854743174379094919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29935941236495449586063279 44903911854743174379094919)
  ·
    refine ⟨67355867782114761568642379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44903911854743174379094919 67355867782114761568642379)
    ·
      refine ⟨101033801673172142352963569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67355867782114761568642379 101033801673172142352963569)
      ·
        refine ⟨75775351254879106764722677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101033801673172142352963569 75775351254879106764722677)
        ·
          refine ⟨7103939180144916259192751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75775351254879106764722677 7103939180144916259192751)
          ·
            refine ⟨10655908770217374388789127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7103939180144916259192751 10655908770217374388789127)
            ·
              refine ⟨15983863155326061583183691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10655908770217374388789127 15983863155326061583183691)
              ·
                refine ⟨23975794732989092374775537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15983863155326061583183691 23975794732989092374775537)
                ·
                  refine ⟨17981846049741819281081653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23975794732989092374775537 17981846049741819281081653)
                  ·
                    refine ⟨1685798067163295557601405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17981846049741819281081653 1685798067163295557601405)
                    ·
                      refine ⟨632174275186235834100527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1685798067163295557601405 632174275186235834100527)
                      ·
                        rfl

theorem cell23_1231155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 3].length) (baseStart_1231155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231155 prefixEnd_1231155 := by exact prefixLift 1231155
  have htrace : WordTrace (prefixWord ++ tailWord_1231155) baseStart_1231155 baseEnd_1231155 := by
    simpa [prefixWord, tailWord_1231155, baseEnd_1231155] using wordTrace_append hprefix tailTrace_1231155
  have hstable : (prefixWord ++ tailWord_1231155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231155).length < 2 ^ (prefixWord ++ tailWord_1231155).sum := by decide
  have hdescent : baseEnd_1231155 < baseStart_1231155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231166 : List Nat := [4, 2, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_1231166 : Nat := 118140960795 + 1231166 * 2 ^ 59
def prefixEnd_1231166 : Nat := 4983230072969 + 3 ^ 40 * 1231166 * 2
def baseEnd_1231166 : Nat := 210726641157811763687659

theorem tailTrace_1231166 : CollatzResearch.WordTrace tailWord_1231166 prefixEnd_1231166 210726641157811763687659 := by
  unfold tailWord_1231166
  simp only [CollatzResearch.WordTrace]
  refine ⟨5613039132212915407218169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29936208705135548838496901 5613039132212915407218169)
  ·
    refine ⟨4209779349159686555413627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5613039132212915407218169 4209779349159686555413627)
    ·
      refine ⟨6314669023739529833120441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4209779349159686555413627 6314669023739529833120441)
      ·
        refine ⟨4736001767804647374840331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6314669023739529833120441 4736001767804647374840331)
        ·
          refine ⟨7104002651706971062260497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4736001767804647374840331 7104002651706971062260497)
          ·
            refine ⟨5328001988780228296695373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7104002651706971062260497 5328001988780228296695373)
            ·
              refine ⟨1998000745792585611260765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5328001988780228296695373 1998000745792585611260765)
              ·
                refine ⟨749250279672219604222787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1998000745792585611260765 749250279672219604222787)
                ·
                  refine ⟨1123875419508329406334181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 749250279672219604222787 1123875419508329406334181)
                  ·
                    refine ⟨210726641157811763687659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1123875419508329406334181 210726641157811763687659)
                    ·
                      rfl

theorem cell23_1231166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_1231166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231166 prefixEnd_1231166 := by exact prefixLift 1231166
  have htrace : WordTrace (prefixWord ++ tailWord_1231166) baseStart_1231166 baseEnd_1231166 := by
    simpa [prefixWord, tailWord_1231166, baseEnd_1231166] using wordTrace_append hprefix tailTrace_1231166
  have hstable : (prefixWord ++ tailWord_1231166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231166).length < 2 ^ (prefixWord ++ tailWord_1231166).sum := by decide
  have hdescent : baseEnd_1231166 < baseStart_1231166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231182 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2]
def baseStart_1231182 : Nat := 118140960795 + 1231182 * 2 ^ 59
def prefixEnd_1231182 : Nat := 4983230072969 + 3 ^ 40 * 1231182 * 2
def baseEnd_1231182 : Nat := 632188139163907228462903

theorem tailTrace_1231182 : CollatzResearch.WordTrace tailWord_1231182 prefixEnd_1231182 632188139163907228462903 := by
  unfold tailWord_1231182
  simp only [CollatzResearch.WordTrace]
  refine ⟨5613112078205669748790975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29936597750430238660218533 5613112078205669748790975)
  ·
    refine ⟨8419668117308504623186463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5613112078205669748790975 8419668117308504623186463)
    ·
      refine ⟨12629502175962756934779695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8419668117308504623186463 12629502175962756934779695)
      ·
        refine ⟨18944253263944135402169543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12629502175962756934779695 18944253263944135402169543)
        ·
          refine ⟨28416379895916203103254315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18944253263944135402169543 28416379895916203103254315)
          ·
            refine ⟨42624569843874304654881473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28416379895916203103254315 42624569843874304654881473)
            ·
              refine ⟨31968427382905728491161105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42624569843874304654881473 31968427382905728491161105)
              ·
                refine ⟨23976320537179296368370829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31968427382905728491161105 23976320537179296368370829)
                ·
                  refine ⟨8991120201442236138139061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23976320537179296368370829 8991120201442236138139061)
                  ·
                    refine ⟨842917518885209637950537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8991120201442236138139061 842917518885209637950537)
                    ·
                      refine ⟨632188139163907228462903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 842917518885209637950537 632188139163907228462903)
                      ·
                        rfl

theorem cell23_1231182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_1231182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231182 prefixEnd_1231182 := by exact prefixLift 1231182
  have htrace : WordTrace (prefixWord ++ tailWord_1231182) baseStart_1231182 baseEnd_1231182 := by
    simpa [prefixWord, tailWord_1231182, baseEnd_1231182] using wordTrace_append hprefix tailTrace_1231182
  have hstable : (prefixWord ++ tailWord_1231182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231182).length < 2 ^ (prefixWord ++ tailWord_1231182).sum := by decide
  have hdescent : baseEnd_1231182 < baseStart_1231182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231235 : List Nat := [1, 1, 1, 3, 6, 11]
def baseStart_1231235 : Nat := 118140960795 + 1231235 * 2 ^ 59
def prefixEnd_1231235 : Nat := 4983230072969 + 3 ^ 40 * 1231235 * 2
def baseEnd_1231235 : Nat := 2601709274232903379013

theorem tailTrace_1231235 : CollatzResearch.WordTrace tailWord_1231235 prefixEnd_1231235 2601709274232903379013 := by
  unfold tailWord_1231235
  simp only [CollatzResearch.WordTrace]
  refine ⟨44906829694453348042007159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29937886462968898694671439 44906829694453348042007159)
  ·
    refine ⟨67360244541680022063010739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44906829694453348042007159 67360244541680022063010739)
    ·
      refine ⟨101040366812520033094516109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67360244541680022063010739 101040366812520033094516109)
      ·
        refine ⟨37890137554695012410443541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101040366812520033094516109 37890137554695012410443541)
        ·
          refine ⟨1776100197876328706739541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37890137554695012410443541 1776100197876328706739541)
          ·
            refine ⟨2601709274232903379013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1776100197876328706739541 2601709274232903379013)
            ·
              rfl

theorem cell23_1231235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 11].length) (baseStart_1231235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231235 prefixEnd_1231235 := by exact prefixLift 1231235
  have htrace : WordTrace (prefixWord ++ tailWord_1231235) baseStart_1231235 baseEnd_1231235 := by
    simpa [prefixWord, tailWord_1231235, baseEnd_1231235] using wordTrace_append hprefix tailTrace_1231235
  have hstable : (prefixWord ++ tailWord_1231235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231235).length < 2 ^ (prefixWord ++ tailWord_1231235).sum := by decide
  have hdescent : baseEnd_1231235 < baseStart_1231235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231239 : List Nat := [1, 1, 4, 2, 2, 1, 4, 2, 2, 4]
def baseStart_1231239 : Nat := 118140960795 + 1231239 * 2 ^ 59
def prefixEnd_1231239 : Nat := 4983230072969 + 3 ^ 40 * 1231239 * 2
def baseEnd_1231239 : Nat := 210739135853737835150047

theorem tailTrace_1231239 : CollatzResearch.WordTrace tailWord_1231239 prefixEnd_1231239 210739135853737835150047 := by
  unfold tailWord_1231239
  simp only [CollatzResearch.WordTrace]
  refine ⟨44906975586438856725152771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29937983724292571150101847 44906975586438856725152771)
  ·
    refine ⟨67360463379658285087729157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44906975586438856725152771 67360463379658285087729157)
    ·
      refine ⟨12630086883685928453949217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67360463379658285087729157 12630086883685928453949217)
      ·
        refine ⟨9472565162764446340461913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12630086883685928453949217 9472565162764446340461913)
        ·
          refine ⟨7104423872073334755346435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9472565162764446340461913 7104423872073334755346435)
          ·
            refine ⟨10656635808110002133019653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7104423872073334755346435 10656635808110002133019653)
            ·
              refine ⟨1998119214020625399941185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10656635808110002133019653 1998119214020625399941185)
              ·
                refine ⟨1498589410515469049955889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1998119214020625399941185 1498589410515469049955889)
                ·
                  refine ⟨1123942057886601787466917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1498589410515469049955889 1123942057886601787466917)
                  ·
                    refine ⟨210739135853737835150047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1123942057886601787466917 210739135853737835150047)
                    ·
                      rfl

theorem cell23_1231239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_1231239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231239 prefixEnd_1231239 := by exact prefixLift 1231239
  have htrace : WordTrace (prefixWord ++ tailWord_1231239) baseStart_1231239 baseEnd_1231239 := by
    simpa [prefixWord, tailWord_1231239, baseEnd_1231239] using wordTrace_append hprefix tailTrace_1231239
  have hstable : (prefixWord ++ tailWord_1231239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231239).length < 2 ^ (prefixWord ++ tailWord_1231239).sum := by decide
  have hdescent : baseEnd_1231239 < baseStart_1231239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231255 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 6]
def baseStart_1231255 : Nat := 118140960795 + 1231255 * 2 ^ 59
def prefixEnd_1231255 : Nat := 4983230072969 + 3 ^ 40 * 1231255 * 2
def baseEnd_1231255 : Nat := 632225623251685442850067

theorem tailTrace_1231255 : CollatzResearch.WordTrace tailWord_1231255 prefixEnd_1231255 632225623251685442850067 := by
  unfold tailWord_1231255
  simp only [CollatzResearch.WordTrace]
  refine ⟨44907559154380891457735219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29938372769587260971823479 44907559154380891457735219)
  ·
    refine ⟨67361338731571337186602829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44907559154380891457735219 67361338731571337186602829)
    ·
      refine ⟨25260502024339251444976061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67361338731571337186602829 25260502024339251444976061)
      ·
        refine ⟨9472688259127219291866023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25260502024339251444976061 9472688259127219291866023)
        ·
          refine ⟨14209032388690828937799035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9472688259127219291866023 14209032388690828937799035)
          ·
            refine ⟨21313548583036243406698553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14209032388690828937799035 21313548583036243406698553)
            ·
              refine ⟨15985161437277182555023915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21313548583036243406698553 15985161437277182555023915)
              ·
                refine ⟨23977742155915773832535873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15985161437277182555023915 23977742155915773832535873)
                ·
                  refine ⟨17983306616936830374401905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23977742155915773832535873 17983306616936830374401905)
                  ·
                    refine ⟨13487479962702622780801429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17983306616936830374401905 13487479962702622780801429)
                    ·
                      refine ⟨632225623251685442850067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13487479962702622780801429 632225623251685442850067)
                      ·
                        rfl

theorem cell23_1231255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_1231255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231255 prefixEnd_1231255 := by exact prefixLift 1231255
  have htrace : WordTrace (prefixWord ++ tailWord_1231255) baseStart_1231255 baseEnd_1231255 := by
    simpa [prefixWord, tailWord_1231255, baseEnd_1231255] using wordTrace_append hprefix tailTrace_1231255
  have hstable : (prefixWord ++ tailWord_1231255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231255).length < 2 ^ (prefixWord ++ tailWord_1231255).sum := by decide
  have hdescent : baseEnd_1231255 < baseStart_1231255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231297 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_1231297 : Nat := 118140960795 + 1231297 * 2 ^ 59
def prefixEnd_1231297 : Nat := 4983230072969 + 3 ^ 40 * 1231297 * 2
def baseEnd_1231297 : Nat := 632247189439174278524875

theorem tailTrace_1231297 : CollatzResearch.WordTrace tailWord_1231297 prefixEnd_1231297 632247189439174278524875 := by
  unfold tailWord_1231297
  simp only [CollatzResearch.WordTrace]
  refine ⟨44909091020228732630764145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29939394013485821753842763 44909091020228732630764145)
  ·
    refine ⟨33681818265171549473073109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44909091020228732630764145 33681818265171549473073109)
    ·
      refine ⟨789417615589958190775151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 33681818265171549473073109 789417615589958190775151)
      ·
        refine ⟨1184126423384937286162727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789417615589958190775151 1184126423384937286162727)
        ·
          refine ⟨1776189635077405929244091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1184126423384937286162727 1776189635077405929244091)
          ·
            refine ⟨2664284452616108893866137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776189635077405929244091 2664284452616108893866137)
            ·
              refine ⟨1998213339462081670399603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2664284452616108893866137 1998213339462081670399603)
              ·
                refine ⟨2997320009193122505599405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1998213339462081670399603 2997320009193122505599405)
                ·
                  refine ⟨1123995003447420939599777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2997320009193122505599405 1123995003447420939599777)
                  ·
                    refine ⟨842996252585565704699833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1123995003447420939599777 842996252585565704699833)
                    ·
                      refine ⟨632247189439174278524875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 842996252585565704699833 632247189439174278524875)
                      ·
                        rfl

theorem cell23_1231297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_1231297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231297 prefixEnd_1231297 := by exact prefixLift 1231297
  have htrace : WordTrace (prefixWord ++ tailWord_1231297) baseStart_1231297 baseEnd_1231297 := by
    simpa [prefixWord, tailWord_1231297, baseEnd_1231297] using wordTrace_append hprefix tailTrace_1231297
  have hstable : (prefixWord ++ tailWord_1231297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231297).length < 2 ^ (prefixWord ++ tailWord_1231297).sum := by decide
  have hdescent : baseEnd_1231297 < baseStart_1231297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231322 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5]
def baseStart_1231322 : Nat := 118140960795 + 1231322 * 2 ^ 59
def prefixEnd_1231322 : Nat := 4983230072969 + 3 ^ 40 * 1231322 * 2
def baseEnd_1231322 : Nat := 632260026455536680712259

theorem tailTrace_1231322 : CollatzResearch.WordTrace tailWord_1231322 prefixEnd_1231322 632260026455536680712259 := by
  unfold tailWord_1231322
  simp only [CollatzResearch.WordTrace]
  refine ⟨11227500711284540475106055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29940001896758774600282813 11227500711284540475106055)
  ·
    refine ⟨16841251066926810712659083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11227500711284540475106055 16841251066926810712659083)
    ·
      refine ⟨25261876600390216068988625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16841251066926810712659083 25261876600390216068988625)
      ·
        refine ⟨18946407450292662051741469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25261876600390216068988625 18946407450292662051741469)
        ·
          refine ⟨7104902793859748269403051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18946407450292662051741469 7104902793859748269403051)
          ·
            refine ⟨10657354190789622404104577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7104902793859748269403051 10657354190789622404104577)
            ·
              refine ⟨7993015643092216803078433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10657354190789622404104577 7993015643092216803078433)
              ·
                refine ⟨5994761732319162602308825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7993015643092216803078433 5994761732319162602308825)
                ·
                  refine ⟨4496071299239371951731619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5994761732319162602308825 4496071299239371951731619)
                  ·
                    refine ⟨6744106948859057927597429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4496071299239371951731619 6744106948859057927597429)
                    ·
                      refine ⟨632260026455536680712259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6744106948859057927597429 632260026455536680712259)
                      ·
                        rfl

theorem cell23_1231322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_1231322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231322 prefixEnd_1231322 := by exact prefixLift 1231322
  have htrace : WordTrace (prefixWord ++ tailWord_1231322) baseStart_1231322 baseEnd_1231322 := by
    simpa [prefixWord, tailWord_1231322, baseEnd_1231322] using wordTrace_append hprefix tailTrace_1231322
  have hstable : (prefixWord ++ tailWord_1231322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231322).length < 2 ^ (prefixWord ++ tailWord_1231322).sum := by decide
  have hdescent : baseEnd_1231322 < baseStart_1231322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231336 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 4, 2, 2]
def baseStart_1231336 : Nat := 118140960795 + 1231336 * 2 ^ 59
def prefixEnd_1231336 : Nat := 4983230072969 + 3 ^ 40 * 1231336 * 2
def baseEnd_1231336 : Nat := 632267215184699625937195

theorem tailTrace_1231336 : CollatzResearch.WordTrace tailWord_1231336 prefixEnd_1231336 632267215184699625937195 := by
  unfold tailWord_1231336
  simp only [CollatzResearch.WordTrace]
  refine ⟨22455256733543721145716931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29940342311391628194289241 22455256733543721145716931)
  ·
    refine ⟨33682885100315581718575397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22455256733543721145716931 33682885100315581718575397)
    ·
      refine ⟨6315540956309171572232887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33682885100315581718575397 6315540956309171572232887)
      ·
        refine ⟨9473311434463757358349331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6315540956309171572232887 9473311434463757358349331)
        ·
          refine ⟨14209967151695636037523997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9473311434463757358349331 14209967151695636037523997)
          ·
            refine ⟨5328737681885863514071499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14209967151695636037523997 5328737681885863514071499)
            ·
              refine ⟨7993106522828795271107249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5328737681885863514071499 7993106522828795271107249)
              ·
                refine ⟨5994829892121596453330437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7993106522828795271107249 5994829892121596453330437)
                ·
                  refine ⟨1124030604772799334999457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5994829892121596453330437 1124030604772799334999457)
                  ·
                    refine ⟨843022953579599501249593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1124030604772799334999457 843022953579599501249593)
                    ·
                      refine ⟨632267215184699625937195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 843022953579599501249593 632267215184699625937195)
                      ·
                        rfl

theorem cell23_1231336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_1231336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231336 prefixEnd_1231336 := by exact prefixLift 1231336
  have htrace : WordTrace (prefixWord ++ tailWord_1231336) baseStart_1231336 baseEnd_1231336 := by
    simpa [prefixWord, tailWord_1231336, baseEnd_1231336] using wordTrace_append hprefix tailTrace_1231336
  have hstable : (prefixWord ++ tailWord_1231336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231336).length < 2 ^ (prefixWord ++ tailWord_1231336).sum := by decide
  have hdescent : baseEnd_1231336 < baseStart_1231336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231389 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 2, 5]
def baseStart_1231389 : Nat := 118140960795 + 1231389 * 2 ^ 59
def prefixEnd_1231389 : Nat := 4983230072969 + 3 ^ 40 * 1231389 * 2
def baseEnd_1231389 : Nat := 210764809886462639524817

theorem tailTrace_1231389 : CollatzResearch.WordTrace tailWord_1231389 prefixEnd_1231389 210764809886462639524817 := by
  unfold tailWord_1231389
  simp only [CollatzResearch.WordTrace]
  refine ⟨44912446535895432343113221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29941631023930288228742147 44912446535895432343113221)
  ·
    refine ⟨8421083725480393564333729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44912446535895432343113221 8421083725480393564333729)
    ·
      refine ⟨6315812794110295173250297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8421083725480393564333729 6315812794110295173250297)
      ·
        refine ⟨4736859595582721379937723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6315812794110295173250297 4736859595582721379937723)
        ·
          refine ⟨7105289393374082069906585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4736859595582721379937723 7105289393374082069906585)
          ·
            refine ⟨5328967045030561552429939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7105289393374082069906585 5328967045030561552429939)
            ·
              refine ⟨7993450567545842328644909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5328967045030561552429939 7993450567545842328644909)
              ·
                refine ⟨2997543962829690873241841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7993450567545842328644909 2997543962829690873241841)
                ·
                  refine ⟨2248157972122268154931381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2997543962829690873241841 2248157972122268154931381)
                  ·
                    refine ⟨210764809886462639524817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2248157972122268154931381 210764809886462639524817)
                    ·
                      rfl

theorem cell23_1231389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_1231389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231389 prefixEnd_1231389 := by exact prefixLift 1231389
  have htrace : WordTrace (prefixWord ++ tailWord_1231389) baseStart_1231389 baseEnd_1231389 := by
    simpa [prefixWord, tailWord_1231389, baseEnd_1231389] using wordTrace_append hprefix tailTrace_1231389
  have hstable : (prefixWord ++ tailWord_1231389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231389).length < 2 ^ (prefixWord ++ tailWord_1231389).sum := by decide
  have hdescent : baseEnd_1231389 < baseStart_1231389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231409 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 2, 1, 4]
def baseStart_1231409 : Nat := 118140960795 + 1231409 * 2 ^ 59
def prefixEnd_1231409 : Nat := 4983230072969 + 3 ^ 40 * 1231409 * 2
def baseEnd_1231409 : Nat := 632304699272477840324359

theorem tailTrace_1231409 : CollatzResearch.WordTrace tailWord_1231409 prefixEnd_1231409 632304699272477840324359 := by
  unfold tailWord_1231409
  simp only [CollatzResearch.WordTrace]
  refine ⟨44913175995822975758841281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29942117330548650505894187 44913175995822975758841281)
  ·
    refine ⟨33684881996867231819130961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44913175995822975758841281 33684881996867231819130961)
    ·
      refine ⟨25263661497650423864348221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33684881996867231819130961 25263661497650423864348221)
      ·
        refine ⟨9473873061618908949130583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25263661497650423864348221 9473873061618908949130583)
        ·
          refine ⟨14210809592428363423695875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9473873061618908949130583 14210809592428363423695875)
          ·
            refine ⟨21316214388642545135543813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14210809592428363423695875 21316214388642545135543813)
            ·
              refine ⟨3996790197870477212914465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21316214388642545135543813 3996790197870477212914465)
              ·
                refine ⟨2997592648402857909685849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3996790197870477212914465 2997592648402857909685849)
                ·
                  refine ⟨2248194486302143432264387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2997592648402857909685849 2248194486302143432264387)
                  ·
                    refine ⟨3372291729453215148396581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2248194486302143432264387 3372291729453215148396581)
                    ·
                      refine ⟨632304699272477840324359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3372291729453215148396581 632304699272477840324359)
                      ·
                        rfl

theorem cell23_1231409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_1231409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231409 prefixEnd_1231409 := by exact prefixLift 1231409
  have htrace : WordTrace (prefixWord ++ tailWord_1231409) baseStart_1231409 baseEnd_1231409 := by
    simpa [prefixWord, tailWord_1231409, baseEnd_1231409] using wordTrace_append hprefix tailTrace_1231409
  have hstable : (prefixWord ++ tailWord_1231409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231409).length < 2 ^ (prefixWord ++ tailWord_1231409).sum := by decide
  have hdescent : baseEnd_1231409 < baseStart_1231409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231469 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_1231469 : Nat := 118140960795 + 1231469 * 2 ^ 59
def prefixEnd_1231469 : Nat := 4983230072969 + 3 ^ 40 * 1231469 * 2
def baseEnd_1231469 : Nat := 632335508111747605574083

theorem tailTrace_1231469 : CollatzResearch.WordTrace tailWord_1231469 prefixEnd_1231469 632335508111747605574083 := by
  unfold tailWord_1231469
  simp only [CollatzResearch.WordTrace]
  refine ⟨44915364375605606006025461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29943576250403737337350307 44915364375605606006025461)
  ·
    refine ⟨4210815410213025563064887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44915364375605606006025461 4210815410213025563064887)
    ·
      refine ⟨6316223115319538344597331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4210815410213025563064887 6316223115319538344597331)
      ·
        refine ⟨9474334672979307516895997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6316223115319538344597331 9474334672979307516895997)
        ·
          refine ⟨3552875502367240318835999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9474334672979307516895997 3552875502367240318835999)
          ·
            refine ⟨5329313253550860478253999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3552875502367240318835999 5329313253550860478253999)
            ·
              refine ⟨7993969880326290717380999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5329313253550860478253999 7993969880326290717380999)
              ·
                refine ⟨11990954820489436076071499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7993969880326290717380999 11990954820489436076071499)
                ·
                  refine ⟨17986432230734154114107249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11990954820489436076071499 17986432230734154114107249)
                  ·
                    refine ⟨13489824173050615585580437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17986432230734154114107249 13489824173050615585580437)
                    ·
                      refine ⟨632335508111747605574083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13489824173050615585580437 632335508111747605574083)
                      ·
                        rfl

theorem cell23_1231469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_1231469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231469 prefixEnd_1231469 := by exact prefixLift 1231469
  have htrace : WordTrace (prefixWord ++ tailWord_1231469) baseStart_1231469 baseEnd_1231469 := by
    simpa [prefixWord, tailWord_1231469, baseEnd_1231469] using wordTrace_append hprefix tailTrace_1231469
  have hstable : (prefixWord ++ tailWord_1231469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231469).length < 2 ^ (prefixWord ++ tailWord_1231469).sum := by decide
  have hdescent : baseEnd_1231469 < baseStart_1231469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231527 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_1231527 : Nat := 118140960795 + 1231527 * 2 ^ 59
def prefixEnd_1231527 : Nat := 4983230072969 + 3 ^ 40 * 1231527 * 2
def baseEnd_1231527 : Nat := 632365289989708378648817

theorem tailTrace_1231527 : CollatzResearch.WordTrace tailWord_1231527 prefixEnd_1231527 632365289989708378648817 := by
  unfold tailWord_1231527
  simp only [CollatzResearch.WordTrace]
  refine ⟨44917479809395481911636835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29944986539596987941091223 44917479809395481911636835)
  ·
    refine ⟨67376219714093222867455253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44917479809395481911636835 67376219714093222867455253)
    ·
      refine ⟨3158260299098119821911965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67376219714093222867455253 3158260299098119821911965)
      ·
        refine ⟨1184347612161794933216987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3158260299098119821911965 1184347612161794933216987)
        ·
          refine ⟨1776521418242692399825481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1184347612161794933216987 1776521418242692399825481)
          ·
            refine ⟨1332391063682019299869111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1776521418242692399825481 1332391063682019299869111)
            ·
              refine ⟨1998586595523028949803667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1332391063682019299869111 1998586595523028949803667)
              ·
                refine ⟨2997879893284543424705501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1998586595523028949803667 2997879893284543424705501)
                ·
                  refine ⟨1124204959981703784264563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2997879893284543424705501 1124204959981703784264563)
                  ·
                    refine ⟨1686307439972555676396845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1124204959981703784264563 1686307439972555676396845)
                    ·
                      refine ⟨632365289989708378648817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1686307439972555676396845 632365289989708378648817)
                      ·
                        rfl

theorem cell23_1231527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_1231527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231527 prefixEnd_1231527 := by exact prefixLift 1231527
  have htrace : WordTrace (prefixWord ++ tailWord_1231527) baseStart_1231527 baseEnd_1231527 := by
    simpa [prefixWord, tailWord_1231527, baseEnd_1231527] using wordTrace_append hprefix tailTrace_1231527
  have hstable : (prefixWord ++ tailWord_1231527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231527).length < 2 ^ (prefixWord ++ tailWord_1231527).sum := by decide
  have hdescent : baseEnd_1231527 < baseStart_1231527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231539 : List Nat := [1, 1, 1, 2, 3, 5, 2, 8]
def baseStart_1231539 : Nat := 118140960795 + 1231539 * 2 ^ 59
def prefixEnd_1231539 : Nat := 4983230072969 + 3 ^ 40 * 1231539 * 2
def baseEnd_1231539 : Nat := 23421164879909715988843

theorem tailTrace_1231539 : CollatzResearch.WordTrace tailWord_1231539 prefixEnd_1231539 23421164879909715988843 := by
  unfold tailWord_1231539
  simp only [CollatzResearch.WordTrace]
  refine ⟨44917917485352007961073671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29945278323568005307382447 44917917485352007961073671)
  ·
    refine ⟨67376876228028011941610507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44917917485352007961073671 67376876228028011941610507)
    ·
      refine ⟨101065314342042017912415761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67376876228028011941610507 101065314342042017912415761)
      ·
        refine ⟨75798985756531513434311821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101065314342042017912415761 75798985756531513434311821)
        ·
          refine ⟨28424619658699317537866933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75798985756531513434311821 28424619658699317537866933)
          ·
            refine ⟨2664808093003061019175025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28424619658699317537866933 2664808093003061019175025)
            ·
              refine ⟨1998606069752295764381269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2664808093003061019175025 1998606069752295764381269)
              ·
                refine ⟨23421164879909715988843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1998606069752295764381269 23421164879909715988843)
                ·
                  rfl

theorem cell23_1231539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 8].length) (baseStart_1231539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231539 prefixEnd_1231539 := by exact prefixLift 1231539
  have htrace : WordTrace (prefixWord ++ tailWord_1231539) baseStart_1231539 baseEnd_1231539 := by
    simpa [prefixWord, tailWord_1231539, baseEnd_1231539] using wordTrace_append hprefix tailTrace_1231539
  have hstable : (prefixWord ++ tailWord_1231539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231539).length < 2 ^ (prefixWord ++ tailWord_1231539).sum := by decide
  have hdescent : baseEnd_1231539 < baseStart_1231539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231543 : List Nat := [1, 1, 3, 1, 6, 1, 1, 3, 2, 4]
def baseStart_1231543 : Nat := 118140960795 + 1231543 * 2 ^ 59
def prefixEnd_1231543 : Nat := 4983230072969 + 3 ^ 40 * 1231543 * 2
def baseEnd_1231543 : Nat := 210791168560060105349581

theorem tailTrace_1231543 : CollatzResearch.WordTrace tailWord_1231543 prefixEnd_1231543 210791168560060105349581 := by
  unfold tailWord_1231543
  simp only [CollatzResearch.WordTrace]
  refine ⟨44918063377337516644219283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29945375584891677762812855 44918063377337516644219283)
  ·
    refine ⟨67377095066006274966328925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44918063377337516644219283 67377095066006274966328925)
    ·
      refine ⟨25266410649752353112373347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67377095066006274966328925 25266410649752353112373347)
      ·
        refine ⟨37899615974628529668560021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25266410649752353112373347 37899615974628529668560021)
        ·
          refine ⟨1776544498810712328213751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37899615974628529668560021 1776544498810712328213751)
          ·
            refine ⟨2664816748216068492320627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776544498810712328213751 2664816748216068492320627)
            ·
              refine ⟨3997225122324102738480941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2664816748216068492320627 3997225122324102738480941)
              ·
                refine ⟨1498959420871538526930353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3997225122324102738480941 1498959420871538526930353)
                ·
                  refine ⟨1124219565653653895197765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1498959420871538526930353 1124219565653653895197765)
                  ·
                    refine ⟨210791168560060105349581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1124219565653653895197765 210791168560060105349581)
                    ·
                      rfl

theorem cell23_1231543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_1231543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231543 prefixEnd_1231543 := by exact prefixLift 1231543
  have htrace : WordTrace (prefixWord ++ tailWord_1231543) baseStart_1231543 baseEnd_1231543 := by
    simpa [prefixWord, tailWord_1231543, baseEnd_1231543] using wordTrace_append hprefix tailTrace_1231543
  have hstable : (prefixWord ++ tailWord_1231543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231543).length < 2 ^ (prefixWord ++ tailWord_1231543).sum := by decide
  have hdescent : baseEnd_1231543 < baseStart_1231543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231566 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3]
def baseStart_1231566 : Nat := 118140960795 + 1231566 * 2 ^ 59
def prefixEnd_1231566 : Nat := 4983230072969 + 3 ^ 40 * 1231566 * 2
def baseEnd_1231566 : Nat := 632385315735233726061137

theorem tailTrace_1231566 : CollatzResearch.WordTrace tailWord_1231566 prefixEnd_1231566 632385315735233726061137 := by
  unfold tailWord_1231566
  simp only [CollatzResearch.WordTrace]
  refine ⟨5614862782031773946538319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29945934837502794381537701 5614862782031773946538319)
  ·
    refine ⟨8422294173047660919807479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5614862782031773946538319 8422294173047660919807479)
    ·
      refine ⟨12633441259571491379711219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8422294173047660919807479 12633441259571491379711219)
      ·
        refine ⟨18950161889357237069566829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12633441259571491379711219 18950161889357237069566829)
        ·
          refine ⟨7106310708508963901087561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18950161889357237069566829 7106310708508963901087561)
          ·
            refine ⟨5329733031381722925815671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7106310708508963901087561 5329733031381722925815671)
            ·
              refine ⟨7994599547072584388723507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5329733031381722925815671 7994599547072584388723507)
              ·
                refine ⟨11991899320608876583085261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7994599547072584388723507 11991899320608876583085261)
                ·
                  refine ⟨4496962245228328718656973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11991899320608876583085261 4496962245228328718656973)
                  ·
                    refine ⟨1686360841960623269496365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4496962245228328718656973 1686360841960623269496365)
                    ·
                      refine ⟨632385315735233726061137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1686360841960623269496365 632385315735233726061137)
                      ·
                        rfl

theorem cell23_1231566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_1231566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231566 prefixEnd_1231566 := by exact prefixLift 1231566
  have htrace : WordTrace (prefixWord ++ tailWord_1231566) baseStart_1231566 baseEnd_1231566 := by
    simpa [prefixWord, tailWord_1231566, baseEnd_1231566] using wordTrace_append hprefix tailTrace_1231566
  have hstable : (prefixWord ++ tailWord_1231566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231566).length < 2 ^ (prefixWord ++ tailWord_1231566).sum := by decide
  have hdescent : baseEnd_1231566 < baseStart_1231566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231570 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 1, 1, 5]
def baseStart_1231570 : Nat := 118140960795 + 1231570 * 2 ^ 59
def prefixEnd_1231570 : Nat := 4983230072969 + 3 ^ 40 * 1231570 * 2
def baseEnd_1231570 : Nat := 632387369657851710411119

theorem tailTrace_1231570 : CollatzResearch.WordTrace tailWord_1231570 prefixEnd_1231570 632387369657851710411119 := by
  unfold tailWord_1231570
  simp only [CollatzResearch.WordTrace]
  refine ⟨11229762037059925063863041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29946032098826466836968109 11229762037059925063863041)
  ·
    refine ⟨8422321527794943797897281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11229762037059925063863041 8422321527794943797897281)
    ·
      refine ⟨6316741145846207848422961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8422321527794943797897281 6316741145846207848422961)
      ·
        refine ⟨4737555859384655886317221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6316741145846207848422961 4737555859384655886317221)
        ·
          refine ⟨888291723634622978684479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4737555859384655886317221 888291723634622978684479)
          ·
            refine ⟨1332437585451934468026719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888291723634622978684479 1332437585451934468026719)
            ·
              refine ⟨1998656378177901702040079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1332437585451934468026719 1998656378177901702040079)
              ·
                refine ⟨2997984567266852553060119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1998656378177901702040079 2997984567266852553060119)
                ·
                  refine ⟨4496976850900278829590179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2997984567266852553060119 4496976850900278829590179)
                  ·
                    refine ⟨6745465276350418244385269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4496976850900278829590179 6745465276350418244385269)
                    ·
                      refine ⟨632387369657851710411119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6745465276350418244385269 632387369657851710411119)
                      ·
                        rfl

theorem cell23_1231570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_1231570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231570 prefixEnd_1231570 := by exact prefixLift 1231570
  have htrace : WordTrace (prefixWord ++ tailWord_1231570) baseStart_1231570 baseEnd_1231570 := by
    simpa [prefixWord, tailWord_1231570, baseEnd_1231570] using wordTrace_append hprefix tailTrace_1231570
  have hstable : (prefixWord ++ tailWord_1231570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231570).length < 2 ^ (prefixWord ++ tailWord_1231570).sum := by decide
  have hdescent : baseEnd_1231570 < baseStart_1231570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231583 : List Nat := [1, 1, 2, 3, 2, 3, 1, 4, 2, 1, 3]
def baseStart_1231583 : Nat := 118140960795 + 1231583 * 2 ^ 59
def prefixEnd_1231583 : Nat := 4983230072969 + 3 ^ 40 * 1231583 * 2
def baseEnd_1231583 : Nat := 632394044906360159548559

theorem tailTrace_1231583 : CollatzResearch.WordTrace tailWord_1231583 prefixEnd_1231583 632394044906360159548559 := by
  unfold tailWord_1231583
  simp only [CollatzResearch.WordTrace]
  refine ⟨44919522297192603475675403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29946348198128402317116935 44919522297192603475675403)
  ·
    refine ⟨67379283445788905213513105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44919522297192603475675403 67379283445788905213513105)
    ·
      refine ⟨50534462584341678910134829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67379283445788905213513105 50534462584341678910134829)
      ·
        refine ⟨18950423469128129591300561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50534462584341678910134829 18950423469128129591300561)
        ·
          refine ⟨14212817601846097193475421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18950423469128129591300561 14212817601846097193475421)
          ·
            refine ⟨5329806600692286447553283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14212817601846097193475421 5329806600692286447553283)
            ·
              refine ⟨7994709901038429671329925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5329806600692286447553283 7994709901038429671329925)
              ·
                refine ⟨1499008106444705563374361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7994709901038429671329925 1499008106444705563374361)
                ·
                  refine ⟨1124256079833529172530771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1499008106444705563374361 1124256079833529172530771)
                  ·
                    refine ⟨1686384119750293758796157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1124256079833529172530771 1686384119750293758796157)
                    ·
                      refine ⟨632394044906360159548559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1686384119750293758796157 632394044906360159548559)
                      ·
                        rfl

theorem cell23_1231583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_1231583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231583 prefixEnd_1231583 := by exact prefixLift 1231583
  have htrace : WordTrace (prefixWord ++ tailWord_1231583) baseStart_1231583 baseEnd_1231583 := by
    simpa [prefixWord, tailWord_1231583, baseEnd_1231583] using wordTrace_append hprefix tailTrace_1231583
  have hstable : (prefixWord ++ tailWord_1231583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231583).length < 2 ^ (prefixWord ++ tailWord_1231583).sum := by decide
  have hdescent : baseEnd_1231583 < baseStart_1231583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231599 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 1, 8]
def baseStart_1231599 : Nat := 118140960795 + 1231599 * 2 ^ 59
def prefixEnd_1231599 : Nat := 4983230072969 + 3 ^ 40 * 1231599 * 2
def baseEnd_1231599 : Nat := 210800753532277365649495

theorem tailTrace_1231599 : CollatzResearch.WordTrace tailWord_1231599 prefixEnd_1231599 210800753532277365649495 := by
  unfold tailWord_1231599
  simp only [CollatzResearch.WordTrace]
  refine ⟨44920105865134638208257851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29946737243423092138838567 44920105865134638208257851)
  ·
    refine ⟨67380158797701957312386777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44920105865134638208257851 67380158797701957312386777)
    ·
      refine ⟨50535119098276467984290083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67380158797701957312386777 50535119098276467984290083)
      ·
        refine ⟨75802678647414701976435125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50535119098276467984290083 75802678647414701976435125)
        ·
          refine ⟨7106501123195128310290793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75802678647414701976435125 7106501123195128310290793)
          ·
            refine ⟨5329875842396346232718095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7106501123195128310290793 5329875842396346232718095)
            ·
              refine ⟨7994813763594519349077143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5329875842396346232718095 7994813763594519349077143)
              ·
                refine ⟨11992220645391779023615715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7994813763594519349077143 11992220645391779023615715)
                ·
                  refine ⟨17988330968087668535423573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11992220645391779023615715 17988330968087668535423573)
                  ·
                    refine ⟨210800753532277365649495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17988330968087668535423573 210800753532277365649495)
                    ·
                      rfl

theorem cell23_1231599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 8].length) (baseStart_1231599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231599 prefixEnd_1231599 := by exact prefixLift 1231599
  have htrace : WordTrace (prefixWord ++ tailWord_1231599) baseStart_1231599 baseEnd_1231599 := by
    simpa [prefixWord, tailWord_1231599, baseEnd_1231599] using wordTrace_append hprefix tailTrace_1231599
  have hstable : (prefixWord ++ tailWord_1231599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231599).length < 2 ^ (prefixWord ++ tailWord_1231599).sum := by decide
  have hdescent : baseEnd_1231599 < baseStart_1231599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231606 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_1231606 : Nat := 118140960795 + 1231606 * 2 ^ 59
def prefixEnd_1231606 : Nat := 4983230072969 + 3 ^ 40 * 1231606 * 2
def baseEnd_1231606 : Nat := 632405854961413569560953

theorem tailTrace_1231606 : CollatzResearch.WordTrace tailWord_1231606 prefixEnd_1231606 632405854961413569560953 := by
  unfold tailWord_1231606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2807522573506829900235167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29946907450739518935841781 2807522573506829900235167)
  ·
    refine ⟨4211283860260244850352751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2807522573506829900235167 4211283860260244850352751)
    ·
      refine ⟨6316925790390367275529127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4211283860260244850352751 6316925790390367275529127)
      ·
        refine ⟨9475388685585550913293691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6316925790390367275529127 9475388685585550913293691)
        ·
          refine ⟨14213083028378326369940537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9475388685585550913293691 14213083028378326369940537)
          ·
            refine ⟨10659812271283744777455403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14213083028378326369940537 10659812271283744777455403)
            ·
              refine ⟨15989718406925617166183105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10659812271283744777455403 15989718406925617166183105)
              ·
                refine ⟨11992288805194212874637329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15989718406925617166183105 11992288805194212874637329)
                ·
                  refine ⟨8994216603895659655977997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11992288805194212874637329 8994216603895659655977997)
                  ·
                    refine ⟨3372831226460872370991749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8994216603895659655977997 3372831226460872370991749)
                    ·
                      refine ⟨632405854961413569560953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3372831226460872370991749 632405854961413569560953)
                      ·
                        rfl

theorem cell23_1231606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_1231606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231606 prefixEnd_1231606 := by exact prefixLift 1231606
  have htrace : WordTrace (prefixWord ++ tailWord_1231606) baseStart_1231606 baseEnd_1231606 := by
    simpa [prefixWord, tailWord_1231606, baseEnd_1231606] using wordTrace_append hprefix tailTrace_1231606
  have hstable : (prefixWord ++ tailWord_1231606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231606).length < 2 ^ (prefixWord ++ tailWord_1231606).sum := by decide
  have hdescent : baseEnd_1231606 < baseStart_1231606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231609 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 4, 1, 5]
def baseStart_1231609 : Nat := 118140960795 + 1231609 * 2 ^ 59
def prefixEnd_1231609 : Nat := 4983230072969 + 3 ^ 40 * 1231609 * 2
def baseEnd_1231609 : Nat := 632407395403377057823439

theorem tailTrace_1231609 : CollatzResearch.WordTrace tailWord_1231609 prefixEnd_1231609 632407395403377057823439 := by
  unfold tailWord_1231609
  simp only [CollatzResearch.WordTrace]
  refine ⟨44920470595098409916121881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29946980396732273277414587 44920470595098409916121881)
  ·
    refine ⟨33690352946323807437091411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44920470595098409916121881 33690352946323807437091411)
    ·
      refine ⟨50535529419485711155637117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33690352946323807437091411 50535529419485711155637117)
      ·
        refine ⟨18950823532307141683363919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50535529419485711155637117 18950823532307141683363919)
        ·
          refine ⟨28426235298460712525045879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18950823532307141683363919 28426235298460712525045879)
          ·
            refine ⟨42639352947691068787568819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28426235298460712525045879 42639352947691068787568819)
            ·
              refine ⟨63959029421536603181353229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42639352947691068787568819 63959029421536603181353229)
              ·
                refine ⟨23984636033076226193007461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63959029421536603181353229 23984636033076226193007461)
                ·
                  refine ⟨4497119256201792411188899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23984636033076226193007461 4497119256201792411188899)
                  ·
                    refine ⟨6745678884302688616783349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4497119256201792411188899 6745678884302688616783349)
                    ·
                      refine ⟨632407395403377057823439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6745678884302688616783349 632407395403377057823439)
                      ·
                        rfl

theorem cell23_1231609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_1231609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231609 prefixEnd_1231609 := by exact prefixLift 1231609
  have htrace : WordTrace (prefixWord ++ tailWord_1231609) baseStart_1231609 baseEnd_1231609 := by
    simpa [prefixWord, tailWord_1231609, baseEnd_1231609] using wordTrace_append hprefix tailTrace_1231609
  have hstable : (prefixWord ++ tailWord_1231609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231609).length < 2 ^ (prefixWord ++ tailWord_1231609).sum := by decide
  have hdescent : baseEnd_1231609 < baseStart_1231609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231619 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 4]
def baseStart_1231619 : Nat := 118140960795 + 1231619 * 2 ^ 59
def prefixEnd_1231619 : Nat := 4983230072969 + 3 ^ 40 * 1231619 * 2
def baseEnd_1231619 : Nat := 632412530209922018698393

theorem tailTrace_1231619 : CollatzResearch.WordTrace tailWord_1231619 prefixEnd_1231619 632412530209922018698393 := by
  unfold tailWord_1231619
  simp only [CollatzResearch.WordTrace]
  refine ⟨44920835325062181623985911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29947223550041454415990607 44920835325062181623985911)
  ·
    refine ⟨67381252987593272435978867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44920835325062181623985911 67381252987593272435978867)
    ·
      refine ⟨101071879481389908653968301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67381252987593272435978867 101071879481389908653968301)
      ·
        refine ⟨37901954805521215745238113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101071879481389908653968301 37901954805521215745238113)
        ·
          refine ⟨28426466104140911808928585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37901954805521215745238113 28426466104140911808928585)
          ·
            refine ⟨21319849578105683856696439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28426466104140911808928585 21319849578105683856696439)
            ·
              refine ⟨31979774367158525785044659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21319849578105683856696439 31979774367158525785044659)
              ·
                refine ⟨47969661550737788677566989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31979774367158525785044659 47969661550737788677566989)
                ·
                  refine ⟨17988623081526670754087621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47969661550737788677566989 17988623081526670754087621)
                  ·
                    refine ⟨3372866827786250766391429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17988623081526670754087621 3372866827786250766391429)
                    ·
                      refine ⟨632412530209922018698393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3372866827786250766391429 632412530209922018698393)
                      ·
                        rfl

theorem cell23_1231619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_1231619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231619 prefixEnd_1231619 := by exact prefixLift 1231619
  have htrace : WordTrace (prefixWord ++ tailWord_1231619) baseStart_1231619 baseEnd_1231619 := by
    simpa [prefixWord, tailWord_1231619, baseEnd_1231619] using wordTrace_append hprefix tailTrace_1231619
  have hstable : (prefixWord ++ tailWord_1231619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231619).length < 2 ^ (prefixWord ++ tailWord_1231619).sum := by decide
  have hdescent : baseEnd_1231619 < baseStart_1231619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231634 : List Nat := [3, 2, 4, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_1231634 : Nat := 118140960795 + 1231634 * 2 ^ 59
def prefixEnd_1231634 : Nat := 4983230072969 + 3 ^ 40 * 1231634 * 2
def baseEnd_1231634 : Nat := 632420232419739460010825

theorem tailTrace_1231634 : CollatzResearch.WordTrace tailWord_1231634 prefixEnd_1231634 632420232419739460010825 := by
  unfold tailWord_1231634
  simp only [CollatzResearch.WordTrace]
  refine ⟨11230345605001959796445489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29947588280005226123854637 11230345605001959796445489)
  ·
    refine ⟨8422759203751469847334117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11230345605001959796445489 8422759203751469847334117)
    ·
      refine ⟨1579267350703400596375147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8422759203751469847334117 1579267350703400596375147)
      ·
        refine ⟨2368901026055100894562721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1579267350703400596375147 2368901026055100894562721)
        ·
          refine ⟨1776675769541325670922041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2368901026055100894562721 1776675769541325670922041)
          ·
            refine ⟨1332506827155994253191531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1776675769541325670922041 1332506827155994253191531)
            ·
              refine ⟨1998760240733991379787297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1332506827155994253191531 1998760240733991379787297)
              ·
                refine ⟨1499070180550493534840473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1998760240733991379787297 1499070180550493534840473)
                ·
                  refine ⟨1124302635412870151130355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1499070180550493534840473 1124302635412870151130355)
                  ·
                    refine ⟨1686453953119305226695533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1124302635412870151130355 1686453953119305226695533)
                    ·
                      refine ⟨632420232419739460010825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1686453953119305226695533 632420232419739460010825)
                      ·
                        rfl

theorem cell23_1231634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_1231634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231634 prefixEnd_1231634 := by exact prefixLift 1231634
  have htrace : WordTrace (prefixWord ++ tailWord_1231634) baseStart_1231634 baseEnd_1231634 := by
    simpa [prefixWord, tailWord_1231634, baseEnd_1231634] using wordTrace_append hprefix tailTrace_1231634
  have hstable : (prefixWord ++ tailWord_1231634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231634).length < 2 ^ (prefixWord ++ tailWord_1231634).sum := by decide
  have hdescent : baseEnd_1231634 < baseStart_1231634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231659 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 1, 7]
def baseStart_1231659 : Nat := 118140960795 + 1231659 * 2 ^ 59
def prefixEnd_1231659 : Nat := 4983230072969 + 3 ^ 40 * 1231659 * 2
def baseEnd_1231659 : Nat := 210811023145367287399403

theorem tailTrace_1231659 : CollatzResearch.WordTrace tailWord_1231659 prefixEnd_1231659 210811023145367287399403 := by
  unfold tailWord_1231659
  simp only [CollatzResearch.WordTrace]
  refine ⟨44922294244917268455442031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29948196163278178970294687 44922294244917268455442031)
  ·
    refine ⟨67383441367375902683163047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44922294244917268455442031 67383441367375902683163047)
    ·
      refine ⟨101075162051063854024744571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67383441367375902683163047 101075162051063854024744571)
      ·
        refine ⟨151612743076595781037116857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101075162051063854024744571 151612743076595781037116857)
        ·
          refine ⟨113709557307446835777837643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151612743076595781037116857 113709557307446835777837643)
          ·
            refine ⟨170564335961170253666756465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113709557307446835777837643 170564335961170253666756465)
            ·
              refine ⟨127923251970877690250067349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170564335961170253666756465 127923251970877690250067349)
              ·
                refine ⟨5996402436134891730471907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 127923251970877690250067349 5996402436134891730471907)
                ·
                  refine ⟨8994603654202337595707861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5996402436134891730471907 8994603654202337595707861)
                  ·
                    refine ⟨210811023145367287399403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8994603654202337595707861 210811023145367287399403)
                    ·
                      rfl

theorem cell23_1231659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 7].length) (baseStart_1231659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231659 prefixEnd_1231659 := by exact prefixLift 1231659
  have htrace : WordTrace (prefixWord ++ tailWord_1231659) baseStart_1231659 baseEnd_1231659 := by
    simpa [prefixWord, tailWord_1231659, baseEnd_1231659] using wordTrace_append hprefix tailTrace_1231659
  have hstable : (prefixWord ++ tailWord_1231659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231659).length < 2 ^ (prefixWord ++ tailWord_1231659).sum := by decide
  have hdescent : baseEnd_1231659 < baseStart_1231659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231676 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 2, 5]
def baseStart_1231676 : Nat := 118140960795 + 1231676 * 2 ^ 59
def prefixEnd_1231676 : Nat := 4983230072969 + 3 ^ 40 * 1231676 * 2
def baseEnd_1231676 : Nat := 210813932869076098561877

theorem tailTrace_1231676 : CollatzResearch.WordTrace tailWord_1231676 prefixEnd_1231676 210813932869076098561877 := by
  unfold tailWord_1231676
  simp only [CollatzResearch.WordTrace]
  refine ⟨22461457142927840179405441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29948609523903786905873921 22461457142927840179405441)
  ·
    refine ⟨16846092857195880134554081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22461457142927840179405441 16846092857195880134554081)
    ·
      refine ⟨12634569642896910100915561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16846092857195880134554081 12634569642896910100915561)
      ·
        refine ⟨9475927232172682575686671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12634569642896910100915561 9475927232172682575686671)
        ·
          refine ⟨14213890848259023863530007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9475927232172682575686671 14213890848259023863530007)
          ·
            refine ⟨21320836272388535795295011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14213890848259023863530007 21320836272388535795295011)
            ·
              refine ⟨31981254408582803692942517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21320836272388535795295011 31981254408582803692942517)
              ·
                refine ⟨2998242600804637846213361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31981254408582803692942517 2998242600804637846213361)
                ·
                  refine ⟨2248681950603478384660021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2998242600804637846213361 2248681950603478384660021)
                  ·
                    refine ⟨210813932869076098561877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2248681950603478384660021 210813932869076098561877)
                    ·
                      rfl

theorem cell23_1231676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_1231676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231676 prefixEnd_1231676 := by exact prefixLift 1231676
  have htrace : WordTrace (prefixWord ++ tailWord_1231676) baseStart_1231676 baseEnd_1231676 := by
    simpa [prefixWord, tailWord_1231676, baseEnd_1231676] using wordTrace_append hprefix tailTrace_1231676
  have hstable : (prefixWord ++ tailWord_1231676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231676).length < 2 ^ (prefixWord ++ tailWord_1231676).sum := by decide
  have hdescent : baseEnd_1231676 < baseStart_1231676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231696 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 4]
def baseStart_1231696 : Nat := 118140960795 + 1231696 * 2 ^ 59
def prefixEnd_1231696 : Nat := 4983230072969 + 3 ^ 40 * 1231696 * 2
def baseEnd_1231696 : Nat := 632452068220318217435539

theorem tailTrace_1231696 : CollatzResearch.WordTrace tailWord_1231696 prefixEnd_1231696 632452068220318217435539 := by
  unfold tailWord_1231696
  simp only [CollatzResearch.WordTrace]
  refine ⟨22461821872891611887269471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29949095830522149183025961 22461821872891611887269471)
  ·
    refine ⟨33692732809337417830904207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22461821872891611887269471 33692732809337417830904207)
    ·
      refine ⟨50539099214006126746356311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33692732809337417830904207 50539099214006126746356311)
      ·
        refine ⟨75808648821009190119534467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50539099214006126746356311 75808648821009190119534467)
        ·
          refine ⟨113712973231513785179301701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75808648821009190119534467 113712973231513785179301701)
          ·
            refine ⟨21321182480908834721119069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113712973231513785179301701 21321182480908834721119069)
            ·
              refine ⟨7995443430340813020419651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21321182480908834721119069 7995443430340813020419651)
              ·
                refine ⟨11993165145511219530629477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7995443430340813020419651 11993165145511219530629477)
                ·
                  refine ⟨2248718464783353661993027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11993165145511219530629477 2248718464783353661993027)
                  ·
                    refine ⟨3373077697175030492989541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2248718464783353661993027 3373077697175030492989541)
                    ·
                      refine ⟨632452068220318217435539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3373077697175030492989541 632452068220318217435539)
                      ·
                        rfl

theorem cell23_1231696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 4].length) (baseStart_1231696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231696 prefixEnd_1231696 := by exact prefixLift 1231696
  have htrace : WordTrace (prefixWord ++ tailWord_1231696) baseStart_1231696 baseEnd_1231696 := by
    simpa [prefixWord, tailWord_1231696, baseEnd_1231696] using wordTrace_append hprefix tailTrace_1231696
  have hstable : (prefixWord ++ tailWord_1231696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231696).length < 2 ^ (prefixWord ++ tailWord_1231696).sum := by decide
  have hdescent : baseEnd_1231696 < baseStart_1231696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231753 : List Nat := [1, 2, 1, 1, 5, 3, 2, 2, 6]
def baseStart_1231753 : Nat := 118140960795 + 1231753 * 2 ^ 59
def prefixEnd_1231753 : Nat := 4983230072969 + 3 ^ 40 * 1231753 * 2
def baseEnd_1231753 : Nat := 70275704068624943824753

theorem tailTrace_1231753 : CollatzResearch.WordTrace tailWord_1231753 prefixEnd_1231753 70275704068624943824753 := by
  unfold tailWord_1231753
  simp only [CollatzResearch.WordTrace]
  refine ⟨44925722706576722509363913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29950481804384481672909275 44925722706576722509363913)
  ·
    refine ⟨33694292029932541882022935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44925722706576722509363913 33694292029932541882022935)
    ·
      refine ⟨50541438044898812823034403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33694292029932541882022935 50541438044898812823034403)
      ·
        refine ⟨75812157067348219234551605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50541438044898812823034403 75812157067348219234551605)
        ·
          refine ⟨7107389725063895553239213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75812157067348219234551605 7107389725063895553239213)
          ·
            refine ⟨2665271146898960832464705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7107389725063895553239213 2665271146898960832464705)
            ·
              refine ⟨1998953360174220624348529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2665271146898960832464705 1998953360174220624348529)
              ·
                refine ⟨1499215020130665468261397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1998953360174220624348529 1499215020130665468261397)
                ·
                  refine ⟨70275704068624943824753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1499215020130665468261397 70275704068624943824753)
                  ·
                    rfl

theorem cell23_1231753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 6].length) (baseStart_1231753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231753 prefixEnd_1231753 := by exact prefixLift 1231753
  have htrace : WordTrace (prefixWord ++ tailWord_1231753) baseStart_1231753 baseEnd_1231753 := by
    simpa [prefixWord, tailWord_1231753, baseEnd_1231753] using wordTrace_append hprefix tailTrace_1231753
  have hstable : (prefixWord ++ tailWord_1231753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231753).length < 2 ^ (prefixWord ++ tailWord_1231753).sum := by decide
  have hdescent : baseEnd_1231753 < baseStart_1231753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231780 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 3, 1, 3]
def baseStart_1231780 : Nat := 118140960795 + 1231780 * 2 ^ 59
def prefixEnd_1231780 : Nat := 4983230072969 + 3 ^ 40 * 1231780 * 2
def baseEnd_1231780 : Nat := 632495200595295888785153

theorem tailTrace_1231780 : CollatzResearch.WordTrace tailWord_1231780 prefixEnd_1231780 632495200595295888785153 := by
  unfold tailWord_1231780
  simp only [CollatzResearch.WordTrace]
  refine ⟨22463353738739453060298397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29951138318319270747064529 22463353738739453060298397)
  ·
    refine ⟨8423757652027294897611899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22463353738739453060298397 8423757652027294897611899)
    ·
      refine ⟨12635636478040942346417849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8423757652027294897611899 12635636478040942346417849)
      ·
        refine ⟨9476727358530706759813387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12635636478040942346417849 9476727358530706759813387)
        ·
          refine ⟨14215091037796060139720081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9476727358530706759813387 14215091037796060139720081)
          ·
            refine ⟨10661318278347045104790061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14215091037796060139720081 10661318278347045104790061)
            ·
              refine ⟨3997994354380141914296273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10661318278347045104790061 3997994354380141914296273)
              ·
                refine ⟨2998495765785106435722205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3997994354380141914296273 2998495765785106435722205)
                ·
                  refine ⟨1124435912169414913395827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2998495765785106435722205 1124435912169414913395827)
                  ·
                    refine ⟨1686653868254122370093741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1124435912169414913395827 1686653868254122370093741)
                    ·
                      refine ⟨632495200595295888785153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1686653868254122370093741 632495200595295888785153)
                      ·
                        rfl

theorem cell23_1231780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_1231780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231780 prefixEnd_1231780 := by exact prefixLift 1231780
  have htrace : WordTrace (prefixWord ++ tailWord_1231780) baseStart_1231780 baseEnd_1231780 := by
    simpa [prefixWord, tailWord_1231780, baseEnd_1231780] using wordTrace_append hprefix tailTrace_1231780
  have hstable : (prefixWord ++ tailWord_1231780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231780).length < 2 ^ (prefixWord ++ tailWord_1231780).sum := by decide
  have hdescent : baseEnd_1231780 < baseStart_1231780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231800 : List Nat := [2, 1, 2, 1, 2, 4, 4, 1, 1, 5]
def baseStart_1231800 : Nat := 118140960795 + 1231800 * 2 ^ 59
def prefixEnd_1231800 : Nat := 4983230072969 + 3 ^ 40 * 1231800 * 2
def baseEnd_1231800 : Nat := 210835156736128603511687

theorem tailTrace_1231800 : CollatzResearch.WordTrace tailWord_1231800 prefixEnd_1231800 210835156736128603511687 := by
  unfold tailWord_1231800
  simp only [CollatzResearch.WordTrace]
  refine ⟨22463718468703224768162427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29951624624937633024216569 22463718468703224768162427)
  ·
    refine ⟨33695577703054837152243641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22463718468703224768162427 33695577703054837152243641)
    ·
      refine ⟨25271683277291127864182731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33695577703054837152243641 25271683277291127864182731)
      ·
        refine ⟨37907524915936691796274097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25271683277291127864182731 37907524915936691796274097)
        ·
          refine ⟨28430643686952518847205573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37907524915936691796274097 28430643686952518847205573)
          ·
            refine ⟨5330745691303597283851045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28430643686952518847205573 5330745691303597283851045)
            ·
              refine ⟨999514817119424490722071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5330745691303597283851045 999514817119424490722071)
              ·
                refine ⟨1499272225679136736083107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 999514817119424490722071 1499272225679136736083107)
                ·
                  refine ⟨2248908338518705104124661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1499272225679136736083107 2248908338518705104124661)
                  ·
                    refine ⟨210835156736128603511687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2248908338518705104124661 210835156736128603511687)
                    ·
                      rfl

theorem cell23_1231800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 1, 5].length) (baseStart_1231800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231800 prefixEnd_1231800 := by exact prefixLift 1231800
  have htrace : WordTrace (prefixWord ++ tailWord_1231800) baseStart_1231800 baseEnd_1231800 := by
    simpa [prefixWord, tailWord_1231800, baseEnd_1231800] using wordTrace_append hprefix tailTrace_1231800
  have hstable : (prefixWord ++ tailWord_1231800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231800).length < 2 ^ (prefixWord ++ tailWord_1231800).sum := by decide
  have hdescent : baseEnd_1231800 < baseStart_1231800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231821 : List Nat := [1, 6, 3, 1, 1, 1, 3, 1, 6]
def baseStart_1231821 : Nat := 118140960795 + 1231821 * 2 ^ 59
def prefixEnd_1231821 : Nat := 4983230072969 + 3 ^ 40 * 1231821 * 2
def baseEnd_1231821 : Nat := 70279583700236692041385

theorem tailTrace_1231821 : CollatzResearch.WordTrace tailWord_1231821 prefixEnd_1231821 70279583700236692041385 := by
  unfold tailWord_1231821
  simp only [CollatzResearch.WordTrace]
  refine ⟨44928202870330370122839317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29952135246886913415226211 44928202870330370122839317)
  ·
    refine ⟨2106009509546736099508093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44928202870330370122839317 2106009509546736099508093)
    ·
      refine ⟨789753566080026037315535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2106009509546736099508093 789753566080026037315535)
      ·
        refine ⟨1184630349120039055973303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789753566080026037315535 1184630349120039055973303)
        ·
          refine ⟨1776945523680058583959955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1184630349120039055973303 1776945523680058583959955)
          ·
            refine ⟨2665418285520087875939933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776945523680058583959955 2665418285520087875939933)
            ·
              refine ⟨999531857070032953477475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2665418285520087875939933 999531857070032953477475)
              ·
                refine ⟨1499297785605049430216213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 999531857070032953477475 1499297785605049430216213)
                ·
                  refine ⟨70279583700236692041385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1499297785605049430216213 70279583700236692041385)
                  ·
                    rfl

theorem cell23_1231821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_1231821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231821 prefixEnd_1231821 := by exact prefixLift 1231821
  have htrace : WordTrace (prefixWord ++ tailWord_1231821) baseStart_1231821 baseEnd_1231821 := by
    simpa [prefixWord, tailWord_1231821, baseEnd_1231821] using wordTrace_append hprefix tailTrace_1231821
  have hstable : (prefixWord ++ tailWord_1231821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231821).length < 2 ^ (prefixWord ++ tailWord_1231821).sum := by decide
  have hdescent : baseEnd_1231821 < baseStart_1231821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231823 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 5]
def baseStart_1231823 : Nat := 118140960795 + 1231823 * 2 ^ 59
def prefixEnd_1231823 : Nat := 4983230072969 + 3 ^ 40 * 1231823 * 2
def baseEnd_1231823 : Nat := 632517280263439220547455

theorem tailTrace_1231823 : CollatzResearch.WordTrace tailWord_1231823 prefixEnd_1231823 632517280263439220547455 := by
  unfold tailWord_1231823
  simp only [CollatzResearch.WordTrace]
  refine ⟨44928275816323124464412123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29952183877548749642941415 44928275816323124464412123)
  ·
    refine ⟨67392413724484686696618185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44928275816323124464412123 67392413724484686696618185)
    ·
      refine ⟨50544310293363515022463639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67392413724484686696618185 50544310293363515022463639)
      ·
        refine ⟨75816465440045272533695459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50544310293363515022463639 75816465440045272533695459)
        ·
          refine ⟨113724698160067908800543189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75816465440045272533695459 113724698160067908800543189)
          ·
            refine ⟨2665422613126591612512731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 113724698160067908800543189 2665422613126591612512731)
            ·
              refine ⟨3998133919689887418769097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2665422613126591612512731 3998133919689887418769097)
              ·
                refine ⟨2998600439767415564076823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3998133919689887418769097 2998600439767415564076823)
                ·
                  refine ⟨4497900659651123346115235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2998600439767415564076823 4497900659651123346115235)
                  ·
                    refine ⟨6746850989476685019172853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4497900659651123346115235 6746850989476685019172853)
                    ·
                      refine ⟨632517280263439220547455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6746850989476685019172853 632517280263439220547455)
                      ·
                        rfl

theorem cell23_1231823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 5].length) (baseStart_1231823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231823 prefixEnd_1231823 := by exact prefixLift 1231823
  have htrace : WordTrace (prefixWord ++ tailWord_1231823) baseStart_1231823 baseEnd_1231823 := by
    simpa [prefixWord, tailWord_1231823, baseEnd_1231823] using wordTrace_append hprefix tailTrace_1231823
  have hstable : (prefixWord ++ tailWord_1231823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231823).length < 2 ^ (prefixWord ++ tailWord_1231823).sum := by decide
  have hdescent : baseEnd_1231823 < baseStart_1231823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231833 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 1, 1, 6]
def baseStart_1231833 : Nat := 118140960795 + 1231833 * 2 ^ 59
def prefixEnd_1231833 : Nat := 4983230072969 + 3 ^ 40 * 1231833 * 2
def baseEnd_1231833 : Nat := 632522415069984181422409

theorem tailTrace_1231833 : CollatzResearch.WordTrace tailWord_1231833 prefixEnd_1231833 632522415069984181422409 := by
  unfold tailWord_1231833
  simp only [CollatzResearch.WordTrace]
  refine ⟨44928640546286896172276153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29952427030857930781517435 44928640546286896172276153)
  ·
    refine ⟨33696480409715172129207115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44928640546286896172276153 33696480409715172129207115)
    ·
      refine ⟨50544720614572758193810673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33696480409715172129207115 50544720614572758193810673)
      ·
        refine ⟨37908540460929568645358005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50544720614572758193810673 37908540460929568645358005)
        ·
          refine ⟨3553925668212147060502313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37908540460929568645358005 3553925668212147060502313)
          ·
            refine ⟨2665444251159110295376735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3553925668212147060502313 2665444251159110295376735)
            ·
              refine ⟨3998166376738665443065103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2665444251159110295376735 3998166376738665443065103)
              ·
                refine ⟨5997249565107998164597655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3998166376738665443065103 5997249565107998164597655)
                ·
                  refine ⟨8995874347661997246896483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5997249565107998164597655 8995874347661997246896483)
                  ·
                    refine ⟨13493811521492995870344725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8995874347661997246896483 13493811521492995870344725)
                    ·
                      refine ⟨632522415069984181422409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13493811521492995870344725 632522415069984181422409)
                      ·
                        rfl

theorem cell23_1231833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_1231833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231833 prefixEnd_1231833 := by exact prefixLift 1231833
  have htrace : WordTrace (prefixWord ++ tailWord_1231833) baseStart_1231833 baseEnd_1231833 := by
    simpa [prefixWord, tailWord_1231833, baseEnd_1231833] using wordTrace_append hprefix tailTrace_1231833
  have hstable : (prefixWord ++ tailWord_1231833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231833).length < 2 ^ (prefixWord ++ tailWord_1231833).sum := by decide
  have hdescent : baseEnd_1231833 < baseStart_1231833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231837 : List Nat := [1, 4, 3, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_1231837 : Nat := 118140960795 + 1231837 * 2 ^ 59
def prefixEnd_1231837 : Nat := 4983230072969 + 3 ^ 40 * 1231837 * 2
def baseEnd_1231837 : Nat := 632524468992602165772391

theorem tailTrace_1231837 : CollatzResearch.WordTrace tailWord_1231837 prefixEnd_1231837 632524468992602165772391 := by
  unfold tailWord_1231837
  simp only [CollatzResearch.WordTrace]
  refine ⟨44928786438272404855421765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29952524292181603236947843 44928786438272404855421765)
  ·
    refine ⟨8424147457176075910391581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44928786438272404855421765 8424147457176075910391581)
    ·
      refine ⟨3159055296441028466396843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8424147457176075910391581 3159055296441028466396843)
      ·
        refine ⟨4738582944661542699595265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3159055296441028466396843 4738582944661542699595265)
        ·
          refine ⟨3553937208496157024696449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4738582944661542699595265 3553937208496157024696449)
          ·
            refine ⟨2665452906372117768522337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3553937208496157024696449 2665452906372117768522337)
            ·
              refine ⟨1999089679779088326391753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2665452906372117768522337 1999089679779088326391753)
              ·
                refine ⟨1499317259834316244793815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1999089679779088326391753 1499317259834316244793815)
                ·
                  refine ⟨2248975889751474367190723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1499317259834316244793815 2248975889751474367190723)
                  ·
                    refine ⟨3373463834627211550786085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2248975889751474367190723 3373463834627211550786085)
                    ·
                      refine ⟨632524468992602165772391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3373463834627211550786085 632524468992602165772391)
                      ·
                        rfl

theorem cell23_1231837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_1231837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231837 prefixEnd_1231837 := by exact prefixLift 1231837
  have htrace : WordTrace (prefixWord ++ tailWord_1231837) baseStart_1231837 baseEnd_1231837 := by
    simpa [prefixWord, tailWord_1231837, baseEnd_1231837] using wordTrace_append hprefix tailTrace_1231837
  have hstable : (prefixWord ++ tailWord_1231837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231837).length < 2 ^ (prefixWord ++ tailWord_1231837).sum := by decide
  have hdescent : baseEnd_1231837 < baseStart_1231837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231856 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 1, 9]
def baseStart_1231856 : Nat := 118140960795 + 1231856 * 2 ^ 59
def prefixEnd_1231856 : Nat := 4983230072969 + 3 ^ 40 * 1231856 * 2
def baseEnd_1231856 : Nat := 210844741708345863811601

theorem tailTrace_1231856 : CollatzResearch.WordTrace tailWord_1231856 prefixEnd_1231856 210844741708345863811601 := by
  unfold tailWord_1231856
  simp only [CollatzResearch.WordTrace]
  refine ⟨22464739712601785550181711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29952986283469047400242281 22464739712601785550181711)
  ·
    refine ⟨33697109568902678325272567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22464739712601785550181711 33697109568902678325272567)
    ·
      refine ⟨50545664353354017487908851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33697109568902678325272567 50545664353354017487908851)
      ·
        refine ⟨75818496530031026231863277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50545664353354017487908851 75818496530031026231863277)
        ·
          refine ⟨28431936198761634836948729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75818496530031026231863277 28431936198761634836948729)
          ·
            refine ⟨21323952149071226127711547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28431936198761634836948729 21323952149071226127711547)
            ·
              refine ⟨31985928223606839191567321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21323952149071226127711547 31985928223606839191567321)
              ·
                refine ⟨23989446167705129393675491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31985928223606839191567321 23989446167705129393675491)
                ·
                  refine ⟨35984169251557694090513237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23989446167705129393675491 35984169251557694090513237)
                  ·
                    refine ⟨210844741708345863811601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 35984169251557694090513237 210844741708345863811601)
                    ·
                      rfl

theorem cell23_1231856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 9].length) (baseStart_1231856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231856 prefixEnd_1231856 := by exact prefixLift 1231856
  have htrace : WordTrace (prefixWord ++ tailWord_1231856) baseStart_1231856 baseEnd_1231856 := by
    simpa [prefixWord, tailWord_1231856, baseEnd_1231856] using wordTrace_append hprefix tailTrace_1231856
  have hstable : (prefixWord ++ tailWord_1231856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231856).length < 2 ^ (prefixWord ++ tailWord_1231856).sum := by decide
  have hdescent : baseEnd_1231856 < baseStart_1231856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231897 : List Nat := [1, 2, 1, 2, 1, 1, 7, 2, 1, 3, 2]
def baseStart_1231897 : Nat := 118140960795 + 1231897 * 2 ^ 59
def prefixEnd_1231897 : Nat := 4983230072969 + 3 ^ 40 * 1231897 * 2
def baseEnd_1231897 : Nat := 632555277831871931022115

theorem tailTrace_1231897 : CollatzResearch.WordTrace tailWord_1231897 prefixEnd_1231897 632555277831871931022115 := by
  unfold tailWord_1231897
  simp only [CollatzResearch.WordTrace]
  refine ⟨44930974818055035102605945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29953983212036690068403963 44930974818055035102605945)
  ·
    refine ⟨33698231113541276326954459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44930974818055035102605945 33698231113541276326954459)
    ·
      refine ⟨50547346670311914490431689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33698231113541276326954459 50547346670311914490431689)
      ·
        refine ⟨37910510002733935867823767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50547346670311914490431689 37910510002733935867823767)
        ·
          refine ⟨56865765004100903801735651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37910510002733935867823767 56865765004100903801735651)
          ·
            refine ⟨85298647506151355702603477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56865765004100903801735651 85298647506151355702603477)
            ·
              refine ⟨1999187050925422399279769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 85298647506151355702603477 1999187050925422399279769)
              ·
                refine ⟨1499390288194066799459827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1999187050925422399279769 1499390288194066799459827)
                ·
                  refine ⟨2249085432291100199189741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1499390288194066799459827 2249085432291100199189741)
                  ·
                    refine ⟨843407037109162574696153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2249085432291100199189741 843407037109162574696153)
                    ·
                      refine ⟨632555277831871931022115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 843407037109162574696153 632555277831871931022115)
                      ·
                        rfl

theorem cell23_1231897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 3, 2].length) (baseStart_1231897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231897 prefixEnd_1231897 := by exact prefixLift 1231897
  have htrace : WordTrace (prefixWord ++ tailWord_1231897) baseStart_1231897 baseEnd_1231897 := by
    simpa [prefixWord, tailWord_1231897, baseEnd_1231897] using wordTrace_append hprefix tailTrace_1231897
  have hstable : (prefixWord ++ tailWord_1231897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231897).length < 2 ^ (prefixWord ++ tailWord_1231897).sum := by decide
  have hdescent : baseEnd_1231897 < baseStart_1231897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231923 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 4]
def baseStart_1231923 : Nat := 118140960795 + 1231923 * 2 ^ 59
def prefixEnd_1231923 : Nat := 4983230072969 + 3 ^ 40 * 1231923 * 2
def baseEnd_1231923 : Nat := 632568628328888829296995

theorem tailTrace_1231923 : CollatzResearch.WordTrace tailWord_1231923 prefixEnd_1231923 632568628328888829296995 := by
  unfold tailWord_1231923
  simp only [CollatzResearch.WordTrace]
  refine ⟨44931923115960841543052423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29954615410640561028701615 44931923115960841543052423)
  ·
    refine ⟨67397884673941262314578635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44931923115960841543052423 67397884673941262314578635)
    ·
      refine ⟨101096827010911893471867953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67397884673941262314578635 101096827010911893471867953)
      ·
        refine ⟨75822620258183920103900965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101096827010911893471867953 75822620258183920103900965)
        ·
          refine ⟨14216741298409485019481431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75822620258183920103900965 14216741298409485019481431)
          ·
            refine ⟨21325111947614227529222147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14216741298409485019481431 21325111947614227529222147)
            ·
              refine ⟨31987667921421341293833221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21325111947614227529222147 31987667921421341293833221)
              ·
                refine ⟨5997687735266501492593729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31987667921421341293833221 5997687735266501492593729)
                ·
                  refine ⟨4498265801449876119445297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5997687735266501492593729 4498265801449876119445297)
                  ·
                    refine ⟨3373699351087407089583973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4498265801449876119445297 3373699351087407089583973)
                    ·
                      refine ⟨632568628328888829296995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3373699351087407089583973 632568628328888829296995)
                      ·
                        rfl

theorem cell23_1231923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_1231923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231923 prefixEnd_1231923 := by exact prefixLift 1231923
  have htrace : WordTrace (prefixWord ++ tailWord_1231923) baseStart_1231923 baseEnd_1231923 := by
    simpa [prefixWord, tailWord_1231923, baseEnd_1231923] using wordTrace_append hprefix tailTrace_1231923
  have hstable : (prefixWord ++ tailWord_1231923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231923).length < 2 ^ (prefixWord ++ tailWord_1231923).sum := by decide
  have hdescent : baseEnd_1231923 < baseStart_1231923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231965 : List Nat := [1, 4, 4, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_1231965 : Nat := 118140960795 + 1231965 * 2 ^ 59
def prefixEnd_1231965 : Nat := 4983230072969 + 3 ^ 40 * 1231965 * 2
def baseEnd_1231965 : Nat := 632590194516377664971803

theorem tailTrace_1231965 : CollatzResearch.WordTrace tailWord_1231965 prefixEnd_1231965 632590194516377664971803 := by
  unfold tailWord_1231965
  simp only [CollatzResearch.WordTrace]
  refine ⟨44933454981808682716081349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29955636654539121810720899 44933454981808682716081349)
  ·
    refine ⟨8425022809089128009265253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44933454981808682716081349 8425022809089128009265253)
    ·
      refine ⟨1579691776704211501737235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8425022809089128009265253 1579691776704211501737235)
      ·
        refine ⟨2369537665056317252605853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1579691776704211501737235 2369537665056317252605853)
        ·
          refine ⟨888576624396118969727195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2369537665056317252605853 888576624396118969727195)
          ·
            refine ⟨1332864936594178454590793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888576624396118969727195 1332864936594178454590793)
            ·
              refine ⟨999648702445633840943095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1332864936594178454590793 999648702445633840943095)
              ·
                refine ⟨1499473053668450761414643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 999648702445633840943095 1499473053668450761414643)
                ·
                  refine ⟨2249209580502676142121965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1499473053668450761414643 2249209580502676142121965)
                  ·
                    refine ⟨843453592688503553295737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2249209580502676142121965 843453592688503553295737)
                    ·
                      refine ⟨632590194516377664971803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 843453592688503553295737 632590194516377664971803)
                      ·
                        rfl

theorem cell23_1231965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_1231965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231965 prefixEnd_1231965 := by exact prefixLift 1231965
  have htrace : WordTrace (prefixWord ++ tailWord_1231965) baseStart_1231965 baseEnd_1231965 := by
    simpa [prefixWord, tailWord_1231965, baseEnd_1231965] using wordTrace_append hprefix tailTrace_1231965
  have hstable : (prefixWord ++ tailWord_1231965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231965).length < 2 ^ (prefixWord ++ tailWord_1231965).sum := by decide
  have hdescent : baseEnd_1231965 < baseStart_1231965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231990 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1231990 : Nat := 118140960795 + 1231990 * 2 ^ 59
def prefixEnd_1231990 : Nat := 4983230072969 + 3 ^ 40 * 1231990 * 2
def baseEnd_1231990 : Nat := 632603031532740067159187

theorem tailTrace_1231990 : CollatzResearch.WordTrace tailWord_1231990 prefixEnd_1231990 632603031532740067159187 := by
  unfold tailWord_1231990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2808397925419881999108839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29956244537812074657160949 2808397925419881999108839)
  ·
    refine ⟨4212596888129822998663259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2808397925419881999108839 4212596888129822998663259)
    ·
      refine ⟨6318895332194734497994889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4212596888129822998663259 6318895332194734497994889)
      ·
        refine ⟨4739171499146050873496167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6318895332194734497994889 4739171499146050873496167)
        ·
          refine ⟨7108757248719076310244251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4739171499146050873496167 7108757248719076310244251)
          ·
            refine ⟨10663135873078614465366377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7108757248719076310244251 10663135873078614465366377)
            ·
              refine ⟨7997351904808960849024783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10663135873078614465366377 7997351904808960849024783)
              ·
                refine ⟨11996027857213441273537175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7997351904808960849024783 11996027857213441273537175)
                ·
                  refine ⟨17994041785820161910305763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11996027857213441273537175 17994041785820161910305763)
                  ·
                    refine ⟨26991062678730242865458645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17994041785820161910305763 26991062678730242865458645)
                    ·
                      refine ⟨632603031532740067159187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26991062678730242865458645 632603031532740067159187)
                      ·
                        rfl

theorem cell23_1231990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1231990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1231990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1231990 prefixEnd_1231990 := by exact prefixLift 1231990
  have htrace : WordTrace (prefixWord ++ tailWord_1231990) baseStart_1231990 baseEnd_1231990 := by
    simpa [prefixWord, tailWord_1231990, baseEnd_1231990] using wordTrace_append hprefix tailTrace_1231990
  have hstable : (prefixWord ++ tailWord_1231990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231990).length < 2 ^ (prefixWord ++ tailWord_1231990).sum := by decide
  have hdescent : baseEnd_1231990 < baseStart_1231990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232034 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1232034 : Nat := 118140960795 + 1232034 * 2 ^ 59
def prefixEnd_1232034 : Nat := 4983230072969 + 3 ^ 40 * 1232034 * 2
def baseEnd_1232034 : Nat := 632625624681537895008985

theorem tailTrace_1232034 : CollatzResearch.WordTrace tailWord_1232034 prefixEnd_1232034 632625624681537895008985 := by
  unfold tailWord_1232034
  simp only [CollatzResearch.WordTrace]
  refine ⟨11233992904639676875085789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29957314412372471666895437 11233992904639676875085789)
  ·
    refine ⟨4212747339239878828157171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11233992904639676875085789 4212747339239878828157171)
    ·
      refine ⟨6319121008859818242235757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4212747339239878828157171 6319121008859818242235757)
      ·
        refine ⟨2369670378322431840838409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6319121008859818242235757 2369670378322431840838409)
        ·
          refine ⟨1777252783741823880628807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2369670378322431840838409 1777252783741823880628807)
          ·
            refine ⟨2665879175612735820943211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1777252783741823880628807 2665879175612735820943211)
            ·
              refine ⟨3998818763419103731414817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2665879175612735820943211 3998818763419103731414817)
              ·
                refine ⟨2999114072564327798561113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3998818763419103731414817 2999114072564327798561113)
                ·
                  refine ⟨2249335554423245848920835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2999114072564327798561113 2249335554423245848920835)
                  ·
                    refine ⟨3374003331634868773381253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2249335554423245848920835 3374003331634868773381253)
                    ·
                      refine ⟨632625624681537895008985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3374003331634868773381253 632625624681537895008985)
                      ·
                        rfl

theorem cell23_1232034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1232034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232034 prefixEnd_1232034 := by exact prefixLift 1232034
  have htrace : WordTrace (prefixWord ++ tailWord_1232034) baseStart_1232034 baseEnd_1232034 := by
    simpa [prefixWord, tailWord_1232034, baseEnd_1232034] using wordTrace_append hprefix tailTrace_1232034
  have hstable : (prefixWord ++ tailWord_1232034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232034).length < 2 ^ (prefixWord ++ tailWord_1232034).sum := by decide
  have hdescent : baseEnd_1232034 < baseStart_1232034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232037 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 2, 2, 3]
def baseStart_1232037 : Nat := 118140960795 + 1232037 * 2 ^ 59
def prefixEnd_1232037 : Nat := 4983230072969 + 3 ^ 40 * 1232037 * 2
def baseEnd_1232037 : Nat := 632627165123501383271471

theorem tailTrace_1232037 : CollatzResearch.WordTrace tailWord_1232037 prefixEnd_1232037 632627165123501383271471 := by
  unfold tailWord_1232037
  simp only [CollatzResearch.WordTrace]
  refine ⟨44936081037547839012702365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29957387358365226008468243 44936081037547839012702365)
  ·
    refine ⟨16851030389080439629763387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44936081037547839012702365 16851030389080439629763387)
    ·
      refine ⟨25276545583620659444645081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16851030389080439629763387 25276545583620659444645081)
      ·
        refine ⟨18957409187715494583483811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25276545583620659444645081 18957409187715494583483811)
        ·
          refine ⟨28436113781573241875225717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18957409187715494583483811 28436113781573241875225717)
          ·
            refine ⟨2665885667022491425802411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28436113781573241875225717 2665885667022491425802411)
            ·
              refine ⟨3998828500533737138703617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2665885667022491425802411 3998828500533737138703617)
              ·
                refine ⟨2999121375400302854027713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3998828500533737138703617 2999121375400302854027713)
                ·
                  refine ⟨2249341031550227140520785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2999121375400302854027713 2249341031550227140520785)
                  ·
                    refine ⟨1687005773662670355390589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2249341031550227140520785 1687005773662670355390589)
                    ·
                      refine ⟨632627165123501383271471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1687005773662670355390589 632627165123501383271471)
                      ·
                        rfl

theorem cell23_1232037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_1232037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232037 prefixEnd_1232037 := by exact prefixLift 1232037
  have htrace : WordTrace (prefixWord ++ tailWord_1232037) baseStart_1232037 baseEnd_1232037 := by
    simpa [prefixWord, tailWord_1232037, baseEnd_1232037] using wordTrace_append hprefix tailTrace_1232037
  have hstable : (prefixWord ++ tailWord_1232037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232037).length < 2 ^ (prefixWord ++ tailWord_1232037).sum := by decide
  have hdescent : baseEnd_1232037 < baseStart_1232037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232057 : List Nat := [1, 2, 1, 4, 1, 3, 4, 1, 6]
def baseStart_1232057 : Nat := 118140960795 + 1232057 * 2 ^ 59
def prefixEnd_1232057 : Nat := 4983230072969 + 3 ^ 40 * 1232057 * 2
def baseEnd_1232057 : Nat := 70293048304065700557931

theorem tailTrace_1232057 : CollatzResearch.WordTrace tailWord_1232057 prefixEnd_1232057 70293048304065700557931 := by
  unfold tailWord_1232057
  simp only [CollatzResearch.WordTrace]
  refine ⟨44936810497475382428430425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29957873664983588285620283 44936810497475382428430425)
  ·
    refine ⟨33702607873106536821322819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44936810497475382428430425 33702607873106536821322819)
    ·
      refine ⟨50553911809659805231984229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33702607873106536821322819 50553911809659805231984229)
      ·
        refine ⟨9478858464311213480997043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50553911809659805231984229 9478858464311213480997043)
        ·
          refine ⟨14218287696466820221495565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9478858464311213480997043 14218287696466820221495565)
          ·
            refine ⟨5331857886175057583060837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14218287696466820221495565 5331857886175057583060837)
            ·
              refine ⟨999723353657823296823907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5331857886175057583060837 999723353657823296823907)
              ·
                refine ⟨1499585030486734945235861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 999723353657823296823907 1499585030486734945235861)
                ·
                  refine ⟨70293048304065700557931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1499585030486734945235861 70293048304065700557931)
                  ·
                    rfl

theorem cell23_1232057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 6].length) (baseStart_1232057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232057 prefixEnd_1232057 := by exact prefixLift 1232057
  have htrace : WordTrace (prefixWord ++ tailWord_1232057) baseStart_1232057 baseEnd_1232057 := by
    simpa [prefixWord, tailWord_1232057, baseEnd_1232057] using wordTrace_append hprefix tailTrace_1232057
  have hstable : (prefixWord ++ tailWord_1232057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232057).length < 2 ^ (prefixWord ++ tailWord_1232057).sum := by decide
  have hdescent : baseEnd_1232057 < baseStart_1232057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232127 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 3]
def baseStart_1232127 : Nat := 118140960795 + 1232127 * 2 ^ 59
def prefixEnd_1232127 : Nat := 4983230072969 + 3 ^ 40 * 1232127 * 2
def baseEnd_1232127 : Nat := 632673378382406031146057

theorem tailTrace_1232127 : CollatzResearch.WordTrace tailWord_1232127 prefixEnd_1232127 632673378382406031146057 := by
  unfold tailWord_1232127
  simp only [CollatzResearch.WordTrace]
  refine ⟨44939363607221784383478635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29959575738147856255652423 44939363607221784383478635)
  ·
    refine ⟨67409045410832676575217953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44939363607221784383478635 67409045410832676575217953)
    ·
      refine ⟨50556784058124507431413465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67409045410832676575217953 50556784058124507431413465)
      ·
        refine ⟨37917588043593380573560099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50556784058124507431413465 37917588043593380573560099)
        ·
          refine ⟨56876382065390070860340149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37917588043593380573560099 56876382065390070860340149)
          ·
            refine ⟨5332160818630319143156889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56876382065390070860340149 5332160818630319143156889)
            ·
              refine ⟨3999120613972739357367667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5332160818630319143156889 3999120613972739357367667)
              ·
                refine ⟨5998680920959109036051501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3999120613972739357367667 5998680920959109036051501)
                ·
                  refine ⟨2249505345359665888519313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5998680920959109036051501 2249505345359665888519313)
                  ·
                    refine ⟨1687129009019749416389485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2249505345359665888519313 1687129009019749416389485)
                    ·
                      refine ⟨632673378382406031146057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1687129009019749416389485 632673378382406031146057)
                      ·
                        rfl

theorem cell23_1232127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_1232127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232127 prefixEnd_1232127 := by exact prefixLift 1232127
  have htrace : WordTrace (prefixWord ++ tailWord_1232127) baseStart_1232127 baseEnd_1232127 := by
    simpa [prefixWord, tailWord_1232127, baseEnd_1232127] using wordTrace_append hprefix tailTrace_1232127
  have hstable : (prefixWord ++ tailWord_1232127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232127).length < 2 ^ (prefixWord ++ tailWord_1232127).sum := by decide
  have hdescent : baseEnd_1232127 < baseStart_1232127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232198 : List Nat := [6, 1, 1, 3, 2, 1, 9]
def baseStart_1232198 : Nat := 118140960795 + 1232198 * 2 ^ 59
def prefixEnd_1232198 : Nat := 4983230072969 + 3 ^ 40 * 1232198 * 2
def baseEnd_1232198 : Nat := 7811232537146608066151

theorem tailTrace_1232198 : CollatzResearch.WordTrace tailWord_1232198 prefixEnd_1232198 7811232537146608066151 := by
  unfold tailWord_1232198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1404436037186392609666039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29961302126643042339542165 1404436037186392609666039)
  ·
    refine ⟨2106654055779588914499059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1404436037186392609666039 2106654055779588914499059)
    ·
      refine ⟨3159981083669383371748589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2106654055779588914499059 3159981083669383371748589)
      ·
        refine ⟨1184992906376018764405721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3159981083669383371748589 1184992906376018764405721)
        ·
          refine ⟨888744679782014073304291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1184992906376018764405721 888744679782014073304291)
          ·
            refine ⟨1333117019673021109956437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888744679782014073304291 1333117019673021109956437)
            ·
              refine ⟨7811232537146608066151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1333117019673021109956437 7811232537146608066151)
              ·
                rfl

theorem cell23_1232198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 9].length) (baseStart_1232198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232198 prefixEnd_1232198 := by exact prefixLift 1232198
  have htrace : WordTrace (prefixWord ++ tailWord_1232198) baseStart_1232198 baseEnd_1232198 := by
    simpa [prefixWord, tailWord_1232198, baseEnd_1232198] using wordTrace_append hprefix tailTrace_1232198
  have hstable : (prefixWord ++ tailWord_1232198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232198).length < 2 ^ (prefixWord ++ tailWord_1232198).sum := by decide
  have hdescent : baseEnd_1232198 < baseStart_1232198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232267 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 2, 5]
def baseStart_1232267 : Nat := 118140960795 + 1232267 * 2 ^ 59
def prefixEnd_1232267 : Nat := 4983230072969 + 3 ^ 40 * 1232267 * 2
def baseEnd_1232267 : Nat := 210915088558011827798471

theorem tailTrace_1232267 : CollatzResearch.WordTrace tailWord_1232267 prefixEnd_1232267 210915088558011827798471 := by
  unfold tailWord_1232267
  simp only [CollatzResearch.WordTrace]
  refine ⟨44944469826714588293575055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29962979884476392195716703 44944469826714588293575055)
  ·
    refine ⟨67416704740071882440362583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44944469826714588293575055 67416704740071882440362583)
    ·
      refine ⟨101125057110107823660543875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67416704740071882440362583 101125057110107823660543875)
      ·
        refine ⟨151687585665161735490815813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101125057110107823660543875 151687585665161735490815813)
        ·
          refine ⟨28441422312217825404527965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151687585665161735490815813 28441422312217825404527965)
          ·
            refine ⟨10665533367081684526697987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28441422312217825404527965 10665533367081684526697987)
            ·
              refine ⟨15998300050622526790046981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10665533367081684526697987 15998300050622526790046981)
              ·
                refine ⟨2999681259491723773133809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15998300050622526790046981 2999681259491723773133809)
                ·
                  refine ⟨2249760944618792829850357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2999681259491723773133809 2249760944618792829850357)
                  ·
                    refine ⟨210915088558011827798471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2249760944618792829850357 210915088558011827798471)
                    ·
                      rfl

theorem cell23_1232267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 5].length) (baseStart_1232267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232267 prefixEnd_1232267 := by exact prefixLift 1232267
  have htrace : WordTrace (prefixWord ++ tailWord_1232267) baseStart_1232267 baseEnd_1232267 := by
    simpa [prefixWord, tailWord_1232267, baseEnd_1232267] using wordTrace_append hprefix tailTrace_1232267
  have hstable : (prefixWord ++ tailWord_1232267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232267).length < 2 ^ (prefixWord ++ tailWord_1232267).sum := by decide
  have hdescent : baseEnd_1232267 < baseStart_1232267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232277 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_1232277 : Nat := 118140960795 + 1232277 * 2 ^ 59
def prefixEnd_1232277 : Nat := 4983230072969 + 3 ^ 40 * 1232277 * 2
def baseEnd_1232277 : Nat := 632750400480580444270367

theorem tailTrace_1232277 : CollatzResearch.WordTrace tailWord_1232277 prefixEnd_1232277 632750400480580444270367 := by
  unfold tailWord_1232277
  simp only [CollatzResearch.WordTrace]
  refine ⟨44944834556678360001439085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29963223037785573334292723 44944834556678360001439085)
  ·
    refine ⟨16854312958754385000539657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44944834556678360001439085 16854312958754385000539657)
    ·
      refine ⟨12640734719065788750404743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16854312958754385000539657 12640734719065788750404743)
      ·
        refine ⟨18961102078598683125607115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12640734719065788750404743 18961102078598683125607115)
        ·
          refine ⟨28441653117898024688410673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18961102078598683125607115 28441653117898024688410673)
          ·
            refine ⟨21331239838423518516308005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28441653117898024688410673 21331239838423518516308005)
            ·
              refine ⟨3999607469704409721807751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21331239838423518516308005 3999607469704409721807751)
              ·
                refine ⟨5999411204556614582711627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3999607469704409721807751 5999411204556614582711627)
                ·
                  refine ⟨8999116806834921874067441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5999411204556614582711627 8999116806834921874067441)
                  ·
                    refine ⟨6749337605126191405550581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8999116806834921874067441 6749337605126191405550581)
                    ·
                      refine ⟨632750400480580444270367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6749337605126191405550581 632750400480580444270367)
                      ·
                        rfl

theorem cell23_1232277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_1232277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232277 prefixEnd_1232277 := by exact prefixLift 1232277
  have htrace : WordTrace (prefixWord ++ tailWord_1232277) baseStart_1232277 baseEnd_1232277 := by
    simpa [prefixWord, tailWord_1232277, baseEnd_1232277] using wordTrace_append hprefix tailTrace_1232277
  have hstable : (prefixWord ++ tailWord_1232277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232277).length < 2 ^ (prefixWord ++ tailWord_1232277).sum := by decide
  have hdescent : baseEnd_1232277 < baseStart_1232277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232301 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1232301 : Nat := 118140960795 + 1232301 * 2 ^ 59
def prefixEnd_1232301 : Nat := 4983230072969 + 3 ^ 40 * 1232301 * 2
def baseEnd_1232301 : Nat := 210920908005429450123419

theorem tailTrace_1232301 : CollatzResearch.WordTrace tailWord_1232301 prefixEnd_1232301 210920908005429450123419 := by
  unfold tailWord_1232301
  simp only [CollatzResearch.WordTrace]
  refine ⟨44945709908591412100312757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29963806605727608066875171 44945709908591412100312757)
  ·
    refine ⟨4213660303930444884404321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44945709908591412100312757 4213660303930444884404321)
    ·
      refine ⟨3160245227947833663303241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4213660303930444884404321 3160245227947833663303241)
      ·
        refine ⟨2370183920960875247477431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3160245227947833663303241 2370183920960875247477431)
        ·
          refine ⟨3555275881441312871216147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2370183920960875247477431 3555275881441312871216147)
          ·
            refine ⟨5332913822161969306824221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3555275881441312871216147 5332913822161969306824221)
            ·
              refine ⟨1999842683310738490059083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5332913822161969306824221 1999842683310738490059083)
              ·
                refine ⟨2999764024966107735088625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1999842683310738490059083 2999764024966107735088625)
                ·
                  refine ⟨2249823018724580801316469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2999764024966107735088625 2249823018724580801316469)
                  ·
                    refine ⟨210920908005429450123419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2249823018724580801316469 210920908005429450123419)
                    ·
                      rfl

theorem cell23_1232301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1232301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232301 prefixEnd_1232301 := by exact prefixLift 1232301
  have htrace : WordTrace (prefixWord ++ tailWord_1232301) baseStart_1232301 baseEnd_1232301 := by
    simpa [prefixWord, tailWord_1232301, baseEnd_1232301] using wordTrace_append hprefix tailTrace_1232301
  have hstable : (prefixWord ++ tailWord_1232301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232301).length < 2 ^ (prefixWord ++ tailWord_1232301).sum := by decide
  have hdescent : baseEnd_1232301 < baseStart_1232301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232317 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_1232317 : Nat := 118140960795 + 1232317 * 2 ^ 59
def prefixEnd_1232317 : Nat := 4983230072969 + 3 ^ 40 * 1232317 * 2
def baseEnd_1232317 : Nat := 632770939706760287770183

theorem tailTrace_1232317 : CollatzResearch.WordTrace tailWord_1232317 prefixEnd_1232317 632770939706760287770183 := by
  unfold tailWord_1232317
  simp only [CollatzResearch.WordTrace]
  refine ⟨44946293476533446832895205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29964195651022297888596803 44946293476533446832895205)
  ·
    refine ⟨8427430026850021281167851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44946293476533446832895205 8427430026850021281167851)
    ·
      refine ⟨12641145040275031921751777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8427430026850021281167851 12641145040275031921751777)
      ·
        refine ⟨9480858780206273941313833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12641145040275031921751777 9480858780206273941313833)
        ·
          refine ⟨7110644085154705455985375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9480858780206273941313833 7110644085154705455985375)
          ·
            refine ⟨10665966127732058183978063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7110644085154705455985375 10665966127732058183978063)
            ·
              refine ⟨15998949191598087275967095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10665966127732058183978063 15998949191598087275967095)
              ·
                refine ⟨23998423787397130913950643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15998949191598087275967095 23998423787397130913950643)
                ·
                  refine ⟨35997635681095696370925965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23998423787397130913950643 35997635681095696370925965)
                  ·
                    refine ⟨13499113380410886139097237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35997635681095696370925965 13499113380410886139097237)
                    ·
                      refine ⟨632770939706760287770183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13499113380410886139097237 632770939706760287770183)
                      ·
                        rfl

theorem cell23_1232317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_1232317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232317 prefixEnd_1232317 := by exact prefixLift 1232317
  have htrace : WordTrace (prefixWord ++ tailWord_1232317) baseStart_1232317 baseEnd_1232317 := by
    simpa [prefixWord, tailWord_1232317, baseEnd_1232317] using wordTrace_append hprefix tailTrace_1232317
  have hstable : (prefixWord ++ tailWord_1232317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232317).length < 2 ^ (prefixWord ++ tailWord_1232317).sum := by decide
  have hdescent : baseEnd_1232317 < baseStart_1232317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232327 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 8]
def baseStart_1232327 : Nat := 118140960795 + 1232327 * 2 ^ 59
def prefixEnd_1232327 : Nat := 4983230072969 + 3 ^ 40 * 1232327 * 2
def baseEnd_1232327 : Nat := 70308452723700583182793

theorem tailTrace_1232327 : CollatzResearch.WordTrace tailWord_1232327 prefixEnd_1232327 70308452723700583182793 := by
  unfold tailWord_1232327
  simp only [CollatzResearch.WordTrace]
  refine ⟨44946658206497218540759235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29964438804331479027172823 44946658206497218540759235)
  ·
    refine ⟨67419987309745827811138853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44946658206497218540759235 67419987309745827811138853)
    ·
      refine ⟨12641247620577342714588535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67419987309745827811138853 12641247620577342714588535)
      ·
        refine ⟨18961871430866014071882803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12641247620577342714588535 18961871430866014071882803)
        ·
          refine ⟨28442807146299021107824205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18961871430866014071882803 28442807146299021107824205)
          ·
            refine ⟨10666052679862132915434077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28442807146299021107824205 10666052679862132915434077)
            ·
              refine ⟨3999769754948299843287779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10666052679862132915434077 3999769754948299843287779)
              ·
                refine ⟨5999654632422449764931669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3999769754948299843287779 5999654632422449764931669)
                ·
                  refine ⟨70308452723700583182793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5999654632422449764931669 70308452723700583182793)
                  ·
                    rfl

theorem cell23_1232327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 8].length) (baseStart_1232327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232327 prefixEnd_1232327 := by exact prefixLift 1232327
  have htrace : WordTrace (prefixWord ++ tailWord_1232327) baseStart_1232327 baseEnd_1232327 := by
    simpa [prefixWord, tailWord_1232327, baseEnd_1232327] using wordTrace_append hprefix tailTrace_1232327
  have hstable : (prefixWord ++ tailWord_1232327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232327).length < 2 ^ (prefixWord ++ tailWord_1232327).sum := by decide
  have hdescent : baseEnd_1232327 < baseStart_1232327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232331 : List Nat := [1, 1, 1, 1, 3, 3, 4, 4, 1, 4]
def baseStart_1232331 : Nat := 118140960795 + 1232331 * 2 ^ 59
def prefixEnd_1232331 : Nat := 4983230072969 + 3 ^ 40 * 1232331 * 2
def baseEnd_1232331 : Nat := 210926042811974410998373

theorem tailTrace_1232331 : CollatzResearch.WordTrace tailWord_1232331 prefixEnd_1232331 210926042811974410998373 := by
  unfold tailWord_1232331
  simp only [CollatzResearch.WordTrace]
  refine ⟨44946804098482727223904847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29964536065655151482603231 44946804098482727223904847)
  ·
    refine ⟨67420206147724090835857271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44946804098482727223904847 67420206147724090835857271)
    ·
      refine ⟨101130309221586136253785907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67420206147724090835857271 101130309221586136253785907)
      ·
        refine ⟨151695463832379204380678861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101130309221586136253785907 151695463832379204380678861)
        ·
          refine ⟨56885798937142201642754573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151695463832379204380678861 56885798937142201642754573)
          ·
            refine ⟨21332174601428325616032965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56885798937142201642754573 21332174601428325616032965)
            ·
              refine ⟨3999782737767811053006181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21332174601428325616032965 3999782737767811053006181)
              ·
                refine ⟨749959263331464572438659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3999782737767811053006181 749959263331464572438659)
                ·
                  refine ⟨1124938894997196858657989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 749959263331464572438659 1124938894997196858657989)
                  ·
                    refine ⟨210926042811974410998373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1124938894997196858657989 210926042811974410998373)
                    ·
                      rfl

theorem cell23_1232331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 1, 4].length) (baseStart_1232331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232331 prefixEnd_1232331 := by exact prefixLift 1232331
  have htrace : WordTrace (prefixWord ++ tailWord_1232331) baseStart_1232331 baseEnd_1232331 := by
    simpa [prefixWord, tailWord_1232331, baseEnd_1232331] using wordTrace_append hprefix tailTrace_1232331
  have hstable : (prefixWord ++ tailWord_1232331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232331).length < 2 ^ (prefixWord ++ tailWord_1232331).sum := by decide
  have hdescent : baseEnd_1232331 < baseStart_1232331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232381 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 4, 3, 2]
def baseStart_1232381 : Nat := 118140960795 + 1232381 * 2 ^ 59
def prefixEnd_1232381 : Nat := 4983230072969 + 3 ^ 40 * 1232381 * 2
def baseEnd_1232381 : Nat := 632803802468648037369889

theorem tailTrace_1232381 : CollatzResearch.WordTrace tailWord_1232381 prefixEnd_1232381 632803802468648037369889 := by
  unfold tailWord_1232381
  simp only [CollatzResearch.WordTrace]
  refine ⟨44948627748301585763224997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29965751832201057175483331 44948627748301585763224997)
  ·
    refine ⟨8427867702806547330604687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44948627748301585763224997 8427867702806547330604687)
    ·
      refine ⟨12641801554209820995907031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8427867702806547330604687 12641801554209820995907031)
      ·
        refine ⟨18962702331314731493860547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12641801554209820995907031 18962702331314731493860547)
        ·
          refine ⟨28444053496972097240790821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18962702331314731493860547 28444053496972097240790821)
          ·
            refine ⟨5333260030682268232648279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28444053496972097240790821 5333260030682268232648279)
            ·
              refine ⟨7999890046023402348972419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5333260030682268232648279 7999890046023402348972419)
              ·
                refine ⟨11999835069035103523458629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7999890046023402348972419 11999835069035103523458629)
                ·
                  refine ⟨2249969075444081910648493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11999835069035103523458629 2249969075444081910648493)
                  ·
                    refine ⟨843738403291530716493185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2249969075444081910648493 843738403291530716493185)
                    ·
                      refine ⟨632803802468648037369889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 843738403291530716493185 632803802468648037369889)
                      ·
                        rfl

theorem cell23_1232381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_1232381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232381 prefixEnd_1232381 := by exact prefixLift 1232381
  have htrace : WordTrace (prefixWord ++ tailWord_1232381) baseStart_1232381 baseEnd_1232381 := by
    simpa [prefixWord, tailWord_1232381, baseEnd_1232381] using wordTrace_append hprefix tailTrace_1232381
  have hstable : (prefixWord ++ tailWord_1232381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232381).length < 2 ^ (prefixWord ++ tailWord_1232381).sum := by decide
  have hdescent : baseEnd_1232381 < baseStart_1232381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232382 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_1232382 : Nat := 118140960795 + 1232382 * 2 ^ 59
def prefixEnd_1232382 : Nat := 4983230072969 + 3 ^ 40 * 1232382 * 2
def baseEnd_1232382 : Nat := 210934771983100844485795

theorem tailTrace_1232382 : CollatzResearch.WordTrace tailWord_1232382 prefixEnd_1232382 210934771983100844485795 := by
  unfold tailWord_1232382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5618583027662245366751425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29965776147531975289340933 5618583027662245366751425)
  ·
    refine ⟨4213937270746684025063569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5618583027662245366751425 4213937270746684025063569)
    ·
      refine ⟨3160452953060013018797677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4213937270746684025063569 3160452953060013018797677)
      ·
        refine ⟨1185169857397504882049129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3160452953060013018797677 1185169857397504882049129)
        ·
          refine ⟨888877393048128661536847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1185169857397504882049129 888877393048128661536847)
          ·
            refine ⟨1333316089572192992305271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888877393048128661536847 1333316089572192992305271)
            ·
              refine ⟨1999974134358289488457907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333316089572192992305271 1999974134358289488457907)
              ·
                refine ⟨2999961201537434232686861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1999974134358289488457907 2999961201537434232686861)
                ·
                  refine ⟨1124985450576537837257573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2999961201537434232686861 1124985450576537837257573)
                  ·
                    refine ⟨210934771983100844485795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1124985450576537837257573 210934771983100844485795)
                    ·
                      rfl

theorem cell23_1232382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_1232382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232382 prefixEnd_1232382 := by exact prefixLift 1232382
  have htrace : WordTrace (prefixWord ++ tailWord_1232382) baseStart_1232382 baseEnd_1232382 := by
    simpa [prefixWord, tailWord_1232382, baseEnd_1232382] using wordTrace_append hprefix tailTrace_1232382
  have hstable : (prefixWord ++ tailWord_1232382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232382).length < 2 ^ (prefixWord ++ tailWord_1232382).sum := by decide
  have hdescent : baseEnd_1232382 < baseStart_1232382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232387 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 5, 6]
def baseStart_1232387 : Nat := 118140960795 + 1232387 * 2 ^ 59
def prefixEnd_1232387 : Nat := 4983230072969 + 3 ^ 40 * 1232387 * 2
def baseEnd_1232387 : Nat := 210935627784191671298287

theorem tailTrace_1232387 : CollatzResearch.WordTrace tailWord_1232387 prefixEnd_1232387 210935627784191671298287 := by
  unfold tailWord_1232387
  simp only [CollatzResearch.WordTrace]
  refine ⟨44948846586279848787943415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29965897724186565858628943 44948846586279848787943415)
  ·
    refine ⟨67423269879419773181915123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44948846586279848787943415 67423269879419773181915123)
    ·
      refine ⟨101134904819129659772872685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67423269879419773181915123 101134904819129659772872685)
      ·
        refine ⟨37925589307173622414827257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101134904819129659772872685 37925589307173622414827257)
        ·
          refine ⟨28444191980380216811120443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37925589307173622414827257 28444191980380216811120443)
          ·
            refine ⟨42666287970570325216680665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28444191980380216811120443 42666287970570325216680665)
            ·
              refine ⟨31999715977927743912510499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42666287970570325216680665 31999715977927743912510499)
              ·
                refine ⟨47999573966891615868765749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31999715977927743912510499 47999573966891615868765749)
                ·
                  refine ⟨4499960059396088987696789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47999573966891615868765749 4499960059396088987696789)
                  ·
                    refine ⟨210935627784191671298287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4499960059396088987696789 210935627784191671298287)
                    ·
                      rfl

theorem cell23_1232387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 6].length) (baseStart_1232387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232387 prefixEnd_1232387 := by exact prefixLift 1232387
  have htrace : WordTrace (prefixWord ++ tailWord_1232387) baseStart_1232387 baseEnd_1232387 := by
    simpa [prefixWord, tailWord_1232387, baseEnd_1232387] using wordTrace_append hprefix tailTrace_1232387
  have hstable : (prefixWord ++ tailWord_1232387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232387).length < 2 ^ (prefixWord ++ tailWord_1232387).sum := by decide
  have hdescent : baseEnd_1232387 < baseStart_1232387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232408 : List Nat := [2, 1, 2, 3, 4, 2, 1, 2, 1, 5]
def baseStart_1232408 : Nat := 118140960795 + 1232408 * 2 ^ 59
def prefixEnd_1232408 : Nat := 4983230072969 + 3 ^ 40 * 1232408 * 2
def baseEnd_1232408 : Nat := 210939222148773143910755

theorem tailTrace_1232408 : CollatzResearch.WordTrace tailWord_1232408 prefixEnd_1232408 210939222148773143910755 := by
  unfold tailWord_1232408
  simp only [CollatzResearch.WordTrace]
  refine ⟨22474806259601884687228939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29966408346135846249638585 22474806259601884687228939)
  ·
    refine ⟨33712209389402827030843409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22474806259601884687228939 33712209389402827030843409)
    ·
      refine ⟨25284157042052120273132557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33712209389402827030843409 25284157042052120273132557)
      ·
        refine ⟨9481558890769545102424709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25284157042052120273132557 9481558890769545102424709)
        ·
          refine ⟨1777792292019289706704633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9481558890769545102424709 1777792292019289706704633)
          ·
            refine ⟨1333344219014467280028475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1777792292019289706704633 1333344219014467280028475)
            ·
              refine ⟨2000016328521700920042713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333344219014467280028475 2000016328521700920042713)
              ·
                refine ⟨1500012246391275690032035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2000016328521700920042713 1500012246391275690032035)
                ·
                  refine ⟨2250018369586913535048053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500012246391275690032035 2250018369586913535048053)
                  ·
                    refine ⟨210939222148773143910755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2250018369586913535048053 210939222148773143910755)
                    ·
                      rfl

theorem cell23_1232408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_1232408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232408 prefixEnd_1232408 := by exact prefixLift 1232408
  have htrace : WordTrace (prefixWord ++ tailWord_1232408) baseStart_1232408 baseEnd_1232408 := by
    simpa [prefixWord, tailWord_1232408, baseEnd_1232408] using wordTrace_append hprefix tailTrace_1232408
  have hstable : (prefixWord ++ tailWord_1232408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232408).length < 2 ^ (prefixWord ++ tailWord_1232408).sum := by decide
  have hdescent : baseEnd_1232408 < baseStart_1232408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232524 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 7]
def baseStart_1232524 : Nat := 118140960795 + 1232524 * 2 ^ 59
def prefixEnd_1232524 : Nat := 4983230072969 + 3 ^ 40 * 1232524 * 2
def baseEnd_1232524 : Nat := 70319692244693441986859

theorem tailTrace_1232524 : CollatzResearch.WordTrace tailWord_1232524 prefixEnd_1232524 70319692244693441986859 := by
  unfold tailWord_1232524
  simp only [CollatzResearch.WordTrace]
  refine ⟨22476921693391760592840313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29969228924522347457120417 22476921693391760592840313)
  ·
    refine ⟨16857691270043820444630235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22476921693391760592840313 16857691270043820444630235)
    ·
      refine ⟨25286536905065730666945353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16857691270043820444630235 25286536905065730666945353)
      ·
        refine ⟨18964902678799298000209015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25286536905065730666945353 18964902678799298000209015)
        ·
          refine ⟨28447354018198947000313523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18964902678799298000209015 28447354018198947000313523)
          ·
            refine ⟨42671031027298420500470285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28447354018198947000313523 42671031027298420500470285)
            ·
              refine ⟨16001636635236907687676357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42671031027298420500470285 16001636635236907687676357)
              ·
                refine ⟨3000306869106920191439317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16001636635236907687676357 3000306869106920191439317)
                ·
                  refine ⟨70319692244693441986859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3000306869106920191439317 70319692244693441986859)
                  ·
                    rfl

theorem cell23_1232524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 7].length) (baseStart_1232524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232524 prefixEnd_1232524 := by exact prefixLift 1232524
  have htrace : WordTrace (prefixWord ++ tailWord_1232524) baseStart_1232524 baseEnd_1232524 := by
    simpa [prefixWord, tailWord_1232524, baseEnd_1232524] using wordTrace_append hprefix tailTrace_1232524
  have hstable : (prefixWord ++ tailWord_1232524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232524).length < 2 ^ (prefixWord ++ tailWord_1232524).sum := by decide
  have hdescent : baseEnd_1232524 < baseStart_1232524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232631 : List Nat := [1, 1, 3, 1, 1, 1, 6, 3, 6]
def baseStart_1232631 : Nat := 118140960795 + 1232631 * 2 ^ 59
def prefixEnd_1232631 : Nat := 4983230072969 + 3 ^ 40 * 1232631 * 2
def baseEnd_1232631 : Nat := 70325796959141339915971

theorem tailTrace_1232631 : CollatzResearch.WordTrace tailWord_1232631 prefixEnd_1232631 70325796959141339915971 := by
  unfold tailWord_1232631
  simp only [CollatzResearch.WordTrace]
  refine ⟨44957745997395878459825747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29971830664930585639883831 44957745997395878459825747)
  ·
    refine ⟨67436618996093817689738621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44957745997395878459825747 67436618996093817689738621)
    ·
      refine ⟨25288732123535181633651983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67436618996093817689738621 25288732123535181633651983)
      ·
        refine ⟨37933098185302772450477975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25288732123535181633651983 37933098185302772450477975)
        ·
          refine ⟨56899647277954158675716963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37933098185302772450477975 56899647277954158675716963)
          ·
            refine ⟨85349470916931238013575445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56899647277954158675716963 85349470916931238013575445)
            ·
              refine ⟨4000756449231151781886349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85349470916931238013575445 4000756449231151781886349)
              ·
                refine ⟨1500283668461681918207381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4000756449231151781886349 1500283668461681918207381)
                ·
                  refine ⟨70325796959141339915971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1500283668461681918207381 70325796959141339915971)
                  ·
                    rfl

theorem cell23_1232631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 6].length) (baseStart_1232631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232631 prefixEnd_1232631 := by exact prefixLift 1232631
  have htrace : WordTrace (prefixWord ++ tailWord_1232631) baseStart_1232631 baseEnd_1232631 := by
    simpa [prefixWord, tailWord_1232631, baseEnd_1232631] using wordTrace_append hprefix tailTrace_1232631
  have hstable : (prefixWord ++ tailWord_1232631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232631).length < 2 ^ (prefixWord ++ tailWord_1232631).sum := by decide
  have hdescent : baseEnd_1232631 < baseStart_1232631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232692 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_1232692 : Nat := 118140960795 + 1232692 * 2 ^ 59
def prefixEnd_1232692 : Nat := 4983230072969 + 3 ^ 40 * 1232692 * 2
def baseEnd_1232692 : Nat := 632963494952196320580959

theorem tailTrace_1232692 : CollatzResearch.WordTrace tailWord_1232692 prefixEnd_1232692 632963494952196320580959 := by
  unfold tailWord_1232692
  simp only [CollatzResearch.WordTrace]
  refine ⟨22479985425087442938898165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29973313900116590585197553 22479985425087442938898165)
  ·
    refine ⟨2107498633601947775521703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22479985425087442938898165 2107498633601947775521703)
    ·
      refine ⟨3161247950402921663282555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2107498633601947775521703 3161247950402921663282555)
      ·
        refine ⟨4741871925604382494923833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3161247950402921663282555 4741871925604382494923833)
        ·
          refine ⟨3556403944203286871192875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4741871925604382494923833 3556403944203286871192875)
          ·
            refine ⟨5334605916304930306789313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3556403944203286871192875 5334605916304930306789313)
            ·
              refine ⟨4000954437228697730091985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5334605916304930306789313 4000954437228697730091985)
              ·
                refine ⟨3000715827921523297568989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4000954437228697730091985 3000715827921523297568989)
                ·
                  refine ⟨1125268435470571236588371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3000715827921523297568989 1125268435470571236588371)
                  ·
                    refine ⟨1687902653205856854882557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1125268435470571236588371 1687902653205856854882557)
                    ·
                      refine ⟨632963494952196320580959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1687902653205856854882557 632963494952196320580959)
                      ·
                        rfl

theorem cell23_1232692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_1232692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232692 prefixEnd_1232692 := by exact prefixLift 1232692
  have htrace : WordTrace (prefixWord ++ tailWord_1232692) baseStart_1232692 baseEnd_1232692 := by
    simpa [prefixWord, tailWord_1232692, baseEnd_1232692] using wordTrace_append hprefix tailTrace_1232692
  have hstable : (prefixWord ++ tailWord_1232692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232692).length < 2 ^ (prefixWord ++ tailWord_1232692).sum := by decide
  have hdescent : baseEnd_1232692 < baseStart_1232692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232718 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3]
def baseStart_1232718 : Nat := 118140960795 + 1232718 * 2 ^ 59
def prefixEnd_1232718 : Nat := 4983230072969 + 3 ^ 40 * 1232718 * 2
def baseEnd_1232718 : Nat := 632976845449213218855839

theorem tailTrace_1232718 : CollatzResearch.WordTrace tailWord_1232718 prefixEnd_1232718 632976845449213218855839 := by
  unfold tailWord_1232718
  simp only [CollatzResearch.WordTrace]
  refine ⟨5620114893510086539780351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29973946098720461545495205 5620114893510086539780351)
  ·
    refine ⟨8430172340265129809670527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5620114893510086539780351 8430172340265129809670527)
    ·
      refine ⟨12645258510397694714505791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8430172340265129809670527 12645258510397694714505791)
      ·
        refine ⟨18967887765596542071758687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12645258510397694714505791 18967887765596542071758687)
        ·
          refine ⟨28451831648394813107638031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18967887765596542071758687 28451831648394813107638031)
          ·
            refine ⟨42677747472592219661457047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28451831648394813107638031 42677747472592219661457047)
            ·
              refine ⟨64016621208888329492185571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42677747472592219661457047 64016621208888329492185571)
              ·
                refine ⟨96024931813332494238278357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64016621208888329492185571 96024931813332494238278357)
                ·
                  refine ⟨2250584339374980333709649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 96024931813332494238278357 2250584339374980333709649)
                  ·
                    refine ⟨1687938254531235250282237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2250584339374980333709649 1687938254531235250282237)
                    ·
                      refine ⟨632976845449213218855839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1687938254531235250282237 632976845449213218855839)
                      ·
                        rfl

theorem cell23_1232718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_1232718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232718 prefixEnd_1232718 := by exact prefixLift 1232718
  have htrace : WordTrace (prefixWord ++ tailWord_1232718) baseStart_1232718 baseEnd_1232718 := by
    simpa [prefixWord, tailWord_1232718, baseEnd_1232718] using wordTrace_append hprefix tailTrace_1232718
  have hstable : (prefixWord ++ tailWord_1232718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232718).length < 2 ^ (prefixWord ++ tailWord_1232718).sum := by decide
  have hdescent : baseEnd_1232718 < baseStart_1232718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232721 : List Nat := [1, 2, 2, 1, 5, 1, 11]
def baseStart_1232721 : Nat := 118140960795 + 1232721 * 2 ^ 59
def prefixEnd_1232721 : Nat := 4983230072969 + 3 ^ 40 * 1232721 * 2
def baseEnd_1232721 : Nat := 7814547973965144532325

theorem tailTrace_1232721 : CollatzResearch.WordTrace tailWord_1232721 prefixEnd_1232721 7814547973965144532325 := by
  unfold tailWord_1232721
  simp only [CollatzResearch.WordTrace]
  refine ⟨44961028567069823830602017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29974019044713215887068011 44961028567069823830602017)
  ·
    refine ⟨33720771425302367872951513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44961028567069823830602017 33720771425302367872951513)
    ·
      refine ⟨25290578568976775904713635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33720771425302367872951513 25290578568976775904713635)
      ·
        refine ⟨37935867853465163857070453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25290578568976775904713635 37935867853465163857070453)
        ·
          refine ⟨3556487611262359111600355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37935867853465163857070453 3556487611262359111600355)
          ·
            refine ⟨5334731416893538667400533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3556487611262359111600355 5334731416893538667400533)
            ·
              refine ⟨7814547973965144532325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5334731416893538667400533 7814547973965144532325)
              ·
                rfl

theorem cell23_1232721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 11].length) (baseStart_1232721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232721 prefixEnd_1232721 := by exact prefixLift 1232721
  have htrace : WordTrace (prefixWord ++ tailWord_1232721) baseStart_1232721 baseEnd_1232721 := by
    simpa [prefixWord, tailWord_1232721, baseEnd_1232721] using wordTrace_append hprefix tailTrace_1232721
  have hstable : (prefixWord ++ tailWord_1232721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232721).length < 2 ^ (prefixWord ++ tailWord_1232721).sum := by decide
  have hdescent : baseEnd_1232721 < baseStart_1232721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232738 : List Nat := [3, 3, 2, 1, 2, 1, 1, 10]
def baseStart_1232738 : Nat := 118140960795 + 1232738 * 2 ^ 59
def prefixEnd_1232738 : Nat := 4983230072969 + 3 ^ 40 * 1232738 * 2
def baseEnd_1232738 : Nat := 23443967224529745948361

theorem tailTrace_1232738 : CollatzResearch.WordTrace tailWord_1232738 prefixEnd_1232738 23443967224529745948361 := by
  unfold tailWord_1232738
  simp only [CollatzResearch.WordTrace]
  refine ⟨11240412152002058933492717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29974432405338823822647245 11240412152002058933492717)
  ·
    refine ⟨4215154557000772100059769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11240412152002058933492717 4215154557000772100059769)
    ·
      refine ⟨3161365917750579075044827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4215154557000772100059769 3161365917750579075044827)
      ·
        refine ⟨4742048876625868612567241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3161365917750579075044827 4742048876625868612567241)
        ·
          refine ⟨3556536657469401459425431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4742048876625868612567241 3556536657469401459425431)
          ·
            refine ⟨5334804986204102189138147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3556536657469401459425431 5334804986204102189138147)
            ·
              refine ⟨8002207479306153283707221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5334804986204102189138147 8002207479306153283707221)
              ·
                refine ⟨23443967224529745948361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8002207479306153283707221 23443967224529745948361)
                ·
                  rfl

theorem cell23_1232738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 10].length) (baseStart_1232738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232738 prefixEnd_1232738 := by exact prefixLift 1232738
  have htrace : WordTrace (prefixWord ++ tailWord_1232738) baseStart_1232738 baseEnd_1232738 := by
    simpa [prefixWord, tailWord_1232738, baseEnd_1232738] using wordTrace_append hprefix tailTrace_1232738
  have hstable : (prefixWord ++ tailWord_1232738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232738).length < 2 ^ (prefixWord ++ tailWord_1232738).sum := by decide
  have hdescent : baseEnd_1232738 < baseStart_1232738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232741 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 1, 4, 6]
def baseStart_1232741 : Nat := 118140960795 + 1232741 * 2 ^ 59
def prefixEnd_1232741 : Nat := 4983230072969 + 3 ^ 40 * 1232741 * 2
def baseEnd_1232741 : Nat := 632988655504266628868233

theorem tailTrace_1232741 : CollatzResearch.WordTrace tailWord_1232741 prefixEnd_1232741 632988655504266628868233 := by
  unfold tailWord_1232741
  simp only [CollatzResearch.WordTrace]
  refine ⟨44961758026997367246330077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29974505351331578164220051 44961758026997367246330077)
  ·
    refine ⟨16860659260124012717373779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44961758026997367246330077 16860659260124012717373779)
    ·
      refine ⟨25290988890186019076060669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16860659260124012717373779 25290988890186019076060669)
      ·
        refine ⟨9484120833819757153522751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25290988890186019076060669 9484120833819757153522751)
        ·
          refine ⟨14226181250729635730284127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9484120833819757153522751 14226181250729635730284127)
          ·
            refine ⟨21339271876094453595426191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14226181250729635730284127 21339271876094453595426191)
            ·
              refine ⟨32008907814141680393139287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21339271876094453595426191 32008907814141680393139287)
              ·
                refine ⟨48013361721212520589708931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32008907814141680393139287 48013361721212520589708931)
                ·
                  refine ⟨72020042581818780884563397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48013361721212520589708931 72020042581818780884563397)
                  ·
                    refine ⟨13503757984091021415855637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72020042581818780884563397 13503757984091021415855637)
                    ·
                      refine ⟨632988655504266628868233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13503757984091021415855637 632988655504266628868233)
                      ·
                        rfl

theorem cell23_1232741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_1232741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232741 prefixEnd_1232741 := by exact prefixLift 1232741
  have htrace : WordTrace (prefixWord ++ tailWord_1232741) baseStart_1232741 baseEnd_1232741 := by
    simpa [prefixWord, tailWord_1232741, baseEnd_1232741] using wordTrace_append hprefix tailTrace_1232741
  have hstable : (prefixWord ++ tailWord_1232741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232741).length < 2 ^ (prefixWord ++ tailWord_1232741).sum := by decide
  have hdescent : baseEnd_1232741 < baseStart_1232741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232769 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 1, 1, 5]
def baseStart_1232769 : Nat := 118140960795 + 1232769 * 2 ^ 59
def prefixEnd_1232769 : Nat := 4983230072969 + 3 ^ 40 * 1232769 * 2
def baseEnd_1232769 : Nat := 633003032962592519318105

theorem tailTrace_1232769 : CollatzResearch.WordTrace tailWord_1232769 prefixEnd_1232769 633003032962592519318105 := by
  unfold tailWord_1232769
  simp only [CollatzResearch.WordTrace]
  refine ⟨44962779270895928028349361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29975186180597285352232907 44962779270895928028349361)
  ·
    refine ⟨33722084453171946021262021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44962779270895928028349361 33722084453171946021262021)
    ·
      refine ⟨6322890834969739878986629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33722084453171946021262021 6322890834969739878986629)
      ·
        refine ⟨1185542031556826227309993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6322890834969739878986629 1185542031556826227309993)
        ·
          refine ⟨889156523667619670482495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1185542031556826227309993 889156523667619670482495)
          ·
            refine ⟨1333734785501429505723743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889156523667619670482495 1333734785501429505723743)
            ·
              refine ⟨2000602178252144258585615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333734785501429505723743 2000602178252144258585615)
              ·
                refine ⟨3000903267378216387878423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2000602178252144258585615 3000903267378216387878423)
                ·
                  refine ⟨4501354901067324581817635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3000903267378216387878423 4501354901067324581817635)
                  ·
                    refine ⟨6752032351600986872726453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4501354901067324581817635 6752032351600986872726453)
                    ·
                      refine ⟨633003032962592519318105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6752032351600986872726453 633003032962592519318105)
                      ·
                        rfl

theorem cell23_1232769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_1232769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232769 prefixEnd_1232769 := by exact prefixLift 1232769
  have htrace : WordTrace (prefixWord ++ tailWord_1232769) baseStart_1232769 baseEnd_1232769 := by
    simpa [prefixWord, tailWord_1232769, baseEnd_1232769] using wordTrace_append hprefix tailTrace_1232769
  have hstable : (prefixWord ++ tailWord_1232769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232769).length < 2 ^ (prefixWord ++ tailWord_1232769).sum := by decide
  have hdescent : baseEnd_1232769 < baseStart_1232769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232865 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 2, 5, 2]
def baseStart_1232865 : Nat := 118140960795 + 1232865 * 2 ^ 59
def prefixEnd_1232865 : Nat := 4983230072969 + 3 ^ 40 * 1232865 * 2
def baseEnd_1232865 : Nat := 633052327105424143717663

theorem tailTrace_1232865 : CollatzResearch.WordTrace tailWord_1232865 prefixEnd_1232865 633052327105424143717663 := by
  unfold tailWord_1232865
  simp only [CollatzResearch.WordTrace]
  refine ⟨44966280678548136423844049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29977520452365424282562699 44966280678548136423844049)
  ·
    refine ⟨33724710508911102317883037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44966280678548136423844049 33724710508911102317883037)
    ·
      refine ⟨12646766440841663369206139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33724710508911102317883037 12646766440841663369206139)
      ·
        refine ⟨18970149661262495053809209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12646766440841663369206139 18970149661262495053809209)
        ·
          refine ⟨14227612245946871290356907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18970149661262495053809209 14227612245946871290356907)
          ·
            refine ⟨21341418368920306935535361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14227612245946871290356907 21341418368920306935535361)
            ·
              refine ⟨16006063776690230201651521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21341418368920306935535361 16006063776690230201651521)
              ·
                refine ⟨12004547832517672651238641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16006063776690230201651521 12004547832517672651238641)
                ·
                  refine ⟨9003410874388254488428981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12004547832517672651238641 9003410874388254488428981)
                  ·
                    refine ⟨844069769473898858290217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9003410874388254488428981 844069769473898858290217)
                    ·
                      refine ⟨633052327105424143717663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 844069769473898858290217 633052327105424143717663)
                      ·
                        rfl

theorem cell23_1232865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_1232865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232865 prefixEnd_1232865 := by exact prefixLift 1232865
  have htrace : WordTrace (prefixWord ++ tailWord_1232865) baseStart_1232865 baseEnd_1232865 := by
    simpa [prefixWord, tailWord_1232865, baseEnd_1232865] using wordTrace_append hprefix tailTrace_1232865
  have hstable : (prefixWord ++ tailWord_1232865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232865).length < 2 ^ (prefixWord ++ tailWord_1232865).sum := by decide
  have hdescent : baseEnd_1232865 < baseStart_1232865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232895 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 4, 4, 2]
def baseStart_1232895 : Nat := 118140960795 + 1232895 * 2 ^ 59
def prefixEnd_1232895 : Nat := 4983230072969 + 3 ^ 40 * 1232895 * 2
def baseEnd_1232895 : Nat := 633067731525059026342525

theorem tailTrace_1232895 : CollatzResearch.WordTrace tailWord_1232895 prefixEnd_1232895 633067731525059026342525 := by
  unfold tailWord_1232895
  simp only [CollatzResearch.WordTrace]
  refine ⟨44967374868439451547436139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29978249912292967698290759 44967374868439451547436139)
  ·
    refine ⟨67451062302659177321154209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44967374868439451547436139 67451062302659177321154209)
    ·
      refine ⟨50588296726994382990865657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67451062302659177321154209 50588296726994382990865657)
      ·
        refine ⟨37941222545245787243149243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50588296726994382990865657 37941222545245787243149243)
        ·
          refine ⟨56911833817868680864723865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37941222545245787243149243 56911833817868680864723865)
          ·
            refine ⟨42683875363401510648542899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56911833817868680864723865 42683875363401510648542899)
            ·
              refine ⟨64025813045102265972814349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42683875363401510648542899 64025813045102265972814349)
              ·
                refine ⟨24009679891913349739805381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64025813045102265972814349 24009679891913349739805381)
                ·
                  refine ⟨4501814979733753076213509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24009679891913349739805381 4501814979733753076213509)
                  ·
                    refine ⟨844090308700078701790033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4501814979733753076213509 844090308700078701790033)
                    ·
                      refine ⟨633067731525059026342525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 844090308700078701790033 633067731525059026342525)
                      ·
                        rfl

theorem cell23_1232895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 4, 2].length) (baseStart_1232895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232895 prefixEnd_1232895 := by exact prefixLift 1232895
  have htrace : WordTrace (prefixWord ++ tailWord_1232895) baseStart_1232895 baseEnd_1232895 := by
    simpa [prefixWord, tailWord_1232895, baseEnd_1232895] using wordTrace_append hprefix tailTrace_1232895
  have hstable : (prefixWord ++ tailWord_1232895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232895).length < 2 ^ (prefixWord ++ tailWord_1232895).sum := by decide
  have hdescent : baseEnd_1232895 < baseStart_1232895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232952 : List Nat := [2, 1, 2, 1, 6, 1, 2, 2, 6]
def baseStart_1232952 : Nat := 118140960795 + 1232952 * 2 ^ 59
def prefixEnd_1232952 : Nat := 4983230072969 + 3 ^ 40 * 1232952 * 2
def baseEnd_1232952 : Nat := 70344111102485033703307

theorem tailTrace_1232952 : CollatzResearch.WordTrace tailWord_1232952 prefixEnd_1232952 70344111102485033703307 := by
  unfold tailWord_1232952
  simp only [CollatzResearch.WordTrace]
  refine ⟨22484726914616475141130555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29979635886155300188174073 22484726914616475141130555)
  ·
    refine ⟨33727090371924712711695833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22484726914616475141130555 33727090371924712711695833)
    ·
      refine ⟨25295317778943534533771875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33727090371924712711695833 25295317778943534533771875)
      ·
        refine ⟨37942976668415301800657813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25295317778943534533771875 37942976668415301800657813)
        ·
          refine ⟨1778577031331967271905835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37942976668415301800657813 1778577031331967271905835)
          ·
            refine ⟨2667865546997950907858753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1778577031331967271905835 2667865546997950907858753)
            ·
              refine ⟨2000899160248463180894065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2667865546997950907858753 2000899160248463180894065)
              ·
                refine ⟨1500674370186347385670549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2000899160248463180894065 1500674370186347385670549)
                ·
                  refine ⟨70344111102485033703307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1500674370186347385670549 70344111102485033703307)
                  ·
                    rfl

theorem cell23_1232952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 6].length) (baseStart_1232952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232952 prefixEnd_1232952 := by exact prefixLift 1232952
  have htrace : WordTrace (prefixWord ++ tailWord_1232952) baseStart_1232952 baseEnd_1232952 := by
    simpa [prefixWord, tailWord_1232952, baseEnd_1232952] using wordTrace_append hprefix tailTrace_1232952
  have hstable : (prefixWord ++ tailWord_1232952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232952).length < 2 ^ (prefixWord ++ tailWord_1232952).sum := by decide
  have hdescent : baseEnd_1232952 < baseStart_1232952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232972 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 4, 3, 2]
def baseStart_1232972 : Nat := 118140960795 + 1232972 * 2 ^ 59
def prefixEnd_1232972 : Nat := 4983230072969 + 3 ^ 40 * 1232972 * 2
def baseEnd_1232972 : Nat := 633107269535455225079671

theorem tailTrace_1232972 : CollatzResearch.WordTrace tailWord_1232972 prefixEnd_1232972 633107269535455225079671 := by
  unfold tailWord_1232972
  simp only [CollatzResearch.WordTrace]
  refine ⟨22485091644580246848994585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29980122192773662465326113 22485091644580246848994585)
  ·
    refine ⟨16863818733435185136745939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22485091644580246848994585 16863818733435185136745939)
    ·
      refine ⟨25295728100152777705118909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16863818733435185136745939 25295728100152777705118909)
      ·
        refine ⟨9485898037557291639419591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25295728100152777705118909 9485898037557291639419591)
        ·
          refine ⟨14228847056335937459129387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9485898037557291639419591 14228847056335937459129387)
          ·
            refine ⟨21343270584503906188694081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14228847056335937459129387 21343270584503906188694081)
            ·
              refine ⟨16007452938377929641520561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21343270584503906188694081 16007452938377929641520561)
              ·
                refine ⟨12005589703783447231140421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16007452938377929641520561 12005589703783447231140421)
                ·
                  refine ⟨2251048069459396355838829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12005589703783447231140421 2251048069459396355838829)
                  ·
                    refine ⟨844143026047273633439561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2251048069459396355838829 844143026047273633439561)
                    ·
                      refine ⟨633107269535455225079671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 844143026047273633439561 633107269535455225079671)
                      ·
                        rfl

theorem cell23_1232972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_1232972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232972 prefixEnd_1232972 := by exact prefixLift 1232972
  have htrace : WordTrace (prefixWord ++ tailWord_1232972) baseStart_1232972 baseEnd_1232972 := by
    simpa [prefixWord, tailWord_1232972, baseEnd_1232972] using wordTrace_append hprefix tailTrace_1232972
  have hstable : (prefixWord ++ tailWord_1232972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232972).length < 2 ^ (prefixWord ++ tailWord_1232972).sum := by decide
  have hdescent : baseEnd_1232972 < baseStart_1232972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232985 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 3, 1, 4]
def baseStart_1232985 : Nat := 118140960795 + 1232985 * 2 ^ 59
def prefixEnd_1232985 : Nat := 4983230072969 + 3 ^ 40 * 1232985 * 2
def baseEnd_1232985 : Nat := 633113944783963674217111

theorem tailTrace_1232985 : CollatzResearch.WordTrace tailWord_1232985 prefixEnd_1232985 633113944783963674217111 := by
  unfold tailWord_1232985
  simp only [CollatzResearch.WordTrace]
  refine ⟨44970657438113396918212409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29980438292075597945474939 44970657438113396918212409)
  ·
    refine ⟨33727993078585047688659307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44970657438113396918212409 33727993078585047688659307)
    ·
      refine ⟨50591989617877571532988961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33727993078585047688659307 50591989617877571532988961)
      ·
        refine ⟨37943992213408178649741721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50591989617877571532988961 37943992213408178649741721)
        ·
          refine ⟨28457994160056133987306291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37943992213408178649741721 28457994160056133987306291)
          ·
            refine ⟨42686991240084200980959437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28457994160056133987306291 42686991240084200980959437)
            ·
              refine ⟨16007621715031575367859789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42686991240084200980959437 16007621715031575367859789)
              ·
                refine ⟨6002858143136840762947421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16007621715031575367859789 6002858143136840762947421)
                ·
                  refine ⟨2251071803676315286105283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6002858143136840762947421 2251071803676315286105283)
                  ·
                    refine ⟨3376607705514472929157925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2251071803676315286105283 3376607705514472929157925)
                    ·
                      refine ⟨633113944783963674217111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3376607705514472929157925 633113944783963674217111)
                      ·
                        rfl

theorem cell23_1232985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_1232985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232985 prefixEnd_1232985 := by exact prefixLift 1232985
  have htrace : WordTrace (prefixWord ++ tailWord_1232985) baseStart_1232985 baseEnd_1232985 := by
    simpa [prefixWord, tailWord_1232985, baseEnd_1232985] using wordTrace_append hprefix tailTrace_1232985
  have hstable : (prefixWord ++ tailWord_1232985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232985).length < 2 ^ (prefixWord ++ tailWord_1232985).sum := by decide
  have hdescent : baseEnd_1232985 < baseStart_1232985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232990 : List Nat := [4, 4, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_1232990 : Nat := 118140960795 + 1232990 * 2 ^ 59
def prefixEnd_1232990 : Nat := 4983230072969 + 3 ^ 40 * 1232990 * 2
def baseEnd_1232990 : Nat := 211038837395745384884863

theorem tailTrace_1232990 : CollatzResearch.WordTrace tailWord_1232990 prefixEnd_1232990 211038837395745384884863 := by
  unfold tailWord_1232990
  simp only [CollatzResearch.WordTrace]
  refine ⟨5621354975386910346518053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29980559868730188514762949 5621354975386910346518053)
  ·
    refine ⟨1054004057885045689972135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5621354975386910346518053 1054004057885045689972135)
    ·
      refine ⟨1581006086827568534958203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1054004057885045689972135 1581006086827568534958203)
      ·
        refine ⟨2371509130241352802437305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1581006086827568534958203 2371509130241352802437305)
        ·
          refine ⟨1778631847681014601827979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2371509130241352802437305 1778631847681014601827979)
          ·
            refine ⟨2667947771521521902741969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1778631847681014601827979 2667947771521521902741969)
            ·
              refine ⟨2000960828641141427056477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2667947771521521902741969 2000960828641141427056477)
              ·
                refine ⟨750360310740428035146179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2000960828641141427056477 750360310740428035146179)
                ·
                  refine ⟨1125540466110642052719269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750360310740428035146179 1125540466110642052719269)
                  ·
                    refine ⟨211038837395745384884863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1125540466110642052719269 211038837395745384884863)
                    ·
                      rfl

theorem cell23_1232990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_1232990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232990 prefixEnd_1232990 := by exact prefixLift 1232990
  have htrace : WordTrace (prefixWord ++ tailWord_1232990) baseStart_1232990 baseEnd_1232990 := by
    simpa [prefixWord, tailWord_1232990, baseEnd_1232990] using wordTrace_append hprefix tailTrace_1232990
  have hstable : (prefixWord ++ tailWord_1232990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232990).length < 2 ^ (prefixWord ++ tailWord_1232990).sum := by decide
  have hdescent : baseEnd_1232990 < baseStart_1232990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232995 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 1, 6]
def baseStart_1232995 : Nat := 118140960795 + 1232995 * 2 ^ 59
def prefixEnd_1232995 : Nat := 4983230072969 + 3 ^ 40 * 1232995 * 2
def baseEnd_1232995 : Nat := 211039693196836211697355

theorem tailTrace_1232995 : CollatzResearch.WordTrace tailWord_1232995 prefixEnd_1232995 211039693196836211697355 := by
  unfold tailWord_1232995
  simp only [CollatzResearch.WordTrace]
  refine ⟨44971022168077168626076439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29980681445384779084050959 44971022168077168626076439)
  ·
    refine ⟨67456533252115752939114659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44971022168077168626076439 67456533252115752939114659)
    ·
      refine ⟨101184799878173629408671989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67456533252115752939114659 101184799878173629408671989)
      ·
        refine ⟨9486074988578777757062999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101184799878173629408671989 9486074988578777757062999)
        ·
          refine ⟨14229112482868166635594499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9486074988578777757062999 14229112482868166635594499)
          ·
            refine ⟨21343668724302249953391749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14229112482868166635594499 21343668724302249953391749)
            ·
              refine ⟨4001937885806671866260953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21343668724302249953391749 4001937885806671866260953)
              ·
                refine ⟨3001453414355003899695715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4001937885806671866260953 3001453414355003899695715)
                ·
                  refine ⟨4502180121532505849543573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3001453414355003899695715 4502180121532505849543573)
                  ·
                    refine ⟨211039693196836211697355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4502180121532505849543573 211039693196836211697355)
                    ·
                      rfl

theorem cell23_1232995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 6].length) (baseStart_1232995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1232995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1232995 prefixEnd_1232995 := by exact prefixLift 1232995
  have htrace : WordTrace (prefixWord ++ tailWord_1232995) baseStart_1232995 baseEnd_1232995 := by
    simpa [prefixWord, tailWord_1232995, baseEnd_1232995] using wordTrace_append hprefix tailTrace_1232995
  have hstable : (prefixWord ++ tailWord_1232995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232995).length < 2 ^ (prefixWord ++ tailWord_1232995).sum := by decide
  have hdescent : baseEnd_1232995 < baseStart_1232995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233032 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1233032 : Nat := 118140960795 + 1233032 * 2 ^ 59
def prefixEnd_1233032 : Nat := 4983230072969 + 3 ^ 40 * 1233032 * 2
def baseEnd_1233032 : Nat := 633138078374724990329395

theorem tailTrace_1233032 : CollatzResearch.WordTrace tailWord_1233032 prefixEnd_1233032 633138078374724990329395 := by
  unfold tailWord_1233032
  simp only [CollatzResearch.WordTrace]
  refine ⟨22486185834471561972586675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29981581112628749296782233 22486185834471561972586675)
  ·
    refine ⟨33729278751707342958880013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22486185834471561972586675 33729278751707342958880013)
    ·
      refine ⟨12648479531890253609580005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33729278751707342958880013 12648479531890253609580005)
      ·
        refine ⟨2371589912229422551796251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12648479531890253609580005 2371589912229422551796251)
        ·
          refine ⟨3557384868344133827694377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2371589912229422551796251 3557384868344133827694377)
          ·
            refine ⟨2668038651258100370770783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3557384868344133827694377 2668038651258100370770783)
            ·
              refine ⟨4002057976887150556156175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668038651258100370770783 4002057976887150556156175)
              ·
                refine ⟨6003086965330725834234263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4002057976887150556156175 6003086965330725834234263)
                ·
                  refine ⟨9004630447996088751351395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6003086965330725834234263 9004630447996088751351395)
                  ·
                    refine ⟨13506945671994133127027093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9004630447996088751351395 13506945671994133127027093)
                    ·
                      refine ⟨633138078374724990329395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13506945671994133127027093 633138078374724990329395)
                      ·
                        rfl

theorem cell23_1233032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1233032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233032 prefixEnd_1233032 := by exact prefixLift 1233032
  have htrace : WordTrace (prefixWord ++ tailWord_1233032) baseStart_1233032 baseEnd_1233032 := by
    simpa [prefixWord, tailWord_1233032, baseEnd_1233032] using wordTrace_append hprefix tailTrace_1233032
  have hstable : (prefixWord ++ tailWord_1233032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233032).length < 2 ^ (prefixWord ++ tailWord_1233032).sum := by decide
  have hdescent : baseEnd_1233032 < baseStart_1233032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233052 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1233052 : Nat := 118140960795 + 1233052 * 2 ^ 59
def prefixEnd_1233052 : Nat := 4983230072969 + 3 ^ 40 * 1233052 * 2
def baseEnd_1233052 : Nat := 633148347987814912079303

theorem tailTrace_1233052 : CollatzResearch.WordTrace tailWord_1233052 prefixEnd_1233052 633148347987814912079303 := by
  unfold tailWord_1233052
  simp only [CollatzResearch.WordTrace]
  refine ⟨22486550564435333680450705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29982067419247111573934273 22486550564435333680450705)
  ·
    refine ⟨16864912923326500260338029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22486550564435333680450705 16864912923326500260338029)
    ·
      refine ⟨6324342346247437597626761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16864912923326500260338029 6324342346247437597626761)
      ·
        refine ⟨4743256759685578198220071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6324342346247437597626761 4743256759685578198220071)
        ·
          refine ⟨7114885139528367297330107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4743256759685578198220071 7114885139528367297330107)
          ·
            refine ⟨10672327709292550945995161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7114885139528367297330107 10672327709292550945995161)
            ·
              refine ⟨8004245781969413209496371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10672327709292550945995161 8004245781969413209496371)
              ·
                refine ⟨12006368672954119814244557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8004245781969413209496371 12006368672954119814244557)
                ·
                  refine ⟨4502388252357794930341709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12006368672954119814244557 4502388252357794930341709)
                  ·
                    refine ⟨1688395594634173098878141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4502388252357794930341709 1688395594634173098878141)
                    ·
                      refine ⟨633148347987814912079303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1688395594634173098878141 633148347987814912079303)
                      ·
                        rfl

theorem cell23_1233052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1233052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233052 prefixEnd_1233052 := by exact prefixLift 1233052
  have htrace : WordTrace (prefixWord ++ tailWord_1233052) baseStart_1233052 baseEnd_1233052 := by
    simpa [prefixWord, tailWord_1233052, baseEnd_1233052] using wordTrace_append hprefix tailTrace_1233052
  have hstable : (prefixWord ++ tailWord_1233052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233052).length < 2 ^ (prefixWord ++ tailWord_1233052).sum := by decide
  have hdescent : baseEnd_1233052 < baseStart_1233052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233053 : List Nat := [1, 4, 2, 1, 1, 3, 3, 3, 1, 2, 2]
def baseStart_1233053 : Nat := 118140960795 + 1233053 * 2 ^ 59
def prefixEnd_1233053 : Nat := 4983230072969 + 3 ^ 40 * 1233053 * 2
def baseEnd_1233053 : Nat := 633148861468469408166799

theorem tailTrace_1233053 : CollatzResearch.WordTrace tailWord_1233053 prefixEnd_1233053 633148861468469408166799 := by
  unfold tailWord_1233053
  simp only [CollatzResearch.WordTrace]
  refine ⟨44973137601867044531687813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29982091734578029687791875 44973137601867044531687813)
  ·
    refine ⟨8432463300350070849691465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44973137601867044531687813 8432463300350070849691465)
    ·
      refine ⟨6324347475262553137268599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8432463300350070849691465 6324347475262553137268599)
      ·
        refine ⟨9486521212893829705902899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6324347475262553137268599 9486521212893829705902899)
        ·
          refine ⟨14229781819340744558854349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9486521212893829705902899 14229781819340744558854349)
          ·
            refine ⟨5336168182252779209570381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14229781819340744558854349 5336168182252779209570381)
            ·
              refine ⟨2001063068344792203588893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5336168182252779209570381 2001063068344792203588893)
              ·
                refine ⟨750398650629297076345835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2001063068344792203588893 750398650629297076345835)
                ·
                  refine ⟨1125597975943945614518753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750398650629297076345835 1125597975943945614518753)
                  ·
                    refine ⟨844198481957959210889065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1125597975943945614518753 844198481957959210889065)
                    ·
                      refine ⟨633148861468469408166799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 844198481957959210889065 633148861468469408166799)
                      ·
                        rfl

theorem cell23_1233053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_1233053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233053 prefixEnd_1233053 := by exact prefixLift 1233053
  have htrace : WordTrace (prefixWord ++ tailWord_1233053) baseStart_1233053 baseEnd_1233053 := by
    simpa [prefixWord, tailWord_1233053, baseEnd_1233053] using wordTrace_append hprefix tailTrace_1233053
  have hstable : (prefixWord ++ tailWord_1233053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233053).length < 2 ^ (prefixWord ++ tailWord_1233053).sum := by decide
  have hdescent : baseEnd_1233053 < baseStart_1233053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233075 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 4]
def baseStart_1233075 : Nat := 118140960795 + 1233075 * 2 ^ 59
def prefixEnd_1233075 : Nat := 4983230072969 + 3 ^ 40 * 1233075 * 2
def baseEnd_1233075 : Nat := 633160158042868322091697

theorem tailTrace_1233075 : CollatzResearch.WordTrace tailWord_1233075 prefixEnd_1233075 633160158042868322091697 := by
  unfold tailWord_1233075
  simp only [CollatzResearch.WordTrace]
  refine ⟨44973940007787342288988679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29982626671858228192659119 44973940007787342288988679)
  ·
    refine ⟨67460910011681013433483019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44973940007787342288988679 67460910011681013433483019)
    ·
      refine ⟨101191365017521520150224529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67460910011681013433483019 101191365017521520150224529)
      ·
        refine ⟨75893523763141140112668397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101191365017521520150224529 75893523763141140112668397)
        ·
          refine ⟨28460071411177927542250649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75893523763141140112668397 28460071411177927542250649)
          ·
            refine ⟨21345053558383445656687987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28460071411177927542250649 21345053558383445656687987)
            ·
              refine ⟨32017580337575168485031981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21345053558383445656687987 32017580337575168485031981)
              ·
                refine ⟨12006592626590688181886993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32017580337575168485031981 12006592626590688181886993)
                ·
                  refine ⟨9004944469943016136415245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12006592626590688181886993 9004944469943016136415245)
                  ·
                    refine ⟨3376854176228631051155717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9004944469943016136415245 3376854176228631051155717)
                    ·
                      refine ⟨633160158042868322091697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3376854176228631051155717 633160158042868322091697)
                      ·
                        rfl

theorem cell23_1233075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_1233075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233075 prefixEnd_1233075 := by exact prefixLift 1233075
  have htrace : WordTrace (prefixWord ++ tailWord_1233075) baseStart_1233075 baseEnd_1233075 := by
    simpa [prefixWord, tailWord_1233075, baseEnd_1233075] using wordTrace_append hprefix tailTrace_1233075
  have hstable : (prefixWord ++ tailWord_1233075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233075).length < 2 ^ (prefixWord ++ tailWord_1233075).sum := by decide
  have hdescent : baseEnd_1233075 < baseStart_1233075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233085 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 1, 8]
def baseStart_1233085 : Nat := 118140960795 + 1233085 * 2 ^ 59
def prefixEnd_1233085 : Nat := 4983230072969 + 3 ^ 40 * 1233085 * 2
def baseEnd_1233085 : Nat := 211055097616471094322217

theorem tailTrace_1233085 : CollatzResearch.WordTrace tailWord_1233085 prefixEnd_1233085 211055097616471094322217 := by
  unfold tailWord_1233085
  simp only [CollatzResearch.WordTrace]
  refine ⟨44974304737751113996852709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29982869825167409331235139 44974304737751113996852709)
  ·
    refine ⟨8432682138328333874409883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44974304737751113996852709 8432682138328333874409883)
    ·
      refine ⟨12649023207492500811614825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8432682138328333874409883 12649023207492500811614825)
      ·
        refine ⟨9486767405619375608711119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12649023207492500811614825 9486767405619375608711119)
        ·
          refine ⟨14230151108429063413066679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9486767405619375608711119 14230151108429063413066679)
          ·
            refine ⟨21345226662643595119600019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14230151108429063413066679 21345226662643595119600019)
            ·
              refine ⟨32017839993965392679400029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21345226662643595119600019 32017839993965392679400029)
              ·
                refine ⟨12006689997737022254775011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32017839993965392679400029 12006689997737022254775011)
                ·
                  refine ⟨18010034996605533382162517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12006689997737022254775011 18010034996605533382162517)
                  ·
                    refine ⟨211055097616471094322217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18010034996605533382162517 211055097616471094322217)
                    ·
                      rfl

theorem cell23_1233085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_1233085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233085 prefixEnd_1233085 := by exact prefixLift 1233085
  have htrace : WordTrace (prefixWord ++ tailWord_1233085) baseStart_1233085 baseEnd_1233085 := by
    simpa [prefixWord, tailWord_1233085, baseEnd_1233085] using wordTrace_append hprefix tailTrace_1233085
  have hstable : (prefixWord ++ tailWord_1233085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233085).length < 2 ^ (prefixWord ++ tailWord_1233085).sum := by decide
  have hdescent : baseEnd_1233085 < baseStart_1233085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233090 : List Nat := [3, 5, 1, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_1233090 : Nat := 118140960795 + 1233090 * 2 ^ 59
def prefixEnd_1233090 : Nat := 4983230072969 + 3 ^ 40 * 1233090 * 2
def baseEnd_1233090 : Nat := 633167860252685763404129

theorem tailTrace_1233090 : CollatzResearch.WordTrace tailWord_1233090 prefixEnd_1233090 633167860252685763404129 := by
  unfold tailWord_1233090
  simp only [CollatzResearch.WordTrace]
  refine ⟨11243621775683249962696181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29982991401821999900523149 11243621775683249962696181)
  ·
    refine ⟨1054089541470304684002767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11243621775683249962696181 1054089541470304684002767)
    ·
      refine ⟨1581134312205457026004151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1054089541470304684002767 1581134312205457026004151)
      ·
        refine ⟨2371701468308185539006227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1581134312205457026004151 2371701468308185539006227)
        ·
          refine ⟨3557552202462278308509341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2371701468308185539006227 3557552202462278308509341)
          ·
            refine ⟨1334082075923354365691003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3557552202462278308509341 1334082075923354365691003)
            ·
              refine ⟨2001123113885031548536505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1334082075923354365691003 2001123113885031548536505)
              ·
                refine ⟨1500842335413773661402379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2001123113885031548536505 1500842335413773661402379)
                ·
                  refine ⟨2251263503120660492103569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500842335413773661402379 2251263503120660492103569)
                  ·
                    refine ⟨1688447627340495369077677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2251263503120660492103569 1688447627340495369077677)
                    ·
                      refine ⟨633167860252685763404129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1688447627340495369077677 633167860252685763404129)
                      ·
                        rfl

theorem cell23_1233090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_1233090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233090 prefixEnd_1233090 := by exact prefixLift 1233090
  have htrace : WordTrace (prefixWord ++ tailWord_1233090) baseStart_1233090 baseEnd_1233090 := by
    simpa [prefixWord, tailWord_1233090, baseEnd_1233090] using wordTrace_append hprefix tailTrace_1233090
  have hstable : (prefixWord ++ tailWord_1233090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233090).length < 2 ^ (prefixWord ++ tailWord_1233090).sum := by decide
  have hdescent : baseEnd_1233090 < baseStart_1233090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233112 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 2, 1, 5]
def baseStart_1233112 : Nat := 118140960795 + 1233112 * 2 ^ 59
def prefixEnd_1233112 : Nat := 4983230072969 + 3 ^ 40 * 1233112 * 2
def baseEnd_1233112 : Nat := 633179156827084677329027

theorem tailTrace_1233112 : CollatzResearch.WordTrace tailWord_1233112 prefixEnd_1233112 633179156827084677329027 := by
  unfold tailWord_1233112
  simp only [CollatzResearch.WordTrace]
  refine ⟨22487644754326648804042795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29983526339102198405390393 22487644754326648804042795)
  ·
    refine ⟨33731467131489973206064193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22487644754326648804042795 33731467131489973206064193)
    ·
      refine ⟨25298600348617479904548145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33731467131489973206064193 25298600348617479904548145)
      ·
        refine ⟨18973950261463109928411109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25298600348617479904548145 18973950261463109928411109)
        ·
          refine ⟨3557615674024333111577083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18973950261463109928411109 3557615674024333111577083)
          ·
            refine ⟨5336423511036499667365625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3557615674024333111577083 5336423511036499667365625)
            ·
              refine ⟨4002317633277374750524219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5336423511036499667365625 4002317633277374750524219)
              ·
                refine ⟨6003476449916062125786329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4002317633277374750524219 6003476449916062125786329)
                ·
                  refine ⟨4502607337437046594339747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6003476449916062125786329 4502607337437046594339747)
                  ·
                    refine ⟨6753911006155569891509621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4502607337437046594339747 6753911006155569891509621)
                    ·
                      refine ⟨633179156827084677329027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6753911006155569891509621 633179156827084677329027)
                      ·
                        rfl

theorem cell23_1233112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_1233112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233112 prefixEnd_1233112 := by exact prefixLift 1233112
  have htrace : WordTrace (prefixWord ++ tailWord_1233112) baseStart_1233112 baseEnd_1233112 := by
    simpa [prefixWord, tailWord_1233112, baseEnd_1233112] using wordTrace_append hprefix tailTrace_1233112
  have hstable : (prefixWord ++ tailWord_1233112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233112).length < 2 ^ (prefixWord ++ tailWord_1233112).sum := by decide
  have hdescent : baseEnd_1233112 < baseStart_1233112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233199 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 2, 4, 2]
def baseStart_1233199 : Nat := 118140960795 + 1233199 * 2 ^ 59
def prefixEnd_1233199 : Nat := 4983230072969 + 3 ^ 40 * 1233199 * 2
def baseEnd_1233199 : Nat := 633223829644025836941127

theorem tailTrace_1233199 : CollatzResearch.WordTrace tailWord_1233199 prefixEnd_1233199 633223829644025836941127 := by
  unfold tailWord_1233199
  simp only [CollatzResearch.WordTrace]
  refine ⟨44978462659338111466502651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29985641772892074311001767 44978462659338111466502651)
  ·
    refine ⟨67467693989007167199753977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44978462659338111466502651 67467693989007167199753977)
    ·
      refine ⟨50600770491755375399815483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67467693989007167199753977 50600770491755375399815483)
      ·
        refine ⟨75901155737633063099723225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50600770491755375399815483 75901155737633063099723225)
        ·
          refine ⟨56925866803224797324792419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75901155737633063099723225 56925866803224797324792419)
          ·
            refine ⟨85388800204837195987188629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56925866803224797324792419 85388800204837195987188629)
            ·
              refine ⟨4002600009601743561899467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85388800204837195987188629 4002600009601743561899467)
              ·
                refine ⟨6003900014402615342849201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4002600009601743561899467 6003900014402615342849201)
                ·
                  refine ⟨4502925010801961507136901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6003900014402615342849201 4502925010801961507136901)
                  ·
                    refine ⟨844298439525367782588169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4502925010801961507136901 844298439525367782588169)
                    ·
                      refine ⟨633223829644025836941127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 844298439525367782588169 633223829644025836941127)
                      ·
                        rfl

theorem cell23_1233199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 4, 2].length) (baseStart_1233199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233199 prefixEnd_1233199 := by exact prefixLift 1233199
  have htrace : WordTrace (prefixWord ++ tailWord_1233199) baseStart_1233199 baseEnd_1233199 := by
    simpa [prefixWord, tailWord_1233199, baseEnd_1233199] using wordTrace_append hprefix tailTrace_1233199
  have hstable : (prefixWord ++ tailWord_1233199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233199).length < 2 ^ (prefixWord ++ tailWord_1233199).sum := by decide
  have hdescent : baseEnd_1233199 < baseStart_1233199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233212 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_1233212 : Nat := 118140960795 + 1233212 * 2 ^ 59
def prefixEnd_1233212 : Nat := 4983230072969 + 3 ^ 40 * 1233212 * 2
def baseEnd_1233212 : Nat := 633230504892534286078567

theorem tailTrace_1233212 : CollatzResearch.WordTrace tailWord_1233212 prefixEnd_1233212 633230504892534286078567 := by
  unfold tailWord_1233212
  simp only [CollatzResearch.WordTrace]
  refine ⟨22489468404145507343362945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29985957872194009791150593 22489468404145507343362945)
  ·
    refine ⟨16867101303109130507522209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22489468404145507343362945 16867101303109130507522209)
    ·
      refine ⟨12650325977331847880641657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16867101303109130507522209 12650325977331847880641657)
      ·
        refine ⟨9487744482998885910481243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12650325977331847880641657 9487744482998885910481243)
        ·
          refine ⟨14231616724498328865721865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9487744482998885910481243 14231616724498328865721865)
          ·
            refine ⟨10673712543373746649291399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14231616724498328865721865 10673712543373746649291399)
            ·
              refine ⟨16010568815060619973937099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10673712543373746649291399 16010568815060619973937099)
              ·
                refine ⟨24015853222590929960905649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16010568815060619973937099 24015853222590929960905649)
                ·
                  refine ⟨18011889916943197470679237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24015853222590929960905649 18011889916943197470679237)
                  ·
                    refine ⟨3377229359426849525752357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18011889916943197470679237 3377229359426849525752357)
                    ·
                      refine ⟨633230504892534286078567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3377229359426849525752357 633230504892534286078567)
                      ·
                        rfl

theorem cell23_1233212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_1233212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233212 prefixEnd_1233212 := by exact prefixLift 1233212
  have htrace : WordTrace (prefixWord ++ tailWord_1233212) baseStart_1233212 baseEnd_1233212 := by
    simpa [prefixWord, tailWord_1233212, baseEnd_1233212] using wordTrace_append hprefix tailTrace_1233212
  have hstable : (prefixWord ++ tailWord_1233212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233212).length < 2 ^ (prefixWord ++ tailWord_1233212).sum := by decide
  have hdescent : baseEnd_1233212 < baseStart_1233212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233236 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_1233236 : Nat := 118140960795 + 1233236 * 2 ^ 59
def prefixEnd_1233236 : Nat := 4983230072969 + 3 ^ 40 * 1233236 * 2
def baseEnd_1233236 : Nat := 633242828428242192178457

theorem tailTrace_1233236 : CollatzResearch.WordTrace tailWord_1233236 prefixEnd_1233236 633242828428242192178457 := by
  unfold tailWord_1233236
  simp only [CollatzResearch.WordTrace]
  refine ⟨22489906080102033392799781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29986541440136044523733041 22489906080102033392799781)
  ·
    refine ⟨4216857390019131261149959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22489906080102033392799781 4216857390019131261149959)
    ·
      refine ⟨6325286085028696891724939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4216857390019131261149959 6325286085028696891724939)
      ·
        refine ⟨9487929127543045337587409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6325286085028696891724939 9487929127543045337587409)
        ·
          refine ⟨7115946845657284003190557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9487929127543045337587409 7115946845657284003190557)
          ·
            refine ⟨2668480067121481501196459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7115946845657284003190557 2668480067121481501196459)
            ·
              refine ⟨4002720100682222251794689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668480067121481501196459 4002720100682222251794689)
              ·
                refine ⟨3002040075511666688846017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4002720100682222251794689 3002040075511666688846017)
                ·
                  refine ⟨2251530056633750016634513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3002040075511666688846017 2251530056633750016634513)
                  ·
                    refine ⟨1688647542475312512475885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2251530056633750016634513 1688647542475312512475885)
                    ·
                      refine ⟨633242828428242192178457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1688647542475312512475885 633242828428242192178457)
                      ·
                        rfl

theorem cell23_1233236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_1233236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233236 prefixEnd_1233236 := by exact prefixLift 1233236
  have htrace : WordTrace (prefixWord ++ tailWord_1233236) baseStart_1233236 baseEnd_1233236 := by
    simpa [prefixWord, tailWord_1233236, baseEnd_1233236] using wordTrace_append hprefix tailTrace_1233236
  have hstable : (prefixWord ++ tailWord_1233236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233236).length < 2 ^ (prefixWord ++ tailWord_1233236).sum := by decide
  have hdescent : baseEnd_1233236 < baseStart_1233236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233256 : List Nat := [2, 1, 4, 2, 2, 1, 4, 1, 6]
def baseStart_1233256 : Nat := 118140960795 + 1233256 * 2 ^ 59
def prefixEnd_1233256 : Nat := 4983230072969 + 3 ^ 40 * 1233256 * 2
def baseEnd_1233256 : Nat := 70361455337925790436485

theorem tailTrace_1233256 : CollatzResearch.WordTrace tailWord_1233256 prefixEnd_1233256 70361455337925790436485 := by
  unfold tailWord_1233256
  simp only [CollatzResearch.WordTrace]
  refine ⟨22490270810065805100663811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29987027746754406800885081 22490270810065805100663811)
  ·
    refine ⟨33735406215098707650995717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22490270810065805100663811 33735406215098707650995717)
    ·
      refine ⟨6325388665331007684561697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33735406215098707650995717 6325388665331007684561697)
      ·
        refine ⟨4744041498998255763421273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6325388665331007684561697 4744041498998255763421273)
        ·
          refine ⟨3558031124248691822565955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4744041498998255763421273 3558031124248691822565955)
          ·
            refine ⟨5337046686373037733848933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3558031124248691822565955 5337046686373037733848933)
            ·
              refine ⟨1000696253694944575096675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5337046686373037733848933 1000696253694944575096675)
              ·
                refine ⟨1501044380542416862645013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1000696253694944575096675 1501044380542416862645013)
                ·
                  refine ⟨70361455337925790436485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1501044380542416862645013 70361455337925790436485)
                  ·
                    rfl

theorem cell23_1233256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 6].length) (baseStart_1233256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233256 prefixEnd_1233256 := by exact prefixLift 1233256
  have htrace : WordTrace (prefixWord ++ tailWord_1233256) baseStart_1233256 baseEnd_1233256 := by
    simpa [prefixWord, tailWord_1233256, baseEnd_1233256] using wordTrace_append hprefix tailTrace_1233256
  have hstable : (prefixWord ++ tailWord_1233256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233256).length < 2 ^ (prefixWord ++ tailWord_1233256).sum := by decide
  have hdescent : baseEnd_1233256 < baseStart_1233256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233270 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1233270 : Nat := 118140960795 + 1233270 * 2 ^ 59
def prefixEnd_1233270 : Nat := 4983230072969 + 3 ^ 40 * 1233270 * 2
def baseEnd_1233270 : Nat := 633260286770495059153301

theorem tailTrace_1233270 : CollatzResearch.WordTrace tailWord_1233270 prefixEnd_1233270 633260286770495059153301 := by
  unfold tailWord_1233270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2811315765130055662021079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29987368161387260394891509 2811315765130055662021079)
  ·
    refine ⟨4216973647695083493031619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2811315765130055662021079 4216973647695083493031619)
    ·
      refine ⟨6325460471542625239547429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4216973647695083493031619 6325460471542625239547429)
      ·
        refine ⟨1186023838414242232415143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6325460471542625239547429 1186023838414242232415143)
        ·
          refine ⟨1779035757621363348622715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186023838414242232415143 1779035757621363348622715)
          ·
            refine ⟨2668553636432045022934073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779035757621363348622715 2668553636432045022934073)
            ·
              refine ⟨2001415227324033767200555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2668553636432045022934073 2001415227324033767200555)
              ·
                refine ⟨3002122840986050650800833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2001415227324033767200555 3002122840986050650800833)
                ·
                  refine ⟨2251592130739537988100625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3002122840986050650800833 2251592130739537988100625)
                  ·
                    refine ⟨1688694098054653491075469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2251592130739537988100625 1688694098054653491075469)
                    ·
                      refine ⟨633260286770495059153301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1688694098054653491075469 633260286770495059153301)
                      ·
                        rfl

theorem cell23_1233270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1233270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233270 prefixEnd_1233270 := by exact prefixLift 1233270
  have htrace : WordTrace (prefixWord ++ tailWord_1233270) baseStart_1233270 baseEnd_1233270 := by
    simpa [prefixWord, tailWord_1233270, baseEnd_1233270] using wordTrace_append hprefix tailTrace_1233270
  have hstable : (prefixWord ++ tailWord_1233270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233270).length < 2 ^ (prefixWord ++ tailWord_1233270).sum := by decide
  have hdescent : baseEnd_1233270 < baseStart_1233270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233316 : List Nat := [2, 3, 1, 2, 1, 1, 4, 3, 2, 4]
def baseStart_1233316 : Nat := 118140960795 + 1233316 * 2 ^ 59
def prefixEnd_1233316 : Nat := 4983230072969 + 3 ^ 40 * 1233316 * 2
def baseEnd_1233316 : Nat := 211094635626867293059363

theorem tailTrace_1233316 : CollatzResearch.WordTrace tailWord_1233316 prefixEnd_1233316 211094635626867293059363 := by
  unfold tailWord_1233316
  simp only [CollatzResearch.WordTrace]
  refine ⟨22491364999957120224255901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29988486666609493632341201 22491364999957120224255901)
  ·
    refine ⟨8434261874983920084095963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22491364999957120224255901 8434261874983920084095963)
    ·
      refine ⟨12651392812475880126143945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8434261874983920084095963 12651392812475880126143945)
      ·
        refine ⟨9488544609356910094607959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12651392812475880126143945 9488544609356910094607959)
        ·
          refine ⟨14232816914035365141911939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9488544609356910094607959 14232816914035365141911939)
          ·
            refine ⟨21349225371053047712867909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14232816914035365141911939 21349225371053047712867909)
            ·
              refine ⟨4002979757072446446162733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21349225371053047712867909 4002979757072446446162733)
              ·
                refine ⟨1501117408902167417311025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4002979757072446446162733 1501117408902167417311025)
                ·
                  refine ⟨1125838056676625562983269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1501117408902167417311025 1125838056676625562983269)
                  ·
                    refine ⟨211094635626867293059363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1125838056676625562983269 211094635626867293059363)
                    ·
                      rfl

theorem cell23_1233316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_1233316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233316 prefixEnd_1233316 := by exact prefixLift 1233316
  have htrace : WordTrace (prefixWord ++ tailWord_1233316) baseStart_1233316 baseEnd_1233316 := by
    simpa [prefixWord, tailWord_1233316, baseEnd_1233316] using wordTrace_append hprefix tailTrace_1233316
  have hstable : (prefixWord ++ tailWord_1233316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233316).length < 2 ^ (prefixWord ++ tailWord_1233316).sum := by decide
  have hdescent : baseEnd_1233316 < baseStart_1233316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233340 : List Nat := [2, 2, 2, 4, 1, 3, 2, 1, 1, 1, 4]
def baseStart_1233340 : Nat := 118140960795 + 1233340 * 2 ^ 59
def prefixEnd_1233340 : Nat := 4983230072969 + 3 ^ 40 * 1233340 * 2
def baseEnd_1233340 : Nat := 633296230416309785277979

theorem tailTrace_1233340 : CollatzResearch.WordTrace tailWord_1233340 prefixEnd_1233340 633296230416309785277979 := by
  unfold tailWord_1233340
  simp only [CollatzResearch.WordTrace]
  refine ⟨22491802675913646273692737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29989070234551528364923649 22491802675913646273692737)
  ·
    refine ⟨16868852006935234705269553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22491802675913646273692737 16868852006935234705269553)
    ·
      refine ⟨12651639005201426028952165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16868852006935234705269553 12651639005201426028952165)
      ·
        refine ⟨2372182313475267380428531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12651639005201426028952165 2372182313475267380428531)
        ·
          refine ⟨3558273470212901070642797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2372182313475267380428531 3558273470212901070642797)
          ·
            refine ⟨1334352551329837901491049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3558273470212901070642797 1334352551329837901491049)
            ·
              refine ⟨1000764413497378426118287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1334352551329837901491049 1000764413497378426118287)
              ·
                refine ⟨1501146620246067639177431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1000764413497378426118287 1501146620246067639177431)
                ·
                  refine ⟨2251719930369101458766147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501146620246067639177431 2251719930369101458766147)
                  ·
                    refine ⟨3377579895553652188149221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2251719930369101458766147 3377579895553652188149221)
                    ·
                      refine ⟨633296230416309785277979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3377579895553652188149221 633296230416309785277979)
                      ·
                        rfl

theorem cell23_1233340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_1233340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233340 prefixEnd_1233340 := by exact prefixLift 1233340
  have htrace : WordTrace (prefixWord ++ tailWord_1233340) baseStart_1233340 baseEnd_1233340 := by
    simpa [prefixWord, tailWord_1233340, baseEnd_1233340] using wordTrace_append hprefix tailTrace_1233340
  have hstable : (prefixWord ++ tailWord_1233340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233340).length < 2 ^ (prefixWord ++ tailWord_1233340).sum := by decide
  have hdescent : baseEnd_1233340 < baseStart_1233340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233413 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 4, 2, 2]
def baseStart_1233413 : Nat := 118140960795 + 1233413 * 2 ^ 59
def prefixEnd_1233413 : Nat := 4983230072969 + 3 ^ 40 * 1233413 * 2
def baseEnd_1233413 : Nat := 633333714504087999665143

theorem tailTrace_1233413 : CollatzResearch.WordTrace tailWord_1233413 prefixEnd_1233413 633333714504087999665143 := by
  unfold tailWord_1233413
  simp only [CollatzResearch.WordTrace]
  refine ⟨44986267880562826014792893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29990845253708550676528595 44986267880562826014792893)
  ·
    refine ⟨16869850455211059755547335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44986267880562826014792893 16869850455211059755547335)
    ·
      refine ⟨25304775682816589633321003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16869850455211059755547335 25304775682816589633321003)
      ·
        refine ⟨37957163524224884449981505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25304775682816589633321003 37957163524224884449981505)
        ·
          refine ⟨28467872643168663337486129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37957163524224884449981505 28467872643168663337486129)
          ·
            refine ⟨21350904482376497503114597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28467872643168663337486129 21350904482376497503114597)
            ·
              refine ⟨4003294590445593281833987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21350904482376497503114597 4003294590445593281833987)
              ·
                refine ⟨6004941885668389922750981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4003294590445593281833987 6004941885668389922750981)
                ·
                  refine ⟨1125926603562823110515809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6004941885668389922750981 1125926603562823110515809)
                  ·
                    refine ⟨844444952672117332886857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1125926603562823110515809 844444952672117332886857)
                    ·
                      refine ⟨633333714504087999665143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 844444952672117332886857 633333714504087999665143)
                      ·
                        rfl

theorem cell23_1233413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 2, 2].length) (baseStart_1233413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233413 prefixEnd_1233413 := by exact prefixLift 1233413
  have htrace : WordTrace (prefixWord ++ tailWord_1233413) baseStart_1233413 baseEnd_1233413 := by
    simpa [prefixWord, tailWord_1233413, baseEnd_1233413] using wordTrace_append hprefix tailTrace_1233413
  have hstable : (prefixWord ++ tailWord_1233413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233413).length < 2 ^ (prefixWord ++ tailWord_1233413).sum := by decide
  have hdescent : baseEnd_1233413 < baseStart_1233413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233447 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_1233447 : Nat := 118140960795 + 1233447 * 2 ^ 59
def prefixEnd_1233447 : Nat := 4983230072969 + 3 ^ 40 * 1233447 * 2
def baseEnd_1233447 : Nat := 633351172846340866639987

theorem tailTrace_1233447 : CollatzResearch.WordTrace tailWord_1233447 prefixEnd_1233447 633351172846340866639987 := by
  unfold tailWord_1233447
  simp only [CollatzResearch.WordTrace]
  refine ⟨44987507962439649821530595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29991671974959766547687063 44987507962439649821530595)
  ·
    refine ⟨67481261943659474732295893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44987507962439649821530595 67481261943659474732295893)
    ·
      refine ⟨1581592076804518939038185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 67481261943659474732295893 1581592076804518939038185)
      ·
        refine ⟨1186194057603389204278639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1581592076804518939038185 1186194057603389204278639)
        ·
          refine ⟨1779291086405083806417959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186194057603389204278639 1779291086405083806417959)
          ·
            refine ⟨2668936629607625709626939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779291086405083806417959 2668936629607625709626939)
            ·
              refine ⟨4003404944411438564440409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668936629607625709626939 4003404944411438564440409)
              ·
                refine ⟨3002553708308578923330307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4003404944411438564440409 3002553708308578923330307)
                ·
                  refine ⟨4503830562462868384995461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3002553708308578923330307 4503830562462868384995461)
                  ·
                    refine ⟨844468230461787822186649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4503830562462868384995461 844468230461787822186649)
                    ·
                      refine ⟨633351172846340866639987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 844468230461787822186649 633351172846340866639987)
                      ·
                        rfl

theorem cell23_1233447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_1233447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233447 prefixEnd_1233447 := by exact prefixLift 1233447
  have htrace : WordTrace (prefixWord ++ tailWord_1233447) baseStart_1233447 baseEnd_1233447 := by
    simpa [prefixWord, tailWord_1233447, baseEnd_1233447] using wordTrace_append hprefix tailTrace_1233447
  have hstable : (prefixWord ++ tailWord_1233447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233447).length < 2 ^ (prefixWord ++ tailWord_1233447).sum := by decide
  have hdescent : baseEnd_1233447 < baseStart_1233447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233459 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 5]
def baseStart_1233459 : Nat := 118140960795 + 1233459 * 2 ^ 59
def prefixEnd_1233459 : Nat := 4983230072969 + 3 ^ 40 * 1233459 * 2
def baseEnd_1233459 : Nat := 633357334614194819689931

theorem tailTrace_1233459 : CollatzResearch.WordTrace tailWord_1233459 prefixEnd_1233459 633357334614194819689931 := by
  unfold tailWord_1233459
  simp only [CollatzResearch.WordTrace]
  refine ⟨44987945638396175870967431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29991963758930783913978287 44987945638396175870967431)
  ·
    refine ⟨67481918457594263806451147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44987945638396175870967431 67481918457594263806451147)
    ·
      refine ⟨101222877686391395709676721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67481918457594263806451147 101222877686391395709676721)
      ·
        refine ⟨75917158264793546782257541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101222877686391395709676721 75917158264793546782257541)
        ·
          refine ⟨14234467174648790021673289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75917158264793546782257541 14234467174648790021673289)
          ·
            refine ⟨10675850380986592516254967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14234467174648790021673289 10675850380986592516254967)
            ·
              refine ⟨16013775571479888774382451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10675850380986592516254967 16013775571479888774382451)
              ·
                refine ⟨24020663357219833161573677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16013775571479888774382451 24020663357219833161573677)
                ·
                  refine ⟨9007748758957437435590129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24020663357219833161573677 9007748758957437435590129)
                  ·
                    refine ⟨6755811569218078076692597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9007748758957437435590129 6755811569218078076692597)
                    ·
                      refine ⟨633357334614194819689931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6755811569218078076692597 633357334614194819689931)
                      ·
                        rfl

theorem cell23_1233459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_1233459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233459 prefixEnd_1233459 := by exact prefixLift 1233459
  have htrace : WordTrace (prefixWord ++ tailWord_1233459) baseStart_1233459 baseEnd_1233459 := by
    simpa [prefixWord, tailWord_1233459, baseEnd_1233459] using wordTrace_append hprefix tailTrace_1233459
  have hstable : (prefixWord ++ tailWord_1233459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233459).length < 2 ^ (prefixWord ++ tailWord_1233459).sum := by decide
  have hdescent : baseEnd_1233459 < baseStart_1233459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233466 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 2, 5]
def baseStart_1233466 : Nat := 118140960795 + 1233466 * 2 ^ 59
def prefixEnd_1233466 : Nat := 4983230072969 + 3 ^ 40 * 1233466 * 2
def baseEnd_1233466 : Nat := 211120309659592097434133

theorem tailTrace_1233466 : CollatzResearch.WordTrace tailWord_1233466 prefixEnd_1233466 211120309659592097434133 := by
  unfold tailWord_1233466
  simp only [CollatzResearch.WordTrace]
  refine ⟨11247050237342704016618063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29992133966247210710981501 11247050237342704016618063)
  ·
    refine ⟨16870575356014056024927095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11247050237342704016618063 16870575356014056024927095)
    ·
      refine ⟨25305863034021084037390643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16870575356014056024927095 25305863034021084037390643)
      ·
        refine ⟨37958794551031626056085965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25305863034021084037390643 37958794551031626056085965)
        ·
          refine ⟨14234547956636859771032237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37958794551031626056085965 14234547956636859771032237)
          ·
            refine ⟨5337955483738822414137089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14234547956636859771032237 5337955483738822414137089)
            ·
              refine ⟨4003466612804116810602817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5337955483738822414137089 4003466612804116810602817)
              ·
                refine ⟨3002599959603087607952113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4003466612804116810602817 3002599959603087607952113)
                ·
                  refine ⟨2251949969702315705964085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3002599959603087607952113 2251949969702315705964085)
                  ·
                    refine ⟨211120309659592097434133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2251949969702315705964085 211120309659592097434133)
                    ·
                      rfl

theorem cell23_1233466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_1233466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233466 prefixEnd_1233466 := by exact prefixLift 1233466
  have htrace : WordTrace (prefixWord ++ tailWord_1233466) baseStart_1233466 baseEnd_1233466 := by
    simpa [prefixWord, tailWord_1233466, baseEnd_1233466] using wordTrace_append hprefix tailTrace_1233466
  have hstable : (prefixWord ++ tailWord_1233466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233466).length < 2 ^ (prefixWord ++ tailWord_1233466).sum := by decide
  have hdescent : baseEnd_1233466 < baseStart_1233466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233473 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_1233473 : Nat := 118140960795 + 1233473 * 2 ^ 59
def prefixEnd_1233473 : Nat := 4983230072969 + 3 ^ 40 * 1233473 * 2
def baseEnd_1233473 : Nat := 633364523343357764914867

theorem tailTrace_1233473 : CollatzResearch.WordTrace tailWord_1233473 prefixEnd_1233473 633364523343357764914867 := by
  unfold tailWord_1233473
  simp only [CollatzResearch.WordTrace]
  refine ⟨44988456260345456261977073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29992304173563637507984715 44988456260345456261977073)
  ·
    refine ⟨33741342195259092196482805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44988456260345456261977073 33741342195259092196482805)
    ·
      refine ⟨3163250830805539893420263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33741342195259092196482805 3163250830805539893420263)
      ·
        refine ⟨4744876246208309840130395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3163250830805539893420263 4744876246208309840130395)
        ·
          refine ⟨7117314369312464760195593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4744876246208309840130395 7117314369312464760195593)
          ·
            refine ⟨5337985776984348570146695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7117314369312464760195593 5337985776984348570146695)
            ·
              refine ⟨8006978665476522855220043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5337985776984348570146695 8006978665476522855220043)
              ·
                refine ⟨12010467998214784282830065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8006978665476522855220043 12010467998214784282830065)
                ·
                  refine ⟨9007850998661088212122549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12010467998214784282830065 9007850998661088212122549)
                  ·
                    refine ⟨844486031124477019886489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9007850998661088212122549 844486031124477019886489)
                    ·
                      refine ⟨633364523343357764914867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 844486031124477019886489 633364523343357764914867)
                      ·
                        rfl

theorem cell23_1233473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_1233473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233473 prefixEnd_1233473 := by exact prefixLift 1233473
  have htrace : WordTrace (prefixWord ++ tailWord_1233473) baseStart_1233473 baseEnd_1233473 := by
    simpa [prefixWord, tailWord_1233473, baseEnd_1233473] using wordTrace_append hprefix tailTrace_1233473
  have hstable : (prefixWord ++ tailWord_1233473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233473).length < 2 ^ (prefixWord ++ tailWord_1233473).sum := by decide
  have hdescent : baseEnd_1233473 < baseStart_1233473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233486 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_1233486 : Nat := 118140960795 + 1233486 * 2 ^ 59
def prefixEnd_1233486 : Nat := 4983230072969 + 3 ^ 40 * 1233486 * 2
def baseEnd_1233486 : Nat := 633371198591866214052307

theorem tailTrace_1233486 : CollatzResearch.WordTrace tailWord_1233486 prefixEnd_1233486 633371198591866214052307 := by
  unfold tailWord_1233486
  simp only [CollatzResearch.WordTrace]
  refine ⟨5623616301162294935275039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29992620272865572988133541 5623616301162294935275039)
  ·
    refine ⟨8435424451743442402912559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5623616301162294935275039 8435424451743442402912559)
    ·
      refine ⟨12653136677615163604368839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8435424451743442402912559 12653136677615163604368839)
      ·
        refine ⟨18979705016422745406553259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12653136677615163604368839 18979705016422745406553259)
        ·
          refine ⟨28469557524634118109829889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18979705016422745406553259 28469557524634118109829889)
          ·
            refine ⟨21352168143475588582372417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28469557524634118109829889 21352168143475588582372417)
            ·
              refine ⟨16014126107606691436779313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21352168143475588582372417 16014126107606691436779313)
              ·
                refine ⟨12010594580705018577584485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16014126107606691436779313 12010594580705018577584485)
                ·
                  refine ⟨2251986483882190983297091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12010594580705018577584485 2251986483882190983297091)
                  ·
                    refine ⟨3377979725823286474945637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2251986483882190983297091 3377979725823286474945637)
                    ·
                      refine ⟨633371198591866214052307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3377979725823286474945637 633371198591866214052307)
                      ·
                        rfl

theorem cell23_1233486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_1233486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233486 prefixEnd_1233486 := by exact prefixLift 1233486
  have htrace : WordTrace (prefixWord ++ tailWord_1233486) baseStart_1233486 baseEnd_1233486 := by
    simpa [prefixWord, tailWord_1233486, baseEnd_1233486] using wordTrace_append hprefix tailTrace_1233486
  have hstable : (prefixWord ++ tailWord_1233486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233486).length < 2 ^ (prefixWord ++ tailWord_1233486).sum := by decide
  have hdescent : baseEnd_1233486 < baseStart_1233486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233496 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 5, 4]
def baseStart_1233496 : Nat := 118140960795 + 1233496 * 2 ^ 59
def prefixEnd_1233496 : Nat := 4983230072969 + 3 ^ 40 * 1233496 * 2
def baseEnd_1233496 : Nat := 211125444466137058309087

theorem tailTrace_1233496 : CollatzResearch.WordTrace tailWord_1233496 prefixEnd_1233496 211125444466137058309087 := by
  unfold tailWord_1233496
  simp only [CollatzResearch.WordTrace]
  refine ⟨22494647569631065595032171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29992863426174754126709561 22494647569631065595032171)
  ·
    refine ⟨33741971354446598392548257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22494647569631065595032171 33741971354446598392548257)
    ·
      refine ⟨25306478515834948794411193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33741971354446598392548257 25306478515834948794411193)
      ·
        refine ⟨18979858886876211595808395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25306478515834948794411193 18979858886876211595808395)
        ·
          refine ⟨28469788330314317393712593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18979858886876211595808395 28469788330314317393712593)
          ·
            refine ⟨21352341247735738045284445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28469788330314317393712593 21352341247735738045284445)
            ·
              refine ⟨8007127967900901766981667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21352341247735738045284445 8007127967900901766981667)
              ·
                refine ⟨12010691951851352650472501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8007127967900901766981667 12010691951851352650472501)
                ·
                  refine ⟨1126002370486064310981797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12010691951851352650472501 1126002370486064310981797)
                  ·
                    refine ⟨211125444466137058309087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1126002370486064310981797 211125444466137058309087)
                    ·
                      rfl

theorem cell23_1233496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_1233496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233496 prefixEnd_1233496 := by exact prefixLift 1233496
  have htrace : WordTrace (prefixWord ++ tailWord_1233496) baseStart_1233496 baseEnd_1233496 := by
    simpa [prefixWord, tailWord_1233496, baseEnd_1233496] using wordTrace_append hprefix tailTrace_1233496
  have hstable : (prefixWord ++ tailWord_1233496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233496).length < 2 ^ (prefixWord ++ tailWord_1233496).sum := by decide
  have hdescent : baseEnd_1233496 < baseStart_1233496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233500 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 2, 5]
def baseStart_1233500 : Nat := 118140960795 + 1233500 * 2 ^ 59
def prefixEnd_1233500 : Nat := 4983230072969 + 3 ^ 40 * 1233500 * 2
def baseEnd_1233500 : Nat := 211126129107009719759081

theorem tailTrace_1233500 : CollatzResearch.WordTrace tailWord_1233500 prefixEnd_1233500 211126129107009719759081 := by
  unfold tailWord_1233500
  simp only [CollatzResearch.WordTrace]
  refine ⟨22494720515623819936604977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29992960687498426582139969 22494720515623819936604977)
  ·
    refine ⟨16871040386717864952453733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22494720515623819936604977 16871040386717864952453733)
    ·
      refine ⟨3163320072509599678585075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16871040386717864952453733 3163320072509599678585075)
      ·
        refine ⟨4744980108764399517877613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3163320072509599678585075 4744980108764399517877613)
        ·
          refine ⟨1779367540786649819204105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4744980108764399517877613 1779367540786649819204105)
          ·
            refine ⟨1334525655589987364403079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1779367540786649819204105 1334525655589987364403079)
            ·
              refine ⟨2001788483384981046604619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1334525655589987364403079 2001788483384981046604619)
              ·
                refine ⟨3002682725077471569906929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2001788483384981046604619 3002682725077471569906929)
                ·
                  refine ⟨2252012043808103677430197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3002682725077471569906929 2252012043808103677430197)
                  ·
                    refine ⟨211126129107009719759081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2252012043808103677430197 211126129107009719759081)
                    ·
                      rfl

theorem cell23_1233500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_1233500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233500 prefixEnd_1233500 := by exact prefixLift 1233500
  have htrace : WordTrace (prefixWord ++ tailWord_1233500) baseStart_1233500 baseEnd_1233500 := by
    simpa [prefixWord, tailWord_1233500, baseEnd_1233500] using wordTrace_append hprefix tailTrace_1233500
  have hstable : (prefixWord ++ tailWord_1233500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233500).length < 2 ^ (prefixWord ++ tailWord_1233500).sum := by decide
  have hdescent : baseEnd_1233500 < baseStart_1233500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233543 : List Nat := [1, 1, 4, 2, 1, 2, 5, 1, 6]
def baseStart_1233543 : Nat := 118140960795 + 1233543 * 2 ^ 59
def prefixEnd_1233543 : Nat := 4983230072969 + 3 ^ 40 * 1233543 * 2
def baseEnd_1233543 : Nat := 70377829665463610115505

theorem tailTrace_1233543 : CollatzResearch.WordTrace tailWord_1233543 prefixEnd_1233543 70377829665463610115505 := by
  unfold tailWord_1233543
  simp only [CollatzResearch.WordTrace]
  refine ⟨44991009370091858217025283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29994006246727905478016855 44991009370091858217025283)
  ·
    refine ⟨67486514055137787325537925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44991009370091858217025283 67486514055137787325537925)
    ·
      refine ⟨12653721385338335123538361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67486514055137787325537925 12653721385338335123538361)
      ·
        refine ⟨9490291039003751342653771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12653721385338335123538361 9490291039003751342653771)
        ·
          refine ⟨14235436558505627013980657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9490291039003751342653771 14235436558505627013980657)
          ·
            refine ⟨10676577418879220260485493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14235436558505627013980657 10676577418879220260485493)
            ·
              refine ⟨1000929133019926899420515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10676577418879220260485493 1000929133019926899420515)
              ·
                refine ⟨1501393699529890349130773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1000929133019926899420515 1501393699529890349130773)
                ·
                  refine ⟨70377829665463610115505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1501393699529890349130773 70377829665463610115505)
                  ·
                    rfl

theorem cell23_1233543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 6].length) (baseStart_1233543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233543 prefixEnd_1233543 := by exact prefixLift 1233543
  have htrace : WordTrace (prefixWord ++ tailWord_1233543) baseStart_1233543 baseEnd_1233543 := by
    simpa [prefixWord, tailWord_1233543, baseEnd_1233543] using wordTrace_append hprefix tailTrace_1233543
  have hstable : (prefixWord ++ tailWord_1233543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233543).length < 2 ^ (prefixWord ++ tailWord_1233543).sum := by decide
  have hdescent : baseEnd_1233543 < baseStart_1233543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233610 : List Nat := [3, 1, 2, 1, 4, 1, 3, 2, 1, 1, 4]
def baseStart_1233610 : Nat := 118140960795 + 1233610 * 2 ^ 59
def prefixEnd_1233610 : Nat := 4983230072969 + 3 ^ 40 * 1233610 * 2
def baseEnd_1233610 : Nat := 633434870193023728901737

theorem tailTrace_1233610 : CollatzResearch.WordTrace tailWord_1233610 prefixEnd_1233610 633434870193023728901737 := by
  unfold tailWord_1233610
  simp only [CollatzResearch.WordTrace]
  refine ⟨11248363265212282164928571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29995635373899419106476189 11248363265212282164928571)
  ·
    refine ⟨16872544897818423247392857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11248363265212282164928571 16872544897818423247392857)
    ·
      refine ⟨12654408673363817435544643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16872544897818423247392857 12654408673363817435544643)
      ·
        refine ⟨18981613010045726153316965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12654408673363817435544643 18981613010045726153316965)
        ·
          refine ⟨3559052439383573653746931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18981613010045726153316965 3559052439383573653746931)
          ·
            refine ⟨5338578659075360480620397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3559052439383573653746931 5338578659075360480620397)
            ·
              refine ⟨2001966997153260180232649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5338578659075360480620397 2001966997153260180232649)
              ·
                refine ⟨1501475247864945135174487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2001966997153260180232649 1501475247864945135174487)
                ·
                  refine ⟨2252212871797417702761731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501475247864945135174487 2252212871797417702761731)
                  ·
                    refine ⟨3378319307696126554142597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2252212871797417702761731 3378319307696126554142597)
                    ·
                      refine ⟨633434870193023728901737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3378319307696126554142597 633434870193023728901737)
                      ·
                        rfl

theorem cell23_1233610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_1233610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233610 prefixEnd_1233610 := by exact prefixLift 1233610
  have htrace : WordTrace (prefixWord ++ tailWord_1233610) baseStart_1233610 baseEnd_1233610 := by
    simpa [prefixWord, tailWord_1233610, baseEnd_1233610] using wordTrace_append hprefix tailTrace_1233610
  have hstable : (prefixWord ++ tailWord_1233610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233610).length < 2 ^ (prefixWord ++ tailWord_1233610).sum := by decide
  have hdescent : baseEnd_1233610 < baseStart_1233610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233620 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_1233620 : Nat := 118140960795 + 1233620 * 2 ^ 59
def prefixEnd_1233620 : Nat := 4983230072969 + 3 ^ 40 * 1233620 * 2
def baseEnd_1233620 : Nat := 211146668333189563258897

theorem tailTrace_1233620 : CollatzResearch.WordTrace tailWord_1233620 prefixEnd_1233620 211146668333189563258897 := by
  unfold tailWord_1233620
  simp only [CollatzResearch.WordTrace]
  refine ⟨22496908895406450183789157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29995878527208600245052209 22496908895406450183789157)
  ·
    refine ⟨4218170417888709409460467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22496908895406450183789157 4218170417888709409460467)
    ·
      refine ⟨6327255626833064114190701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4218170417888709409460467 6327255626833064114190701)
      ·
        refine ⟨2372720860062399042821513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6327255626833064114190701 2372720860062399042821513)
        ·
          refine ⟨1779540645046799282116135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2372720860062399042821513 1779540645046799282116135)
          ·
            refine ⟨2669310967570198923174203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779540645046799282116135 2669310967570198923174203)
            ·
              refine ⟨4003966451355298384761305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2669310967570198923174203 4003966451355298384761305)
              ·
                refine ⟨3002974838516473788570979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4003966451355298384761305 3002974838516473788570979)
                ·
                  refine ⟨4504462257774710682856469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3002974838516473788570979 4504462257774710682856469)
                  ·
                    refine ⟨211146668333189563258897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4504462257774710682856469 211146668333189563258897)
                    ·
                      rfl

theorem cell23_1233620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_1233620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233620 prefixEnd_1233620 := by exact prefixLift 1233620
  have htrace : WordTrace (prefixWord ++ tailWord_1233620) baseStart_1233620 baseEnd_1233620 := by
    simpa [prefixWord, tailWord_1233620, baseEnd_1233620] using wordTrace_append hprefix tailTrace_1233620
  have hstable : (prefixWord ++ tailWord_1233620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233620).length < 2 ^ (prefixWord ++ tailWord_1233620).sum := by decide
  have hdescent : baseEnd_1233620 < baseStart_1233620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233623 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 4]
def baseStart_1233623 : Nat := 118140960795 + 1233623 * 2 ^ 59
def prefixEnd_1233623 : Nat := 4983230072969 + 3 ^ 40 * 1233623 * 2
def baseEnd_1233623 : Nat := 633441545441532178039177

theorem tailTrace_1233623 : CollatzResearch.WordTrace tailWord_1233623 prefixEnd_1233623 633441545441532178039177 := by
  unfold tailWord_1233623
  simp only [CollatzResearch.WordTrace]
  refine ⟨44993927209802031879937523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29995951473201354586625015 44993927209802031879937523)
  ·
    refine ⟨67490890814703047819906285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44993927209802031879937523 67490890814703047819906285)
    ·
      refine ⟨25309084055513642932464857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67490890814703047819906285 25309084055513642932464857)
      ·
        refine ⟨18981813041635232199348643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25309084055513642932464857 18981813041635232199348643)
        ·
          refine ⟨28472719562452848299022965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18981813041635232199348643 28472719562452848299022965)
          ·
            refine ⟨2669317458979954528033403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28472719562452848299022965 2669317458979954528033403)
            ·
              refine ⟨4003976188469931792050105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2669317458979954528033403 4003976188469931792050105)
              ·
                refine ⟨3002982141352448844037579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4003976188469931792050105 3002982141352448844037579)
                ·
                  refine ⟨4504473212028673266056369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3002982141352448844037579 4504473212028673266056369)
                  ·
                    refine ⟨3378354909021504949542277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4504473212028673266056369 3378354909021504949542277)
                    ·
                      refine ⟨633441545441532178039177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3378354909021504949542277 633441545441532178039177)
                      ·
                        rfl

theorem cell23_1233623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_1233623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233623 prefixEnd_1233623 := by exact prefixLift 1233623
  have htrace : WordTrace (prefixWord ++ tailWord_1233623) baseStart_1233623 baseEnd_1233623 := by
    simpa [prefixWord, tailWord_1233623, baseEnd_1233623] using wordTrace_append hprefix tailTrace_1233623
  have hstable : (prefixWord ++ tailWord_1233623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233623).length < 2 ^ (prefixWord ++ tailWord_1233623).sum := by decide
  have hdescent : baseEnd_1233623 < baseStart_1233623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233660 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 1, 3, 3]
def baseStart_1233660 : Nat := 118140960795 + 1233660 * 2 ^ 59
def prefixEnd_1233660 : Nat := 4983230072969 + 3 ^ 40 * 1233660 * 2
def baseEnd_1233660 : Nat := 633460544225748533276507

theorem tailTrace_1233660 : CollatzResearch.WordTrace tailWord_1233660 prefixEnd_1233660 633460544225748533276507 := by
  unfold tailWord_1233660
  simp only [CollatzResearch.WordTrace]
  refine ⟨22497638355333993599517217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29996851140445324799356289 22497638355333993599517217)
  ·
    refine ⟨16873228766500495199637913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22497638355333993599517217 16873228766500495199637913)
    ·
      refine ⟨12654921574875371399728435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16873228766500495199637913 12654921574875371399728435)
      ·
        refine ⟨18982382362313057099592653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12654921574875371399728435 18982382362313057099592653)
        ·
          refine ⟨7118393385867396412347245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18982382362313057099592653 7118393385867396412347245)
          ·
            refine ⟨2669397519700273654630217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7118393385867396412347245 2669397519700273654630217)
            ·
              refine ⟨2002048139775205240972663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2669397519700273654630217 2002048139775205240972663)
              ·
                refine ⟨3003072209662807861458995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2002048139775205240972663 3003072209662807861458995)
                ·
                  refine ⟨4504608314494211792188493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3003072209662807861458995 4504608314494211792188493)
                  ·
                    refine ⟨1689228117935329422070685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4504608314494211792188493 1689228117935329422070685)
                    ·
                      refine ⟨633460544225748533276507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1689228117935329422070685 633460544225748533276507)
                      ·
                        rfl

theorem cell23_1233660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_1233660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233660 prefixEnd_1233660 := by exact prefixLift 1233660
  have htrace : WordTrace (prefixWord ++ tailWord_1233660) baseStart_1233660 baseEnd_1233660 := by
    simpa [prefixWord, tailWord_1233660, baseEnd_1233660] using wordTrace_append hprefix tailTrace_1233660
  have hstable : (prefixWord ++ tailWord_1233660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233660).length < 2 ^ (prefixWord ++ tailWord_1233660).sum := by decide
  have hdescent : baseEnd_1233660 < baseStart_1233660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233676 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 3, 8]
def baseStart_1233676 : Nat := 118140960795 + 1233676 * 2 ^ 59
def prefixEnd_1233676 : Nat := 4983230072969 + 3 ^ 40 * 1233676 * 2
def baseEnd_1233676 : Nat := 211156253305406823558811

theorem tailTrace_1233676 : CollatzResearch.WordTrace tailWord_1233676 prefixEnd_1233676 211156253305406823558811 := by
  unfold tailWord_1233676
  simp only [CollatzResearch.WordTrace]
  refine ⟨22497930139305010965808441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29997240185740014621077921 22497930139305010965808441)
  ·
    refine ⟨16873447604478758224356331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22497930139305010965808441 16873447604478758224356331)
    ·
      refine ⟨25310171406718137336534497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16873447604478758224356331 25310171406718137336534497)
      ·
        refine ⟨18982628555038603002400873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25310171406718137336534497 18982628555038603002400873)
        ·
          refine ⟨14236971416278952251800655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18982628555038603002400873 14236971416278952251800655)
          ·
            refine ⟨21355457124418428377700983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14236971416278952251800655 21355457124418428377700983)
            ·
              refine ⟨32033185686627642566551475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21355457124418428377700983 32033185686627642566551475)
              ·
                refine ⟨48049778529941463849827213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32033185686627642566551475 48049778529941463849827213)
                ·
                  refine ⟨18018666948728048943685205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48049778529941463849827213 18018666948728048943685205)
                  ·
                    refine ⟨211156253305406823558811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18018666948728048943685205 211156253305406823558811)
                    ·
                      rfl

theorem cell23_1233676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_1233676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233676 prefixEnd_1233676 := by exact prefixLift 1233676
  have htrace : WordTrace (prefixWord ++ tailWord_1233676) baseStart_1233676 baseEnd_1233676 := by
    simpa [prefixWord, tailWord_1233676, baseEnd_1233676] using wordTrace_append hprefix tailTrace_1233676
  have hstable : (prefixWord ++ tailWord_1233676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233676).length < 2 ^ (prefixWord ++ tailWord_1233676).sum := by decide
  have hdescent : baseEnd_1233676 < baseStart_1233676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233710 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 2, 6]
def baseStart_1233710 : Nat := 118140960795 + 1233710 * 2 ^ 59
def prefixEnd_1233710 : Nat := 4983230072969 + 3 ^ 40 * 1233710 * 2
def baseEnd_1233710 : Nat := 211162072752824445883759

theorem tailTrace_1233710 : CollatzResearch.WordTrace tailWord_1233710 prefixEnd_1233710 211162072752824445883759 := by
  unfold tailWord_1233710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5624637545060855717294323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29998066906991230492236389 5624637545060855717294323)
  ·
    refine ⟨8436956317591283575941485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5624637545060855717294323 8436956317591283575941485)
    ·
      refine ⟨3163858619096731340978057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8436956317591283575941485 3163858619096731340978057)
      ·
        refine ⟨2372893964322548505733543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3163858619096731340978057 2372893964322548505733543)
        ·
          refine ⟨3559340946483822758600315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2372893964322548505733543 3559340946483822758600315)
          ·
            refine ⟨5339011419725734137900473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3559340946483822758600315 5339011419725734137900473)
            ·
              refine ⟨4004258564794300603425355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5339011419725734137900473 4004258564794300603425355)
              ·
                refine ⟨6006387847191450905138033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4004258564794300603425355 6006387847191450905138033)
                ·
                  refine ⟨4504790885393588178853525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6006387847191450905138033 4504790885393588178853525)
                  ·
                    refine ⟨211162072752824445883759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4504790885393588178853525 211162072752824445883759)
                    ·
                      rfl

theorem cell23_1233710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_1233710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233710 prefixEnd_1233710 := by exact prefixLift 1233710
  have htrace : WordTrace (prefixWord ++ tailWord_1233710) baseStart_1233710 baseEnd_1233710 := by
    simpa [prefixWord, tailWord_1233710, baseEnd_1233710] using wordTrace_append hprefix tailTrace_1233710
  have hstable : (prefixWord ++ tailWord_1233710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233710).length < 2 ^ (prefixWord ++ tailWord_1233710).sum := by decide
  have hdescent : baseEnd_1233710 < baseStart_1233710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233713 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 2, 2, 4]
def baseStart_1233713 : Nat := 118140960795 + 1233713 * 2 ^ 59
def prefixEnd_1233713 : Nat := 4983230072969 + 3 ^ 40 * 1233713 * 2
def baseEnd_1233713 : Nat := 633487758700436825913763

theorem tailTrace_1233713 : CollatzResearch.WordTrace tailWord_1233713 prefixEnd_1233713 633487758700436825913763 := by
  unfold tailWord_1233713
  simp only [CollatzResearch.WordTrace]
  refine ⟨44997209779475977250713793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29998139852983984833809195 44997209779475977250713793)
  ·
    refine ⟨33747907334606982938035345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44997209779475977250713793 33747907334606982938035345)
    ·
      refine ⟨25310930500955237203526509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33747907334606982938035345 25310930500955237203526509)
      ·
        refine ⟨9491598937858213951322441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25310930500955237203526509 9491598937858213951322441)
        ·
          refine ⟨7118699203393660463491831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9491598937858213951322441 7118699203393660463491831)
          ·
            refine ⟨10678048805090490695237747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7118699203393660463491831 10678048805090490695237747)
            ·
              refine ⟨16017073207635736042856621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10678048805090490695237747 16017073207635736042856621)
              ·
                refine ⟨6006402452863401016071233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16017073207635736042856621 6006402452863401016071233)
                ·
                  refine ⟨4504801839647550762053425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6006402452863401016071233 4504801839647550762053425)
                  ·
                    refine ⟨3378601379735663071540069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4504801839647550762053425 3378601379735663071540069)
                    ·
                      refine ⟨633487758700436825913763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3378601379735663071540069 633487758700436825913763)
                      ·
                        rfl

theorem cell23_1233713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_1233713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233713 prefixEnd_1233713 := by exact prefixLift 1233713
  have htrace : WordTrace (prefixWord ++ tailWord_1233713) baseStart_1233713 baseEnd_1233713 := by
    simpa [prefixWord, tailWord_1233713, baseEnd_1233713] using wordTrace_append hprefix tailTrace_1233713
  have hstable : (prefixWord ++ tailWord_1233713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233713).length < 2 ^ (prefixWord ++ tailWord_1233713).sum := by decide
  have hdescent : baseEnd_1233713 < baseStart_1233713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233717 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 1, 4, 2]
def baseStart_1233717 : Nat := 118140960795 + 1233717 * 2 ^ 59
def prefixEnd_1233717 : Nat := 4983230072969 + 3 ^ 40 * 1233717 * 2
def baseEnd_1233717 : Nat := 633489812623054810263745

theorem tailTrace_1233717 : CollatzResearch.WordTrace tailWord_1233717 prefixEnd_1233717 633489812623054810263745 := by
  unfold tailWord_1233717
  simp only [CollatzResearch.WordTrace]
  refine ⟨44997355671461485933859405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29998237114307657289239603 44997355671461485933859405)
  ·
    refine ⟨16874008376798057225197277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44997355671461485933859405 16874008376798057225197277)
    ·
      refine ⟨6327753141299271459448979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16874008376798057225197277 6327753141299271459448979)
      ·
        refine ⟨9491629711948907189173469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6327753141299271459448979 9491629711948907189173469)
        ·
          refine ⟨3559361141980840195940051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9491629711948907189173469 3559361141980840195940051)
          ·
            refine ⟨5339041712971260293910077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3559361141980840195940051 5339041712971260293910077)
            ·
              refine ⟨2002140642364222610216279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5339041712971260293910077 2002140642364222610216279)
              ·
                refine ⟨3003210963546333915324419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2002140642364222610216279 3003210963546333915324419)
                ·
                  refine ⟨4504816445319500872986629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3003210963546333915324419 4504816445319500872986629)
                  ·
                    refine ⟨844653083497406413684993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4504816445319500872986629 844653083497406413684993)
                    ·
                      refine ⟨633489812623054810263745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 844653083497406413684993 633489812623054810263745)
                      ·
                        rfl

theorem cell23_1233717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_1233717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233717 prefixEnd_1233717 := by exact prefixLift 1233717
  have htrace : WordTrace (prefixWord ++ tailWord_1233717) baseStart_1233717 baseEnd_1233717 := by
    simpa [prefixWord, tailWord_1233717, baseEnd_1233717] using wordTrace_append hprefix tailTrace_1233717
  have hstable : (prefixWord ++ tailWord_1233717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233717).length < 2 ^ (prefixWord ++ tailWord_1233717).sum := by decide
  have hdescent : baseEnd_1233717 < baseStart_1233717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233733 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 4, 3, 3]
def baseStart_1233733 : Nat := 118140960795 + 1233733 * 2 ^ 59
def prefixEnd_1233733 : Nat := 4983230072969 + 3 ^ 40 * 1233733 * 2
def baseEnd_1233733 : Nat := 633498028313526747663671

theorem tailTrace_1233733 : CollatzResearch.WordTrace tailWord_1233733 prefixEnd_1233733 633498028313526747663671 := by
  unfold tailWord_1233733
  simp only [CollatzResearch.WordTrace]
  refine ⟨44997939239403520666441853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29998626159602347110961235 44997939239403520666441853)
  ·
    refine ⟨16874227214776320249915695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44997939239403520666441853 16874227214776320249915695)
    ·
      refine ⟨25311340822164480374873543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16874227214776320249915695 25311340822164480374873543)
      ·
        refine ⟨37967011233246720562310315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25311340822164480374873543 37967011233246720562310315)
        ·
          refine ⟨56950516849870080843465473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37967011233246720562310315 56950516849870080843465473)
          ·
            refine ⟨42712887637402560632599105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56950516849870080843465473 42712887637402560632599105)
            ·
              refine ⟨32034665728051920474449329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42712887637402560632599105 32034665728051920474449329)
              ·
                refine ⟨24025999296038940355836997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32034665728051920474449329 24025999296038940355836997)
                ·
                  refine ⟨4504874868007301316719437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24025999296038940355836997 4504874868007301316719437)
                  ·
                    refine ⟨1689328075502737993769789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4504874868007301316719437 1689328075502737993769789)
                    ·
                      refine ⟨633498028313526747663671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1689328075502737993769789 633498028313526747663671)
                      ·
                        rfl

theorem cell23_1233733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_1233733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233733 prefixEnd_1233733 := by exact prefixLift 1233733
  have htrace : WordTrace (prefixWord ++ tailWord_1233733) baseStart_1233733 baseEnd_1233733 := by
    simpa [prefixWord, tailWord_1233733, baseEnd_1233733] using wordTrace_append hprefix tailTrace_1233733
  have hstable : (prefixWord ++ tailWord_1233733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233733).length < 2 ^ (prefixWord ++ tailWord_1233733).sum := by decide
  have hdescent : baseEnd_1233733 < baseStart_1233733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233753 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 4, 5]
def baseStart_1233753 : Nat := 118140960795 + 1233753 * 2 ^ 59
def prefixEnd_1233753 : Nat := 4983230072969 + 3 ^ 40 * 1233753 * 2
def baseEnd_1233753 : Nat := 211169432642205556471193

theorem tailTrace_1233753 : CollatzResearch.WordTrace tailWord_1233753 prefixEnd_1233753 211169432642205556471193 := by
  unfold tailWord_1233753
  simp only [CollatzResearch.WordTrace]
  refine ⟨44998668699331064082169913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29999112466220709388113275 44998668699331064082169913)
  ·
    refine ⟨33749001524498298061627435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44998668699331064082169913 33749001524498298061627435)
    ·
      refine ⟨50623502286747447092441153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33749001524498298061627435 50623502286747447092441153)
      ·
        refine ⟨37967626715060585319330865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50623502286747447092441153 37967626715060585319330865)
        ·
          refine ⟨28475720036295438989498149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37967626715060585319330865 28475720036295438989498149)
          ·
            refine ⟨5339197506805394810530903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28475720036295438989498149 5339197506805394810530903)
            ·
              refine ⟨8008796260208092215796355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5339197506805394810530903 8008796260208092215796355)
              ·
                refine ⟨12013194390312138323694533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8008796260208092215796355 12013194390312138323694533)
                ·
                  refine ⟨2252473948183525935692725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12013194390312138323694533 2252473948183525935692725)
                  ·
                    refine ⟨211169432642205556471193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2252473948183525935692725 211169432642205556471193)
                    ·
                      rfl

theorem cell23_1233753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 5].length) (baseStart_1233753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233753 prefixEnd_1233753 := by exact prefixLift 1233753
  have htrace : WordTrace (prefixWord ++ tailWord_1233753) baseStart_1233753 baseEnd_1233753 := by
    simpa [prefixWord, tailWord_1233753, baseEnd_1233753] using wordTrace_append hprefix tailTrace_1233753
  have hstable : (prefixWord ++ tailWord_1233753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233753).length < 2 ^ (prefixWord ++ tailWord_1233753).sum := by decide
  have hdescent : baseEnd_1233753 < baseStart_1233753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233760 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 2, 5, 2]
def baseStart_1233760 : Nat := 118140960795 + 1233760 * 2 ^ 59
def prefixEnd_1233760 : Nat := 4983230072969 + 3 ^ 40 * 1233760 * 2
def baseEnd_1233760 : Nat := 633511892291198142026047

theorem tailTrace_1233760 : CollatzResearch.WordTrace tailWord_1233760 prefixEnd_1233760 633511892291198142026047 := by
  unfold tailWord_1233760
  simp only [CollatzResearch.WordTrace]
  refine ⟨22499462005152852138837367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29999282673537136185116489 22499462005152852138837367)
  ·
    refine ⟨33749193007729278208256051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22499462005152852138837367 33749193007729278208256051)
    ·
      refine ⟨50623789511593917312384077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33749193007729278208256051 50623789511593917312384077)
      ·
        refine ⟨18983921066847718992144029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50623789511593917312384077 18983921066847718992144029)
        ·
          refine ⟨7118970400067894622054011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18983921066847718992144029 7118970400067894622054011)
          ·
            refine ⟨10678455600101841933081017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7118970400067894622054011 10678455600101841933081017)
            ·
              refine ⟨8008841700076381449810763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10678455600101841933081017 8008841700076381449810763)
              ·
                refine ⟨12013262550114572174716145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8008841700076381449810763 12013262550114572174716145)
                ·
                  refine ⟨9009946912585929131037109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12013262550114572174716145 9009946912585929131037109)
                  ·
                    refine ⟨844682523054930856034729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9009946912585929131037109 844682523054930856034729)
                    ·
                      refine ⟨633511892291198142026047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 844682523054930856034729 633511892291198142026047)
                      ·
                        rfl

theorem cell23_1233760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_1233760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233760 prefixEnd_1233760 := by exact prefixLift 1233760
  have htrace : WordTrace (prefixWord ++ tailWord_1233760) baseStart_1233760 baseEnd_1233760 := by
    simpa [prefixWord, tailWord_1233760, baseEnd_1233760] using wordTrace_append hprefix tailTrace_1233760
  have hstable : (prefixWord ++ tailWord_1233760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233760).length < 2 ^ (prefixWord ++ tailWord_1233760).sum := by decide
  have hdescent : baseEnd_1233760 < baseStart_1233760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233763 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 7]
def baseStart_1233763 : Nat := 118140960795 + 1233763 * 2 ^ 59
def prefixEnd_1233763 : Nat := 4983230072969 + 3 ^ 40 * 1233763 * 2
def baseEnd_1233763 : Nat := 633513432733161630288533

theorem tailTrace_1233763 : CollatzResearch.WordTrace tailWord_1233763 prefixEnd_1233763 633513432733161630288533 := by
  unfold tailWord_1233763
  simp only [CollatzResearch.WordTrace]
  refine ⟨44999033429294835790033943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29999355619529890526689295 44999033429294835790033943)
  ·
    refine ⟨67498550143942253685050915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44999033429294835790033943 67498550143942253685050915)
    ·
      refine ⟨101247825215913380527576373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67498550143942253685050915 101247825215913380527576373)
      ·
        refine ⟨9491983613991879424460285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101247825215913380527576373 9491983613991879424460285)
        ·
          refine ⟨3559493855246954784172607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9491983613991879424460285 3559493855246954784172607)
          ·
            refine ⟨5339240782870432176258911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3559493855246954784172607 5339240782870432176258911)
            ·
              refine ⟨8008861174305648264388367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5339240782870432176258911 8008861174305648264388367)
              ·
                refine ⟨12013291761458472396582551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8008861174305648264388367 12013291761458472396582551)
                ·
                  refine ⟨18019937642187708594873827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12013291761458472396582551 18019937642187708594873827)
                  ·
                    refine ⟨27029906463281562892310741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18019937642187708594873827 27029906463281562892310741)
                    ·
                      refine ⟨633513432733161630288533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27029906463281562892310741 633513432733161630288533)
                      ·
                        rfl

theorem cell23_1233763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_1233763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233763 prefixEnd_1233763 := by exact prefixLift 1233763
  have htrace : WordTrace (prefixWord ++ tailWord_1233763) baseStart_1233763 baseEnd_1233763 := by
    simpa [prefixWord, tailWord_1233763, baseEnd_1233763] using wordTrace_append hprefix tailTrace_1233763
  have hstable : (prefixWord ++ tailWord_1233763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233763).length < 2 ^ (prefixWord ++ tailWord_1233763).sum := by decide
  have hdescent : baseEnd_1233763 < baseStart_1233763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233814 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1233814 : Nat := 118140960795 + 1233814 * 2 ^ 59
def prefixEnd_1233814 : Nat := 4983230072969 + 3 ^ 40 * 1233814 * 2
def baseEnd_1233814 : Nat := 633539620246540930750799

theorem tailTrace_1233814 : CollatzResearch.WordTrace tailWord_1233814 prefixEnd_1233814 633539620246540930750799 := by
  unfold tailWord_1233814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2812555847006879468758781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30000595701406714333426997 2812555847006879468758781)
  ·
    refine ⟨1054708442627579800784543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2812555847006879468758781 1054708442627579800784543)
    ·
      refine ⟨1582062663941369701176815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1054708442627579800784543 1582062663941369701176815)
      ·
        refine ⟨2373093995912054551765223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582062663941369701176815 2373093995912054551765223)
        ·
          refine ⟨3559640993868081827647835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373093995912054551765223 3559640993868081827647835)
          ·
            refine ⟨5339461490802122741471753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3559640993868081827647835 5339461490802122741471753)
            ·
              refine ⟨4004596118101592056103815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5339461490802122741471753 4004596118101592056103815)
              ·
                refine ⟨6006894177152388084155723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4004596118101592056103815 6006894177152388084155723)
                ·
                  refine ⟨9010341265728582126233585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6006894177152388084155723 9010341265728582126233585)
                  ·
                    refine ⟨6757755949296436594675189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9010341265728582126233585 6757755949296436594675189)
                    ·
                      refine ⟨633539620246540930750799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6757755949296436594675189 633539620246540930750799)
                      ·
                        rfl

theorem cell23_1233814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1233814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233814 prefixEnd_1233814 := by exact prefixLift 1233814
  have htrace : WordTrace (prefixWord ++ tailWord_1233814) baseStart_1233814 baseEnd_1233814 := by
    simpa [prefixWord, tailWord_1233814, baseEnd_1233814] using wordTrace_append hprefix tailTrace_1233814
  have hstable : (prefixWord ++ tailWord_1233814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233814).length < 2 ^ (prefixWord ++ tailWord_1233814).sum := by decide
  have hdescent : baseEnd_1233814 < baseStart_1233814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233844 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1233844 : Nat := 118140960795 + 1233844 * 2 ^ 59
def prefixEnd_1233844 : Nat := 4983230072969 + 3 ^ 40 * 1233844 * 2
def baseEnd_1233844 : Nat := 633555024666175813375661

theorem tailTrace_1233844 : CollatzResearch.WordTrace tailWord_1233844 prefixEnd_1233844 633555024666175813375661 := by
  unfold tailWord_1233844
  simp only [CollatzResearch.WordTrace]
  refine ⟨22500993871000693311866293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30001325161334257749155057 22500993871000693311866293)
  ·
    refine ⟨2109468175406314997987465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22500993871000693311866293 2109468175406314997987465)
    ·
      refine ⟨1582101131554736248490599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2109468175406314997987465 1582101131554736248490599)
      ·
        refine ⟨2373151697332104372735899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582101131554736248490599 2373151697332104372735899)
        ·
          refine ⟨3559727545998156559103849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373151697332104372735899 3559727545998156559103849)
          ·
            refine ⟨2669795659498617419327887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3559727545998156559103849 2669795659498617419327887)
            ·
              refine ⟨4004693489247926128991831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2669795659498617419327887 4004693489247926128991831)
              ·
                refine ⟨6007040233871889193487747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4004693489247926128991831 6007040233871889193487747)
                ·
                  refine ⟨9010560350807833790231621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6007040233871889193487747 9010560350807833790231621)
                  ·
                    refine ⟨1689480065776468835668429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9010560350807833790231621 1689480065776468835668429)
                    ·
                      refine ⟨633555024666175813375661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1689480065776468835668429 633555024666175813375661)
                      ·
                        rfl

theorem cell23_1233844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1233844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233844 prefixEnd_1233844 := by exact prefixLift 1233844
  have htrace : WordTrace (prefixWord ++ tailWord_1233844) baseStart_1233844 baseEnd_1233844 := by
    simpa [prefixWord, tailWord_1233844, baseEnd_1233844] using wordTrace_append hprefix tailTrace_1233844
  have hstable : (prefixWord ++ tailWord_1233844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233844).length < 2 ^ (prefixWord ++ tailWord_1233844).sum := by decide
  have hdescent : baseEnd_1233844 < baseStart_1233844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233864 : List Nat := [2, 1, 3, 1, 6, 1, 1, 2, 6]
def baseStart_1233864 : Nat := 118140960795 + 1233864 * 2 ^ 59
def prefixEnd_1233864 : Nat := 4983230072969 + 3 ^ 40 * 1233864 * 2
def baseEnd_1233864 : Nat := 70396143808807303902841

theorem tailTrace_1233864 : CollatzResearch.WordTrace tailWord_1233864 prefixEnd_1233864 70396143808807303902841 := by
  unfold tailWord_1233864
  simp only [CollatzResearch.WordTrace]
  refine ⟨22501358600964465019730323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30001811467952620026307097 22501358600964465019730323)
  ·
    refine ⟨33752037901446697529595485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22501358600964465019730323 33752037901446697529595485)
    ·
      refine ⟨12657014213042511573598307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33752037901446697529595485 12657014213042511573598307)
      ·
        refine ⟨18985521319563767360397461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12657014213042511573598307 18985521319563767360397461)
        ·
          refine ⟨889946311854551595018631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18985521319563767360397461 889946311854551595018631)
          ·
            refine ⟨1334919467781827392527947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889946311854551595018631 1334919467781827392527947)
            ·
              refine ⟨2002379201672741088791921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1334919467781827392527947 2002379201672741088791921)
              ·
                refine ⟨1501784401254555816593941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2002379201672741088791921 1501784401254555816593941)
                ·
                  refine ⟨70396143808807303902841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1501784401254555816593941 70396143808807303902841)
                  ·
                    rfl

theorem cell23_1233864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 6].length) (baseStart_1233864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233864 prefixEnd_1233864 := by exact prefixLift 1233864
  have htrace : WordTrace (prefixWord ++ tailWord_1233864) baseStart_1233864 baseEnd_1233864 := by
    simpa [prefixWord, tailWord_1233864, baseEnd_1233864] using wordTrace_append hprefix tailTrace_1233864
  have hstable : (prefixWord ++ tailWord_1233864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233864).length < 2 ^ (prefixWord ++ tailWord_1233864).sum := by decide
  have hdescent : baseEnd_1233864 < baseStart_1233864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233874 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_1233874 : Nat := 118140960795 + 1233874 * 2 ^ 59
def prefixEnd_1233874 : Nat := 4983230072969 + 3 ^ 40 * 1233874 * 2
def baseEnd_1233874 : Nat := 633570429085810696000523

theorem tailTrace_1233874 : CollatzResearch.WordTrace tailWord_1233874 prefixEnd_1233874 633570429085810696000523 := by
  unfold tailWord_1233874
  simp only [CollatzResearch.WordTrace]
  refine ⟨11250770482973175436831169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30002054621261801164883117 11250770482973175436831169)
  ·
    refine ⟨8438077862229881577623377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11250770482973175436831169 8438077862229881577623377)
    ·
      refine ⟨6328558396672411183217533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8438077862229881577623377 6328558396672411183217533)
      ·
        refine ⟨2373209398752154193706575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6328558396672411183217533 2373209398752154193706575)
        ·
          refine ⟨3559814098128231290559863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373209398752154193706575 3559814098128231290559863)
          ·
            refine ⟨5339721147192346935839795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3559814098128231290559863 5339721147192346935839795)
            ·
              refine ⟨8009581720788520403759693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5339721147192346935839795 8009581720788520403759693)
              ·
                refine ⟨3003593145295695151409885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8009581720788520403759693 3003593145295695151409885)
                ·
                  refine ⟨1126347429485885681778707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3003593145295695151409885 1126347429485885681778707)
                  ·
                    refine ⟨1689521144228828522668061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1126347429485885681778707 1689521144228828522668061)
                    ·
                      refine ⟨633570429085810696000523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1689521144228828522668061 633570429085810696000523)
                      ·
                        rfl

theorem cell23_1233874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_1233874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233874 prefixEnd_1233874 := by exact prefixLift 1233874
  have htrace : WordTrace (prefixWord ++ tailWord_1233874) baseStart_1233874 baseEnd_1233874 := by
    simpa [prefixWord, tailWord_1233874, baseEnd_1233874] using wordTrace_append hprefix tailTrace_1233874
  have hstable : (prefixWord ++ tailWord_1233874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233874).length < 2 ^ (prefixWord ++ tailWord_1233874).sum := by decide
  have hdescent : baseEnd_1233874 < baseStart_1233874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233931 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 3, 2, 2]
def baseStart_1233931 : Nat := 118140960795 + 1233931 * 2 ^ 59
def prefixEnd_1233931 : Nat := 4983230072969 + 3 ^ 40 * 1233931 * 2
def baseEnd_1233931 : Nat := 633599697483116972987761

theorem tailTrace_1233931 : CollatzResearch.WordTrace tailWord_1233931 prefixEnd_1233931 633599697483116972987761 := by
  unfold tailWord_1233931
  simp only [CollatzResearch.WordTrace]
  refine ⟨45005160892686200482149647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30003440595124133654766431 45005160892686200482149647)
  ·
    refine ⟨67507741339029300723224471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45005160892686200482149647 67507741339029300723224471)
    ·
      refine ⟨101261612008543951084836707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67507741339029300723224471 101261612008543951084836707)
      ·
        refine ⟨151892418012815926627255061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101261612008543951084836707 151892418012815926627255061)
        ·
          refine ⟨7119957094350746560652581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 151892418012815926627255061 7119957094350746560652581)
          ·
            refine ⟨1334991955190764980122359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7119957094350746560652581 1334991955190764980122359)
            ·
              refine ⟨2002487932786147470183539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1334991955190764980122359 2002487932786147470183539)
              ·
                refine ⟨3003731899179221205275309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2002487932786147470183539 3003731899179221205275309)
                ·
                  refine ⟨1126399462192207951978241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3003731899179221205275309 1126399462192207951978241)
                  ·
                    refine ⟨844799596644155963983681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1126399462192207951978241 844799596644155963983681)
                    ·
                      refine ⟨633599697483116972987761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 844799596644155963983681 633599697483116972987761)
                      ·
                        rfl

theorem cell23_1233931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 2, 2].length) (baseStart_1233931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233931 prefixEnd_1233931 := by exact prefixLift 1233931
  have htrace : WordTrace (prefixWord ++ tailWord_1233931) baseStart_1233931 baseEnd_1233931 := by
    simpa [prefixWord, tailWord_1233931, baseEnd_1233931] using wordTrace_append hprefix tailTrace_1233931
  have hstable : (prefixWord ++ tailWord_1233931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233931).length < 2 ^ (prefixWord ++ tailWord_1233931).sum := by decide
  have hdescent : baseEnd_1233931 < baseStart_1233931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233941 : List Nat := [1, 3, 2, 1, 4, 3, 2, 1, 2, 4]
def baseStart_1233941 : Nat := 118140960795 + 1233941 * 2 ^ 59
def prefixEnd_1233941 : Nat := 4983230072969 + 3 ^ 40 * 1233941 * 2
def baseEnd_1233941 : Nat := 211201610763220644620905

theorem tailTrace_1233941 : CollatzResearch.WordTrace tailWord_1233941 prefixEnd_1233941 211201610763220644620905 := by
  unfold tailWord_1233941
  simp only [CollatzResearch.WordTrace]
  refine ⟨45005525622649972190013677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30003683748433314793342451 45005525622649972190013677)
  ·
    refine ⟨16877072108493739571255129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45005525622649972190013677 16877072108493739571255129)
    ·
      refine ⟨12657804081370304678441347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16877072108493739571255129 12657804081370304678441347)
      ·
        refine ⟨18986706122055457017662021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12657804081370304678441347 18986706122055457017662021)
        ·
          refine ⟨3560007397885398190811629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18986706122055457017662021 3560007397885398190811629)
          ·
            refine ⟨1335002774207024321554361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3560007397885398190811629 1335002774207024321554361)
            ·
              refine ⟨1001252080655268241165771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1335002774207024321554361 1001252080655268241165771)
              ·
                refine ⟨1501878120982902361748657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1001252080655268241165771 1501878120982902361748657)
                ·
                  refine ⟨1126408590737176771311493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1501878120982902361748657 1126408590737176771311493)
                  ·
                    refine ⟨211201610763220644620905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1126408590737176771311493 211201610763220644620905)
                    ·
                      rfl

theorem cell23_1233941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_1233941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233941 prefixEnd_1233941 := by exact prefixLift 1233941
  have htrace : WordTrace (prefixWord ++ tailWord_1233941) baseStart_1233941 baseEnd_1233941 := by
    simpa [prefixWord, tailWord_1233941, baseEnd_1233941] using wordTrace_append hprefix tailTrace_1233941
  have hstable : (prefixWord ++ tailWord_1233941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233941).length < 2 ^ (prefixWord ++ tailWord_1233941).sum := by decide
  have hdescent : baseEnd_1233941 < baseStart_1233941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233981 : List Nat := [1, 4, 1, 3, 1, 3, 2, 2, 2, 1, 3]
def baseStart_1233981 : Nat := 118140960795 + 1233981 * 2 ^ 59
def prefixEnd_1233981 : Nat := 4983230072969 + 3 ^ 40 * 1233981 * 2
def baseEnd_1233981 : Nat := 633625371515841777362531

theorem tailTrace_1233981 : CollatzResearch.WordTrace tailWord_1233981 prefixEnd_1233981 633625371515841777362531 := by
  unfold tailWord_1233981
  simp only [CollatzResearch.WordTrace]
  refine ⟨45006984542505059021469797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30004656361670039347646531 45006984542505059021469797)
  ·
    refine ⟨8438809601719698566525587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45006984542505059021469797 8438809601719698566525587)
    ·
      refine ⟨12658214402579547849788381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8438809601719698566525587 12658214402579547849788381)
      ·
        refine ⟨4746830400967330443670643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12658214402579547849788381 4746830400967330443670643)
        ·
          refine ⟨7120245601450995665505965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4746830400967330443670643 7120245601450995665505965)
          ·
            refine ⟨2670092100544123374564737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7120245601450995665505965 2670092100544123374564737)
            ·
              refine ⟨2002569075408092530923553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2670092100544123374564737 2002569075408092530923553)
              ·
                refine ⟨1501926806556069398192665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2002569075408092530923553 1501926806556069398192665)
                ·
                  refine ⟨1126445104917052048644499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1501926806556069398192665 1126445104917052048644499)
                  ·
                    refine ⟨1689667657375578072966749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1126445104917052048644499 1689667657375578072966749)
                    ·
                      refine ⟨633625371515841777362531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1689667657375578072966749 633625371515841777362531)
                      ·
                        rfl

theorem cell23_1233981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_1233981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233981 prefixEnd_1233981 := by exact prefixLift 1233981
  have htrace : WordTrace (prefixWord ++ tailWord_1233981) baseStart_1233981 baseEnd_1233981 := by
    simpa [prefixWord, tailWord_1233981, baseEnd_1233981] using wordTrace_append hprefix tailTrace_1233981
  have hstable : (prefixWord ++ tailWord_1233981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233981).length < 2 ^ (prefixWord ++ tailWord_1233981).sum := by decide
  have hdescent : baseEnd_1233981 < baseStart_1233981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233982 : List Nat := [4, 2, 1, 3, 1, 3, 2, 2, 1, 2, 2]
def baseStart_1233982 : Nat := 118140960795 + 1233982 * 2 ^ 59
def prefixEnd_1233982 : Nat := 4983230072969 + 3 ^ 40 * 1233982 * 2
def baseEnd_1233982 : Nat := 633625884996496273450027

theorem tailTrace_1233982 : CollatzResearch.WordTrace tailWord_1233982 prefixEnd_1233982 633625884996496273450027 := by
  unfold tailWord_1233982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5625877626937679524032025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30004680677000957461504133 5625877626937679524032025)
  ·
    refine ⟨4219408220203259643024019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5625877626937679524032025 4219408220203259643024019)
    ·
      refine ⟨6329112330304889464536029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4219408220203259643024019 6329112330304889464536029)
      ·
        refine ⟨2373417123864333549201011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6329112330304889464536029 2373417123864333549201011)
        ·
          refine ⟨3560125685796500323801517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373417123864333549201011 3560125685796500323801517)
          ·
            refine ⟨1335047132173687621425569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3560125685796500323801517 1335047132173687621425569)
            ·
              refine ⟨1001285349130265716069177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1335047132173687621425569 1001285349130265716069177)
              ·
                refine ⟨750964011847699287051883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1001285349130265716069177 750964011847699287051883)
                ·
                  refine ⟨1126446017771548930577825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750964011847699287051883 1126446017771548930577825)
                  ·
                    refine ⟨844834513328661697933369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1126446017771548930577825 844834513328661697933369)
                    ·
                      refine ⟨633625884996496273450027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 844834513328661697933369 633625884996496273450027)
                      ·
                        rfl

theorem cell23_1233982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_1233982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233982 prefixEnd_1233982 := by exact prefixLift 1233982
  have htrace : WordTrace (prefixWord ++ tailWord_1233982) baseStart_1233982 baseEnd_1233982 := by
    simpa [prefixWord, tailWord_1233982, baseEnd_1233982] using wordTrace_append hprefix tailTrace_1233982
  have hstable : (prefixWord ++ tailWord_1233982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233982).length < 2 ^ (prefixWord ++ tailWord_1233982).sum := by decide
  have hdescent : baseEnd_1233982 < baseStart_1233982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233987 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 3, 4, 2]
def baseStart_1233987 : Nat := 118140960795 + 1233987 * 2 ^ 59
def prefixEnd_1233987 : Nat := 4983230072969 + 3 ^ 40 * 1233987 * 2
def baseEnd_1233987 : Nat := 633628452399768753887503

theorem tailTrace_1233987 : CollatzResearch.WordTrace tailWord_1233987 prefixEnd_1233987 633628452399768753887503 := by
  unfold tailWord_1233987
  simp only [CollatzResearch.WordTrace]
  refine ⟨45007203380483322046188215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30004802253655548030792143 45007203380483322046188215)
  ·
    refine ⟨67510805070724983069282323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45007203380483322046188215 67510805070724983069282323)
    ·
      refine ⟨101266207606087474603923485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67510805070724983069282323 101266207606087474603923485)
      ·
        refine ⟨37974827852282802976471307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101266207606087474603923485 37974827852282802976471307)
        ·
          refine ⟨56962241778424204464706961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37974827852282802976471307 56962241778424204464706961)
          ·
            refine ⟨42721681333818153348530221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56962241778424204464706961 42721681333818153348530221)
            ·
              refine ⟨16020630500181807505698833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42721681333818153348530221 16020630500181807505698833)
              ·
                refine ⟨12015472875136355629274125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16020630500181807505698833 12015472875136355629274125)
                ·
                  refine ⟨4505802328176133360977797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12015472875136355629274125 4505802328176133360977797)
                  ·
                    refine ⟨844837936533025005183337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4505802328176133360977797 844837936533025005183337)
                    ·
                      refine ⟨633628452399768753887503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 844837936533025005183337 633628452399768753887503)
                      ·
                        rfl

theorem cell23_1233987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 4, 2].length) (baseStart_1233987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233987 prefixEnd_1233987 := by exact prefixLift 1233987
  have htrace : WordTrace (prefixWord ++ tailWord_1233987) baseStart_1233987 baseEnd_1233987 := by
    simpa [prefixWord, tailWord_1233987, baseEnd_1233987] using wordTrace_append hprefix tailTrace_1233987
  have hstable : (prefixWord ++ tailWord_1233987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233987).length < 2 ^ (prefixWord ++ tailWord_1233987).sum := by decide
  have hdescent : baseEnd_1233987 < baseStart_1233987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233997 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_1233997 : Nat := 118140960795 + 1233997 * 2 ^ 59
def prefixEnd_1233997 : Nat := 4983230072969 + 3 ^ 40 * 1233997 * 2
def baseEnd_1233997 : Nat := 211211195735437904920819

theorem tailTrace_1233997 : CollatzResearch.WordTrace tailWord_1233997 prefixEnd_1233997 211211195735437904920819 := by
  unfold tailWord_1233997
  simp only [CollatzResearch.WordTrace]
  refine ⟨45007568110447093754052245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30005045406964729169368163 45007568110447093754052245)
  ·
    refine ⟨2109729755177207519721199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45007568110447093754052245 2109729755177207519721199)
    ·
      refine ⟨3164594632765811279581799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2109729755177207519721199 3164594632765811279581799)
      ·
        refine ⟨4746891949148716919372699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3164594632765811279581799 4746891949148716919372699)
        ·
          refine ⟨7120337923723075379059049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4746891949148716919372699 7120337923723075379059049)
          ·
            refine ⟨5340253442792306534294287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7120337923723075379059049 5340253442792306534294287)
            ·
              refine ⟨8010380164188459801441431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5340253442792306534294287 8010380164188459801441431)
              ·
                refine ⟨12015570246282689702162147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8010380164188459801441431 12015570246282689702162147)
                ·
                  refine ⟨18023355369424034553243221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12015570246282689702162147 18023355369424034553243221)
                  ·
                    refine ⟨211211195735437904920819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18023355369424034553243221 211211195735437904920819)
                    ·
                      rfl

theorem cell23_1233997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_1233997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1233997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1233997 prefixEnd_1233997 := by exact prefixLift 1233997
  have htrace : WordTrace (prefixWord ++ tailWord_1233997) baseStart_1233997 baseEnd_1233997 := by
    simpa [prefixWord, tailWord_1233997, baseEnd_1233997] using wordTrace_append hprefix tailTrace_1233997
  have hstable : (prefixWord ++ tailWord_1233997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233997).length < 2 ^ (prefixWord ++ tailWord_1233997).sum := by decide
  have hdescent : baseEnd_1233997 < baseStart_1233997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234004 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 1, 4, 2]
def baseStart_1234004 : Nat := 118140960795 + 1234004 * 2 ^ 59
def prefixEnd_1234004 : Nat := 4983230072969 + 3 ^ 40 * 1234004 * 2
def baseEnd_1234004 : Nat := 633637181570895187374925

theorem tailTrace_1234004 : CollatzResearch.WordTrace tailWord_1234004 prefixEnd_1234004 633637181570895187374925 := by
  unfold tailWord_1234004
  simp only [CollatzResearch.WordTrace]
  refine ⟨22503911710710866974778533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30005215614281155966371377 22503911710710866974778533)
  ·
    refine ⟨4219483445758287557770975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22503911710710866974778533 4219483445758287557770975)
    ·
      refine ⟨6329225168637431336656463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4219483445758287557770975 6329225168637431336656463)
      ·
        refine ⟨9493837752956147004984695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6329225168637431336656463 9493837752956147004984695)
        ·
          refine ⟨14240756629434220507477043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9493837752956147004984695 14240756629434220507477043)
          ·
            refine ⟨21361134944151330761215565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14240756629434220507477043 21361134944151330761215565)
            ·
              refine ⟨8010425604056749035455837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21361134944151330761215565 8010425604056749035455837)
              ·
                refine ⟨3003909601521280888295939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8010425604056749035455837 3003909601521280888295939)
                ·
                  refine ⟨4505864402281921332443909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3003909601521280888295939 4505864402281921332443909)
                  ·
                    refine ⟨844849575427860249833233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4505864402281921332443909 844849575427860249833233)
                    ·
                      refine ⟨633637181570895187374925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 844849575427860249833233 633637181570895187374925)
                      ·
                        rfl

theorem cell23_1234004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_1234004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234004 prefixEnd_1234004 := by exact prefixLift 1234004
  have htrace : WordTrace (prefixWord ++ tailWord_1234004) baseStart_1234004 baseEnd_1234004 := by
    simpa [prefixWord, tailWord_1234004, baseEnd_1234004] using wordTrace_append hprefix tailTrace_1234004
  have hstable : (prefixWord ++ tailWord_1234004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234004).length < 2 ^ (prefixWord ++ tailWord_1234004).sum := by decide
  have hdescent : baseEnd_1234004 < baseStart_1234004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234020 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_1234020 : Nat := 118140960795 + 1234020 * 2 ^ 59
def prefixEnd_1234020 : Nat := 4983230072969 + 3 ^ 40 * 1234020 * 2
def baseEnd_1234020 : Nat := 633645397261367124774851

theorem tailTrace_1234020 : CollatzResearch.WordTrace tailWord_1234020 prefixEnd_1234020 633645397261367124774851 := by
  unfold tailWord_1234020
  simp only [CollatzResearch.WordTrace]
  refine ⟨22504203494681884341069757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30005604659575845788093009 22504203494681884341069757)
  ·
    refine ⟨8439076310505706627901159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22504203494681884341069757 8439076310505706627901159)
    ·
      refine ⟨12658614465758559941851739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8439076310505706627901159 12658614465758559941851739)
      ·
        refine ⟨18987921698637839912777609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12658614465758559941851739 18987921698637839912777609)
        ·
          refine ⟨14240941273978379934583207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18987921698637839912777609 14240941273978379934583207)
          ·
            refine ⟨21361411910967569901874811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14240941273978379934583207 21361411910967569901874811)
            ·
              refine ⟨32042117866451354852812217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21361411910967569901874811 32042117866451354852812217)
              ·
                refine ⟨24031588399838516139609163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32042117866451354852812217 24031588399838516139609163)
                ·
                  refine ⟨36047382599757774209413745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24031588399838516139609163 36047382599757774209413745)
                  ·
                    refine ⟨27035536949818330657060309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36047382599757774209413745 27035536949818330657060309)
                    ·
                      refine ⟨633645397261367124774851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27035536949818330657060309 633645397261367124774851)
                      ·
                        rfl

theorem cell23_1234020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_1234020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234020 prefixEnd_1234020 := by exact prefixLift 1234020
  have htrace : WordTrace (prefixWord ++ tailWord_1234020) baseStart_1234020 baseEnd_1234020 := by
    simpa [prefixWord, tailWord_1234020, baseEnd_1234020] using wordTrace_append hprefix tailTrace_1234020
  have hstable : (prefixWord ++ tailWord_1234020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234020).length < 2 ^ (prefixWord ++ tailWord_1234020).sum := by decide
  have hdescent : baseEnd_1234020 < baseStart_1234020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234077 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_1234077 : Nat := 118140960795 + 1234077 * 2 ^ 59
def prefixEnd_1234077 : Nat := 4983230072969 + 3 ^ 40 * 1234077 * 2
def baseEnd_1234077 : Nat := 633674665658673401762089

theorem tailTrace_1234077 : CollatzResearch.WordTrace tailWord_1234077 prefixEnd_1234077 633674665658673401762089 := by
  unfold tailWord_1234077
  simp only [CollatzResearch.WordTrace]
  refine ⟨45010485950157267416964485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30006990633438178277976323 45010485950157267416964485)
  ·
    refine ⟨8439466115654487640680841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45010485950157267416964485 8439466115654487640680841)
    ·
      refine ⟨6329599586740865730510631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8439466115654487640680841 6329599586740865730510631)
      ·
        refine ⟨9494399380111298595765947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6329599586740865730510631 9494399380111298595765947)
        ·
          refine ⟨14241599070166947893648921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9494399380111298595765947 14241599070166947893648921)
          ·
            refine ⟨10681199302625210920236691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14241599070166947893648921 10681199302625210920236691)
            ·
              refine ⟨16021798953937816380355037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10681199302625210920236691 16021798953937816380355037)
              ·
                refine ⟨6008174607726681142633139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16021798953937816380355037 6008174607726681142633139)
                ·
                  refine ⟨9012261911590021713949709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6008174607726681142633139 9012261911590021713949709)
                  ·
                    refine ⟨3379598216846258142731141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9012261911590021713949709 3379598216846258142731141)
                    ·
                      refine ⟨633674665658673401762089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3379598216846258142731141 633674665658673401762089)
                      ·
                        rfl

theorem cell23_1234077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_1234077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234077 prefixEnd_1234077 := by exact prefixLift 1234077
  have htrace : WordTrace (prefixWord ++ tailWord_1234077) baseStart_1234077 baseEnd_1234077 := by
    simpa [prefixWord, tailWord_1234077, baseEnd_1234077] using wordTrace_append hprefix tailTrace_1234077
  have hstable : (prefixWord ++ tailWord_1234077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234077).length < 2 ^ (prefixWord ++ tailWord_1234077).sum := by decide
  have hdescent : baseEnd_1234077 < baseStart_1234077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234078 : List Nat := [4, 3, 1, 1, 2, 3, 1, 3, 5]
def baseStart_1234078 : Nat := 118140960795 + 1234078 * 2 ^ 59
def prefixEnd_1234078 : Nat := 4983230072969 + 3 ^ 40 * 1234078 * 2
def baseEnd_1234078 : Nat := 70408353237703099761065

theorem tailTrace_1234078 : CollatzResearch.WordTrace tailWord_1234078 prefixEnd_1234078 70408353237703099761065 := by
  unfold tailWord_1234078
  simp only [CollatzResearch.WordTrace]
  refine ⟨5626315302894205573468861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30007014948769096391833925 5626315302894205573468861)
  ·
    refine ⟨2109868238585327090050823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5626315302894205573468861 2109868238585327090050823)
    ·
      refine ⟨3164802357877990635076235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2109868238585327090050823 3164802357877990635076235)
      ·
        refine ⟨4747203536816985952614353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3164802357877990635076235 4747203536816985952614353)
        ·
          refine ⟨3560402652612739464460765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4747203536816985952614353 3560402652612739464460765)
          ·
            refine ⟨1335150994729777299172787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3560402652612739464460765 1335150994729777299172787)
            ·
              refine ⟨2002726492094665948759181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335150994729777299172787 2002726492094665948759181)
              ·
                refine ⟨751022434535499730784693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2002726492094665948759181 751022434535499730784693)
                ·
                  refine ⟨70408353237703099761065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 751022434535499730784693 70408353237703099761065)
                  ·
                    rfl

theorem cell23_1234078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_1234078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234078 prefixEnd_1234078 := by exact prefixLift 1234078
  have htrace : WordTrace (prefixWord ++ tailWord_1234078) baseStart_1234078 baseEnd_1234078 := by
    simpa [prefixWord, tailWord_1234078, baseEnd_1234078] using wordTrace_append hprefix tailTrace_1234078
  have hstable : (prefixWord ++ tailWord_1234078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234078).length < 2 ^ (prefixWord ++ tailWord_1234078).sum := by decide
  have hdescent : baseEnd_1234078 < baseStart_1234078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234151 : List Nat := [1, 1, 5, 3, 2, 1, 2, 2, 6]
def baseStart_1234151 : Nat := 118140960795 + 1234151 * 2 ^ 59
def prefixEnd_1234151 : Nat := 4983230072969 + 3 ^ 40 * 1234151 * 2
def baseEnd_1234151 : Nat := 70412518136345123581861

theorem tailTrace_1234151 : CollatzResearch.WordTrace tailWord_1234151 prefixEnd_1234151 70412518136345123581861 := by
  unfold tailWord_1234151
  simp only [CollatzResearch.WordTrace]
  refine ⟨45013184951889178055158307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30008789967926118703438871 45013184951889178055158307)
  ·
    refine ⟨67519777427833767082737461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45013184951889178055158307 67519777427833767082737461)
    ·
      refine ⟨6329979133859415664006637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67519777427833767082737461 6329979133859415664006637)
      ·
        refine ⟨2373742175197280874002489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6329979133859415664006637 2373742175197280874002489)
        ·
          refine ⟨1780306631397960655501867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2373742175197280874002489 1780306631397960655501867)
          ·
            refine ⟨2670459947096940983252801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1780306631397960655501867 2670459947096940983252801)
            ·
              refine ⟨2002844960322705737439601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2670459947096940983252801 2002844960322705737439601)
              ·
                refine ⟨1502133720242029303079701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2002844960322705737439601 1502133720242029303079701)
                ·
                  refine ⟨70412518136345123581861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1502133720242029303079701 70412518136345123581861)
                  ·
                    rfl

theorem cell23_1234151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 6].length) (baseStart_1234151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234151 prefixEnd_1234151 := by exact prefixLift 1234151
  have htrace : WordTrace (prefixWord ++ tailWord_1234151) baseStart_1234151 baseEnd_1234151 := by
    simpa [prefixWord, tailWord_1234151, baseEnd_1234151] using wordTrace_append hprefix tailTrace_1234151
  have hstable : (prefixWord ++ tailWord_1234151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234151).length < 2 ^ (prefixWord ++ tailWord_1234151).sum := by decide
  have hdescent : baseEnd_1234151 < baseStart_1234151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234188 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 2, 3, 2]
def baseStart_1234188 : Nat := 118140960795 + 1234188 * 2 ^ 59
def prefixEnd_1234188 : Nat := 4983230072969 + 3 ^ 40 * 1234188 * 2
def baseEnd_1234188 : Nat := 633731662011322467474079

theorem tailTrace_1234188 : CollatzResearch.WordTrace tailWord_1234188 prefixEnd_1234188 633731662011322467474079 := by
  unfold tailWord_1234188
  simp only [CollatzResearch.WordTrace]
  refine ⟨22507267226377566687127609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30009689635170088916170145 22507267226377566687127609)
  ·
    refine ⟨16880450419783175015345707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22507267226377566687127609 16880450419783175015345707)
    ·
      refine ⟨25320675629674762523018561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16880450419783175015345707 25320675629674762523018561)
      ·
        refine ⟨18990506722256071892263921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25320675629674762523018561 18990506722256071892263921)
        ·
          refine ⟨14242880041692053919197941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18990506722256071892263921 14242880041692053919197941)
          ·
            refine ⟨1335270003908630054924807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14242880041692053919197941 1335270003908630054924807)
            ·
              refine ⟨2002905005862945082387211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335270003908630054924807 2002905005862945082387211)
              ·
                refine ⟨3004357508794417623580817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2002905005862945082387211 3004357508794417623580817)
                ·
                  refine ⟨2253268131595813217685613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3004357508794417623580817 2253268131595813217685613)
                  ·
                    refine ⟨844975549348429956632105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2253268131595813217685613 844975549348429956632105)
                    ·
                      refine ⟨633731662011322467474079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 844975549348429956632105 633731662011322467474079)
                      ·
                        rfl

theorem cell23_1234188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_1234188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234188 prefixEnd_1234188 := by exact prefixLift 1234188
  have htrace : WordTrace (prefixWord ++ tailWord_1234188) baseStart_1234188 baseEnd_1234188 := by
    simpa [prefixWord, tailWord_1234188, baseEnd_1234188] using wordTrace_append hprefix tailTrace_1234188
  have hstable : (prefixWord ++ tailWord_1234188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234188).length < 2 ^ (prefixWord ++ tailWord_1234188).sum := by decide
  have hdescent : baseEnd_1234188 < baseStart_1234188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234197 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_1234197 : Nat := 118140960795 + 1234197 * 2 ^ 59
def prefixEnd_1234197 : Nat := 4983230072969 + 3 ^ 40 * 1234197 * 2
def baseEnd_1234197 : Nat := 633736283337212932261537

theorem tailTrace_1234197 : CollatzResearch.WordTrace tailWord_1234197 prefixEnd_1234197 633736283337212932261537 := by
  unfold tailWord_1234197
  simp only [CollatzResearch.WordTrace]
  refine ⟨45014862709722527911332845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30009908473148351940888563 45014862709722527911332845)
  ·
    refine ⟨16880573516145947966749817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45014862709722527911332845 16880573516145947966749817)
    ·
      refine ⟨12660430137109460975062363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16880573516145947966749817 12660430137109460975062363)
      ·
        refine ⟨18990645205664191462593545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12660430137109460975062363 18990645205664191462593545)
        ·
          refine ⟨14242983904248143596945159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18990645205664191462593545 14242983904248143596945159)
          ·
            refine ⟨21364475856372215395417739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14242983904248143596945159 21364475856372215395417739)
            ·
              refine ⟨32046713784558323093126609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21364475856372215395417739 32046713784558323093126609)
              ·
                refine ⟨24035035338418742319844957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32046713784558323093126609 24035035338418742319844957)
                ·
                  refine ⟨9013138251907028369941859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24035035338418742319844957 9013138251907028369941859)
                  ·
                    refine ⟨13519707377860542554912789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9013138251907028369941859 13519707377860542554912789)
                    ·
                      refine ⟨633736283337212932261537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13519707377860542554912789 633736283337212932261537)
                      ·
                        rfl

theorem cell23_1234197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_1234197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234197 prefixEnd_1234197 := by exact prefixLift 1234197
  have htrace : WordTrace (prefixWord ++ tailWord_1234197) baseStart_1234197 baseEnd_1234197 := by
    simpa [prefixWord, tailWord_1234197, baseEnd_1234197] using wordTrace_append hprefix tailTrace_1234197
  have hstable : (prefixWord ++ tailWord_1234197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234197).length < 2 ^ (prefixWord ++ tailWord_1234197).sum := by decide
  have hdescent : baseEnd_1234197 < baseStart_1234197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234211 : List Nat := [1, 1, 1, 4, 2, 3, 3, 2, 2, 4]
def baseStart_1234211 : Nat := 118140960795 + 1234211 * 2 ^ 59
def prefixEnd_1234211 : Nat := 4983230072969 + 3 ^ 40 * 1234211 * 2
def baseEnd_1234211 : Nat := 211247824022125292495491

theorem tailTrace_1234211 : CollatzResearch.WordTrace tailWord_1234211 prefixEnd_1234211 211247824022125292495491 := by
  unfold tailWord_1234211
  simp only [CollatzResearch.WordTrace]
  refine ⟨45015373331671808302342487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30010248887781205534894991 45015373331671808302342487)
  ·
    refine ⟨67523059997507712453513731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45015373331671808302342487 67523059997507712453513731)
    ·
      refine ⟨101284589996261568680270597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67523059997507712453513731 101284589996261568680270597)
      ·
        refine ⟨18990860624299044127550737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101284589996261568680270597 18990860624299044127550737)
        ·
          refine ⟨14243145468224283095663053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18990860624299044127550737 14243145468224283095663053)
          ·
            refine ⟨5341179550584106160873645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14243145468224283095663053 5341179550584106160873645)
            ·
              refine ⟨2002942331469039810327617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5341179550584106160873645 2002942331469039810327617)
              ·
                refine ⟨1502206748601779857745713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2002942331469039810327617 1502206748601779857745713)
                ·
                  refine ⟨1126655061451334893309285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1502206748601779857745713 1126655061451334893309285)
                  ·
                    refine ⟨211247824022125292495491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1126655061451334893309285 211247824022125292495491)
                    ·
                      rfl

theorem cell23_1234211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 4].length) (baseStart_1234211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234211 prefixEnd_1234211 := by exact prefixLift 1234211
  have htrace : WordTrace (prefixWord ++ tailWord_1234211) baseStart_1234211 baseEnd_1234211 := by
    simpa [prefixWord, tailWord_1234211, baseEnd_1234211] using wordTrace_append hprefix tailTrace_1234211
  have hstable : (prefixWord ++ tailWord_1234211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234211).length < 2 ^ (prefixWord ++ tailWord_1234211).sum := by decide
  have hdescent : baseEnd_1234211 < baseStart_1234211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234221 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1234221 : Nat := 118140960795 + 1234221 * 2 ^ 59
def prefixEnd_1234221 : Nat := 4983230072969 + 3 ^ 40 * 1234221 * 2
def baseEnd_1234221 : Nat := 633748606872920838361427

theorem tailTrace_1234221 : CollatzResearch.WordTrace tailWord_1234221 prefixEnd_1234221 633748606872920838361427 := by
  unfold tailWord_1234221
  simp only [CollatzResearch.WordTrace]
  refine ⟨45015738061635580010206517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30010492041090386673471011 45015738061635580010206517)
  ·
    refine ⟨4220225443278335625956861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45015738061635580010206517 4220225443278335625956861)
    ·
      refine ⟨1582584541229375859733823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4220225443278335625956861 1582584541229375859733823)
      ·
        refine ⟨2373876811844063789600735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582584541229375859733823 2373876811844063789600735)
        ·
          refine ⟨3560815217766095684401103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373876811844063789600735 3560815217766095684401103)
          ·
            refine ⟨5341222826649143526601655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3560815217766095684401103 5341222826649143526601655)
            ·
              refine ⟨8011834239973715289902483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5341222826649143526601655 8011834239973715289902483)
              ·
                refine ⟨12017751359960572934853725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8011834239973715289902483 12017751359960572934853725)
                ·
                  refine ⟨4506656759985214850570147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12017751359960572934853725 4506656759985214850570147)
                  ·
                    refine ⟨6759985139977822275855221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4506656759985214850570147 6759985139977822275855221)
                    ·
                      refine ⟨633748606872920838361427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6759985139977822275855221 633748606872920838361427)
                      ·
                        rfl

theorem cell23_1234221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1234221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234221 prefixEnd_1234221 := by exact prefixLift 1234221
  have htrace : WordTrace (prefixWord ++ tailWord_1234221) baseStart_1234221 baseEnd_1234221 := by
    simpa [prefixWord, tailWord_1234221, baseEnd_1234221] using wordTrace_append hprefix tailTrace_1234221
  have hstable : (prefixWord ++ tailWord_1234221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234221).length < 2 ^ (prefixWord ++ tailWord_1234221).sum := by decide
  have hdescent : baseEnd_1234221 < baseStart_1234221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234238 : List Nat := [4, 2, 1, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_1234238 : Nat := 118140960795 + 1234238 * 2 ^ 59
def prefixEnd_1234238 : Nat := 4983230072969 + 3 ^ 40 * 1234238 * 2
def baseEnd_1234238 : Nat := 633757336044047271848849

theorem tailTrace_1234238 : CollatzResearch.WordTrace tailWord_1234238 prefixEnd_1234238 633757336044047271848849 := by
  unfold tailWord_1234238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5627044762821748989196921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30010905401715994609050245 5627044762821748989196921)
  ·
    refine ⟨4220283572116311741897691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5627044762821748989196921 4220283572116311741897691)
    ·
      refine ⟨6330425358174467612846537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4220283572116311741897691 6330425358174467612846537)
      ·
        refine ⟨4747819018630850709634903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6330425358174467612846537 4747819018630850709634903)
        ·
          refine ⟨7121728527946276064452355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4747819018630850709634903 7121728527946276064452355)
          ·
            refine ⟨10682592791919414096678533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7121728527946276064452355 10682592791919414096678533)
            ·
              refine ⟨2002986148484890143127225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10682592791919414096678533 2002986148484890143127225)
              ·
                refine ⟨1502239611363667607345419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2002986148484890143127225 1502239611363667607345419)
                ·
                  refine ⟨2253359417045501411018129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502239611363667607345419 2253359417045501411018129)
                  ·
                    refine ⟨1690019562784126058263597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2253359417045501411018129 1690019562784126058263597)
                    ·
                      refine ⟨633757336044047271848849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1690019562784126058263597 633757336044047271848849)
                      ·
                        rfl

theorem cell23_1234238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_1234238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234238 prefixEnd_1234238 := by exact prefixLift 1234238
  have htrace : WordTrace (prefixWord ++ tailWord_1234238) baseStart_1234238 baseEnd_1234238 := by
    simpa [prefixWord, tailWord_1234238, baseEnd_1234238] using wordTrace_append hprefix tailTrace_1234238
  have hstable : (prefixWord ++ tailWord_1234238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234238).length < 2 ^ (prefixWord ++ tailWord_1234238).sum := by decide
  have hdescent : baseEnd_1234238 < baseStart_1234238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234241 : List Nat := [1, 2, 5, 2, 1, 1, 4, 7]
def baseStart_1234241 : Nat := 118140960795 + 1234241 * 2 ^ 59
def prefixEnd_1234241 : Nat := 4983230072969 + 3 ^ 40 * 1234241 * 2
def baseEnd_1234241 : Nat := 23472550980963361485605

theorem tailTrace_1234241 : CollatzResearch.WordTrace tailWord_1234241 prefixEnd_1234241 23472550980963361485605 := by
  unfold tailWord_1234241
  simp only [CollatzResearch.WordTrace]
  refine ⟨45016467521563123425934577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30010978347708748950623051 45016467521563123425934577)
  ·
    refine ⟨33762350641172342569450933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45016467521563123425934577 33762350641172342569450933)
    ·
      refine ⟨3165220372609907115886025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33762350641172342569450933 3165220372609907115886025)
      ·
        refine ⟨2373915279457430336914519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3165220372609907115886025 2373915279457430336914519)
        ·
          refine ⟨3560872919186145505371779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373915279457430336914519 3560872919186145505371779)
          ·
            refine ⟨5341309378779218258057669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3560872919186145505371779 5341309378779218258057669)
            ·
              refine ⟨1001495508521103423385813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5341309378779218258057669 1001495508521103423385813)
              ·
                refine ⟨23472550980963361485605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1001495508521103423385813 23472550980963361485605)
                ·
                  rfl

theorem cell23_1234241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 7].length) (baseStart_1234241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234241 prefixEnd_1234241 := by exact prefixLift 1234241
  have htrace : WordTrace (prefixWord ++ tailWord_1234241) baseStart_1234241 baseEnd_1234241 := by
    simpa [prefixWord, tailWord_1234241, baseEnd_1234241] using wordTrace_append hprefix tailTrace_1234241
  have hstable : (prefixWord ++ tailWord_1234241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234241).length < 2 ^ (prefixWord ++ tailWord_1234241).sum := by decide
  have hdescent : baseEnd_1234241 < baseStart_1234241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234246 : List Nat := [6, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_1234246 : Nat := 118140960795 + 1234246 * 2 ^ 59
def prefixEnd_1234246 : Nat := 4983230072969 + 3 ^ 40 * 1234246 * 2
def baseEnd_1234246 : Nat := 633761443889283240548813

theorem tailTrace_1234246 : CollatzResearch.WordTrace tailWord_1234246 prefixEnd_1234246 633761443889283240548813 := by
  unfold tailWord_1234246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1406770308954531539995831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30011099924363339519911061 1406770308954531539995831)
  ·
    refine ⟨2110155463431797309993747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1406770308954531539995831 2110155463431797309993747)
    ·
      refine ⟨3165233195147695964990621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2110155463431797309993747 3165233195147695964990621)
      ·
        refine ⟨1186962448180385986871483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3165233195147695964990621 1186962448180385986871483)
        ·
          refine ⟨1780443672270578980307225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186962448180385986871483 1780443672270578980307225)
          ·
            refine ⟨1335332754202934235230419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1780443672270578980307225 1335332754202934235230419)
            ·
              refine ⟨2002999131304401352845629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335332754202934235230419 2002999131304401352845629)
              ·
                refine ⟨751124674239150507317111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2002999131304401352845629 751124674239150507317111)
                ·
                  refine ⟨1126687011358725760975667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 751124674239150507317111 1126687011358725760975667)
                  ·
                    refine ⟨1690030517038088641463501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1126687011358725760975667 1690030517038088641463501)
                    ·
                      refine ⟨633761443889283240548813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1690030517038088641463501 633761443889283240548813)
                      ·
                        rfl

theorem cell23_1234246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_1234246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234246 prefixEnd_1234246 := by exact prefixLift 1234246
  have htrace : WordTrace (prefixWord ++ tailWord_1234246) baseStart_1234246 baseEnd_1234246 := by
    simpa [prefixWord, tailWord_1234246, baseEnd_1234246] using wordTrace_append hprefix tailTrace_1234246
  have hstable : (prefixWord ++ tailWord_1234246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234246).length < 2 ^ (prefixWord ++ tailWord_1234246).sum := by decide
  have hdescent : baseEnd_1234246 < baseStart_1234246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234252 : List Nat := [2, 2, 1, 3, 2, 4, 1, 3, 1, 2, 2]
def baseStart_1234252 : Nat := 118140960795 + 1234252 * 2 ^ 59
def prefixEnd_1234252 : Nat := 4983230072969 + 3 ^ 40 * 1234252 * 2
def baseEnd_1234252 : Nat := 633764524773210217073785

theorem tailTrace_1234252 : CollatzResearch.WordTrace tailWord_1234252 prefixEnd_1234252 633764524773210217073785 := by
  unfold tailWord_1234252
  simp only [CollatzResearch.WordTrace]
  refine ⟨22508434362261636152292505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30011245816348848203056673 22508434362261636152292505)
  ·
    refine ⟨16881325771696227114219379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22508434362261636152292505 16881325771696227114219379)
    ·
      refine ⟨25321988657544340671329069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16881325771696227114219379 25321988657544340671329069)
      ·
        refine ⟨9495745746579127751748401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25321988657544340671329069 9495745746579127751748401)
        ·
          refine ⟨7121809309934345813811301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9495745746579127751748401 7121809309934345813811301)
          ·
            refine ⟨1335339245612689840089619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7121809309934345813811301 1335339245612689840089619)
            ·
              refine ⟨2003008868419034760134429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335339245612689840089619 2003008868419034760134429)
              ·
                refine ⟨751128325657138035050411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2003008868419034760134429 751128325657138035050411)
                ·
                  refine ⟨1126692488485707052575617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 751128325657138035050411 1126692488485707052575617)
                  ·
                    refine ⟨845019366364280289431713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1126692488485707052575617 845019366364280289431713)
                    ·
                      refine ⟨633764524773210217073785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 845019366364280289431713 633764524773210217073785)
                      ·
                        rfl

theorem cell23_1234252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_1234252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234252 prefixEnd_1234252 := by exact prefixLift 1234252
  have htrace : WordTrace (prefixWord ++ tailWord_1234252) baseStart_1234252 baseEnd_1234252 := by
    simpa [prefixWord, tailWord_1234252, baseEnd_1234252] using wordTrace_append hprefix tailTrace_1234252
  have hstable : (prefixWord ++ tailWord_1234252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234252).length < 2 ^ (prefixWord ++ tailWord_1234252).sum := by decide
  have hdescent : baseEnd_1234252 < baseStart_1234252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234285 : List Nat := [1, 5, 1, 1, 1, 3, 4, 1, 2, 1, 3]
def baseStart_1234285 : Nat := 118140960795 + 1234285 * 2 ^ 59
def prefixEnd_1234285 : Nat := 4983230072969 + 3 ^ 40 * 1234285 * 2
def baseEnd_1234285 : Nat := 633781469634808587961133

theorem tailTrace_1234285 : CollatzResearch.WordTrace tailWord_1234285 prefixEnd_1234285 633781469634808587961133 := by
  unfold tailWord_1234285
  simp only [CollatzResearch.WordTrace]
  refine ⟨45018072333403718940536309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30012048222269145960357539 45018072333403718940536309)
  ·
    refine ⟨4220444281256598650675279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45018072333403718940536309 4220444281256598650675279)
    ·
      refine ⟨6330666421884897976012919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4220444281256598650675279 6330666421884897976012919)
      ·
        refine ⟨9495999632827346964019379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6330666421884897976012919 9495999632827346964019379)
        ·
          refine ⟨14243999449241020446029069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9495999632827346964019379 14243999449241020446029069)
          ·
            refine ⟨5341499793465382667260901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14243999449241020446029069 5341499793465382667260901)
            ·
              refine ⟨1001531211274759250111419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5341499793465382667260901 1001531211274759250111419)
              ·
                refine ⟨1502296816912138875167129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1001531211274759250111419 1502296816912138875167129)
                ·
                  refine ⟨1126722612684104156375347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1502296816912138875167129 1126722612684104156375347)
                  ·
                    refine ⟨1690083919026156234563021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1126722612684104156375347 1690083919026156234563021)
                    ·
                      refine ⟨633781469634808587961133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1690083919026156234563021 633781469634808587961133)
                      ·
                        rfl

theorem cell23_1234285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_1234285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234285 prefixEnd_1234285 := by exact prefixLift 1234285
  have htrace : WordTrace (prefixWord ++ tailWord_1234285) baseStart_1234285 baseEnd_1234285 := by
    simpa [prefixWord, tailWord_1234285, baseEnd_1234285] using wordTrace_append hprefix tailTrace_1234285
  have hstable : (prefixWord ++ tailWord_1234285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234285).length < 2 ^ (prefixWord ++ tailWord_1234285).sum := by decide
  have hdescent : baseEnd_1234285 < baseStart_1234285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234308 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 1, 4, 2]
def baseStart_1234308 : Nat := 118140960795 + 1234308 * 2 ^ 59
def prefixEnd_1234308 : Nat := 4983230072969 + 3 ^ 40 * 1234308 * 2
def baseEnd_1234308 : Nat := 633793279689861997973527

theorem tailTrace_1234308 : CollatzResearch.WordTrace tailWord_1234308 prefixEnd_1234308 633793279689861997973527 := by
  unfold tailWord_1234308
  simp only [CollatzResearch.WordTrace]
  refine ⟨22509455606160196934311789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30012607474880262579082385 22509455606160196934311789)
  ·
    refine ⟨8441045852310073850366921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22509455606160196934311789 8441045852310073850366921)
    ·
      refine ⟨6330784389232555387775191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8441045852310073850366921 6330784389232555387775191)
      ·
        refine ⟨9496176583848833081662787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6330784389232555387775191 9496176583848833081662787)
        ·
          refine ⟨14244264875773249622494181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9496176583848833081662787 14244264875773249622494181)
          ·
            refine ⟨2670799664207484304217659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14244264875773249622494181 2670799664207484304217659)
            ·
              refine ⟨4006199496311226456326489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670799664207484304217659 4006199496311226456326489)
              ·
                refine ⟨3004649622233419842244867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4006199496311226456326489 3004649622233419842244867)
                ·
                  refine ⟨4506974433350129763367301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3004649622233419842244867 4506974433350129763367301)
                  ·
                    refine ⟨845057706253149330631369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4506974433350129763367301 845057706253149330631369)
                    ·
                      refine ⟨633793279689861997973527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 845057706253149330631369 633793279689861997973527)
                      ·
                        rfl

theorem cell23_1234308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_1234308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234308 prefixEnd_1234308 := by exact prefixLift 1234308
  have htrace : WordTrace (prefixWord ++ tailWord_1234308) baseStart_1234308 baseEnd_1234308 := by
    simpa [prefixWord, tailWord_1234308, baseEnd_1234308] using wordTrace_append hprefix tailTrace_1234308
  have hstable : (prefixWord ++ tailWord_1234308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234308).length < 2 ^ (prefixWord ++ tailWord_1234308).sum := by decide
  have hdescent : baseEnd_1234308 < baseStart_1234308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234354 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_1234354 : Nat := 118140960795 + 1234354 * 2 ^ 59
def prefixEnd_1234354 : Nat := 4983230072969 + 3 ^ 40 * 1234354 * 2
def baseEnd_1234354 : Nat := 633816899799968817998315

theorem tailTrace_1234354 : CollatzResearch.WordTrace tailWord_1234354 prefixEnd_1234354 633816899799968817998315 := by
  unfold tailWord_1234354
  simp only [CollatzResearch.WordTrace]
  refine ⟨11255147242538435931199529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30013725980102495816532077 11255147242538435931199529)
  ·
    refine ⟨8441360431903826948399647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11255147242538435931199529 8441360431903826948399647)
    ·
      refine ⟨12662040647855740422599471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8441360431903826948399647 12662040647855740422599471)
      ·
        refine ⟨18993060971783610633899207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12662040647855740422599471 18993060971783610633899207)
        ·
          refine ⟨28489591457675415950848811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18993060971783610633899207 28489591457675415950848811)
          ·
            refine ⟨42734387186513123926273217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28489591457675415950848811 42734387186513123926273217)
            ·
              refine ⟨32050790389884842944704913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42734387186513123926273217 32050790389884842944704913)
              ·
                refine ⟨24038092792413632208528685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32050790389884842944704913 24038092792413632208528685)
                ·
                  refine ⟨9014284797155112078198257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24038092792413632208528685 9014284797155112078198257)
                  ·
                    refine ⟨6760713597866334058648693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9014284797155112078198257 6760713597866334058648693)
                    ·
                      refine ⟨633816899799968817998315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6760713597866334058648693 633816899799968817998315)
                      ·
                        rfl

theorem cell23_1234354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_1234354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234354 prefixEnd_1234354 := by exact prefixLift 1234354
  have htrace : WordTrace (prefixWord ++ tailWord_1234354) baseStart_1234354 baseEnd_1234354 := by
    simpa [prefixWord, tailWord_1234354, baseEnd_1234354] using wordTrace_append hprefix tailTrace_1234354
  have hstable : (prefixWord ++ tailWord_1234354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234354).length < 2 ^ (prefixWord ++ tailWord_1234354).sum := by decide
  have hdescent : baseEnd_1234354 < baseStart_1234354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234361 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 1, 7]
def baseStart_1234361 : Nat := 118140960795 + 1234361 * 2 ^ 59
def prefixEnd_1234361 : Nat := 4983230072969 + 3 ^ 40 * 1234361 * 2
def baseEnd_1234361 : Nat := 211273498054850096870261

theorem tailTrace_1234361 : CollatzResearch.WordTrace tailWord_1234361 prefixEnd_1234361 211273498054850096870261 := by
  unfold tailWord_1234361
  simp only [CollatzResearch.WordTrace]
  refine ⟨45020844281128383920302937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30013896187418922613535291 45020844281128383920302937)
  ·
    refine ⟨33765633210846287940227203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45020844281128383920302937 33765633210846287940227203)
    ·
      refine ⟨50648449816269431910340805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33765633210846287940227203 50648449816269431910340805)
      ·
        refine ⟨9496584340550518483188901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50648449816269431910340805 9496584340550518483188901)
        ·
          refine ⟨1780609563853222215597919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9496584340550518483188901 1780609563853222215597919)
          ·
            refine ⟨2670914345779833323396879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1780609563853222215597919 2670914345779833323396879)
            ·
              refine ⟨4006371518669749985095319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670914345779833323396879 4006371518669749985095319)
              ·
                refine ⟨6009557278004624977642979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4006371518669749985095319 6009557278004624977642979)
                ·
                  refine ⟨9014335917006937466464469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6009557278004624977642979 9014335917006937466464469)
                  ·
                    refine ⟨211273498054850096870261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9014335917006937466464469 211273498054850096870261)
                    ·
                      rfl

theorem cell23_1234361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 7].length) (baseStart_1234361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234361 prefixEnd_1234361 := by exact prefixLift 1234361
  have htrace : WordTrace (prefixWord ++ tailWord_1234361) baseStart_1234361 baseEnd_1234361 := by
    simpa [prefixWord, tailWord_1234361, baseEnd_1234361] using wordTrace_append hprefix tailTrace_1234361
  have hstable : (prefixWord ++ tailWord_1234361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234361).length < 2 ^ (prefixWord ++ tailWord_1234361).sum := by decide
  have hdescent : baseEnd_1234361 < baseStart_1234361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234401 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 1, 4, 3]
def baseStart_1234401 : Nat := 118140960795 + 1234401 * 2 ^ 59
def prefixEnd_1234401 : Nat := 4983230072969 + 3 ^ 40 * 1234401 * 2
def baseEnd_1234401 : Nat := 633841033390730134110599

theorem tailTrace_1234401 : CollatzResearch.WordTrace tailWord_1234401 prefixEnd_1234401 633841033390730134110599 := by
  unfold tailWord_1234401
  simp only [CollatzResearch.WordTrace]
  refine ⟨45022303200983470751759057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30014868800655647167839371 45022303200983470751759057)
  ·
    refine ⟨33766727400737603063819293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45022303200983470751759057 33766727400737603063819293)
    ·
      refine ⟨12662522775276601148932235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33766727400737603063819293 12662522775276601148932235)
      ·
        refine ⟨18993784162914901723398353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12662522775276601148932235 18993784162914901723398353)
        ·
          refine ⟨14245338122186176292548765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18993784162914901723398353 14245338122186176292548765)
          ·
            refine ⟨5342001795819816109705787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14245338122186176292548765 5342001795819816109705787)
            ·
              refine ⟨8013002693729724164558681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5342001795819816109705787 8013002693729724164558681)
              ·
                refine ⟨6009752020297293123419011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8013002693729724164558681 6009752020297293123419011)
                ·
                  refine ⟨9014628030445939685128517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6009752020297293123419011 9014628030445939685128517)
                  ·
                    refine ⟨1690242755708613690961597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9014628030445939685128517 1690242755708613690961597)
                    ·
                      refine ⟨633841033390730134110599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1690242755708613690961597 633841033390730134110599)
                      ·
                        rfl

theorem cell23_1234401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_1234401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234401 prefixEnd_1234401 := by exact prefixLift 1234401
  have htrace : WordTrace (prefixWord ++ tailWord_1234401) baseStart_1234401 baseEnd_1234401 := by
    simpa [prefixWord, tailWord_1234401, baseEnd_1234401] using wordTrace_append hprefix tailTrace_1234401
  have hstable : (prefixWord ++ tailWord_1234401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234401).length < 2 ^ (prefixWord ++ tailWord_1234401).sum := by decide
  have hdescent : baseEnd_1234401 < baseStart_1234401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234418 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 1, 4, 3]
def baseStart_1234418 : Nat := 118140960795 + 1234418 * 2 ^ 59
def prefixEnd_1234418 : Nat := 4983230072969 + 3 ^ 40 * 1234418 * 2
def baseEnd_1234418 : Nat := 633849762561856567598021

theorem tailTrace_1234418 : CollatzResearch.WordTrace tailWord_1234418 prefixEnd_1234418 633849762561856567598021 := by
  unfold tailWord_1234418
  simp only [CollatzResearch.WordTrace]
  refine ⟨11255730810480470663781977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30015282161281255103418605 11255730810480470663781977)
  ·
    refine ⟨8441798107860352997836483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11255730810480470663781977 8441798107860352997836483)
    ·
      refine ⟨12662697161790529496754725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8441798107860352997836483 12662697161790529496754725)
      ·
        refine ⟨2374255717835724280641511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12662697161790529496754725 2374255717835724280641511)
        ·
          refine ⟨3561383576753586420962267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2374255717835724280641511 3561383576753586420962267)
          ·
            refine ⟨5342075365130379631443401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3561383576753586420962267 5342075365130379631443401)
            ·
              refine ⟨4006556523847784723582551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5342075365130379631443401 4006556523847784723582551)
              ·
                refine ⟨6009834785771677085373827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4006556523847784723582551 6009834785771677085373827)
                ·
                  refine ⟨9014752178657515628060741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6009834785771677085373827 9014752178657515628060741)
                  ·
                    refine ⟨1690266033498284180261389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9014752178657515628060741 1690266033498284180261389)
                    ·
                      refine ⟨633849762561856567598021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1690266033498284180261389 633849762561856567598021)
                      ·
                        rfl

theorem cell23_1234418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_1234418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234418 prefixEnd_1234418 := by exact prefixLift 1234418
  have htrace : WordTrace (prefixWord ++ tailWord_1234418) baseStart_1234418 baseEnd_1234418 := by
    simpa [prefixWord, tailWord_1234418, baseEnd_1234418] using wordTrace_append hprefix tailTrace_1234418
  have hstable : (prefixWord ++ tailWord_1234418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234418).length < 2 ^ (prefixWord ++ tailWord_1234418).sum := by decide
  have hdescent : baseEnd_1234418 < baseStart_1234418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234442 : List Nat := [3, 1, 2, 2, 2, 3, 3, 2, 1, 4]
def baseStart_1234442 : Nat := 118140960795 + 1234442 * 2 ^ 59
def prefixEnd_1234442 : Nat := 4983230072969 + 3 ^ 40 * 1234442 * 2
def baseEnd_1234442 : Nat := 211287362032521491232637

theorem tailTrace_1234442 : CollatzResearch.WordTrace tailWord_1234442 prefixEnd_1234442 211287362032521491232637 := by
  unfold tailWord_1234442
  simp only [CollatzResearch.WordTrace]
  refine ⟨11255949648458733688500395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30015865729223289836001053 11255949648458733688500395)
  ·
    refine ⟨16883924472688100532750593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11255949648458733688500395 16883924472688100532750593)
    ·
      refine ⟨12662943354516075399562945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16883924472688100532750593 12662943354516075399562945)
      ·
        refine ⟨9497207515887056549672209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12662943354516075399562945 9497207515887056549672209)
        ·
          refine ⟨7122905636915292412254157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9497207515887056549672209 7122905636915292412254157)
          ·
            refine ⟨2671089613843234654595309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7122905636915292412254157 2671089613843234654595309)
            ·
              refine ⟨1001658605191212995473241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2671089613843234654595309 1001658605191212995473241)
              ·
                refine ⟨751243953893409746604931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1001658605191212995473241 751243953893409746604931)
                ·
                  refine ⟨1126865930840114619907397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 751243953893409746604931 1126865930840114619907397)
                  ·
                    refine ⟨211287362032521491232637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1126865930840114619907397 211287362032521491232637)
                    ·
                      rfl

theorem cell23_1234442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_1234442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234442 prefixEnd_1234442 := by exact prefixLift 1234442
  have htrace : WordTrace (prefixWord ++ tailWord_1234442) baseStart_1234442 baseEnd_1234442 := by
    simpa [prefixWord, tailWord_1234442, baseEnd_1234442] using wordTrace_append hprefix tailTrace_1234442
  have hstable : (prefixWord ++ tailWord_1234442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234442).length < 2 ^ (prefixWord ++ tailWord_1234442).sum := by decide
  have hdescent : baseEnd_1234442 < baseStart_1234442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234458 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2]
def baseStart_1234458 : Nat := 118140960795 + 1234458 * 2 ^ 59
def prefixEnd_1234458 : Nat := 4983230072969 + 3 ^ 40 * 1234458 * 2
def baseEnd_1234458 : Nat := 633870301788036411097837

theorem tailTrace_1234458 : CollatzResearch.WordTrace tailWord_1234458 prefixEnd_1234458 633870301788036411097837 := by
  unfold tailWord_1234458
  simp only [CollatzResearch.WordTrace]
  refine ⟨11256095540444242371646007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30016254774517979657722685 11256095540444242371646007)
  ·
    refine ⟨16884143310666363557469011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11256095540444242371646007 16884143310666363557469011)
    ·
      refine ⟨25326214965999545336203517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16884143310666363557469011 25326214965999545336203517)
      ·
        refine ⟨9497330612249829501076319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25326214965999545336203517 9497330612249829501076319)
        ·
          refine ⟨14245995918374744251614479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9497330612249829501076319 14245995918374744251614479)
          ·
            refine ⟨21368993877562116377421719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14245995918374744251614479 21368993877562116377421719)
            ·
              refine ⟨32053490816343174566132579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21368993877562116377421719 32053490816343174566132579)
              ·
                refine ⟨48080236224514761849198869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32053490816343174566132579 48080236224514761849198869)
                ·
                  refine ⟨2253761073024129461681197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48080236224514761849198869 2253761073024129461681197)
                  ·
                    refine ⟨845160402384048548130449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2253761073024129461681197 845160402384048548130449)
                    ·
                      refine ⟨633870301788036411097837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 845160402384048548130449 633870301788036411097837)
                      ·
                        rfl

theorem cell23_1234458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_1234458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234458 prefixEnd_1234458 := by exact prefixLift 1234458
  have htrace : WordTrace (prefixWord ++ tailWord_1234458) baseStart_1234458 baseEnd_1234458 := by
    simpa [prefixWord, tailWord_1234458, baseEnd_1234458] using wordTrace_append hprefix tailTrace_1234458
  have hstable : (prefixWord ++ tailWord_1234458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234458).length < 2 ^ (prefixWord ++ tailWord_1234458).sum := by decide
  have hdescent : baseEnd_1234458 < baseStart_1234458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234485 : List Nat := [1, 3, 3, 1, 1, 4, 3, 1, 1, 5]
def baseStart_1234485 : Nat := 118140960795 + 1234485 * 2 ^ 59
def prefixEnd_1234485 : Nat := 4983230072969 + 3 ^ 40 * 1234485 * 2
def baseEnd_1234485 : Nat := 211294721921902601820071

theorem tailTrace_1234485 : CollatzResearch.WordTrace tailWord_1234485 prefixEnd_1234485 211294721921902601820071 := by
  unfold tailWord_1234485
  simp only [CollatzResearch.WordTrace]
  refine ⟨45025366932679153097816909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30016911288452768731877939 45025366932679153097816909)
  ·
    refine ⟨16884512599754682411681341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45025366932679153097816909 16884512599754682411681341)
    ·
      refine ⟨6331692224908005904380503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16884512599754682411681341 6331692224908005904380503)
      ·
        refine ⟨9497538337362008856570755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6331692224908005904380503 9497538337362008856570755)
        ·
          refine ⟨14246307506043013284856133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9497538337362008856570755 14246307506043013284856133)
          ·
            refine ⟨2671182657383064990910525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14246307506043013284856133 2671182657383064990910525)
            ·
              refine ⟨1001693496518649371591447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2671182657383064990910525 1001693496518649371591447)
              ·
                refine ⟨1502540244777974057387171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1001693496518649371591447 1502540244777974057387171)
                ·
                  refine ⟨2253810367166961086080757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502540244777974057387171 2253810367166961086080757)
                  ·
                    refine ⟨211294721921902601820071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2253810367166961086080757 211294721921902601820071)
                    ·
                      rfl

theorem cell23_1234485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_1234485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234485 prefixEnd_1234485 := by exact prefixLift 1234485
  have htrace : WordTrace (prefixWord ++ tailWord_1234485) baseStart_1234485 baseEnd_1234485 := by
    simpa [prefixWord, tailWord_1234485, baseEnd_1234485] using wordTrace_append hprefix tailTrace_1234485
  have hstable : (prefixWord ++ tailWord_1234485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234485).length < 2 ^ (prefixWord ++ tailWord_1234485).sum := by decide
  have hdescent : baseEnd_1234485 < baseStart_1234485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234501 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 3, 2, 4]
def baseStart_1234501 : Nat := 118140960795 + 1234501 * 2 ^ 59
def prefixEnd_1234501 : Nat := 4983230072969 + 3 ^ 40 * 1234501 * 2
def baseEnd_1234501 : Nat := 633892381456179742860139

theorem tailTrace_1234501 : CollatzResearch.WordTrace tailWord_1234501 prefixEnd_1234501 633892381456179742860139 := by
  unfold tailWord_1234501
  simp only [CollatzResearch.WordTrace]
  refine ⟨45025950500621187830399357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30017300333747458553599571 45025950500621187830399357)
  ·
    refine ⟨16884731437732945436399759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45025950500621187830399357 16884731437732945436399759)
    ·
      refine ⟨25327097156599418154599639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16884731437732945436399759 25327097156599418154599639)
      ·
        refine ⟨37990645734899127231899459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25327097156599418154599639 37990645734899127231899459)
        ·
          refine ⟨56985968602348690847849189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37990645734899127231899459 56985968602348690847849189)
          ·
            refine ⟨10684869112940379533971723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56985968602348690847849189 10684869112940379533971723)
            ·
              refine ⟨16027303669410569300957585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10684869112940379533971723 16027303669410569300957585)
              ·
                refine ⟨12020477752057926975718189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16027303669410569300957585 12020477752057926975718189)
                ·
                  refine ⟨4507679157021722615894321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12020477752057926975718189 4507679157021722615894321)
                  ·
                    refine ⟨3380759367766291961920741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4507679157021722615894321 3380759367766291961920741)
                    ·
                      refine ⟨633892381456179742860139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3380759367766291961920741 633892381456179742860139)
                      ·
                        rfl

theorem cell23_1234501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_1234501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234501 prefixEnd_1234501 := by exact prefixLift 1234501
  have htrace : WordTrace (prefixWord ++ tailWord_1234501) baseStart_1234501 baseEnd_1234501 := by
    simpa [prefixWord, tailWord_1234501, baseEnd_1234501] using wordTrace_append hprefix tailTrace_1234501
  have hstable : (prefixWord ++ tailWord_1234501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234501).length < 2 ^ (prefixWord ++ tailWord_1234501).sum := by decide
  have hdescent : baseEnd_1234501 < baseStart_1234501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234508 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 3, 2, 3]
def baseStart_1234508 : Nat := 118140960795 + 1234508 * 2 ^ 59
def prefixEnd_1234508 : Nat := 4983230072969 + 3 ^ 40 * 1234508 * 2
def baseEnd_1234508 : Nat := 633895975820761215472607

theorem tailTrace_1234508 : CollatzResearch.WordTrace tailWord_1234508 prefixEnd_1234508 633895975820761215472607 := by
  unfold tailWord_1234508
  simp only [CollatzResearch.WordTrace]
  refine ⟨22513102905797914012952089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30017470541063885350602785 22513102905797914012952089)
  ·
    refine ⟨16884827179348435509714067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22513102905797914012952089 16884827179348435509714067)
    ·
      refine ⟨25327240769022653264571101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16884827179348435509714067 25327240769022653264571101)
      ·
        refine ⟨9497715288383494974214163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25327240769022653264571101 9497715288383494974214163)
        ·
          refine ⟨14246572932575242461321245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9497715288383494974214163 14246572932575242461321245)
          ·
            refine ⟨5342464849715715922995467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14246572932575242461321245 5342464849715715922995467)
            ·
              refine ⟨8013697274573573884493201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5342464849715715922995467 8013697274573573884493201)
              ·
                refine ⟨6010272955930180413369901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8013697274573573884493201 6010272955930180413369901)
                ·
                  refine ⟨2253852358473817655013713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6010272955930180413369901 2253852358473817655013713)
                  ·
                    refine ⟨1690389268855363241260285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2253852358473817655013713 1690389268855363241260285)
                    ·
                      refine ⟨633895975820761215472607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1690389268855363241260285 633895975820761215472607)
                      ·
                        rfl

theorem cell23_1234508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_1234508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234508 prefixEnd_1234508 := by exact prefixLift 1234508
  have htrace : WordTrace (prefixWord ++ tailWord_1234508) baseStart_1234508 baseEnd_1234508 := by
    simpa [prefixWord, tailWord_1234508, baseEnd_1234508] using wordTrace_append hprefix tailTrace_1234508
  have hstable : (prefixWord ++ tailWord_1234508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234508).length < 2 ^ (prefixWord ++ tailWord_1234508).sum := by decide
  have hdescent : baseEnd_1234508 < baseStart_1234508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234542 : List Nat := [4, 1, 2, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_1234542 : Nat := 118140960795 + 1234542 * 2 ^ 59
def prefixEnd_1234542 : Nat := 4983230072969 + 3 ^ 40 * 1234542 * 2
def baseEnd_1234542 : Nat := 633913434163014082447451

theorem tailTrace_1234542 : CollatzResearch.WordTrace tailWord_1234542 prefixEnd_1234542 633913434163014082447451 := by
  unfold tailWord_1234542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5628430736684081479080235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30018297262315101221761253 5628430736684081479080235)
  ·
    refine ⟨8442646105026122218620353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5628430736684081479080235 8442646105026122218620353)
    ·
      refine ⟨6331984578769591663965265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8442646105026122218620353 6331984578769591663965265)
      ·
        refine ⟨4748988434077193747973949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6331984578769591663965265 4748988434077193747973949)
        ·
          refine ⟨1780870662778947655490231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4748988434077193747973949 1780870662778947655490231)
          ·
            refine ⟨2671305994168421483235347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1780870662778947655490231 2671305994168421483235347)
            ·
              refine ⟨4006958991252632224853021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2671305994168421483235347 4006958991252632224853021)
              ·
                refine ⟨1502609621719737084319883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4006958991252632224853021 1502609621719737084319883)
                ·
                  refine ⟨2253914432579605626479825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502609621719737084319883 2253914432579605626479825)
                  ·
                    refine ⟨1690435824434704219859869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2253914432579605626479825 1690435824434704219859869)
                    ·
                      refine ⟨633913434163014082447451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1690435824434704219859869 633913434163014082447451)
                      ·
                        rfl

theorem cell23_1234542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_1234542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234542 prefixEnd_1234542 := by exact prefixLift 1234542
  have htrace : WordTrace (prefixWord ++ tailWord_1234542) baseStart_1234542 baseEnd_1234542 := by
    simpa [prefixWord, tailWord_1234542, baseEnd_1234542] using wordTrace_append hprefix tailTrace_1234542
  have hstable : (prefixWord ++ tailWord_1234542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234542).length < 2 ^ (prefixWord ++ tailWord_1234542).sum := by decide
  have hdescent : baseEnd_1234542 < baseStart_1234542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234571 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 2, 6]
def baseStart_1234571 : Nat := 118140960795 + 1234571 * 2 ^ 59
def prefixEnd_1234571 : Nat := 4983230072969 + 3 ^ 40 * 1234571 * 2
def baseEnd_1234571 : Nat := 211309441700664822994939

theorem tailTrace_1234571 : CollatzResearch.WordTrace tailWord_1234571 prefixEnd_1234571 211309441700664822994939 := by
  unfold tailWord_1234571
  simp only [CollatzResearch.WordTrace]
  refine ⟨45028503610367589785447567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30019002406911726523631711 45028503610367589785447567)
  ·
    refine ⟨67542755415551384678171351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45028503610367589785447567 67542755415551384678171351)
    ·
      refine ⟨101314133123327077017257027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67542755415551384678171351 101314133123327077017257027)
      ·
        refine ⟨151971199684990615525885541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101314133123327077017257027 151971199684990615525885541)
        ·
          refine ⟨28494599940935740411103539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151971199684990615525885541 28494599940935740411103539)
          ·
            refine ⟨42741899911403610616655309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28494599940935740411103539 42741899911403610616655309)
            ·
              refine ⟨16028212466776353981245741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42741899911403610616655309 16028212466776353981245741)
              ·
                refine ⟨6010579675041132742967153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16028212466776353981245741 6010579675041132742967153)
                ·
                  refine ⟨4507934756280849557225365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6010579675041132742967153 4507934756280849557225365)
                  ·
                    refine ⟨211309441700664822994939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4507934756280849557225365 211309441700664822994939)
                    ·
                      rfl

theorem cell23_1234571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 6].length) (baseStart_1234571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234571 prefixEnd_1234571 := by exact prefixLift 1234571
  have htrace : WordTrace (prefixWord ++ tailWord_1234571) baseStart_1234571 baseEnd_1234571 := by
    simpa [prefixWord, tailWord_1234571, baseEnd_1234571] using wordTrace_append hprefix tailTrace_1234571
  have hstable : (prefixWord ++ tailWord_1234571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234571).length < 2 ^ (prefixWord ++ tailWord_1234571).sum := by decide
  have hdescent : baseEnd_1234571 < baseStart_1234571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234572 : List Nat := [2, 2, 1, 2, 1, 1, 7, 1, 2, 1, 3]
def baseStart_1234572 : Nat := 118140960795 + 1234572 * 2 ^ 59
def prefixEnd_1234572 : Nat := 4983230072969 + 3 ^ 40 * 1234572 * 2
def baseEnd_1234572 : Nat := 633928838582648965072313

theorem tailTrace_1234572 : CollatzResearch.WordTrace tailWord_1234572 prefixEnd_1234572 633928838582648965072313 := by
  unfold tailWord_1234572
  simp only [CollatzResearch.WordTrace]
  refine ⟨22514270041681983478116985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30019026722242644637489313 22514270041681983478116985)
  ·
    refine ⟨16885702531261487608587739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22514270041681983478116985 16885702531261487608587739)
    ·
      refine ⟨25328553796892231412881609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16885702531261487608587739 25328553796892231412881609)
      ·
        refine ⟨18996415347669173559661207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25328553796892231412881609 18996415347669173559661207)
        ·
          refine ⟨28494623021503760339491811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18996415347669173559661207 28494623021503760339491811)
          ·
            refine ⟨42741934532255640509237717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28494623021503760339491811 42741934532255640509237717)
            ·
              refine ⟨1001764090599741574435259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 42741934532255640509237717 1001764090599741574435259)
              ·
                refine ⟨1502646135899612361652889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1001764090599741574435259 1502646135899612361652889)
                ·
                  refine ⟨1126984601924709271239667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1502646135899612361652889 1126984601924709271239667)
                  ·
                    refine ⟨1690476902887063906859501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1126984601924709271239667 1690476902887063906859501)
                    ·
                      refine ⟨633928838582648965072313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1690476902887063906859501 633928838582648965072313)
                      ·
                        rfl

theorem cell23_1234572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_1234572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234572 prefixEnd_1234572 := by exact prefixLift 1234572
  have htrace : WordTrace (prefixWord ++ tailWord_1234572) baseStart_1234572 baseEnd_1234572 := by
    simpa [prefixWord, tailWord_1234572, baseEnd_1234572] using wordTrace_append hprefix tailTrace_1234572
  have hstable : (prefixWord ++ tailWord_1234572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234572).length < 2 ^ (prefixWord ++ tailWord_1234572).sum := by decide
  have hdescent : baseEnd_1234572 < baseStart_1234572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234581 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_1234581 : Nat := 118140960795 + 1234581 * 2 ^ 59
def prefixEnd_1234581 : Nat := 4983230072969 + 3 ^ 40 * 1234581 * 2
def baseEnd_1234581 : Nat := 633933459908539429859771

theorem tailTrace_1234581 : CollatzResearch.WordTrace tailWord_1234581 prefixEnd_1234581 633933459908539429859771 := by
  unfold tailWord_1234581
  simp only [CollatzResearch.WordTrace]
  refine ⟨45028868340331361493311597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30019245560220907662207731 45028868340331361493311597)
  ·
    refine ⟨16885825627624260559991849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45028868340331361493311597 16885825627624260559991849)
    ·
      refine ⟨12664369220718195419993887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16885825627624260559991849 12664369220718195419993887)
      ·
        refine ⟨18996553831077293129990831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12664369220718195419993887 18996553831077293129990831)
        ·
          refine ⟨28494830746615939694986247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18996553831077293129990831 28494830746615939694986247)
          ·
            refine ⟨42742246119923909542479371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28494830746615939694986247 42742246119923909542479371)
            ·
              refine ⟨64113369179885864313719057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42742246119923909542479371 64113369179885864313719057)
              ·
                refine ⟨48085026884914398235289293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64113369179885864313719057 48085026884914398235289293)
                ·
                  refine ⟨18031885081842899338233485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48085026884914398235289293 18031885081842899338233485)
                  ·
                    refine ⟨6761956905691087251837557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18031885081842899338233485 6761956905691087251837557)
                    ·
                      refine ⟨633933459908539429859771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6761956905691087251837557 633933459908539429859771)
                      ·
                        rfl

theorem cell23_1234581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_1234581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234581 prefixEnd_1234581 := by exact prefixLift 1234581
  have htrace : WordTrace (prefixWord ++ tailWord_1234581) baseStart_1234581 baseEnd_1234581 := by
    simpa [prefixWord, tailWord_1234581, baseEnd_1234581] using wordTrace_append hprefix tailTrace_1234581
  have hstable : (prefixWord ++ tailWord_1234581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234581).length < 2 ^ (prefixWord ++ tailWord_1234581).sum := by decide
  have hdescent : baseEnd_1234581 < baseStart_1234581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234595 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 6, 2, 2]
def baseStart_1234595 : Nat := 118140960795 + 1234595 * 2 ^ 59
def prefixEnd_1234595 : Nat := 4983230072969 + 3 ^ 40 * 1234595 * 2
def baseEnd_1234595 : Nat := 633940648637702375084707

theorem tailTrace_1234595 : CollatzResearch.WordTrace tailWord_1234595 prefixEnd_1234595 633940648637702375084707 := by
  unfold tailWord_1234595
  simp only [CollatzResearch.WordTrace]
  refine ⟨45029378962280641884321239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30019585974853761256214159 45029378962280641884321239)
  ·
    refine ⟨67544068443420962826481859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45029378962280641884321239 67544068443420962826481859)
    ·
      refine ⟨101316102665131444239722789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67544068443420962826481859 101316102665131444239722789)
      ·
        refine ⟨18996769249712145794948023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101316102665131444239722789 18996769249712145794948023)
        ·
          refine ⟨28495153874568218692422035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18996769249712145794948023 28495153874568218692422035)
          ·
            refine ⟨42742730811852328038633053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28495153874568218692422035 42742730811852328038633053)
            ·
              refine ⟨16028524054444623014487395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42742730811852328038633053 16028524054444623014487395)
              ·
                refine ⟨24042786081666934521731093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16028524054444623014487395 24042786081666934521731093)
                ·
                  refine ⟨1127005597578137555706145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24042786081666934521731093 1127005597578137555706145)
                  ·
                    refine ⟨845254198183603166779609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1127005597578137555706145 845254198183603166779609)
                    ·
                      refine ⟨633940648637702375084707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 845254198183603166779609 633940648637702375084707)
                      ·
                        rfl

theorem cell23_1234595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_1234595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234595 prefixEnd_1234595 := by exact prefixLift 1234595
  have htrace : WordTrace (prefixWord ++ tailWord_1234595) baseStart_1234595 baseEnd_1234595 := by
    simpa [prefixWord, tailWord_1234595, baseEnd_1234595] using wordTrace_append hprefix tailTrace_1234595
  have hstable : (prefixWord ++ tailWord_1234595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234595).length < 2 ^ (prefixWord ++ tailWord_1234595).sum := by decide
  have hdescent : baseEnd_1234595 < baseStart_1234595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234611 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 7]
def baseStart_1234611 : Nat := 118140960795 + 1234611 * 2 ^ 59
def prefixEnd_1234611 : Nat := 4983230072969 + 3 ^ 40 * 1234611 * 2
def baseEnd_1234611 : Nat := 633948864328174312484633

theorem tailTrace_1234611 : CollatzResearch.WordTrace tailWord_1234611 prefixEnd_1234611 633948864328174312484633 := by
  unfold tailWord_1234611
  simp only [CollatzResearch.WordTrace]
  refine ⟨45029962530222676616903687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30019975020148451077935791 45029962530222676616903687)
  ·
    refine ⟨67544943795334014925355531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45029962530222676616903687 67544943795334014925355531)
    ·
      refine ⟨101317415693001022388033297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67544943795334014925355531 101317415693001022388033297)
      ·
        refine ⟨75988061769750766791024973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101317415693001022388033297 75988061769750766791024973)
        ·
          refine ⟨28495523163656537546634365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75988061769750766791024973 28495523163656537546634365)
          ·
            refine ⟨10685821186371201579987887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28495523163656537546634365 10685821186371201579987887)
            ·
              refine ⟨16028731779556802369981831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10685821186371201579987887 16028731779556802369981831)
              ·
                refine ⟨24043097669335203554972747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16028731779556802369981831 24043097669335203554972747)
                ·
                  refine ⟨36064646504002805332459121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24043097669335203554972747 36064646504002805332459121)
                  ·
                    refine ⟨27048484878002103999344341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36064646504002805332459121 27048484878002103999344341)
                    ·
                      refine ⟨633948864328174312484633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27048484878002103999344341 633948864328174312484633)
                      ·
                        rfl

theorem cell23_1234611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_1234611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234611 prefixEnd_1234611 := by exact prefixLift 1234611
  have htrace : WordTrace (prefixWord ++ tailWord_1234611) baseStart_1234611 baseEnd_1234611 := by
    simpa [prefixWord, tailWord_1234611, baseEnd_1234611] using wordTrace_append hprefix tailTrace_1234611
  have hstable : (prefixWord ++ tailWord_1234611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234611).length < 2 ^ (prefixWord ++ tailWord_1234611).sum := by decide
  have hdescent : baseEnd_1234611 < baseStart_1234611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234618 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 7]
def baseStart_1234618 : Nat := 118140960795 + 1234618 * 2 ^ 59
def prefixEnd_1234618 : Nat := 4983230072969 + 3 ^ 40 * 1234618 * 2
def baseEnd_1234618 : Nat := 70439162076972865010789

theorem tailTrace_1234618 : CollatzResearch.WordTrace tailWord_1234618 prefixEnd_1234618 70439162076972865010789 := by
  unfold tailWord_1234618
  simp only [CollatzResearch.WordTrace]
  refine ⟨11257554460299329203102127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30020145227464877874939005 11257554460299329203102127)
  ·
    refine ⟨16886331690448993804653191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11257554460299329203102127 16886331690448993804653191)
    ·
      refine ⟨25329497535673490706979787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16886331690448993804653191 25329497535673490706979787)
      ·
        refine ⟨37994246303510236060469681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25329497535673490706979787 37994246303510236060469681)
        ·
          refine ⟨28495684727632677045352261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37994246303510236060469681 28495684727632677045352261)
          ·
            refine ⟨5342940886431126946003549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28495684727632677045352261 5342940886431126946003549)
            ·
              refine ⟨2003602832411672604751331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5342940886431126946003549 2003602832411672604751331)
              ·
                refine ⟨3005404248617508907126997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003602832411672604751331 3005404248617508907126997)
                ·
                  refine ⟨70439162076972865010789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3005404248617508907126997 70439162076972865010789)
                  ·
                    rfl

theorem cell23_1234618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 7].length) (baseStart_1234618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234618 prefixEnd_1234618 := by exact prefixLift 1234618
  have htrace : WordTrace (prefixWord ++ tailWord_1234618) baseStart_1234618 baseEnd_1234618 := by
    simpa [prefixWord, tailWord_1234618, baseEnd_1234618] using wordTrace_append hprefix tailTrace_1234618
  have hstable : (prefixWord ++ tailWord_1234618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234618).length < 2 ^ (prefixWord ++ tailWord_1234618).sum := by decide
  have hdescent : baseEnd_1234618 < baseStart_1234618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234646 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_1234646 : Nat := 118140960795 + 1234646 * 2 ^ 59
def prefixEnd_1234646 : Nat := 4983230072969 + 3 ^ 40 * 1234646 * 2
def baseEnd_1234646 : Nat := 633966836151081675546973

theorem tailTrace_1234646 : CollatzResearch.WordTrace tailWord_1234646 prefixEnd_1234646 633966836151081675546973 := by
  unfold tailWord_1234646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2814452442818492349651737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30020826056730585062951861 2814452442818492349651737)
  ·
    refine ⟨2110839332113869262238803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2814452442818492349651737 2110839332113869262238803)
    ·
      refine ⟨3166258998170803893358205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2110839332113869262238803 3166258998170803893358205)
      ·
        refine ⟨1187347124314051460009327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3166258998170803893358205 1187347124314051460009327)
        ·
          refine ⟨1781020686471077190013991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187347124314051460009327 1781020686471077190013991)
          ·
            refine ⟨2671531029706615785020987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1781020686471077190013991 2671531029706615785020987)
            ·
              refine ⟨4007296544559923677531481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2671531029706615785020987 4007296544559923677531481)
              ·
                refine ⟨3005472408419942758148611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4007296544559923677531481 3005472408419942758148611)
                ·
                  refine ⟨4508208612629914137222917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3005472408419942758148611 4508208612629914137222917)
                  ·
                    refine ⟨845289114868108900729297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4508208612629914137222917 845289114868108900729297)
                    ·
                      refine ⟨633966836151081675546973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 845289114868108900729297 633966836151081675546973)
                      ·
                        rfl

theorem cell23_1234646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_1234646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234646 prefixEnd_1234646 := by exact prefixLift 1234646
  have htrace : WordTrace (prefixWord ++ tailWord_1234646) baseStart_1234646 baseEnd_1234646 := by
    simpa [prefixWord, tailWord_1234646, baseEnd_1234646] using wordTrace_append hprefix tailTrace_1234646
  have hstable : (prefixWord ++ tailWord_1234646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234646).length < 2 ^ (prefixWord ++ tailWord_1234646).sum := by decide
  have hdescent : baseEnd_1234646 < baseStart_1234646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234669 : List Nat := [1, 5, 1, 2, 1, 4, 2, 2, 5]
def baseStart_1234669 : Nat := 118140960795 + 1234669 * 2 ^ 59
def prefixEnd_1234669 : Nat := 4983230072969 + 3 ^ 40 * 1234669 * 2
def baseEnd_1234669 : Nat := 70442071800681676173263

theorem tailTrace_1234669 : CollatzResearch.WordTrace tailWord_1234669 prefixEnd_1234669 70442071800681676173263 := by
  unfold tailWord_1234669
  simp only [CollatzResearch.WordTrace]
  refine ⟨45032077964012552522515061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30021385309341701681676707 45032077964012552522515061)
  ·
    refine ⟨4221757309126176798985787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45032077964012552522515061 4221757309126176798985787)
    ·
      refine ⟨6332635963689265198478681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4221757309126176798985787 6332635963689265198478681)
      ·
        refine ⟨4749476972766948898859011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6332635963689265198478681 4749476972766948898859011)
        ·
          refine ⟨7124215459150423348288517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4749476972766948898859011 7124215459150423348288517)
          ·
            refine ⟨1335790398590704377804097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7124215459150423348288517 1335790398590704377804097)
            ·
              refine ⟨1001842798943028283353073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1335790398590704377804097 1001842798943028283353073)
              ·
                refine ⟨751382099207271212514805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1001842798943028283353073 751382099207271212514805)
                ·
                  refine ⟨70442071800681676173263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 751382099207271212514805 70442071800681676173263)
                  ·
                    rfl

theorem cell23_1234669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_1234669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234669 prefixEnd_1234669 := by exact prefixLift 1234669
  have htrace : WordTrace (prefixWord ++ tailWord_1234669) baseStart_1234669 baseEnd_1234669 := by
    simpa [prefixWord, tailWord_1234669, baseEnd_1234669] using wordTrace_append hprefix tailTrace_1234669
  have hstable : (prefixWord ++ tailWord_1234669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234669).length < 2 ^ (prefixWord ++ tailWord_1234669).sum := by decide
  have hdescent : baseEnd_1234669 < baseStart_1234669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234688 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 3]
def baseStart_1234688 : Nat := 118140960795 + 1234688 * 2 ^ 59
def prefixEnd_1234688 : Nat := 4983230072969 + 3 ^ 40 * 1234688 * 2
def baseEnd_1234688 : Nat := 633988402338570511221779

theorem tailTrace_1234688 : CollatzResearch.WordTrace tailWord_1234688 prefixEnd_1234688 633988402338570511221779 := by
  unfold tailWord_1234688
  simp only [CollatzResearch.WordTrace]
  refine ⟨22516385475471859383728359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30021847300629145844971145 22516385475471859383728359)
  ·
    refine ⟨33774578213207789075592539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22516385475471859383728359 33774578213207789075592539)
    ·
      refine ⟨50661867319811683613388809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33774578213207789075592539 50661867319811683613388809)
      ·
        refine ⟨37996400489858762710041607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50661867319811683613388809 37996400489858762710041607)
        ·
          refine ⟨56994600734788144065062411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37996400489858762710041607 56994600734788144065062411)
          ·
            refine ⟨85491901102182216097593617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56994600734788144065062411 85491901102182216097593617)
            ·
              refine ⟨64118925826636662073195213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85491901102182216097593617 64118925826636662073195213)
              ·
                refine ⟨24044597184988748277448205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64118925826636662073195213 24044597184988748277448205)
                ·
                  refine ⟨9016723944370780604043077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24044597184988748277448205 9016723944370780604043077)
                  ·
                    refine ⟨1690635739569521363258077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9016723944370780604043077 1690635739569521363258077)
                    ·
                      refine ⟨633988402338570511221779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1690635739569521363258077 633988402338570511221779)
                      ·
                        rfl

theorem cell23_1234688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_1234688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234688 prefixEnd_1234688 := by exact prefixLift 1234688
  have htrace : WordTrace (prefixWord ++ tailWord_1234688) baseStart_1234688 baseEnd_1234688 := by
    simpa [prefixWord, tailWord_1234688, baseEnd_1234688] using wordTrace_append hprefix tailTrace_1234688
  have hstable : (prefixWord ++ tailWord_1234688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234688).length < 2 ^ (prefixWord ++ tailWord_1234688).sum := by decide
  have hdescent : baseEnd_1234688 < baseStart_1234688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234712 : List Nat := [2, 1, 2, 3, 1, 1, 3, 5, 1, 4]
def baseStart_1234712 : Nat := 118140960795 + 1234712 * 2 ^ 59
def prefixEnd_1234712 : Nat := 4983230072969 + 3 ^ 40 * 1234712 * 2
def baseEnd_1234712 : Nat := 211333575291426139107223

theorem tailTrace_1234712 : CollatzResearch.WordTrace tailWord_1234712 prefixEnd_1234712 211333575291426139107223 := by
  unfold tailWord_1234712
  simp only [CollatzResearch.WordTrace]
  refine ⟨22516823151428385433165195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30022430868571180577553593 22516823151428385433165195)
  ·
    refine ⟨33775234727142578149747793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22516823151428385433165195 33775234727142578149747793)
    ·
      refine ⟨25331426045356933612310845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33775234727142578149747793 25331426045356933612310845)
      ·
        refine ⟨9499284767008850104616567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25331426045356933612310845 9499284767008850104616567)
        ·
          refine ⟨14248927150513275156924851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9499284767008850104616567 14248927150513275156924851)
          ·
            refine ⟨21373390725769912735387277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14248927150513275156924851 21373390725769912735387277)
            ·
              refine ⟨8015021522163717275770229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21373390725769912735387277 8015021522163717275770229)
              ·
                refine ⟨751408267702848494603459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8015021522163717275770229 751408267702848494603459)
                ·
                  refine ⟨1127112401554272741905189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 751408267702848494603459 1127112401554272741905189)
                  ·
                    refine ⟨211333575291426139107223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1127112401554272741905189 211333575291426139107223)
                    ·
                      rfl

theorem cell23_1234712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 1, 4].length) (baseStart_1234712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234712 prefixEnd_1234712 := by exact prefixLift 1234712
  have htrace : WordTrace (prefixWord ++ tailWord_1234712) baseStart_1234712 baseEnd_1234712 := by
    simpa [prefixWord, tailWord_1234712, baseEnd_1234712] using wordTrace_append hprefix tailTrace_1234712
  have hstable : (prefixWord ++ tailWord_1234712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234712).length < 2 ^ (prefixWord ++ tailWord_1234712).sum := by decide
  have hdescent : baseEnd_1234712 < baseStart_1234712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234725 : List Nat := [1, 3, 1, 2, 3, 2, 3, 2, 6]
def baseStart_1234725 : Nat := 118140960795 + 1234725 * 2 ^ 59
def prefixEnd_1234725 : Nat := 4983230072969 + 3 ^ 40 * 1234725 * 2
def baseEnd_1234725 : Nat := 70445266791420762939901

theorem tailTrace_1234725 : CollatzResearch.WordTrace tailWord_1234725 prefixEnd_1234725 70445266791420762939901 := by
  unfold tailWord_1234725
  simp only [CollatzResearch.WordTrace]
  refine ⟨45034120451809674086553629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30022746967873116057702419 45034120451809674086553629)
  ·
    refine ⟨16887795169428627782457611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45034120451809674086553629 16887795169428627782457611)
    ·
      refine ⟨25331692754142941673686417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16887795169428627782457611 25331692754142941673686417)
      ·
        refine ⟨18998769565607206255264813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25331692754142941673686417 18998769565607206255264813)
        ·
          refine ⟨7124538587102702345724305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18998769565607206255264813 7124538587102702345724305)
          ·
            refine ⟨5343403940327026759293229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7124538587102702345724305 5343403940327026759293229)
            ·
              refine ⟨2003776477622635034734961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5343403940327026759293229 2003776477622635034734961)
              ·
                refine ⟨1502832358216976276051221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2003776477622635034734961 1502832358216976276051221)
                ·
                  refine ⟨70445266791420762939901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1502832358216976276051221 70445266791420762939901)
                  ·
                    rfl

theorem cell23_1234725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 6].length) (baseStart_1234725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234725 prefixEnd_1234725 := by exact prefixLift 1234725
  have htrace : WordTrace (prefixWord ++ tailWord_1234725) baseStart_1234725 baseEnd_1234725 := by
    simpa [prefixWord, tailWord_1234725, baseEnd_1234725] using wordTrace_append hprefix tailTrace_1234725
  have hstable : (prefixWord ++ tailWord_1234725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234725).length < 2 ^ (prefixWord ++ tailWord_1234725).sum := by decide
  have hdescent : baseEnd_1234725 < baseStart_1234725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234735 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 7, 1, 3]
def baseStart_1234735 : Nat := 118140960795 + 1234735 * 2 ^ 59
def prefixEnd_1234735 : Nat := 4983230072969 + 3 ^ 40 * 1234735 * 2
def baseEnd_1234735 : Nat := 634012535929331827334063

theorem tailTrace_1234735 : CollatzResearch.WordTrace tailWord_1234735 prefixEnd_1234735 634012535929331827334063 := by
  unfold tailWord_1234735
  simp only [CollatzResearch.WordTrace]
  refine ⟨45034485181773445794417659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30022990121182297196278439 45034485181773445794417659)
  ·
    refine ⟨67551727772660168691626489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45034485181773445794417659 67551727772660168691626489)
    ·
      refine ⟨50663795829495126518719867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67551727772660168691626489 50663795829495126518719867)
      ·
        refine ⟨75995693744242689778079801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50663795829495126518719867 75995693744242689778079801)
        ·
          refine ⟨56996770308182017333559851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75995693744242689778079801 56996770308182017333559851)
          ·
            refine ⟨85495155462273026000339777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56996770308182017333559851 85495155462273026000339777)
            ·
              refine ⟨64121366596704769500254833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85495155462273026000339777 64121366596704769500254833)
              ·
                refine ⟨48091024947528577125191125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64121366596704769500254833 48091024947528577125191125)
                ·
                  refine ⟨1127133397207701026371667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 48091024947528577125191125 1127133397207701026371667)
                  ·
                    refine ⟨1690700095811551539557501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1127133397207701026371667 1690700095811551539557501)
                    ·
                      refine ⟨634012535929331827334063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1690700095811551539557501 634012535929331827334063)
                      ·
                        rfl

theorem cell23_1234735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 1, 3].length) (baseStart_1234735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234735 prefixEnd_1234735 := by exact prefixLift 1234735
  have htrace : WordTrace (prefixWord ++ tailWord_1234735) baseStart_1234735 baseEnd_1234735 := by
    simpa [prefixWord, tailWord_1234735, baseEnd_1234735] using wordTrace_append hprefix tailTrace_1234735
  have hstable : (prefixWord ++ tailWord_1234735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234735).length < 2 ^ (prefixWord ++ tailWord_1234735).sum := by decide
  have hdescent : baseEnd_1234735 < baseStart_1234735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234748 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_1234748 : Nat := 118140960795 + 1234748 * 2 ^ 59
def prefixEnd_1234748 : Nat := 4983230072969 + 3 ^ 40 * 1234748 * 2
def baseEnd_1234748 : Nat := 634019211177840276471503

theorem tailTrace_1234748 : CollatzResearch.WordTrace tailWord_1234748 prefixEnd_1234748 634019211177840276471503 := by
  unfold tailWord_1234748
  simp only [CollatzResearch.WordTrace]
  refine ⟨22517479665363174507320449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30023306220484232676427265 22517479665363174507320449)
  ·
    refine ⟨16888109749022380880490337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22517479665363174507320449 16888109749022380880490337)
    ·
      refine ⟨12666082311766785660367753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16888109749022380880490337 12666082311766785660367753)
      ·
        refine ⟨9499561733825089245275815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12666082311766785660367753 9499561733825089245275815)
        ·
          refine ⟨14249342600737633867913723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9499561733825089245275815 14249342600737633867913723)
          ·
            refine ⟨21374013901106450801870585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14249342600737633867913723 21374013901106450801870585)
            ·
              refine ⟨16030510425829838101402939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21374013901106450801870585 16030510425829838101402939)
              ·
                refine ⟨24045765638744757152104409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16030510425829838101402939 24045765638744757152104409)
                ·
                  refine ⟨18034324229058567864078307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24045765638744757152104409 18034324229058567864078307)
                  ·
                    refine ⟨27051486343587851796117461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18034324229058567864078307 27051486343587851796117461)
                    ·
                      refine ⟨634019211177840276471503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27051486343587851796117461 634019211177840276471503)
                      ·
                        rfl

theorem cell23_1234748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_1234748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234748 prefixEnd_1234748 := by exact prefixLift 1234748
  have htrace : WordTrace (prefixWord ++ tailWord_1234748) baseStart_1234748 baseEnd_1234748 := by
    simpa [prefixWord, tailWord_1234748, baseEnd_1234748] using wordTrace_append hprefix tailTrace_1234748
  have hstable : (prefixWord ++ tailWord_1234748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234748).length < 2 ^ (prefixWord ++ tailWord_1234748).sum := by decide
  have hdescent : baseEnd_1234748 < baseStart_1234748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234755 : List Nat := [1, 1, 1, 3, 1, 5, 1, 4, 1, 5]
def baseStart_1234755 : Nat := 118140960795 + 1234755 * 2 ^ 59
def prefixEnd_1234755 : Nat := 4983230072969 + 3 ^ 40 * 1234755 * 2
def baseEnd_1234755 : Nat := 211340935180807249694657

theorem tailTrace_1234755 : CollatzResearch.WordTrace tailWord_1234755 prefixEnd_1234755 211340935180807249694657 := by
  unfold tailWord_1234755
  simp only [CollatzResearch.WordTrace]
  refine ⟨45035214641700989210145719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30023476427800659473430479 45035214641700989210145719)
  ·
    refine ⟨67552821962551483815218579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45035214641700989210145719 67552821962551483815218579)
    ·
      refine ⟨101329232943827225722827869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67552821962551483815218579 101329232943827225722827869)
      ·
        refine ⟨37998462353935209646060451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101329232943827225722827869 37998462353935209646060451)
        ·
          refine ⟨56997693530902814469090677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37998462353935209646060451 56997693530902814469090677)
          ·
            refine ⟨5343533768522138856477251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56997693530902814469090677 5343533768522138856477251)
            ·
              refine ⟨8015300652783208284715877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5343533768522138856477251 8015300652783208284715877)
              ·
                refine ⟨1502868872396851553384227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8015300652783208284715877 1502868872396851553384227)
                ·
                  refine ⟨2254303308595277330076341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502868872396851553384227 2254303308595277330076341)
                  ·
                    refine ⟨211340935180807249694657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2254303308595277330076341 211340935180807249694657)
                    ·
                      rfl

theorem cell23_1234755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 5].length) (baseStart_1234755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234755 prefixEnd_1234755 := by exact prefixLift 1234755
  have htrace : WordTrace (prefixWord ++ tailWord_1234755) baseStart_1234755 baseEnd_1234755 := by
    simpa [prefixWord, tailWord_1234755, baseEnd_1234755] using wordTrace_append hprefix tailTrace_1234755
  have hstable : (prefixWord ++ tailWord_1234755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234755).length < 2 ^ (prefixWord ++ tailWord_1234755).sum := by decide
  have hdescent : baseEnd_1234755 < baseStart_1234755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234762 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 2, 3, 2]
def baseStart_1234762 : Nat := 118140960795 + 1234762 * 2 ^ 59
def prefixEnd_1234762 : Nat := 4983230072969 + 3 ^ 40 * 1234762 * 2
def baseEnd_1234762 : Nat := 634026399907003221696439

theorem tailTrace_1234762 : CollatzResearch.WordTrace tailWord_1234762 prefixEnd_1234762 634026399907003221696439 := by
  unfold tailWord_1234762
  simp only [CollatzResearch.WordTrace]
  refine ⟨11258867488168907351412635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30023646635117086270433693 11258867488168907351412635)
  ·
    refine ⟨16888301232253361027118953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11258867488168907351412635 16888301232253361027118953)
    ·
      refine ⟨12666225924190020770339215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16888301232253361027118953 12666225924190020770339215)
      ·
        refine ⟨18999338886285031155508823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12666225924190020770339215 18999338886285031155508823)
        ·
          refine ⟨28499008329427546733263235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18999338886285031155508823 28499008329427546733263235)
          ·
            refine ⟨42748512494141320099894853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28499008329427546733263235 42748512494141320099894853)
            ·
              refine ⟨8015346092651497518730285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42748512494141320099894853 8015346092651497518730285)
              ·
                refine ⟨3005754784744311569523857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8015346092651497518730285 3005754784744311569523857)
                ·
                  refine ⟨2254316088558233677142893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3005754784744311569523857 2254316088558233677142893)
                  ·
                    refine ⟨845368533209337628928585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2254316088558233677142893 845368533209337628928585)
                    ·
                      refine ⟨634026399907003221696439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 845368533209337628928585 634026399907003221696439)
                      ·
                        rfl

theorem cell23_1234762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_1234762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234762 prefixEnd_1234762 := by exact prefixLift 1234762
  have htrace : WordTrace (prefixWord ++ tailWord_1234762) baseStart_1234762 baseEnd_1234762 := by
    simpa [prefixWord, tailWord_1234762, baseEnd_1234762] using wordTrace_append hprefix tailTrace_1234762
  have hstable : (prefixWord ++ tailWord_1234762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234762).length < 2 ^ (prefixWord ++ tailWord_1234762).sum := by decide
  have hdescent : baseEnd_1234762 < baseStart_1234762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234768 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 3, 6]
def baseStart_1234768 : Nat := 118140960795 + 1234768 * 2 ^ 59
def prefixEnd_1234768 : Nat := 4983230072969 + 3 ^ 40 * 1234768 * 2
def baseEnd_1234768 : Nat := 211343160263643399407137

theorem tailTrace_1234768 : CollatzResearch.WordTrace tailWord_1234768 prefixEnd_1234768 211343160263643399407137 := by
  unfold tailWord_1234768
  simp only [CollatzResearch.WordTrace]
  refine ⟨22517844395326946215184479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30023792527102594953579305 22517844395326946215184479)
  ·
    refine ⟨33776766592990419322776719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22517844395326946215184479 33776766592990419322776719)
    ·
      refine ⟨50665149889485628984165079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33776766592990419322776719 50665149889485628984165079)
      ·
        refine ⟨75997724834228443476247619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50665149889485628984165079 75997724834228443476247619)
        ·
          refine ⟨113996587251342665214371429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75997724834228443476247619 113996587251342665214371429)
          ·
            refine ⟨21374360109626749727694643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113996587251342665214371429 21374360109626749727694643)
            ·
              refine ⟨32061540164440124591541965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21374360109626749727694643 32061540164440124591541965)
              ·
                refine ⟨12023077561665046721828237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32061540164440124591541965 12023077561665046721828237)
                ·
                  refine ⟨4508654085624392520685589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12023077561665046721828237 4508654085624392520685589)
                  ·
                    refine ⟨211343160263643399407137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4508654085624392520685589 211343160263643399407137)
                    ·
                      rfl

theorem cell23_1234768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 3, 6].length) (baseStart_1234768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234768 prefixEnd_1234768 := by exact prefixLift 1234768
  have htrace : WordTrace (prefixWord ++ tailWord_1234768) baseStart_1234768 baseEnd_1234768 := by
    simpa [prefixWord, tailWord_1234768, baseEnd_1234768] using wordTrace_append hprefix tailTrace_1234768
  have hstable : (prefixWord ++ tailWord_1234768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234768).length < 2 ^ (prefixWord ++ tailWord_1234768).sum := by decide
  have hdescent : baseEnd_1234768 < baseStart_1234768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234772 : List Nat := [2, 4, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_1234772 : Nat := 118140960795 + 1234772 * 2 ^ 59
def prefixEnd_1234772 : Nat := 4983230072969 + 3 ^ 40 * 1234772 * 2
def baseEnd_1234772 : Nat := 211343844904516060857131

theorem tailTrace_1234772 : CollatzResearch.WordTrace tailWord_1234772 prefixEnd_1234772 211343844904516060857131 := by
  unfold tailWord_1234772
  simp only [CollatzResearch.WordTrace]
  refine ⟨22517917341319700556757285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30023889788426267409009713 22517917341319700556757285)
  ·
    refine ⟨4222109501497443854391991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22517917341319700556757285 4222109501497443854391991)
    ·
      refine ⟨6333164252246165781587987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4222109501497443854391991 6333164252246165781587987)
      ·
        refine ⟨9499746378369248672381981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6333164252246165781587987 9499746378369248672381981)
        ·
          refine ⟨3562404891888468252143243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9499746378369248672381981 3562404891888468252143243)
          ·
            refine ⟨5343607337832702378214865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562404891888468252143243 5343607337832702378214865)
            ·
              refine ⟨4007705503374526783661149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5343607337832702378214865 4007705503374526783661149)
              ·
                refine ⟨1502889563765447543872931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4007705503374526783661149 1502889563765447543872931)
                ·
                  refine ⟨2254334345648171315809397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502889563765447543872931 2254334345648171315809397)
                  ·
                    refine ⟨211343844904516060857131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2254334345648171315809397 211343844904516060857131)
                    ·
                      rfl

theorem cell23_1234772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_1234772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234772 prefixEnd_1234772 := by exact prefixLift 1234772
  have htrace : WordTrace (prefixWord ++ tailWord_1234772) baseStart_1234772 baseEnd_1234772 := by
    simpa [prefixWord, tailWord_1234772, baseEnd_1234772] using wordTrace_append hprefix tailTrace_1234772
  have hstable : (prefixWord ++ tailWord_1234772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234772).length < 2 ^ (prefixWord ++ tailWord_1234772).sum := by decide
  have hdescent : baseEnd_1234772 < baseStart_1234772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234785 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 4, 4]
def baseStart_1234785 : Nat := 118140960795 + 1234785 * 2 ^ 59
def prefixEnd_1234785 : Nat := 4983230072969 + 3 ^ 40 * 1234785 * 2
def baseEnd_1234785 : Nat := 211346069987352210569611

theorem tailTrace_1234785 : CollatzResearch.WordTrace tailWord_1234785 prefixEnd_1234785 211346069987352210569611 := by
  unfold tailWord_1234785
  simp only [CollatzResearch.WordTrace]
  refine ⟨45036308831592304333737809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30024205887728202889158539 45036308831592304333737809)
  ·
    refine ⟨33777231623694228250303357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45036308831592304333737809 33777231623694228250303357)
    ·
      refine ⟨12666461858885335593863759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33777231623694228250303357 12666461858885335593863759)
      ·
        refine ⟨18999692788328003390795639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12666461858885335593863759 18999692788328003390795639)
        ·
          refine ⟨28499539182492005086193459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18999692788328003390795639 28499539182492005086193459)
          ·
            refine ⟨42749308773738007629290189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28499539182492005086193459 42749308773738007629290189)
            ·
              refine ⟨16030990790151752860983821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42749308773738007629290189 16030990790151752860983821)
              ·
                refine ⟨6011621546306907322868933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16030990790151752860983821 6011621546306907322868933)
                ·
                  refine ⟨1127179039932545123037925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6011621546306907322868933 1127179039932545123037925)
                  ·
                    refine ⟨211346069987352210569611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1127179039932545123037925 211346069987352210569611)
                    ·
                      rfl

theorem cell23_1234785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_1234785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234785 prefixEnd_1234785 := by exact prefixLift 1234785
  have htrace : WordTrace (prefixWord ++ tailWord_1234785) baseStart_1234785 baseEnd_1234785 := by
    simpa [prefixWord, tailWord_1234785, baseEnd_1234785] using wordTrace_append hprefix tailTrace_1234785
  have hstable : (prefixWord ++ tailWord_1234785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234785).length < 2 ^ (prefixWord ++ tailWord_1234785).sum := by decide
  have hdescent : baseEnd_1234785 < baseStart_1234785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234786 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_1234786 : Nat := 118140960795 + 1234786 * 2 ^ 59
def prefixEnd_1234786 : Nat := 4983230072969 + 3 ^ 40 * 1234786 * 2
def baseEnd_1234786 : Nat := 634038723442711127796329

theorem tailTrace_1234786 : CollatzResearch.WordTrace tailWord_1234786 prefixEnd_1234786 634038723442711127796329 := by
  unfold tailWord_1234786
  simp only [CollatzResearch.WordTrace]
  refine ⟨11259086326147170376131053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30024230203059121003016141 11259086326147170376131053)
  ·
    refine ⟨4222157372305188891049145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11259086326147170376131053 4222157372305188891049145)
    ·
      refine ⟨3166618029228891668286859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4222157372305188891049145 3166618029228891668286859)
      ·
        refine ⟨4749927043843337502430289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3166618029228891668286859 4749927043843337502430289)
        ·
          refine ⟨3562445282882503126822717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4749927043843337502430289 3562445282882503126822717)
          ·
            refine ⟨1335916981080938672558519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3562445282882503126822717 1335916981080938672558519)
            ·
              refine ⟨2003875471621408008837779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335916981080938672558519 2003875471621408008837779)
              ·
                refine ⟨3005813207432112013256669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003875471621408008837779 3005813207432112013256669)
                ·
                  refine ⟨1127179952787042004971251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3005813207432112013256669 1127179952787042004971251)
                  ·
                    refine ⟨1690769929180563007456877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1127179952787042004971251 1690769929180563007456877)
                    ·
                      refine ⟨634038723442711127796329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1690769929180563007456877 634038723442711127796329)
                      ·
                        rfl

theorem cell23_1234786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_1234786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234786 prefixEnd_1234786 := by exact prefixLift 1234786
  have htrace : WordTrace (prefixWord ++ tailWord_1234786) baseStart_1234786 baseEnd_1234786 := by
    simpa [prefixWord, tailWord_1234786, baseEnd_1234786] using wordTrace_append hprefix tailTrace_1234786
  have hstable : (prefixWord ++ tailWord_1234786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234786).length < 2 ^ (prefixWord ++ tailWord_1234786).sum := by decide
  have hdescent : baseEnd_1234786 < baseStart_1234786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234795 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 3]
def baseStart_1234795 : Nat := 118140960795 + 1234795 * 2 ^ 59
def prefixEnd_1234795 : Nat := 4983230072969 + 3 ^ 40 * 1234795 * 2
def baseEnd_1234795 : Nat := 634043344768601592583787

theorem tailTrace_1234795 : CollatzResearch.WordTrace tailWord_1234795 prefixEnd_1234795 634043344768601592583787 := by
  unfold tailWord_1234795
  simp only [CollatzResearch.WordTrace]
  refine ⟨45036673561556076041601839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30024449041037384027734559 45036673561556076041601839)
  ·
    refine ⟨67555010342334114062402759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45036673561556076041601839 67555010342334114062402759)
    ·
      refine ⟨101332515513501171093604139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67555010342334114062402759 101332515513501171093604139)
      ·
        refine ⟨151998773270251756640406209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101332515513501171093604139 151998773270251756640406209)
        ·
          refine ⟨113999079952688817480304657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151998773270251756640406209 113999079952688817480304657)
          ·
            refine ⟨85499309964516613110228493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113999079952688817480304657 85499309964516613110228493)
            ·
              refine ⟨32062241236693729916335685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85499309964516613110228493 32062241236693729916335685)
              ·
                refine ⟨6011670231880074359312941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32062241236693729916335685 6011670231880074359312941)
                ·
                  refine ⟨2254376336955027884742353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6011670231880074359312941 2254376336955027884742353)
                  ·
                    refine ⟨1690782252716270913556765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2254376336955027884742353 1690782252716270913556765)
                    ·
                      refine ⟨634043344768601592583787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1690782252716270913556765 634043344768601592583787)
                      ·
                        rfl

theorem cell23_1234795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 3].length) (baseStart_1234795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234795 prefixEnd_1234795 := by exact prefixLift 1234795
  have htrace : WordTrace (prefixWord ++ tailWord_1234795) baseStart_1234795 baseEnd_1234795 := by
    simpa [prefixWord, tailWord_1234795, baseEnd_1234795] using wordTrace_append hprefix tailTrace_1234795
  have hstable : (prefixWord ++ tailWord_1234795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234795).length < 2 ^ (prefixWord ++ tailWord_1234795).sum := by decide
  have hdescent : baseEnd_1234795 < baseStart_1234795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234805 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1234805 : Nat := 118140960795 + 1234805 * 2 ^ 59
def prefixEnd_1234805 : Nat := 4983230072969 + 3 ^ 40 * 1234805 * 2
def baseEnd_1234805 : Nat := 634048479575146553458741

theorem tailTrace_1234805 : CollatzResearch.WordTrace tailWord_1234805 prefixEnd_1234805 634048479575146553458741 := by
  unfold tailWord_1234805
  simp only [CollatzResearch.WordTrace]
  refine ⟨45037038291519847749465869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30024692194346565166310579 45037038291519847749465869)
  ·
    refine ⟨16888889359319942906049701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45037038291519847749465869 16888889359319942906049701)
    ·
      refine ⟨3166666754872489294884319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16888889359319942906049701 3166666754872489294884319)
      ·
        refine ⟨4750000132308733942326479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3166666754872489294884319 4750000132308733942326479)
        ·
          refine ⟨7125000198463100913489719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4750000132308733942326479 7125000198463100913489719)
          ·
            refine ⟨10687500297694651370234579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7125000198463100913489719 10687500297694651370234579)
            ·
              refine ⟨16031250446541977055351869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10687500297694651370234579 16031250446541977055351869)
              ·
                refine ⟨6011718917453241395756951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16031250446541977055351869 6011718917453241395756951)
                ·
                  refine ⟨9017578376179862093635427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6011718917453241395756951 9017578376179862093635427)
                  ·
                    refine ⟨13526367564269793140453141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9017578376179862093635427 13526367564269793140453141)
                    ·
                      refine ⟨634048479575146553458741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13526367564269793140453141 634048479575146553458741)
                      ·
                        rfl

theorem cell23_1234805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1234805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234805 prefixEnd_1234805 := by exact prefixLift 1234805
  have htrace : WordTrace (prefixWord ++ tailWord_1234805) baseStart_1234805 baseEnd_1234805 := by
    simpa [prefixWord, tailWord_1234805, baseEnd_1234805] using wordTrace_append hprefix tailTrace_1234805
  have hstable : (prefixWord ++ tailWord_1234805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234805).length < 2 ^ (prefixWord ++ tailWord_1234805).sum := by decide
  have hdescent : baseEnd_1234805 < baseStart_1234805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234806 : List Nat := [5, 1, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_1234806 : Nat := 118140960795 + 1234806 * 2 ^ 59
def prefixEnd_1234806 : Nat := 4983230072969 + 3 ^ 40 * 1234806 * 2
def baseEnd_1234806 : Nat := 211349664351933683182079

theorem tailTrace_1234806 : CollatzResearch.WordTrace tailWord_1234806 prefixEnd_1234806 211349664351933683182079 := by
  unfold tailWord_1234806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2814817172782264057515767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30024716509677483280168181 2814817172782264057515767)
  ·
    refine ⟨4222225759173396086273651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2814817172782264057515767 4222225759173396086273651)
    ·
      refine ⟨6333338638760094129410477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4222225759173396086273651 6333338638760094129410477)
      ·
        refine ⟨2375001989535035298528929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6333338638760094129410477 2375001989535035298528929)
        ·
          refine ⟨1781251492151276473896697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2375001989535035298528929 1781251492151276473896697)
          ·
            refine ⟨1335938619113457355422523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1781251492151276473896697 1335938619113457355422523)
            ·
              refine ⟨2003907928670186033133785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335938619113457355422523 2003907928670186033133785)
              ·
                refine ⟨1502930946502639524850339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2003907928670186033133785 1502930946502639524850339)
                ·
                  refine ⟨2254396419753959287275509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502930946502639524850339 2254396419753959287275509)
                  ·
                    refine ⟨211349664351933683182079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2254396419753959287275509 211349664351933683182079)
                    ·
                      rfl

theorem cell23_1234806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_1234806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234806 prefixEnd_1234806 := by exact prefixLift 1234806
  have htrace : WordTrace (prefixWord ++ tailWord_1234806) baseStart_1234806 baseEnd_1234806 := by
    simpa [prefixWord, tailWord_1234806, baseEnd_1234806] using wordTrace_append hprefix tailTrace_1234806
  have hstable : (prefixWord ++ tailWord_1234806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234806).length < 2 ^ (prefixWord ++ tailWord_1234806).sum := by decide
  have hdescent : baseEnd_1234806 < baseStart_1234806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234826 : List Nat := [3, 1, 2, 4, 2, 1, 3, 1, 1, 1, 4]
def baseStart_1234826 : Nat := 118140960795 + 1234826 * 2 ^ 59
def prefixEnd_1234826 : Nat := 4983230072969 + 3 ^ 40 * 1234826 * 2
def baseEnd_1234826 : Nat := 634059262668890971296145

theorem tailTrace_1234826 : CollatzResearch.WordTrace tailWord_1234826 prefixEnd_1234826 634059262668890971296145 := by
  unfold tailWord_1234826
  simp only [CollatzResearch.WordTrace]
  refine ⟨11259451056110942083995083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30025202816295845557320221 11259451056110942083995083)
  ·
    refine ⟨16889176584166413125992625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11259451056110942083995083 16889176584166413125992625)
    ·
      refine ⟨12666882438124809844494469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16889176584166413125992625 12666882438124809844494469)
      ·
        refine ⟨2375040457148401845842713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12666882438124809844494469 2375040457148401845842713)
        ·
          refine ⟨1781280342861301384382035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2375040457148401845842713 1781280342861301384382035)
          ·
            refine ⟨2671920514291952076573053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1781280342861301384382035 2671920514291952076573053)
            ·
              refine ⟨1001970192859482028714895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2671920514291952076573053 1001970192859482028714895)
              ·
                refine ⟨1502955289289223043072343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1001970192859482028714895 1502955289289223043072343)
                ·
                  refine ⟨2254432933933834564608515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502955289289223043072343 2254432933933834564608515)
                  ·
                    refine ⟨3381649400900751846912773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2254432933933834564608515 3381649400900751846912773)
                    ·
                      refine ⟨634059262668890971296145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3381649400900751846912773 634059262668890971296145)
                      ·
                        rfl

theorem cell23_1234826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_1234826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234826 prefixEnd_1234826 := by exact prefixLift 1234826
  have htrace : WordTrace (prefixWord ++ tailWord_1234826) baseStart_1234826 baseEnd_1234826 := by
    simpa [prefixWord, tailWord_1234826, baseEnd_1234826] using wordTrace_append hprefix tailTrace_1234826
  have hstable : (prefixWord ++ tailWord_1234826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234826).length < 2 ^ (prefixWord ++ tailWord_1234826).sum := by decide
  have hdescent : baseEnd_1234826 < baseStart_1234826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234845 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 2, 7]
def baseStart_1234845 : Nat := 118140960795 + 1234845 * 2 ^ 59
def prefixEnd_1234845 : Nat := 4983230072969 + 3 ^ 40 * 1234845 * 2
def baseEnd_1234845 : Nat := 211356339600442132319519

theorem tailTrace_1234845 : CollatzResearch.WordTrace tailWord_1234845 prefixEnd_1234845 211356339600442132319519 := by
  unfold tailWord_1234845
  simp only [CollatzResearch.WordTrace]
  refine ⟨45038497211374934580921989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30025664807583289720614659 45038497211374934580921989)
  ·
    refine ⟨8444718227132800233922873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45038497211374934580921989 8444718227132800233922873)
    ·
      refine ⟨6333538670349600175442155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8444718227132800233922873 6333538670349600175442155)
      ·
        refine ⟨9500308005524400263163233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6333538670349600175442155 9500308005524400263163233)
        ·
          refine ⟨7125231004143300197372425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9500308005524400263163233 7125231004143300197372425)
          ·
            refine ⟨5343923253107475148029319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7125231004143300197372425 5343923253107475148029319)
            ·
              refine ⟨8015884879661212722043979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5343923253107475148029319 8015884879661212722043979)
              ·
                refine ⟨12023827319491819083065969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8015884879661212722043979 12023827319491819083065969)
                ·
                  refine ⟨9017870489618864312299477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12023827319491819083065969 9017870489618864312299477)
                  ·
                    refine ⟨211356339600442132319519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9017870489618864312299477 211356339600442132319519)
                    ·
                      rfl

theorem cell23_1234845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_1234845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234845 prefixEnd_1234845 := by exact prefixLift 1234845
  have htrace : WordTrace (prefixWord ++ tailWord_1234845) baseStart_1234845 baseEnd_1234845 := by
    simpa [prefixWord, tailWord_1234845, baseEnd_1234845] using wordTrace_append hprefix tailTrace_1234845
  have hstable : (prefixWord ++ tailWord_1234845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234845).length < 2 ^ (prefixWord ++ tailWord_1234845).sum := by decide
  have hdescent : baseEnd_1234845 < baseStart_1234845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234849 : List Nat := [1, 2, 3, 4, 3, 1, 1, 8]
def baseStart_1234849 : Nat := 118140960795 + 1234849 * 2 ^ 59
def prefixEnd_1234849 : Nat := 4983230072969 + 3 ^ 40 * 1234849 * 2
def baseEnd_1234849 : Nat := 23484113804590532641057

theorem tailTrace_1234849 : CollatzResearch.WordTrace tailWord_1234849 prefixEnd_1234849 23484113804590532641057 := by
  unfold tailWord_1234849
  simp only [CollatzResearch.WordTrace]
  refine ⟨45038643103360443264067601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30025762068906962176045067 45038643103360443264067601)
  ·
    refine ⟨33778982327520332448050701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45038643103360443264067601 33778982327520332448050701)
    ·
      refine ⟨12667118372820124668019013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33778982327520332448050701 12667118372820124668019013)
      ·
        refine ⟨2375084694903773375253565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12667118372820124668019013 2375084694903773375253565)
        ·
          refine ⟨890656760588915015720087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2375084694903773375253565 890656760588915015720087)
          ·
            refine ⟨1335985140883372523580131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 890656760588915015720087 1335985140883372523580131)
            ·
              refine ⟨2003977711325058785370197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335985140883372523580131 2003977711325058785370197)
              ·
                refine ⟨23484113804590532641057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2003977711325058785370197 23484113804590532641057)
                ·
                  rfl

theorem cell23_1234849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 8].length) (baseStart_1234849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234849 prefixEnd_1234849 := by exact prefixLift 1234849
  have htrace : WordTrace (prefixWord ++ tailWord_1234849) baseStart_1234849 baseEnd_1234849 := by
    simpa [prefixWord, tailWord_1234849, baseEnd_1234849] using wordTrace_append hprefix tailTrace_1234849
  have hstable : (prefixWord ++ tailWord_1234849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234849).length < 2 ^ (prefixWord ++ tailWord_1234849).sum := by decide
  have hdescent : baseEnd_1234849 < baseStart_1234849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234856 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1234856 : Nat := 118140960795 + 1234856 * 2 ^ 59
def prefixEnd_1234856 : Nat := 4983230072969 + 3 ^ 40 * 1234856 * 2
def baseEnd_1234856 : Nat := 634074667088525853921007

theorem tailTrace_1234856 : CollatzResearch.WordTrace tailWord_1234856 prefixEnd_1234856 634074667088525853921007 := by
  unfold tailWord_1234856
  simp only [CollatzResearch.WordTrace]
  refine ⟨22519449207167541729786211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30025932276223388973048281 22519449207167541729786211)
  ·
    refine ⟨33779173810751312594679317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22519449207167541729786211 33779173810751312594679317)
    ·
      refine ⟨1583398772378967777875593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33779173810751312594679317 1583398772378967777875593)
      ·
        refine ⟨1187549079284225833406695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1583398772378967777875593 1187549079284225833406695)
        ·
          refine ⟨1781323618926338750110043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187549079284225833406695 1781323618926338750110043)
          ·
            refine ⟨2671985428389508125165065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1781323618926338750110043 2671985428389508125165065)
            ·
              refine ⟨2003989071292131093873799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2671985428389508125165065 2003989071292131093873799)
              ·
                refine ⟨3005983606938196640810699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003989071292131093873799 3005983606938196640810699)
                ·
                  refine ⟨4508975410407294961216049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3005983606938196640810699 4508975410407294961216049)
                  ·
                    refine ⟨3381731557805471220912037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4508975410407294961216049 3381731557805471220912037)
                    ·
                      refine ⟨634074667088525853921007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3381731557805471220912037 634074667088525853921007)
                      ·
                        rfl

theorem cell23_1234856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1234856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234856 prefixEnd_1234856 := by exact prefixLift 1234856
  have htrace : WordTrace (prefixWord ++ tailWord_1234856) baseStart_1234856 baseEnd_1234856 := by
    simpa [prefixWord, tailWord_1234856, baseEnd_1234856] using wordTrace_append hprefix tailTrace_1234856
  have hstable : (prefixWord ++ tailWord_1234856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234856).length < 2 ^ (prefixWord ++ tailWord_1234856).sum := by decide
  have hdescent : baseEnd_1234856 < baseStart_1234856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234869 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 3, 3, 2]
def baseStart_1234869 : Nat := 118140960795 + 1234869 * 2 ^ 59
def prefixEnd_1234869 : Nat := 4983230072969 + 3 ^ 40 * 1234869 * 2
def baseEnd_1234869 : Nat := 634081342337034303058447

theorem tailTrace_1234869 : CollatzResearch.WordTrace tailWord_1234869 prefixEnd_1234869 634081342337034303058447 := by
  unfold tailWord_1234869
  simp only [CollatzResearch.WordTrace]
  refine ⟨45039372563287986679795661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30026248375525324453197107 45039372563287986679795661)
  ·
    refine ⟨16889764711232995004923373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45039372563287986679795661 16889764711232995004923373)
    ·
      refine ⟨6333661766712373126846265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16889764711232995004923373 6333661766712373126846265)
      ·
        refine ⟨4750246325034279845134699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6333661766712373126846265 4750246325034279845134699)
        ·
          refine ⟨7125369487551419767702049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4750246325034279845134699 7125369487551419767702049)
          ·
            refine ⟨5344027115663564825776537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7125369487551419767702049 5344027115663564825776537)
            ·
              refine ⟨4008020336747673619332403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5344027115663564825776537 4008020336747673619332403)
              ·
                refine ⟨6012030505121510428998605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4008020336747673619332403 6012030505121510428998605)
                ·
                  refine ⟨2254511439420566410874477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6012030505121510428998605 2254511439420566410874477)
                  ·
                    refine ⟨845441789782712404077929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2254511439420566410874477 845441789782712404077929)
                    ·
                      refine ⟨634081342337034303058447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 845441789782712404077929 634081342337034303058447)
                      ·
                        rfl

theorem cell23_1234869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_1234869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234869 prefixEnd_1234869 := by exact prefixLift 1234869
  have htrace : WordTrace (prefixWord ++ tailWord_1234869) baseStart_1234869 baseEnd_1234869 := by
    simpa [prefixWord, tailWord_1234869, baseEnd_1234869] using wordTrace_append hprefix tailTrace_1234869
  have hstable : (prefixWord ++ tailWord_1234869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234869).length < 2 ^ (prefixWord ++ tailWord_1234869).sum := by decide
  have hdescent : baseEnd_1234869 < baseStart_1234869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234885 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 1, 6, 3]
def baseStart_1234885 : Nat := 118140960795 + 1234885 * 2 ^ 59
def prefixEnd_1234885 : Nat := 4983230072969 + 3 ^ 40 * 1234885 * 2
def baseEnd_1234885 : Nat := 634089558027506240458373

theorem tailTrace_1234885 : CollatzResearch.WordTrace tailWord_1234885 prefixEnd_1234885 634089558027506240458373 := by
  unfold tailWord_1234885
  simp only [CollatzResearch.WordTrace]
  refine ⟨45039956131230021412378109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30026637420820014274918739 45039956131230021412378109)
  ·
    refine ⟨16889983549211258029641791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45039956131230021412378109 16889983549211258029641791)
    ·
      refine ⟨25334975323816887044462687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16889983549211258029641791 25334975323816887044462687)
      ·
        refine ⟨38002462985725330566694031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25334975323816887044462687 38002462985725330566694031)
        ·
          refine ⟨57003694478587995850041047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38002462985725330566694031 57003694478587995850041047)
          ·
            refine ⟨85505541717881993775061571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57003694478587995850041047 85505541717881993775061571)
            ·
              refine ⟨128258312576822990662592357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85505541717881993775061571 128258312576822990662592357)
              ·
                refine ⟨24048433608154310749236067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128258312576822990662592357 24048433608154310749236067)
                ·
                  refine ⟨36072650412231466123854101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24048433608154310749236067 36072650412231466123854101)
                  ·
                    refine ⟨1690905488073349974555661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36072650412231466123854101 1690905488073349974555661)
                    ·
                      refine ⟨634089558027506240458373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1690905488073349974555661 634089558027506240458373)
                      ·
                        rfl

theorem cell23_1234885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_1234885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234885 prefixEnd_1234885 := by exact prefixLift 1234885
  have htrace : WordTrace (prefixWord ++ tailWord_1234885) baseStart_1234885 baseEnd_1234885 := by
    simpa [prefixWord, tailWord_1234885, baseEnd_1234885] using wordTrace_append hprefix tailTrace_1234885
  have hstable : (prefixWord ++ tailWord_1234885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234885).length < 2 ^ (prefixWord ++ tailWord_1234885).sum := by decide
  have hdescent : baseEnd_1234885 < baseStart_1234885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234895 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 4]
def baseStart_1234895 : Nat := 118140960795 + 1234895 * 2 ^ 59
def prefixEnd_1234895 : Nat := 4983230072969 + 3 ^ 40 * 1234895 * 2
def baseEnd_1234895 : Nat := 634094692834051201333327

theorem tailTrace_1234895 : CollatzResearch.WordTrace tailWord_1234895 prefixEnd_1234895 634094692834051201333327 := by
  unfold tailWord_1234895
  simp only [CollatzResearch.WordTrace]
  refine ⟨45040320861193793120242139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30026880574129195413494759 45040320861193793120242139)
  ·
    refine ⟨67560481291790689680363209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45040320861193793120242139 67560481291790689680363209)
    ·
      refine ⟨50670360968843017260272407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67560481291790689680363209 50670360968843017260272407)
      ·
        refine ⟨76005541453264525890408611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50670360968843017260272407 76005541453264525890408611)
        ·
          refine ⟨114008312179896788835612917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76005541453264525890408611 114008312179896788835612917)
          ·
            refine ⟨10688279266865323953338711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114008312179896788835612917 10688279266865323953338711)
            ·
              refine ⟨16032418900297985930008067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10688279266865323953338711 16032418900297985930008067)
              ·
                refine ⟨24048628350446978895012101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16032418900297985930008067 24048628350446978895012101)
                ·
                  refine ⟨4509117815708808542814769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24048628350446978895012101 4509117815708808542814769)
                  ·
                    refine ⟨3381838361781606407111077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4509117815708808542814769 3381838361781606407111077)
                    ·
                      refine ⟨634094692834051201333327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3381838361781606407111077 634094692834051201333327)
                      ·
                        rfl

theorem cell23_1234895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_1234895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234895 prefixEnd_1234895 := by exact prefixLift 1234895
  have htrace : WordTrace (prefixWord ++ tailWord_1234895) baseStart_1234895 baseEnd_1234895 := by
    simpa [prefixWord, tailWord_1234895, baseEnd_1234895] using wordTrace_append hprefix tailTrace_1234895
  have hstable : (prefixWord ++ tailWord_1234895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234895).length < 2 ^ (prefixWord ++ tailWord_1234895).sum := by decide
  have hdescent : baseEnd_1234895 < baseStart_1234895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234935 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 8, 5]
def baseStart_1234935 : Nat := 118140960795 + 1234935 * 2 ^ 59
def prefixEnd_1234935 : Nat := 4983230072969 + 3 ^ 40 * 1234935 * 2
def baseEnd_1234935 : Nat := 211371744020077014944381

theorem tailTrace_1234935 : CollatzResearch.WordTrace tailWord_1234935 prefixEnd_1234935 211371744020077014944381 := by
  unfold tailWord_1234935
  simp only [CollatzResearch.WordTrace]
  refine ⟨45041779781048879951698259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30027853187365919967798839 45041779781048879951698259)
  ·
    refine ⟨67562669671573319927547389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45041779781048879951698259 67562669671573319927547389)
    ·
      refine ⟨25336001126839994972830271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67562669671573319927547389 25336001126839994972830271)
      ·
        refine ⟨38004001690259992459245407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25336001126839994972830271 38004001690259992459245407)
        ·
          refine ⟨57006002535389988688868111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38004001690259992459245407 57006002535389988688868111)
          ·
            refine ⟨85509003803084983033302167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57006002535389988688868111 85509003803084983033302167)
            ·
              refine ⟨128263505704627474549953251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85509003803084983033302167 128263505704627474549953251)
              ·
                refine ⟨192395258556941211824929877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128263505704627474549953251 192395258556941211824929877)
                ·
                  refine ⟨2254631936214154826073397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 192395258556941211824929877 2254631936214154826073397)
                  ·
                    refine ⟨211371744020077014944381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2254631936214154826073397 211371744020077014944381)
                    ·
                      rfl

theorem cell23_1234935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_1234935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234935 prefixEnd_1234935 := by exact prefixLift 1234935
  have htrace : WordTrace (prefixWord ++ tailWord_1234935) baseStart_1234935 baseEnd_1234935 := by
    simpa [prefixWord, tailWord_1234935, baseEnd_1234935] using wordTrace_append hprefix tailTrace_1234935
  have hstable : (prefixWord ++ tailWord_1234935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234935).length < 2 ^ (prefixWord ++ tailWord_1234935).sum := by decide
  have hdescent : baseEnd_1234935 < baseStart_1234935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234952 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 2, 5]
def baseStart_1234952 : Nat := 118140960795 + 1234952 * 2 ^ 59
def prefixEnd_1234952 : Nat := 4983230072969 + 3 ^ 40 * 1234952 * 2
def baseEnd_1234952 : Nat := 211374653743785826106855

theorem tailTrace_1234952 : CollatzResearch.WordTrace tailWord_1234952 prefixEnd_1234952 211374653743785826106855 := by
  unfold tailWord_1234952
  simp only [CollatzResearch.WordTrace]
  refine ⟨22521199910993645927533555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30028266547991527903378073 22521199910993645927533555)
  ·
    refine ⟨33781799866490468891300333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22521199910993645927533555 33781799866490468891300333)
    ·
      refine ⟨12668174949933925834237625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33781799866490468891300333 12668174949933925834237625)
      ·
        refine ⟨9501131212450444375678219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12668174949933925834237625 9501131212450444375678219)
        ·
          refine ⟨14251696818675666563517329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9501131212450444375678219 14251696818675666563517329)
          ·
            refine ⟨10688772614006749922637997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14251696818675666563517329 10688772614006749922637997)
            ·
              refine ⟨4008289730252531220989249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10688772614006749922637997 4008289730252531220989249)
              ·
                refine ⟨3006217297689398415741937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4008289730252531220989249 3006217297689398415741937)
                ·
                  refine ⟨2254662973267048811806453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3006217297689398415741937 2254662973267048811806453)
                  ·
                    refine ⟨211374653743785826106855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2254662973267048811806453 211374653743785826106855)
                    ·
                      rfl

theorem cell23_1234952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_1234952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234952 prefixEnd_1234952 := by exact prefixLift 1234952
  have htrace : WordTrace (prefixWord ++ tailWord_1234952) baseStart_1234952 baseEnd_1234952 := by
    simpa [prefixWord, tailWord_1234952, baseEnd_1234952] using wordTrace_append hprefix tailTrace_1234952
  have hstable : (prefixWord ++ tailWord_1234952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234952).length < 2 ^ (prefixWord ++ tailWord_1234952).sum := by decide
  have hdescent : baseEnd_1234952 < baseStart_1234952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234967 : List Nat := [1, 1, 3, 5, 3, 1, 2, 1, 2, 2, 2]
def baseStart_1234967 : Nat := 118140960795 + 1234967 * 2 ^ 59
def prefixEnd_1234967 : Nat := 4983230072969 + 3 ^ 40 * 1234967 * 2
def baseEnd_1234967 : Nat := 634131663441174919632997

theorem tailTrace_1234967 : CollatzResearch.WordTrace tailWord_1234967 prefixEnd_1234967 634131663441174919632997 := by
  unfold tailWord_1234967
  simp only [CollatzResearch.WordTrace]
  refine ⟨45042946916932949416863155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30028631277955299611242103 45042946916932949416863155)
  ·
    refine ⟨67564420375399424125294733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45042946916932949416863155 67564420375399424125294733)
    ·
      refine ⟨25336657640774784046985525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67564420375399424125294733 25336657640774784046985525)
      ·
        refine ⟨2375311653822636004404893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25336657640774784046985525 2375311653822636004404893)
        ·
          refine ⟨890741870183488501651835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2375311653822636004404893 890741870183488501651835)
          ·
            refine ⟨1336112805275232752477753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 890741870183488501651835 1336112805275232752477753)
            ·
              refine ⟨1002084603956424564358315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1336112805275232752477753 1002084603956424564358315)
              ·
                refine ⟨1503126905934636846537473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002084603956424564358315 1503126905934636846537473)
                ·
                  refine ⟨1127345179450977634903105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1503126905934636846537473 1127345179450977634903105)
                  ·
                    refine ⟨845508884588233226177329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1127345179450977634903105 845508884588233226177329)
                    ·
                      refine ⟨634131663441174919632997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 845508884588233226177329 634131663441174919632997)
                      ·
                        rfl

theorem cell23_1234967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_1234967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234967 prefixEnd_1234967 := by exact prefixLift 1234967
  have htrace : WordTrace (prefixWord ++ tailWord_1234967) baseStart_1234967 baseEnd_1234967 := by
    simpa [prefixWord, tailWord_1234967, baseEnd_1234967] using wordTrace_append hprefix tailTrace_1234967
  have hstable : (prefixWord ++ tailWord_1234967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234967).length < 2 ^ (prefixWord ++ tailWord_1234967).sum := by decide
  have hdescent : baseEnd_1234967 < baseStart_1234967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234995 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 10]
def baseStart_1234995 : Nat := 118140960795 + 1234995 * 2 ^ 59
def prefixEnd_1234995 : Nat := 4983230072969 + 3 ^ 40 * 1234995 * 2
def baseEnd_1234995 : Nat := 70460671211055645564763

theorem tailTrace_1234995 : CollatzResearch.WordTrace tailWord_1234995 prefixEnd_1234995 70460671211055645564763 := by
  unfold tailWord_1234995
  simp only [CollatzResearch.WordTrace]
  refine ⟨45043968160831510198882439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30029312107221006799254959 45043968160831510198882439)
  ·
    refine ⟨67565952241247265298323659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45043968160831510198882439 67565952241247265298323659)
    ·
      refine ⟨101348928361870897947485489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67565952241247265298323659 101348928361870897947485489)
      ·
        refine ⟨76011696271403173460614117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101348928361870897947485489 76011696271403173460614117)
        ·
          refine ⟨14252193050888095023865147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76011696271403173460614117 14252193050888095023865147)
          ·
            refine ⟨21378289576332142535797721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14252193050888095023865147 21378289576332142535797721)
            ·
              refine ⟨16033717182249106901848291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21378289576332142535797721 16033717182249106901848291)
              ·
                refine ⟨24050575773373660352772437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16033717182249106901848291 24050575773373660352772437)
                ·
                  refine ⟨70460671211055645564763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 24050575773373660352772437 70460671211055645564763)
                  ·
                    rfl

theorem cell23_1234995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 10].length) (baseStart_1234995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1234995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1234995 prefixEnd_1234995 := by exact prefixLift 1234995
  have htrace : WordTrace (prefixWord ++ tailWord_1234995) baseStart_1234995 baseEnd_1234995 := by
    simpa [prefixWord, tailWord_1234995, baseEnd_1234995] using wordTrace_append hprefix tailTrace_1234995
  have hstable : (prefixWord ++ tailWord_1234995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234995).length < 2 ^ (prefixWord ++ tailWord_1234995).sum := by decide
  have hdescent : baseEnd_1234995 < baseStart_1234995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235049 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 1, 5, 2]
def baseStart_1235049 : Nat := 118140960795 + 1235049 * 2 ^ 59
def prefixEnd_1235049 : Nat := 4983230072969 + 3 ^ 40 * 1235049 * 2
def baseEnd_1235049 : Nat := 634173768854843598807619

theorem tailTrace_1235049 : CollatzResearch.WordTrace tailWord_1235049 prefixEnd_1235049 634173768854843598807619 := by
  unfold tailWord_1235049
  simp only [CollatzResearch.WordTrace]
  refine ⟨45045937702635877421348201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30030625135090584947565467 45045937702635877421348201)
  ·
    refine ⟨33784453276976908066011151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45045937702635877421348201 33784453276976908066011151)
    ·
      refine ⟨50676679915465362099016727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33784453276976908066011151 50676679915465362099016727)
      ·
        refine ⟨76015019873198043148525091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50676679915465362099016727 76015019873198043148525091)
        ·
          refine ⟨114022529809797064722787637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76015019873198043148525091 114022529809797064722787637)
          ·
            refine ⟨10689612169668474817761341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114022529809797064722787637 10689612169668474817761341)
            ·
              refine ⟨4008604563625678056660503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10689612169668474817761341 4008604563625678056660503)
              ·
                refine ⟨6012906845438517084990755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4008604563625678056660503 6012906845438517084990755)
                ·
                  refine ⟨9019360268157775627486133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6012906845438517084990755 9019360268157775627486133)
                  ·
                    refine ⟨845565025139791465076825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9019360268157775627486133 845565025139791465076825)
                    ·
                      refine ⟨634173768854843598807619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 845565025139791465076825 634173768854843598807619)
                      ·
                        rfl

theorem cell23_1235049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 5, 2].length) (baseStart_1235049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235049 prefixEnd_1235049 := by exact prefixLift 1235049
  have htrace : WordTrace (prefixWord ++ tailWord_1235049) baseStart_1235049 baseEnd_1235049 := by
    simpa [prefixWord, tailWord_1235049, baseEnd_1235049] using wordTrace_append hprefix tailTrace_1235049
  have hstable : (prefixWord ++ tailWord_1235049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235049).length < 2 ^ (prefixWord ++ tailWord_1235049).sum := by decide
  have hdescent : baseEnd_1235049 < baseStart_1235049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235073 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_1235073 : Nat := 118140960795 + 1235073 * 2 ^ 59
def prefixEnd_1235073 : Nat := 4983230072969 + 3 ^ 40 * 1235073 * 2
def baseEnd_1235073 : Nat := 634186092390551504907509

theorem tailTrace_1235073 : CollatzResearch.WordTrace tailWord_1235073 prefixEnd_1235073 634186092390551504907509 := by
  unfold tailWord_1235073
  simp only [CollatzResearch.WordTrace]
  refine ⟨45046813054548929520221873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30031208703032619680147915 45046813054548929520221873)
  ·
    refine ⟨33785109790911697140166405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45046813054548929520221873 33785109790911697140166405)
    ·
      refine ⟨6334708085795943213781201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33785109790911697140166405 6334708085795943213781201)
      ·
        refine ⟨4751031064346957410335901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6334708085795943213781201 4751031064346957410335901)
        ·
          refine ⟨1781636649130109028875963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4751031064346957410335901 1781636649130109028875963)
          ·
            refine ⟨2672454973695163543313945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1781636649130109028875963 2672454973695163543313945)
            ·
              refine ⟨2004341230271372657485459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2672454973695163543313945 2004341230271372657485459)
              ·
                refine ⟨3006511845407058986228189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004341230271372657485459 3006511845407058986228189)
                ·
                  refine ⟨1127441942027647119835571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3006511845407058986228189 1127441942027647119835571)
                  ·
                    refine ⟨1691162913041470679753357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1127441942027647119835571 1691162913041470679753357)
                    ·
                      refine ⟨634186092390551504907509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1691162913041470679753357 634186092390551504907509)
                      ·
                        rfl

theorem cell23_1235073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_1235073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235073 prefixEnd_1235073 := by exact prefixLift 1235073
  have htrace : WordTrace (prefixWord ++ tailWord_1235073) baseStart_1235073 baseEnd_1235073 := by
    simpa [prefixWord, tailWord_1235073, baseEnd_1235073] using wordTrace_append hprefix tailTrace_1235073
  have hstable : (prefixWord ++ tailWord_1235073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235073).length < 2 ^ (prefixWord ++ tailWord_1235073).sum := by decide
  have hdescent : baseEnd_1235073 < baseStart_1235073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235106 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_1235106 : Nat := 118140960795 + 1235106 * 2 ^ 59
def prefixEnd_1235106 : Nat := 4983230072969 + 3 ^ 40 * 1235106 * 2
def baseEnd_1235106 : Nat := 211401012417383291931619

theorem tailTrace_1235106 : CollatzResearch.WordTrace tailWord_1235106 prefixEnd_1235106 211401012417383291931619 := by
  unfold tailWord_1235106
  simp only [CollatzResearch.WordTrace]
  refine ⟨11262004165857344039043293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30032011108952917437448781 11262004165857344039043293)
  ·
    refine ⟨4223251562196504014641235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11262004165857344039043293 4223251562196504014641235)
    ·
      refine ⟨6334877343294756021961853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4223251562196504014641235 6334877343294756021961853)
      ·
        refine ⟨2375579003735533508235695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6334877343294756021961853 2375579003735533508235695)
        ·
          refine ⟨3563368505603300262353543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2375579003735533508235695 3563368505603300262353543)
          ·
            refine ⟨5345052758404950393530315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3563368505603300262353543 5345052758404950393530315)
            ·
              refine ⟨8017579137607425590295473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5345052758404950393530315 8017579137607425590295473)
              ·
                refine ⟨6013184353205569192721605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8017579137607425590295473 6013184353205569192721605)
                ·
                  refine ⟨1127472066226044223635301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6013184353205569192721605 1127472066226044223635301)
                  ·
                    refine ⟨211401012417383291931619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1127472066226044223635301 211401012417383291931619)
                    ·
                      rfl

theorem cell23_1235106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_1235106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235106 prefixEnd_1235106 := by exact prefixLift 1235106
  have htrace : WordTrace (prefixWord ++ tailWord_1235106) baseStart_1235106 baseEnd_1235106 := by
    simpa [prefixWord, tailWord_1235106, baseEnd_1235106] using wordTrace_append hprefix tailTrace_1235106
  have hstable : (prefixWord ++ tailWord_1235106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235106).length < 2 ^ (prefixWord ++ tailWord_1235106).sum := by decide
  have hdescent : baseEnd_1235106 < baseStart_1235106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235124 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_1235124 : Nat := 118140960795 + 1235124 * 2 ^ 59
def prefixEnd_1235124 : Nat := 4983230072969 + 3 ^ 40 * 1235124 * 2
def baseEnd_1235124 : Nat := 634212279903930805369775

theorem tailTrace_1235124 : CollatzResearch.WordTrace tailWord_1235124 prefixEnd_1235124 634212279903930805369775 := by
  unfold tailWord_1235124
  simp only [CollatzResearch.WordTrace]
  refine ⟨22524336588682082615164213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30032448784909443486885617 22524336588682082615164213)
  ·
    refine ⟨2111656555188945245171645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22524336588682082615164213 2111656555188945245171645)
    ·
      refine ⟨791871208195854466939367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2111656555188945245171645 791871208195854466939367)
      ·
        refine ⟨1187806812293781700409051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 791871208195854466939367 1187806812293781700409051)
        ·
          refine ⟨1781710218440672550613577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187806812293781700409051 1781710218440672550613577)
          ·
            refine ⟨1336282663830504412960183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1781710218440672550613577 1336282663830504412960183)
            ·
              refine ⟨2004423995745756619440275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1336282663830504412960183 2004423995745756619440275)
              ·
                refine ⟨3006635993618634929160413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004423995745756619440275 3006635993618634929160413)
                ·
                  refine ⟨1127488497606988098435155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3006635993618634929160413 1127488497606988098435155)
                  ·
                    refine ⟨1691232746410482147652733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1127488497606988098435155 1691232746410482147652733)
                    ·
                      refine ⟨634212279903930805369775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1691232746410482147652733 634212279903930805369775)
                      ·
                        rfl

theorem cell23_1235124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_1235124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235124 prefixEnd_1235124 := by exact prefixLift 1235124
  have htrace : WordTrace (prefixWord ++ tailWord_1235124) baseStart_1235124 baseEnd_1235124 := by
    simpa [prefixWord, tailWord_1235124, baseEnd_1235124] using wordTrace_append hprefix tailTrace_1235124
  have hstable : (prefixWord ++ tailWord_1235124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235124).length < 2 ^ (prefixWord ++ tailWord_1235124).sum := by decide
  have hdescent : baseEnd_1235124 < baseStart_1235124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235140 : List Nat := [2, 3, 3, 1, 2, 3, 2, 1, 2, 4]
def baseStart_1235140 : Nat := 118140960795 + 1235140 * 2 ^ 59
def prefixEnd_1235140 : Nat := 4983230072969 + 3 ^ 40 * 1235140 * 2
def baseEnd_1235140 : Nat := 211406831864800914256567

theorem tailTrace_1235140 : CollatzResearch.WordTrace tailWord_1235140 prefixEnd_1235140 211406831864800914256567 := by
  unfold tailWord_1235140
  simp only [CollatzResearch.WordTrace]
  refine ⟨22524628372653099981455437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30032837830204133308607249 22524628372653099981455437)
  ·
    refine ⟨8446735639744912493045789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22524628372653099981455437 8446735639744912493045789)
    ·
      refine ⟨3167525864904342184892171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8446735639744912493045789 3167525864904342184892171)
      ·
        refine ⟨4751288797356513277338257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3167525864904342184892171 4751288797356513277338257)
        ·
          refine ⟨3563466598017384958003693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4751288797356513277338257 3563466598017384958003693)
          ·
            refine ⟨1336299974256519359251385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3563466598017384958003693 1336299974256519359251385)
            ·
              refine ⟨1002224980692389519438539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1336299974256519359251385 1002224980692389519438539)
              ·
                refine ⟨1503337471038584279157809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002224980692389519438539 1503337471038584279157809)
                ·
                  refine ⟨1127503103278938209368357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1503337471038584279157809 1127503103278938209368357)
                  ·
                    refine ⟨211406831864800914256567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1127503103278938209368357 211406831864800914256567)
                    ·
                      rfl

theorem cell23_1235140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_1235140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235140 prefixEnd_1235140 := by exact prefixLift 1235140
  have htrace : WordTrace (prefixWord ++ tailWord_1235140) baseStart_1235140 baseEnd_1235140 := by
    simpa [prefixWord, tailWord_1235140, baseEnd_1235140] using wordTrace_append hprefix tailTrace_1235140
  have hstable : (prefixWord ++ tailWord_1235140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235140).length < 2 ^ (prefixWord ++ tailWord_1235140).sum := by decide
  have hdescent : baseEnd_1235140 < baseStart_1235140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235181 : List Nat := [1, 5, 1, 2, 4, 1, 2, 2, 1, 2, 2]
def baseStart_1235181 : Nat := 118140960795 + 1235181 * 2 ^ 59
def prefixEnd_1235181 : Nat := 4983230072969 + 3 ^ 40 * 1235181 * 2
def baseEnd_1235181 : Nat := 634241548301237082357013

theorem tailTrace_1235181 : CollatzResearch.WordTrace tailWord_1235181 prefixEnd_1235181 634241548301237082357013 := by
  unfold tailWord_1235181
  simp only [CollatzResearch.WordTrace]
  refine ⟨45050752138157663965153397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30033834758771775976768931 45050752138157663965153397)
  ·
    refine ⟨4223508012952280996733131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45050752138157663965153397 4223508012952280996733131)
    ·
      refine ⟨6335262019428421495099697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4223508012952280996733131 6335262019428421495099697)
      ·
        refine ⟨4751446514571316121324773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6335262019428421495099697 4751446514571316121324773)
        ·
          refine ⟨890896221482121772748395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4751446514571316121324773 890896221482121772748395)
          ·
            refine ⟨1336344332223182659122593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 890896221482121772748395 1336344332223182659122593)
            ·
              refine ⟨1002258249167386994341945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1336344332223182659122593 1002258249167386994341945)
              ·
                refine ⟨751693686875540245756459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1002258249167386994341945 751693686875540245756459)
                ·
                  refine ⟨1127540530313310368634689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 751693686875540245756459 1127540530313310368634689)
                  ·
                    refine ⟨845655397734982776476017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1127540530313310368634689 845655397734982776476017)
                    ·
                      refine ⟨634241548301237082357013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 845655397734982776476017 634241548301237082357013)
                      ·
                        rfl

theorem cell23_1235181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_1235181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235181 prefixEnd_1235181 := by exact prefixLift 1235181
  have htrace : WordTrace (prefixWord ++ tailWord_1235181) baseStart_1235181 baseEnd_1235181 := by
    simpa [prefixWord, tailWord_1235181, baseEnd_1235181] using wordTrace_append hprefix tailTrace_1235181
  have hstable : (prefixWord ++ tailWord_1235181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235181).length < 2 ^ (prefixWord ++ tailWord_1235181).sum := by decide
  have hdescent : baseEnd_1235181 < baseStart_1235181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235192 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 11]
def baseStart_1235192 : Nat := 118140960795 + 1235192 * 2 ^ 59
def prefixEnd_1235192 : Nat := 4983230072969 + 3 ^ 40 * 1235192 * 2
def baseEnd_1235192 : Nat := 70471910732048504368829

theorem tailTrace_1235192 : CollatzResearch.WordTrace tailWord_1235192 prefixEnd_1235192 70471910732048504368829 := by
  unfold tailWord_1235192
  simp only [CollatzResearch.WordTrace]
  refine ⟨22525576670558906421901915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30034102227411875229202553 22525576670558906421901915)
  ·
    refine ⟨33788365005838359632852873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22525576670558906421901915 33788365005838359632852873)
    ·
      refine ⟨25341273754378769724639655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33788365005838359632852873 25341273754378769724639655)
      ·
        refine ⟨38011910631568154586959483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25341273754378769724639655 38011910631568154586959483)
        ·
          refine ⟨57017865947352231880439225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38011910631568154586959483 57017865947352231880439225)
          ·
            refine ⟨42763399460514173910329419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57017865947352231880439225 42763399460514173910329419)
            ·
              refine ⟨64145099190771260865494129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42763399460514173910329419 64145099190771260865494129)
              ·
                refine ⟨48108824393078445649120597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64145099190771260865494129 48108824393078445649120597)
                ·
                  refine ⟨70471910732048504368829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 48108824393078445649120597 70471910732048504368829)
                  ·
                    rfl

theorem cell23_1235192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 11].length) (baseStart_1235192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235192 prefixEnd_1235192 := by exact prefixLift 1235192
  have htrace : WordTrace (prefixWord ++ tailWord_1235192) baseStart_1235192 baseEnd_1235192 := by
    simpa [prefixWord, tailWord_1235192, baseEnd_1235192] using wordTrace_append hprefix tailTrace_1235192
  have hstable : (prefixWord ++ tailWord_1235192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235192).length < 2 ^ (prefixWord ++ tailWord_1235192).sum := by decide
  have hdescent : baseEnd_1235192 < baseStart_1235192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235199 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 4]
def baseStart_1235199 : Nat := 118140960795 + 1235199 * 2 ^ 59
def prefixEnd_1235199 : Nat := 4983230072969 + 3 ^ 40 * 1235199 * 2
def baseEnd_1235199 : Nat := 634250790953018011931929

theorem tailTrace_1235199 : CollatzResearch.WordTrace tailWord_1235199 prefixEnd_1235199 634250790953018011931929 := by
  unfold tailWord_1235199
  simp only [CollatzResearch.WordTrace]
  refine ⟨45051408652092453039308651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30034272434728302026205767 45051408652092453039308651)
  ·
    refine ⟨67577112978138679558962977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45051408652092453039308651 67577112978138679558962977)
    ·
      refine ⟨50682834733604009669222233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67577112978138679558962977 50682834733604009669222233)
      ·
        refine ⟨38012126050203007251916675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50682834733604009669222233 38012126050203007251916675)
        ·
          refine ⟨57018189075304510877875013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38012126050203007251916675 57018189075304510877875013)
          ·
            refine ⟨10690910451619595789601565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57018189075304510877875013 10690910451619595789601565)
            ·
              refine ⟨4009091419357348421100587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10690910451619595789601565 4009091419357348421100587)
              ·
                refine ⟨6013637129036022631650881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4009091419357348421100587 6013637129036022631650881)
                ·
                  refine ⟨4510227846777016973738161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6013637129036022631650881 4510227846777016973738161)
                  ·
                    refine ⟨3382670885082762730303621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4510227846777016973738161 3382670885082762730303621)
                    ·
                      refine ⟨634250790953018011931929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3382670885082762730303621 634250790953018011931929)
                      ·
                        rfl

theorem cell23_1235199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_1235199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235199 prefixEnd_1235199 := by exact prefixLift 1235199
  have htrace : WordTrace (prefixWord ++ tailWord_1235199) baseStart_1235199 baseEnd_1235199 := by
    simpa [prefixWord, tailWord_1235199, baseEnd_1235199] using wordTrace_append hprefix tailTrace_1235199
  have hstable : (prefixWord ++ tailWord_1235199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235199).length < 2 ^ (prefixWord ++ tailWord_1235199).sum := by decide
  have hdescent : baseEnd_1235199 < baseStart_1235199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235203 : List Nat := [1, 1, 1, 3, 2, 3, 1, 5, 2, 2, 2]
def baseStart_1235203 : Nat := 118140960795 + 1235203 * 2 ^ 59
def prefixEnd_1235203 : Nat := 4983230072969 + 3 ^ 40 * 1235203 * 2
def baseEnd_1235203 : Nat := 634252844875635996281911

theorem tailTrace_1235203 : CollatzResearch.WordTrace tailWord_1235203 prefixEnd_1235203 634252844875635996281911 := by
  unfold tailWord_1235203
  simp only [CollatzResearch.WordTrace]
  refine ⟨45051554544077961722454263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30034369696051974481636175 45051554544077961722454263)
  ·
    refine ⟨67577331816116942583681395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45051554544077961722454263 67577331816116942583681395)
    ·
      refine ⟨101365997724175413875522093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67577331816116942583681395 101365997724175413875522093)
      ·
        refine ⟨38012249146565780203320785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101365997724175413875522093 38012249146565780203320785)
        ·
          refine ⟨28509186859924335152490589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38012249146565780203320785 28509186859924335152490589)
          ·
            refine ⟨10690945072471625682183971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28509186859924335152490589 10690945072471625682183971)
            ·
              refine ⟨16036417608707438523275957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10690945072471625682183971 16036417608707438523275957)
              ·
                refine ⟨1503414150816322361557121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16036417608707438523275957 1503414150816322361557121)
                ·
                  refine ⟨1127560613112241771167841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1503414150816322361557121 1127560613112241771167841)
                  ·
                    refine ⟨845670459834181328375881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1127560613112241771167841 845670459834181328375881)
                    ·
                      refine ⟨634252844875635996281911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 845670459834181328375881 634252844875635996281911)
                      ·
                        rfl

theorem cell23_1235203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 2, 2].length) (baseStart_1235203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235203 prefixEnd_1235203 := by exact prefixLift 1235203
  have htrace : WordTrace (prefixWord ++ tailWord_1235203) baseStart_1235203 baseEnd_1235203 := by
    simpa [prefixWord, tailWord_1235203, baseEnd_1235203] using wordTrace_append hprefix tailTrace_1235203
  have hstable : (prefixWord ++ tailWord_1235203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235203).length < 2 ^ (prefixWord ++ tailWord_1235203).sum := by decide
  have hdescent : baseEnd_1235203 < baseStart_1235203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235209 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 7]
def baseStart_1235209 : Nat := 118140960795 + 1235209 * 2 ^ 59
def prefixEnd_1235209 : Nat := 4983230072969 + 3 ^ 40 * 1235209 * 2
def baseEnd_1235209 : Nat := 70472880639951441422987

theorem tailTrace_1235209 : CollatzResearch.WordTrace tailWord_1235209 prefixEnd_1235209 70472880639951441422987 := by
  unfold tailWord_1235209
  simp only [CollatzResearch.WordTrace]
  refine ⟨45051773382056224747172681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30034515588037483164781787 45051773382056224747172681)
  ·
    refine ⟨33788830036542168560379511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45051773382056224747172681 33788830036542168560379511)
    ·
      refine ⟨50683245054813252840569267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33788830036542168560379511 50683245054813252840569267)
      ·
        refine ⟨76024867582219879260853901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50683245054813252840569267 76024867582219879260853901)
        ·
          refine ⟨28509325343332454722820213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76024867582219879260853901 28509325343332454722820213)
          ·
            refine ⟨2672749250937417630264395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28509325343332454722820213 2672749250937417630264395)
            ·
              refine ⟨4009123876406126445396593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2672749250937417630264395 4009123876406126445396593)
              ·
                refine ⟨3006842907304594834047445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4009123876406126445396593 3006842907304594834047445)
                ·
                  refine ⟨70472880639951441422987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3006842907304594834047445 70472880639951441422987)
                  ·
                    rfl

theorem cell23_1235209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 7].length) (baseStart_1235209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235209 prefixEnd_1235209 := by exact prefixLift 1235209
  have htrace : WordTrace (prefixWord ++ tailWord_1235209) baseStart_1235209 baseEnd_1235209 := by
    simpa [prefixWord, tailWord_1235209, baseEnd_1235209] using wordTrace_append hprefix tailTrace_1235209
  have hstable : (prefixWord ++ tailWord_1235209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235209).length < 2 ^ (prefixWord ++ tailWord_1235209).sum := by decide
  have hdescent : baseEnd_1235209 < baseStart_1235209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235236 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 2, 3, 3]
def baseStart_1235236 : Nat := 118140960795 + 1235236 * 2 ^ 59
def prefixEnd_1235236 : Nat := 4983230072969 + 3 ^ 40 * 1235236 * 2
def baseEnd_1235236 : Nat := 634269789737234367169259

theorem tailTrace_1235236 : CollatzResearch.WordTrace tailWord_1235236 prefixEnd_1235236 634269789737234367169259 := by
  unfold tailWord_1235236
  simp only [CollatzResearch.WordTrace]
  refine ⟨22526379076479204179202781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30035172101972272238937041 22526379076479204179202781)
  ·
    refine ⟨8447392153679701567201043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22526379076479204179202781 8447392153679701567201043)
    ·
      refine ⟨12671088230519552350801565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8447392153679701567201043 12671088230519552350801565)
      ·
        refine ⟨4751658086444832131550587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12671088230519552350801565 4751658086444832131550587)
        ·
          refine ⟨7127487129667248197325881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4751658086444832131550587 7127487129667248197325881)
          ·
            refine ⟨5345615347250436147994411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7127487129667248197325881 5345615347250436147994411)
            ·
              refine ⟨8018423020875654221991617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5345615347250436147994411 8018423020875654221991617)
              ·
                refine ⟨6013817265656740666493713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8018423020875654221991617 6013817265656740666493713)
                ·
                  refine ⟨4510362949242555499870285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6013817265656740666493713 4510362949242555499870285)
                  ·
                    refine ⟨1691386105965958312451357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4510362949242555499870285 1691386105965958312451357)
                    ·
                      refine ⟨634269789737234367169259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1691386105965958312451357 634269789737234367169259)
                      ·
                        rfl

theorem cell23_1235236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_1235236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235236 prefixEnd_1235236 := by exact prefixLift 1235236
  have htrace : WordTrace (prefixWord ++ tailWord_1235236) baseStart_1235236 baseEnd_1235236 := by
    simpa [prefixWord, tailWord_1235236, baseEnd_1235236] using wordTrace_append hprefix tailTrace_1235236
  have hstable : (prefixWord ++ tailWord_1235236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235236).length < 2 ^ (prefixWord ++ tailWord_1235236).sum := by decide
  have hdescent : baseEnd_1235236 < baseStart_1235236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235237 : List Nat := [1, 3, 1, 2, 5, 2, 1, 2, 2, 2, 2]
def baseStart_1235237 : Nat := 118140960795 + 1235237 * 2 ^ 59
def prefixEnd_1235237 : Nat := 4983230072969 + 3 ^ 40 * 1235237 * 2
def baseEnd_1235237 : Nat := 634270303217888863256755

theorem tailTrace_1235237 : CollatzResearch.WordTrace tailWord_1235237 prefixEnd_1235237 634270303217888863256755 := by
  unfold tailWord_1235237
  simp only [CollatzResearch.WordTrace]
  refine ⟨45052794625954785529191965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30035196417303190352794643 45052794625954785529191965)
  ·
    refine ⟨16894797984733044573446987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45052794625954785529191965 16894797984733044573446987)
    ·
      refine ⟨25342196977099566860170481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16894797984733044573446987 25342196977099566860170481)
      ·
        refine ⟨19006647732824675145127861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25342196977099566860170481 19006647732824675145127861)
        ·
          refine ⟨1781873224952313294855737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19006647732824675145127861 1781873224952313294855737)
          ·
            refine ⟨1336404918714234971141803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1781873224952313294855737 1336404918714234971141803)
            ·
              refine ⟨2004607378071352456712705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1336404918714234971141803 2004607378071352456712705)
              ·
                refine ⟨1503455533553514342534529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2004607378071352456712705 1503455533553514342534529)
                ·
                  refine ⟨1127591650165135756900897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1503455533553514342534529 1127591650165135756900897)
                  ·
                    refine ⟨845693737623851817675673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1127591650165135756900897 845693737623851817675673)
                    ·
                      refine ⟨634270303217888863256755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 845693737623851817675673 634270303217888863256755)
                      ·
                        rfl

theorem cell23_1235237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_1235237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235237 prefixEnd_1235237 := by exact prefixLift 1235237
  have htrace : WordTrace (prefixWord ++ tailWord_1235237) baseStart_1235237 baseEnd_1235237 := by
    simpa [prefixWord, tailWord_1235237, baseEnd_1235237] using wordTrace_append hprefix tailTrace_1235237
  have hstable : (prefixWord ++ tailWord_1235237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235237).length < 2 ^ (prefixWord ++ tailWord_1235237).sum := by decide
  have hdescent : baseEnd_1235237 < baseStart_1235237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235276 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1235276 : Nat := 118140960795 + 1235276 * 2 ^ 59
def prefixEnd_1235276 : Nat := 4983230072969 + 3 ^ 40 * 1235276 * 2
def baseEnd_1235276 : Nat := 634290328963414210669075

theorem tailTrace_1235276 : CollatzResearch.WordTrace tailWord_1235276 prefixEnd_1235276 634290328963414210669075 := by
  unfold tailWord_1235276
  simp only [CollatzResearch.WordTrace]
  refine ⟨22527108536406747594930841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30036144715208996793241121 22527108536406747594930841)
  ·
    refine ⟨16895331402305060696198131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22527108536406747594930841 16895331402305060696198131)
    ·
      refine ⟨25342997103457591044297197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16895331402305060696198131 25342997103457591044297197)
      ·
        refine ⟨9503623913796596641611449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25342997103457591044297197 9503623913796596641611449)
        ·
          refine ⟨7127717935347447481208587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9503623913796596641611449 7127717935347447481208587)
          ·
            refine ⟨10691576903021171221812881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7127717935347447481208587 10691576903021171221812881)
            ·
              refine ⟨8018682677265878416359661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10691576903021171221812881 8018682677265878416359661)
              ·
                refine ⟨3007006003974704406134873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8018682677265878416359661 3007006003974704406134873)
                ·
                  refine ⟨2255254502981028304601155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3007006003974704406134873 2255254502981028304601155)
                  ·
                    refine ⟨3382881754471542456901733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2255254502981028304601155 3382881754471542456901733)
                    ·
                      refine ⟨634290328963414210669075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3382881754471542456901733 634290328963414210669075)
                      ·
                        rfl

theorem cell23_1235276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1235276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235276 prefixEnd_1235276 := by exact prefixLift 1235276
  have htrace : WordTrace (prefixWord ++ tailWord_1235276) baseStart_1235276 baseEnd_1235276 := by
    simpa [prefixWord, tailWord_1235276, baseEnd_1235276] using wordTrace_append hprefix tailTrace_1235276
  have hstable : (prefixWord ++ tailWord_1235276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235276).length < 2 ^ (prefixWord ++ tailWord_1235276).sum := by decide
  have hdescent : baseEnd_1235276 < baseStart_1235276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235294 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 7]
def baseStart_1235294 : Nat := 118140960795 + 1235294 * 2 ^ 59
def prefixEnd_1235294 : Nat := 4983230072969 + 3 ^ 40 * 1235294 * 2
def baseEnd_1235294 : Nat := 70477730179466126693777

theorem tailTrace_1235294 : CollatzResearch.WordTrace tailWord_1235294 prefixEnd_1235294 70477730179466126693777 := by
  unfold tailWord_1235294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5631859198343535533002117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30036582391165522842677957 5631859198343535533002117)
  ·
    refine ⟨1055973599689412912437897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5631859198343535533002117 1055973599689412912437897)
    ·
      refine ⟨791980199767059684328423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1055973599689412912437897 791980199767059684328423)
      ·
        refine ⟨1187970299650589526492635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 791980199767059684328423 1187970299650589526492635)
        ·
          refine ⟨1781955449475884289738953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187970299650589526492635 1781955449475884289738953)
          ·
            refine ⟨1336466587106913217304215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1781955449475884289738953 1336466587106913217304215)
            ·
              refine ⟨2004699880660369825956323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1336466587106913217304215 2004699880660369825956323)
              ·
                refine ⟨3007049820990554738934485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004699880660369825956323 3007049820990554738934485)
                ·
                  refine ⟨70477730179466126693777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3007049820990554738934485 70477730179466126693777)
                  ·
                    rfl

theorem cell23_1235294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_1235294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235294 prefixEnd_1235294 := by exact prefixLift 1235294
  have htrace : WordTrace (prefixWord ++ tailWord_1235294) baseStart_1235294 baseEnd_1235294 := by
    simpa [prefixWord, tailWord_1235294, baseEnd_1235294] using wordTrace_append hprefix tailTrace_1235294
  have hstable : (prefixWord ++ tailWord_1235294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235294).length < 2 ^ (prefixWord ++ tailWord_1235294).sum := by decide
  have hdescent : baseEnd_1235294 < baseStart_1235294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235299 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 8]
def baseStart_1235299 : Nat := 118140960795 + 1235299 * 2 ^ 59
def prefixEnd_1235299 : Nat := 4983230072969 + 3 ^ 40 * 1235299 * 2
def baseEnd_1235299 : Nat := 70478015446496402297941

theorem tailTrace_1235299 : CollatzResearch.WordTrace tailWord_1235299 prefixEnd_1235299 70478015446496402297941 := by
  unfold tailWord_1235299
  simp only [CollatzResearch.WordTrace]
  refine ⟨45055055951730170117948951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30036703967820113411965967 45055055951730170117948951)
  ·
    refine ⟨67582583927595255176923427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45055055951730170117948951 67582583927595255176923427)
    ·
      refine ⟨101373875891392882765385141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67582583927595255176923427 101373875891392882765385141)
      ·
        refine ⟨9503800864818082759254857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101373875891392882765385141 9503800864818082759254857)
        ·
          refine ⟨7127850648613562069441143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9503800864818082759254857 7127850648613562069441143)
          ·
            refine ⟨10691775972920343104161715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7127850648613562069441143 10691775972920343104161715)
            ·
              refine ⟨16037663959380514656242573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10691775972920343104161715 16037663959380514656242573)
              ·
                refine ⟨6014123984767692996090965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16037663959380514656242573 6014123984767692996090965)
                ·
                  refine ⟨70478015446496402297941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6014123984767692996090965 70478015446496402297941)
                  ·
                    rfl

theorem cell23_1235299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 8].length) (baseStart_1235299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235299 prefixEnd_1235299 := by exact prefixLift 1235299
  have htrace : WordTrace (prefixWord ++ tailWord_1235299) baseStart_1235299 baseEnd_1235299 := by
    simpa [prefixWord, tailWord_1235299, baseEnd_1235299] using wordTrace_append hprefix tailTrace_1235299
  have hstable : (prefixWord ++ tailWord_1235299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235299).length < 2 ^ (prefixWord ++ tailWord_1235299).sum := by decide
  have hdescent : baseEnd_1235299 < baseStart_1235299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235303 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 3, 4]
def baseStart_1235303 : Nat := 118140960795 + 1235303 * 2 ^ 59
def prefixEnd_1235303 : Nat := 4983230072969 + 3 ^ 40 * 1235303 * 2
def baseEnd_1235303 : Nat := 211434730980361868343817

theorem tailTrace_1235303 : CollatzResearch.WordTrace tailWord_1235303 prefixEnd_1235303 211434730980361868343817 := by
  unfold tailWord_1235303
  simp only [CollatzResearch.WordTrace]
  refine ⟨45055201843715678801094563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30036801229143785867396375 45055201843715678801094563)
  ·
    refine ⟨67582802765573518201641845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45055201843715678801094563 67582802765573518201641845)
    ·
      refine ⟨6335887759272517331403923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67582802765573518201641845 6335887759272517331403923)
      ·
        refine ⟨9503831638908775997105885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6335887759272517331403923 9503831638908775997105885)
        ·
          refine ⟨3563936864590790998914707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9503831638908775997105885 3563936864590790998914707)
          ·
            refine ⟨5345905296886186498372061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3563936864590790998914707 5345905296886186498372061)
            ·
              refine ⟨2004714486332319936889523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5345905296886186498372061 2004714486332319936889523)
              ·
                refine ⟨3007071729498479905334285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004714486332319936889523 3007071729498479905334285)
                ·
                  refine ⟨1127651898561929964500357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3007071729498479905334285 1127651898561929964500357)
                  ·
                    refine ⟨211434730980361868343817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1127651898561929964500357 211434730980361868343817)
                    ·
                      rfl

theorem cell23_1235303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_1235303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235303 prefixEnd_1235303 := by exact prefixLift 1235303
  have htrace : WordTrace (prefixWord ++ tailWord_1235303) baseStart_1235303 baseEnd_1235303 := by
    simpa [prefixWord, tailWord_1235303, baseEnd_1235303] using wordTrace_append hprefix tailTrace_1235303
  have hstable : (prefixWord ++ tailWord_1235303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235303).length < 2 ^ (prefixWord ++ tailWord_1235303).sum := by decide
  have hdescent : baseEnd_1235303 < baseStart_1235303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235353 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 2, 3, 2]
def baseStart_1235353 : Nat := 118140960795 + 1235353 * 2 ^ 59
def prefixEnd_1235353 : Nat := 4983230072969 + 3 ^ 40 * 1235353 * 2
def baseEnd_1235353 : Nat := 634329866973810409406221

theorem tailTrace_1235353 : CollatzResearch.WordTrace tailWord_1235353 prefixEnd_1235353 634329866973810409406221 := by
  unfold tailWord_1235353
  simp only [CollatzResearch.WordTrace]
  refine ⟨45057025493534537340414713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30038016995689691560276475 45057025493534537340414713)
  ·
    refine ⟨33792769120150903005311035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45057025493534537340414713 33792769120150903005311035)
    ·
      refine ⟨50689153680226354507966553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33792769120150903005311035 50689153680226354507966553)
      ·
        refine ⟨38016865260169765880974915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50689153680226354507966553 38016865260169765880974915)
        ·
          refine ⟨57025297890254648821462373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38016865260169765880974915 57025297890254648821462373)
          ·
            refine ⟨10692243354422746654024195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57025297890254648821462373 10692243354422746654024195)
            ·
              refine ⟨16038365031634119981036293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10692243354422746654024195 16038365031634119981036293)
              ·
                refine ⟨3007193443431397496444305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16038365031634119981036293 3007193443431397496444305)
                ·
                  refine ⟨2255395082573548122333229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3007193443431397496444305 2255395082573548122333229)
                  ·
                    refine ⟨845773155965080545874961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2255395082573548122333229 845773155965080545874961)
                    ·
                      refine ⟨634329866973810409406221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 845773155965080545874961 634329866973810409406221)
                      ·
                        rfl

theorem cell23_1235353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 3, 2].length) (baseStart_1235353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235353 prefixEnd_1235353 := by exact prefixLift 1235353
  have htrace : WordTrace (prefixWord ++ tailWord_1235353) baseStart_1235353 baseEnd_1235353 := by
    simpa [prefixWord, tailWord_1235353, baseEnd_1235353] using wordTrace_append hprefix tailTrace_1235353
  have hstable : (prefixWord ++ tailWord_1235353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235353).length < 2 ^ (prefixWord ++ tailWord_1235353).sum := by decide
  have hdescent : baseEnd_1235353 < baseStart_1235353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235400 : List Nat := [2, 1, 3, 1, 3, 2, 4, 1, 1, 1, 4]
def baseStart_1235400 : Nat := 118140960795 + 1235400 * 2 ^ 59
def prefixEnd_1235400 : Nat := 4983230072969 + 3 ^ 40 * 1235400 * 2
def baseEnd_1235400 : Nat := 634354000564571725518505

theorem tailTrace_1235400 : CollatzResearch.WordTrace tailWord_1235400 prefixEnd_1235400 634354000564571725518505 := by
  unfold tailWord_1235400
  simp only [CollatzResearch.WordTrace]
  refine ⟨22529369862182132183687827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30039159816242842911583769 22529369862182132183687827)
  ·
    refine ⟨33794054793273198275531741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22529369862182132183687827 33794054793273198275531741)
    ·
      refine ⟨12672770547477449353324403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33794054793273198275531741 12672770547477449353324403)
      ·
        refine ⟨19009155821216174029986605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12672770547477449353324403 19009155821216174029986605)
        ·
          refine ⟨7128433432956065261244977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19009155821216174029986605 7128433432956065261244977)
          ·
            refine ⟨5346325074717048945933733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7128433432956065261244977 5346325074717048945933733)
            ·
              refine ⟨1002435951509446677362575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5346325074717048945933733 1002435951509446677362575)
              ·
                refine ⟨1503653927264170016043863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002435951509446677362575 1503653927264170016043863)
                ·
                  refine ⟨2255480890896255024065795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1503653927264170016043863 2255480890896255024065795)
                  ·
                    refine ⟨3383221336344382536098693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2255480890896255024065795 3383221336344382536098693)
                    ·
                      refine ⟨634354000564571725518505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3383221336344382536098693 634354000564571725518505)
                      ·
                        rfl

theorem cell23_1235400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_1235400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235400 prefixEnd_1235400 := by exact prefixLift 1235400
  have htrace : WordTrace (prefixWord ++ tailWord_1235400) baseStart_1235400 baseEnd_1235400 := by
    simpa [prefixWord, tailWord_1235400, baseEnd_1235400] using wordTrace_append hprefix tailTrace_1235400
  have hstable : (prefixWord ++ tailWord_1235400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235400).length < 2 ^ (prefixWord ++ tailWord_1235400).sum := by decide
  have hdescent : baseEnd_1235400 < baseStart_1235400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235417 : List Nat := [1, 2, 1, 2, 4, 1, 1, 6, 1, 2, 2]
def baseStart_1235417 : Nat := 118140960795 + 1235417 * 2 ^ 59
def prefixEnd_1235417 : Nat := 4983230072969 + 3 ^ 40 * 1235417 * 2
def baseEnd_1235417 : Nat := 634362729735698159005927

theorem tailTrace_1235417 : CollatzResearch.WordTrace tailWord_1235417 prefixEnd_1235417 634362729735698159005927 := by
  unfold tailWord_1235417
  simp only [CollatzResearch.WordTrace]
  refine ⟨45059359765302676270744505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30039573176868450847163003 45059359765302676270744505)
  ·
    refine ⟨33794519823977007203058379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45059359765302676270744505 33794519823977007203058379)
    ·
      refine ⟨50691779735965510804587569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33794519823977007203058379 50691779735965510804587569)
      ·
        refine ⟨38018834801974133103440677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50691779735965510804587569 38018834801974133103440677)
        ·
          refine ⟨7128531525370149956895127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38018834801974133103440677 7128531525370149956895127)
          ·
            refine ⟨10692797288055224935342691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7128531525370149956895127 10692797288055224935342691)
            ·
              refine ⟨16039195932082837403014037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10692797288055224935342691 16039195932082837403014037)
              ·
                refine ⟨751837309316383003266283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16039195932082837403014037 751837309316383003266283)
                ·
                  refine ⟨1127755963974574504899425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 751837309316383003266283 1127755963974574504899425)
                  ·
                    refine ⟨845816972980930878674569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1127755963974574504899425 845816972980930878674569)
                    ·
                      refine ⟨634362729735698159005927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 845816972980930878674569 634362729735698159005927)
                      ·
                        rfl

theorem cell23_1235417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 1, 2, 2].length) (baseStart_1235417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235417 prefixEnd_1235417 := by exact prefixLift 1235417
  have htrace : WordTrace (prefixWord ++ tailWord_1235417) baseStart_1235417 baseEnd_1235417 := by
    simpa [prefixWord, tailWord_1235417, baseEnd_1235417] using wordTrace_append hprefix tailTrace_1235417
  have hstable : (prefixWord ++ tailWord_1235417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235417).length < 2 ^ (prefixWord ++ tailWord_1235417).sum := by decide
  have hdescent : baseEnd_1235417 < baseStart_1235417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235427 : List Nat := [1, 1, 1, 6, 3, 1, 3, 1, 2, 4]
def baseStart_1235427 : Nat := 118140960795 + 1235427 * 2 ^ 59
def prefixEnd_1235427 : Nat := 4983230072969 + 3 ^ 40 * 1235427 * 2
def baseEnd_1235427 : Nat := 211455954847414373293627

theorem tailTrace_1235427 : CollatzResearch.WordTrace tailWord_1235427 prefixEnd_1235427 211455954847414373293627 := by
  unfold tailWord_1235427
  simp only [CollatzResearch.WordTrace]
  refine ⟨45059724495266447978608535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30039816330177631985739023 45059724495266447978608535)
  ·
    refine ⟨67589586742899671967912803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45059724495266447978608535 67589586742899671967912803)
    ·
      refine ⟨101384380114349507951869205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67589586742899671967912803 101384380114349507951869205)
      ·
        refine ⟨4752392817860133185243869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 101384380114349507951869205 4752392817860133185243869)
        ·
          refine ⟨1782147306697549944466451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4752392817860133185243869 1782147306697549944466451)
          ·
            refine ⟨2673220960046324916699677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1782147306697549944466451 2673220960046324916699677)
            ·
              refine ⟨1002457860017371843762379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2673220960046324916699677 1002457860017371843762379)
              ·
                refine ⟨1503686790026057765643569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002457860017371843762379 1503686790026057765643569)
                ·
                  refine ⟨1127765092519543324232677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1503686790026057765643569 1127765092519543324232677)
                  ·
                    refine ⟨211455954847414373293627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1127765092519543324232677 211455954847414373293627)
                    ·
                      rfl

theorem cell23_1235427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 2, 4].length) (baseStart_1235427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235427 prefixEnd_1235427 := by exact prefixLift 1235427
  have htrace : WordTrace (prefixWord ++ tailWord_1235427) baseStart_1235427 baseEnd_1235427 := by
    simpa [prefixWord, tailWord_1235427, baseEnd_1235427] using wordTrace_append hprefix tailTrace_1235427
  have hstable : (prefixWord ++ tailWord_1235427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235427).length < 2 ^ (prefixWord ++ tailWord_1235427).sum := by decide
  have hdescent : baseEnd_1235427 < baseStart_1235427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235437 : List Nat := [1, 5, 1, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1235437 : Nat := 118140960795 + 1235437 * 2 ^ 59
def prefixEnd_1235437 : Nat := 4983230072969 + 3 ^ 40 * 1235437 * 2
def baseEnd_1235437 : Nat := 634372999348788080755835

theorem tailTrace_1235437 : CollatzResearch.WordTrace tailWord_1235437 prefixEnd_1235437 634372999348788080755835 := by
  unfold tailWord_1235437
  simp only [CollatzResearch.WordTrace]
  refine ⟨45060089225230219686472565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30040059483486813124315043 45060089225230219686472565)
  ·
    refine ⟨4224383364865333095606803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45060089225230219686472565 4224383364865333095606803)
    ·
      refine ⟨6336575047297999643410205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4224383364865333095606803 6336575047297999643410205)
      ·
        refine ⟨2376215642736749866278827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6336575047297999643410205 2376215642736749866278827)
        ·
          refine ⟨3564323464105124799418241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2376215642736749866278827 3564323464105124799418241)
          ·
            refine ⟨2673242598078843599563681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3564323464105124799418241 2673242598078843599563681)
            ·
              refine ⟨2004931948559132699672761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2673242598078843599563681 2004931948559132699672761)
              ·
                refine ⟨1503698961419349524754571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2004931948559132699672761 1503698961419349524754571)
                ·
                  refine ⟨2255548442129024287131857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1503698961419349524754571 2255548442129024287131857)
                  ·
                    refine ⟨1691661331596768215348893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2255548442129024287131857 1691661331596768215348893)
                    ·
                      refine ⟨634372999348788080755835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1691661331596768215348893 634372999348788080755835)
                      ·
                        rfl

theorem cell23_1235437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1235437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235437 prefixEnd_1235437 := by exact prefixLift 1235437
  have htrace : WordTrace (prefixWord ++ tailWord_1235437) baseStart_1235437 baseEnd_1235437 := by
    simpa [prefixWord, tailWord_1235437, baseEnd_1235437] using wordTrace_append hprefix tailTrace_1235437
  have hstable : (prefixWord ++ tailWord_1235437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235437).length < 2 ^ (prefixWord ++ tailWord_1235437).sum := by decide
  have hdescent : baseEnd_1235437 < baseStart_1235437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235473 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 5, 4, 2]
def baseStart_1235473 : Nat := 118140960795 + 1235473 * 2 ^ 59
def prefixEnd_1235473 : Nat := 4983230072969 + 3 ^ 40 * 1235473 * 2
def baseEnd_1235473 : Nat := 634391484652349939905669

theorem tailTrace_1235473 : CollatzResearch.WordTrace tailWord_1235473 prefixEnd_1235473 634391484652349939905669 := by
  unfold tailWord_1235473
  simp only [CollatzResearch.WordTrace]
  refine ⟨45061402253099797834783073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30040934835399865223188715 45061402253099797834783073)
  ·
    refine ⟨33796051689824848376087305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45061402253099797834783073 33796051689824848376087305)
    ·
      refine ⟨25347038767368636282065479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33796051689824848376087305 25347038767368636282065479)
      ·
        refine ⟨38020558151052954423098219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25347038767368636282065479 38020558151052954423098219)
        ·
          refine ⟨57030837226579431634647329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38020558151052954423098219 57030837226579431634647329)
          ·
            refine ⟨42773127919934573725985497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57030837226579431634647329 42773127919934573725985497)
            ·
              refine ⟨32079845939950930294489123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42773127919934573725985497 32079845939950930294489123)
              ·
                refine ⟨48119768909926395441733685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32079845939950930294489123 48119768909926395441733685)
                ·
                  refine ⟨4511228335305599572662533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48119768909926395441733685 4511228335305599572662533)
                  ·
                    refine ⟨845855312869799919874225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4511228335305599572662533 845855312869799919874225)
                    ·
                      refine ⟨634391484652349939905669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 845855312869799919874225 634391484652349939905669)
                      ·
                        rfl

theorem cell23_1235473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 4, 2].length) (baseStart_1235473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235473 prefixEnd_1235473 := by exact prefixLift 1235473
  have htrace : WordTrace (prefixWord ++ tailWord_1235473) baseStart_1235473 baseEnd_1235473 := by
    simpa [prefixWord, tailWord_1235473, baseEnd_1235473] using wordTrace_append hprefix tailTrace_1235473
  have hstable : (prefixWord ++ tailWord_1235473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235473).length < 2 ^ (prefixWord ++ tailWord_1235473).sum := by decide
  have hdescent : baseEnd_1235473 < baseStart_1235473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235484 : List Nat := [2, 2, 3, 1, 2, 4, 2, 1, 2, 1, 3]
def baseStart_1235484 : Nat := 118140960795 + 1235484 * 2 ^ 59
def prefixEnd_1235484 : Nat := 4983230072969 + 3 ^ 40 * 1235484 * 2
def baseEnd_1235484 : Nat := 634397132939549396868119

theorem tailTrace_1235484 : CollatzResearch.WordTrace tailWord_1235484 prefixEnd_1235484 634397132939549396868119 := by
  unfold tailWord_1235484
  simp only [CollatzResearch.WordTrace]
  refine ⟨22530901728029973356716753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30041202304039964475622337 22530901728029973356716753)
  ·
    refine ⟨16898176296022480017537565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22530901728029973356716753 16898176296022480017537565)
    ·
      refine ⟨6336816111008430006576587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16898176296022480017537565 6336816111008430006576587)
      ·
        refine ⟨9505224166512645009864881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6336816111008430006576587 9505224166512645009864881)
        ·
          refine ⟨7128918124884483757398661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9505224166512645009864881 7128918124884483757398661)
          ·
            refine ⟨1336672148415840704512249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7128918124884483757398661 1336672148415840704512249)
            ·
              refine ⟨1002504111311880528384187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1336672148415840704512249 1002504111311880528384187)
              ·
                refine ⟨1503756166967820792576281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002504111311880528384187 1503756166967820792576281)
                ·
                  refine ⟨1127817125225865594432211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1503756166967820792576281 1127817125225865594432211)
                  ·
                    refine ⟨1691725687838798391648317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1127817125225865594432211 1691725687838798391648317)
                    ·
                      refine ⟨634397132939549396868119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1691725687838798391648317 634397132939549396868119)
                      ·
                        rfl

theorem cell23_1235484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_1235484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235484 prefixEnd_1235484 := by exact prefixLift 1235484
  have htrace : WordTrace (prefixWord ++ tailWord_1235484) baseStart_1235484 baseEnd_1235484 := by
    simpa [prefixWord, tailWord_1235484, baseEnd_1235484] using wordTrace_append hprefix tailTrace_1235484
  have hstable : (prefixWord ++ tailWord_1235484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235484).length < 2 ^ (prefixWord ++ tailWord_1235484).sum := by decide
  have hdescent : baseEnd_1235484 < baseStart_1235484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235490 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 1, 4, 2]
def baseStart_1235490 : Nat := 118140960795 + 1235490 * 2 ^ 59
def prefixEnd_1235490 : Nat := 4983230072969 + 3 ^ 40 * 1235490 * 2
def baseEnd_1235490 : Nat := 634400213823476373393091

theorem tailTrace_1235490 : CollatzResearch.WordTrace tailWord_1235490 prefixEnd_1235490 634400213823476373393091 := by
  unfold tailWord_1235490
  simp only [CollatzResearch.WordTrace]
  refine ⟨11265505573509552434537981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30041348196025473158767949 11265505573509552434537981)
  ·
    refine ⟨4224564590066082162951743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11265505573509552434537981 4224564590066082162951743)
    ·
      refine ⟨6336846885099123244427615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4224564590066082162951743 6336846885099123244427615)
      ·
        refine ⟨9505270327648684866641423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6336846885099123244427615 9505270327648684866641423)
        ·
          refine ⟨14257905491473027299962135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9505270327648684866641423 14257905491473027299962135)
          ·
            refine ⟨21386858237209540949943203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14257905491473027299962135 21386858237209540949943203)
            ·
              refine ⟨32080287355814311424914805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21386858237209540949943203 32080287355814311424914805)
              ·
                refine ⟨3007526939607591696085763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32080287355814311424914805 3007526939607591696085763)
                ·
                  refine ⟨4511290409411387544128645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3007526939607591696085763 4511290409411387544128645)
                  ·
                    refine ⟨845866951764635164524121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4511290409411387544128645 845866951764635164524121)
                    ·
                      refine ⟨634400213823476373393091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 845866951764635164524121 634400213823476373393091)
                      ·
                        rfl

theorem cell23_1235490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_1235490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235490 prefixEnd_1235490 := by exact prefixLift 1235490
  have htrace : WordTrace (prefixWord ++ tailWord_1235490) baseStart_1235490 baseEnd_1235490 := by
    simpa [prefixWord, tailWord_1235490, baseEnd_1235490] using wordTrace_append hprefix tailTrace_1235490
  have hstable : (prefixWord ++ tailWord_1235490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235490).length < 2 ^ (prefixWord ++ tailWord_1235490).sum := by decide
  have hdescent : baseEnd_1235490 < baseStart_1235490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235510 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_1235510 : Nat := 118140960795 + 1235510 * 2 ^ 59
def prefixEnd_1235510 : Nat := 4983230072969 + 3 ^ 40 * 1235510 * 2
def baseEnd_1235510 : Nat := 634410483436566295142999

theorem tailTrace_1235510 : CollatzResearch.WordTrace tailWord_1235510 prefixEnd_1235510 634410483436566295142999 := by
  unfold tailWord_1235510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2816421984622859572117499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30041834502643835435919989 2816421984622859572117499)
  ·
    refine ⟨4224632976934289358176249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2816421984622859572117499 4224632976934289358176249)
    ·
      refine ⟨3168474732700717018632187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4224632976934289358176249 3168474732700717018632187)
      ·
        refine ⟨4752712099051075527948281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3168474732700717018632187 4752712099051075527948281)
        ·
          refine ⟨3564534074288306645961211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4752712099051075527948281 3564534074288306645961211)
          ·
            refine ⟨5346801111432459968941817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3564534074288306645961211 5346801111432459968941817)
            ·
              refine ⟨4010100833574344976706363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5346801111432459968941817 4010100833574344976706363)
              ·
                refine ⟨6015151250361517465059545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4010100833574344976706363 6015151250361517465059545)
                ·
                  refine ⟨4511363437771138098794659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6015151250361517465059545 4511363437771138098794659)
                  ·
                    refine ⟨6767045156656707148191989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4511363437771138098794659 6767045156656707148191989)
                    ·
                      refine ⟨634410483436566295142999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6767045156656707148191989 634410483436566295142999)
                      ·
                        rfl

theorem cell23_1235510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_1235510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235510 prefixEnd_1235510 := by exact prefixLift 1235510
  have htrace : WordTrace (prefixWord ++ tailWord_1235510) baseStart_1235510 baseEnd_1235510 := by
    simpa [prefixWord, tailWord_1235510, baseEnd_1235510] using wordTrace_append hprefix tailTrace_1235510
  have hstable : (prefixWord ++ tailWord_1235510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235510).length < 2 ^ (prefixWord ++ tailWord_1235510).sum := by decide
  have hdescent : baseEnd_1235510 < baseStart_1235510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235530 : List Nat := [3, 1, 2, 1, 1, 5, 1, 4, 5]
def baseStart_1235530 : Nat := 118140960795 + 1235530 * 2 ^ 59
def prefixEnd_1235530 : Nat := 4983230072969 + 3 ^ 40 * 1235530 * 2
def baseEnd_1235530 : Nat := 70491194783295135210323

theorem tailTrace_1235530 : CollatzResearch.WordTrace tailWord_1235530 prefixEnd_1235530 70491194783295135210323 := by
  unfold tailWord_1235530
  simp only [CollatzResearch.WordTrace]
  refine ⟨11265870303473324142402011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30042320809262197713072029 11265870303473324142402011)
  ·
    refine ⟨16898805455209986213603017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11265870303473324142402011 16898805455209986213603017)
    ·
      refine ⟨12674104091407489660202263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16898805455209986213603017 12674104091407489660202263)
      ·
        refine ⟨19011156137111234490303395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12674104091407489660202263 19011156137111234490303395)
        ·
          refine ⟨28516734205666851735455093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19011156137111234490303395 28516734205666851735455093)
          ·
            refine ⟨2673443831781267350198915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28516734205666851735455093 2673443831781267350198915)
            ·
              refine ⟨4010165747671901025298373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2673443831781267350198915 4010165747671901025298373)
              ·
                refine ⟨751906077688481442243445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4010165747671901025298373 751906077688481442243445)
                ·
                  refine ⟨70491194783295135210323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 751906077688481442243445 70491194783295135210323)
                  ·
                    rfl

theorem cell23_1235530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 5].length) (baseStart_1235530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235530 prefixEnd_1235530 := by exact prefixLift 1235530
  have htrace : WordTrace (prefixWord ++ tailWord_1235530) baseStart_1235530 baseEnd_1235530 := by
    simpa [prefixWord, tailWord_1235530, baseEnd_1235530] using wordTrace_append hprefix tailTrace_1235530
  have hstable : (prefixWord ++ tailWord_1235530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235530).length < 2 ^ (prefixWord ++ tailWord_1235530).sum := by decide
  have hdescent : baseEnd_1235530 < baseStart_1235530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235536 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 7]
def baseStart_1235536 : Nat := 118140960795 + 1235536 * 2 ^ 59
def prefixEnd_1235536 : Nat := 4983230072969 + 3 ^ 40 * 1235536 * 2
def baseEnd_1235536 : Nat := 634423833933583193417879

theorem tailTrace_1235536 : CollatzResearch.WordTrace tailWord_1235536 prefixEnd_1235536 634423833933583193417879 := by
  unfold tailWord_1235536
  simp only [CollatzResearch.WordTrace]
  refine ⟨22531850025935779797163231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30042466701247706396217641 22531850025935779797163231)
  ·
    refine ⟨33797775038903669695744847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22531850025935779797163231 33797775038903669695744847)
    ·
      refine ⟨50696662558355504543617271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33797775038903669695744847 50696662558355504543617271)
      ·
        refine ⟨76044993837533256815425907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50696662558355504543617271 76044993837533256815425907)
        ·
          refine ⟨114067490756299885223138861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76044993837533256815425907 114067490756299885223138861)
          ·
            refine ⟨42775309033612456958677073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114067490756299885223138861 42775309033612456958677073)
            ·
              refine ⟨32081481775209342719007805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42775309033612456958677073 32081481775209342719007805)
              ·
                refine ⟨12030555665703503519627927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32081481775209342719007805 12030555665703503519627927)
                ·
                  refine ⟨18045833498555255279441891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12030555665703503519627927 18045833498555255279441891)
                  ·
                    refine ⟨27068750247832882919162837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18045833498555255279441891 27068750247832882919162837)
                    ·
                      refine ⟨634423833933583193417879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27068750247832882919162837 634423833933583193417879)
                      ·
                        rfl

theorem cell23_1235536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_1235536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235536 prefixEnd_1235536 := by exact prefixLift 1235536
  have htrace : WordTrace (prefixWord ++ tailWord_1235536) baseStart_1235536 baseEnd_1235536 := by
    simpa [prefixWord, tailWord_1235536, baseEnd_1235536] using wordTrace_append hprefix tailTrace_1235536
  have hstable : (prefixWord ++ tailWord_1235536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235536).length < 2 ^ (prefixWord ++ tailWord_1235536).sum := by decide
  have hdescent : baseEnd_1235536 < baseStart_1235536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235540 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_1235540 : Nat := 118140960795 + 1235540 * 2 ^ 59
def prefixEnd_1235540 : Nat := 4983230072969 + 3 ^ 40 * 1235540 * 2
def baseEnd_1235540 : Nat := 634425887856201177767861

theorem tailTrace_1235540 : CollatzResearch.WordTrace tailWord_1235540 prefixEnd_1235540 634425887856201177767861 := by
  unfold tailWord_1235540
  simp only [CollatzResearch.WordTrace]
  refine ⟨22531922971928534138736037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30042563962571378851648049 22531922971928534138736037)
  ·
    refine ⟨4224735557236600151013007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22531922971928534138736037 4224735557236600151013007)
    ·
      refine ⟨6337103335854900226519511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4224735557236600151013007 6337103335854900226519511)
      ·
        refine ⟨9505655003782350339779267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6337103335854900226519511 9505655003782350339779267)
        ·
          refine ⟨14258482505673525509668901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9505655003782350339779267 14258482505673525509668901)
          ·
            refine ⟨2673465469813786033062919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14258482505673525509668901 2673465469813786033062919)
            ·
              refine ⟨4010198204720679049594379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2673465469813786033062919 4010198204720679049594379)
              ·
                refine ⟨6015297307081018574391569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4010198204720679049594379 6015297307081018574391569)
                ·
                  refine ⟨4511472980310763930793677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6015297307081018574391569 4511472980310763930793677)
                  ·
                    refine ⟨1691802367616536474047629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4511472980310763930793677 1691802367616536474047629)
                    ·
                      refine ⟨634425887856201177767861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1691802367616536474047629 634425887856201177767861)
                      ·
                        rfl

theorem cell23_1235540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_1235540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235540 prefixEnd_1235540 := by exact prefixLift 1235540
  have htrace : WordTrace (prefixWord ++ tailWord_1235540) baseStart_1235540 baseEnd_1235540 := by
    simpa [prefixWord, tailWord_1235540, baseEnd_1235540] using wordTrace_append hprefix tailTrace_1235540
  have hstable : (prefixWord ++ tailWord_1235540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235540).length < 2 ^ (prefixWord ++ tailWord_1235540).sum := by decide
  have hdescent : baseEnd_1235540 < baseStart_1235540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235560 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 1, 7]
def baseStart_1235560 : Nat := 118140960795 + 1235560 * 2 ^ 59
def prefixEnd_1235560 : Nat := 4983230072969 + 3 ^ 40 * 1235560 * 2
def baseEnd_1235560 : Nat := 211478719156430366505923

theorem tailTrace_1235560 : CollatzResearch.WordTrace tailWord_1235560 prefixEnd_1235560 211478719156430366505923 := by
  unfold tailWord_1235560
  simp only [CollatzResearch.WordTrace]
  refine ⟨22532287701892305846600067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30043050269189741128800089 22532287701892305846600067)
  ·
    refine ⟨33798431552838458769900101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22532287701892305846600067 33798431552838458769900101)
    ·
      refine ⟨6337205916157211019356269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33798431552838458769900101 6337205916157211019356269)
      ·
        refine ⟨2376452218558954132258601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6337205916157211019356269 2376452218558954132258601)
        ·
          refine ⟨1782339163919215599193951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2376452218558954132258601 1782339163919215599193951)
          ·
            refine ⟨2673508745878823398790927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1782339163919215599193951 2673508745878823398790927)
            ·
              refine ⟨4010263118818235098186391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2673508745878823398790927 4010263118818235098186391)
              ·
                refine ⟨6015394678227352647279587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4010263118818235098186391 6015394678227352647279587)
                ·
                  refine ⟨9023092017341028970919381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6015394678227352647279587 9023092017341028970919381)
                  ·
                    refine ⟨211478719156430366505923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9023092017341028970919381 211478719156430366505923)
                    ·
                      rfl

theorem cell23_1235560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_1235560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235560 prefixEnd_1235560 := by exact prefixLift 1235560
  have htrace : WordTrace (prefixWord ++ tailWord_1235560) baseStart_1235560 baseEnd_1235560 := by
    simpa [prefixWord, tailWord_1235560, baseEnd_1235560] using wordTrace_append hprefix tailTrace_1235560
  have hstable : (prefixWord ++ tailWord_1235560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235560).length < 2 ^ (prefixWord ++ tailWord_1235560).sum := by decide
  have hdescent : baseEnd_1235560 < baseStart_1235560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235563 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 4]
def baseStart_1235563 : Nat := 118140960795 + 1235563 * 2 ^ 59
def prefixEnd_1235563 : Nat := 4983230072969 + 3 ^ 40 * 1235563 * 2
def baseEnd_1235563 : Nat := 634437697911254587780255

theorem tailTrace_1235563 : CollatzResearch.WordTrace tailWord_1235563 prefixEnd_1235563 634437697911254587780255 := by
  unfold tailWord_1235563
  simp only [CollatzResearch.WordTrace]
  refine ⟨45064684822773743205559343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30043123215182495470372895 45064684822773743205559343)
  ·
    refine ⟨67597027234160614808339015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45064684822773743205559343 67597027234160614808339015)
    ·
      refine ⟨101395540851240922212508523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67597027234160614808339015 101395540851240922212508523)
      ·
        refine ⟨152093311276861383318762785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101395540851240922212508523 152093311276861383318762785)
        ·
          refine ⟨114069983457646037489072089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152093311276861383318762785 114069983457646037489072089)
          ·
            refine ⟨85552487593234528116804067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114069983457646037489072089 85552487593234528116804067)
            ·
              refine ⟨128328731389851792175206101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85552487593234528116804067 128328731389851792175206101)
              ·
                refine ⟨3007704641949651379106393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 128328731389851792175206101 3007704641949651379106393)
                ·
                  refine ⟨2255778481462238534329795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3007704641949651379106393 2255778481462238534329795)
                  ·
                    refine ⟨3383667722193357801494693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2255778481462238534329795 3383667722193357801494693)
                    ·
                      refine ⟨634437697911254587780255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3383667722193357801494693 634437697911254587780255)
                      ·
                        rfl

theorem cell23_1235563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 4].length) (baseStart_1235563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235563 prefixEnd_1235563 := by exact prefixLift 1235563
  have htrace : WordTrace (prefixWord ++ tailWord_1235563) baseStart_1235563 baseEnd_1235563 := by
    simpa [prefixWord, tailWord_1235563, baseEnd_1235563] using wordTrace_append hprefix tailTrace_1235563
  have hstable : (prefixWord ++ tailWord_1235563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235563).length < 2 ^ (prefixWord ++ tailWord_1235563).sum := by decide
  have hdescent : baseEnd_1235563 < baseStart_1235563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235580 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 2, 4, 2]
def baseStart_1235580 : Nat := 118140960795 + 1235580 * 2 ^ 59
def prefixEnd_1235580 : Nat := 4983230072969 + 3 ^ 40 * 1235580 * 2
def baseEnd_1235580 : Nat := 634446427082381021267677

theorem tailTrace_1235580 : CollatzResearch.WordTrace tailWord_1235580 prefixEnd_1235580 634446427082381021267677 := by
  unfold tailWord_1235580
  simp only [CollatzResearch.WordTrace]
  refine ⟨22532652431856077554464097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30043536575808103405952129 22532652431856077554464097)
  ·
    refine ⟨16899489323892058165848073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22532652431856077554464097 16899489323892058165848073)
    ·
      refine ⟨12674616992919043624386055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16899489323892058165848073 12674616992919043624386055)
      ·
        refine ⟨19011925489378565436579083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12674616992919043624386055 19011925489378565436579083)
        ·
          refine ⟨28517888234067848154868625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19011925489378565436579083 28517888234067848154868625)
          ·
            refine ⟨21388416175550886116151469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28517888234067848154868625 21388416175550886116151469)
            ·
              refine ⟨8020656065831582293556801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21388416175550886116151469 8020656065831582293556801)
              ·
                refine ⟨6015492049373686720167601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8020656065831582293556801 6015492049373686720167601)
                ·
                  refine ⟨4511619037030265040125701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6015492049373686720167601 4511619037030265040125701)
                  ·
                    refine ⟨845928569443174695023569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4511619037030265040125701 845928569443174695023569)
                    ·
                      refine ⟨634446427082381021267677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 845928569443174695023569 634446427082381021267677)
                      ·
                        rfl

theorem cell23_1235580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_1235580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235580 prefixEnd_1235580 := by exact prefixLift 1235580
  have htrace : WordTrace (prefixWord ++ tailWord_1235580) baseStart_1235580 baseEnd_1235580 := by
    simpa [prefixWord, tailWord_1235580, baseEnd_1235580] using wordTrace_append hprefix tailTrace_1235580
  have hstable : (prefixWord ++ tailWord_1235580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235580).length < 2 ^ (prefixWord ++ tailWord_1235580).sum := by decide
  have hdescent : baseEnd_1235580 < baseStart_1235580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235647 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 3, 1, 3]
def baseStart_1235647 : Nat := 118140960795 + 1235647 * 2 ^ 59
def prefixEnd_1235647 : Nat := 4983230072969 + 3 ^ 40 * 1235647 * 2
def baseEnd_1235647 : Nat := 634480830286232259129869

theorem tailTrace_1235647 : CollatzResearch.WordTrace tailWord_1235647 prefixEnd_1235647 634480830286232259129869 := by
  unfold tailWord_1235647
  simp only [CollatzResearch.WordTrace]
  refine ⟨45067748554469425551617195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30045165702979617034411463 45067748554469425551617195)
  ·
    refine ⟨67601622831704138327425793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45067748554469425551617195 67601622831704138327425793)
    ·
      refine ⟨50701217123778103745569345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67601622831704138327425793 50701217123778103745569345)
      ·
        refine ⟨38025912842833577809177009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50701217123778103745569345 38025912842833577809177009)
        ·
          refine ⟨28519434632125183356882757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38025912842833577809177009 28519434632125183356882757)
          ·
            refine ⟨5347393993523471879415517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28519434632125183356882757 5347393993523471879415517)
            ·
              refine ⟨2005272747571301954780819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5347393993523471879415517 2005272747571301954780819)
              ·
                refine ⟨3007909121356952932171229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2005272747571301954780819 3007909121356952932171229)
                ·
                  refine ⟨1127965920508857349564211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3007909121356952932171229 1127965920508857349564211)
                  ·
                    refine ⟨1691948880763286024346317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1127965920508857349564211 1691948880763286024346317)
                    ·
                      refine ⟨634480830286232259129869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1691948880763286024346317 634480830286232259129869)
                      ·
                        rfl

theorem cell23_1235647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 1, 3].length) (baseStart_1235647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235647 prefixEnd_1235647 := by exact prefixLift 1235647
  have htrace : WordTrace (prefixWord ++ tailWord_1235647) baseStart_1235647 baseEnd_1235647 := by
    simpa [prefixWord, tailWord_1235647, baseEnd_1235647] using wordTrace_append hprefix tailTrace_1235647
  have hstable : (prefixWord ++ tailWord_1235647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235647).length < 2 ^ (prefixWord ++ tailWord_1235647).sum := by decide
  have hdescent : baseEnd_1235647 < baseStart_1235647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235697 : List Nat := [1, 2, 2, 2, 2, 2, 4, 2, 2, 4]
def baseStart_1235697 : Nat := 118140960795 + 1235697 * 2 ^ 59
def prefixEnd_1235697 : Nat := 4983230072969 + 3 ^ 40 * 1235697 * 2
def baseEnd_1235697 : Nat := 211502168106319021168213

theorem tailTrace_1235697 : CollatzResearch.WordTrace tailWord_1235697 prefixEnd_1235697 211502168106319021168213 := by
  unfold tailWord_1235697
  simp only [CollatzResearch.WordTrace]
  refine ⟨45069572204288284090937345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30046381469525522727291563 45069572204288284090937345)
  ·
    refine ⟨33802179153216213068203009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45069572204288284090937345 33802179153216213068203009)
    ·
      refine ⟨25351634364912159801152257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33802179153216213068203009 25351634364912159801152257)
      ·
        refine ⟨19013725773684119850864193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25351634364912159801152257 19013725773684119850864193)
        ·
          refine ⟨14260294330263089888148145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19013725773684119850864193 14260294330263089888148145)
          ·
            refine ⟨10695220747697317416111109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14260294330263089888148145 10695220747697317416111109)
            ·
              refine ⟨2005353890193247015520833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10695220747697317416111109 2005353890193247015520833)
              ·
                refine ⟨1504015417644935261640625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2005353890193247015520833 1504015417644935261640625)
                ·
                  refine ⟨1128011563233701446230469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1504015417644935261640625 1128011563233701446230469)
                  ·
                    refine ⟨211502168106319021168213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1128011563233701446230469 211502168106319021168213)
                    ·
                      rfl

theorem cell23_1235697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_1235697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235697 prefixEnd_1235697 := by exact prefixLift 1235697
  have htrace : WordTrace (prefixWord ++ tailWord_1235697) baseStart_1235697 baseEnd_1235697 := by
    simpa [prefixWord, tailWord_1235697, baseEnd_1235697] using wordTrace_append hprefix tailTrace_1235697
  have hstable : (prefixWord ++ tailWord_1235697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235697).length < 2 ^ (prefixWord ++ tailWord_1235697).sum := by decide
  have hdescent : baseEnd_1235697 < baseStart_1235697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235698 : List Nat := [3, 2, 1, 3, 1, 4, 2, 2, 1, 1, 3]
def baseStart_1235698 : Nat := 118140960795 + 1235698 * 2 ^ 59
def prefixEnd_1235698 : Nat := 4983230072969 + 3 ^ 40 * 1235698 * 2
def baseEnd_1235698 : Nat := 634507017799611559592135

theorem tailTrace_1235698 : CollatzResearch.WordTrace tailWord_1235698 prefixEnd_1235698 634507017799611559592135 := by
  unfold tailWord_1235698
  simp only [CollatzResearch.WordTrace]
  refine ⟨11267402169321165315430937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30046405784856440841149165 11267402169321165315430937)
  ·
    refine ⟨8450551626990873986573203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11267402169321165315430937 8450551626990873986573203)
    ·
      refine ⟨12675827440486310979859805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8450551626990873986573203 12675827440486310979859805)
      ·
        refine ⟨4753435290182366617447427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12675827440486310979859805 4753435290182366617447427)
        ·
          refine ⟨7130152935273549926171141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4753435290182366617447427 7130152935273549926171141)
          ·
            refine ⟨1336903675363790611157089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7130152935273549926171141 1336903675363790611157089)
            ·
              refine ⟨1002677756522842958367817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1336903675363790611157089 1002677756522842958367817)
              ·
                refine ⟨752008317392132218775863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1002677756522842958367817 752008317392132218775863)
                ·
                  refine ⟨1128012476088198328163795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 752008317392132218775863 1128012476088198328163795)
                  ·
                    refine ⟨1692018714132297492245693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1128012476088198328163795 1692018714132297492245693)
                    ·
                      refine ⟨634507017799611559592135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1692018714132297492245693 634507017799611559592135)
                      ·
                        rfl

theorem cell23_1235698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_1235698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235698 prefixEnd_1235698 := by exact prefixLift 1235698
  have htrace : WordTrace (prefixWord ++ tailWord_1235698) baseStart_1235698 baseEnd_1235698 := by
    simpa [prefixWord, tailWord_1235698, baseEnd_1235698] using wordTrace_append hprefix tailTrace_1235698
  have hstable : (prefixWord ++ tailWord_1235698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235698).length < 2 ^ (prefixWord ++ tailWord_1235698).sum := by decide
  have hdescent : baseEnd_1235698 < baseStart_1235698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235714 : List Nat := [3, 4, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_1235714 : Nat := 118140960795 + 1235714 * 2 ^ 59
def prefixEnd_1235714 : Nat := 4983230072969 + 3 ^ 40 * 1235714 * 2
def baseEnd_1235714 : Nat := 211505077830027832330687

theorem tailTrace_1235714 : CollatzResearch.WordTrace tailWord_1235714 prefixEnd_1235714 211505077830027832330687 := by
  unfold tailWord_1235714
  simp only [CollatzResearch.WordTrace]
  refine ⟨11267548061306673998576549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30046794830151130662870797 11267548061306673998576549)
  ·
    refine ⟨2112665261495001374733103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11267548061306673998576549 2112665261495001374733103)
    ·
      refine ⟨3168997892242502062099655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2112665261495001374733103 3168997892242502062099655)
      ·
        refine ⟨4753496838363753093149483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3168997892242502062099655 4753496838363753093149483)
        ·
          refine ⟨7130245257545629639724225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4753496838363753093149483 7130245257545629639724225)
          ·
            refine ⟨5347683943159222229793169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7130245257545629639724225 5347683943159222229793169)
            ·
              refine ⟨4010762957369416672344877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5347683943159222229793169 4010762957369416672344877)
              ·
                refine ⟨1504036109013531252129329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4010762957369416672344877 1504036109013531252129329)
                ·
                  refine ⟨1128027081760148439096997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1504036109013531252129329 1128027081760148439096997)
                  ·
                    refine ⟨211505077830027832330687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1128027081760148439096997 211505077830027832330687)
                    ·
                      rfl

theorem cell23_1235714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_1235714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235714 prefixEnd_1235714 := by exact prefixLift 1235714
  have htrace : WordTrace (prefixWord ++ tailWord_1235714) baseStart_1235714 baseEnd_1235714 := by
    simpa [prefixWord, tailWord_1235714, baseEnd_1235714] using wordTrace_append hprefix tailTrace_1235714
  have hstable : (prefixWord ++ tailWord_1235714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235714).length < 2 ^ (prefixWord ++ tailWord_1235714).sum := by decide
  have hdescent : baseEnd_1235714 < baseStart_1235714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235723 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 4, 7]
def baseStart_1235723 : Nat := 118140960795 + 1235723 * 2 ^ 59
def prefixEnd_1235723 : Nat := 4983230072969 + 3 ^ 40 * 1235723 * 2
def baseEnd_1235723 : Nat := 211506618271991320593173

theorem tailTrace_1235723 : CollatzResearch.WordTrace tailWord_1235723 prefixEnd_1235723 211506618271991320593173 := by
  unfold tailWord_1235723
  simp only [CollatzResearch.WordTrace]
  refine ⟨45070520502194090531383823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30047013668129393687589215 45070520502194090531383823)
  ·
    refine ⟨67605780753291135797075735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45070520502194090531383823 67605780753291135797075735)
    ·
      refine ⟨101408671129936703695613603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67605780753291135797075735 101408671129936703695613603)
      ·
        refine ⟨152113006694905055543420405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101408671129936703695613603 152113006694905055543420405)
        ·
          refine ⟨14260594377647348957195663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152113006694905055543420405 14260594377647348957195663)
          ·
            refine ⟨21390891566471023435793495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14260594377647348957195663 21390891566471023435793495)
            ·
              refine ⟨32086337349706535153690243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21390891566471023435793495 32086337349706535153690243)
              ·
                refine ⟨48129506024559802730535365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32086337349706535153690243 48129506024559802730535365)
                ·
                  refine ⟨9024282379604963011975381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48129506024559802730535365 9024282379604963011975381)
                  ·
                    refine ⟨211506618271991320593173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9024282379604963011975381 211506618271991320593173)
                    ·
                      rfl

theorem cell23_1235723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 7].length) (baseStart_1235723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235723 prefixEnd_1235723 := by exact prefixLift 1235723
  have htrace : WordTrace (prefixWord ++ tailWord_1235723) baseStart_1235723 baseEnd_1235723 := by
    simpa [prefixWord, tailWord_1235723, baseEnd_1235723] using wordTrace_append hprefix tailTrace_1235723
  have hstable : (prefixWord ++ tailWord_1235723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235723).length < 2 ^ (prefixWord ++ tailWord_1235723).sum := by decide
  have hdescent : baseEnd_1235723 < baseStart_1235723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235741 : List Nat := [1, 4, 2, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1235741 : Nat := 118140960795 + 1235741 * 2 ^ 59
def prefixEnd_1235741 : Nat := 4983230072969 + 3 ^ 40 * 1235741 * 2
def baseEnd_1235741 : Nat := 634529097467754891354437

theorem tailTrace_1235741 : CollatzResearch.WordTrace tailWord_1235741 prefixEnd_1235741 634529097467754891354437 := by
  unfold tailWord_1235741
  simp only [CollatzResearch.WordTrace]
  refine ⟨45071177016128879605539077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30047451344085919737026051 45071177016128879605539077)
  ·
    refine ⟨8450845690524164926038577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45071177016128879605539077 8450845690524164926038577)
    ·
      refine ⟨6338134267893123694528933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8450845690524164926038577 6338134267893123694528933)
      ·
        refine ⟨1188400175229960692724175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6338134267893123694528933 1188400175229960692724175)
        ·
          refine ⟨1782600262844941039086263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1188400175229960692724175 1782600262844941039086263)
          ·
            refine ⟨2673900394267411558629395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1782600262844941039086263 2673900394267411558629395)
            ·
              refine ⟨4010850591401117337944093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2673900394267411558629395 4010850591401117337944093)
              ·
                refine ⟨1504068971775419001729035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4010850591401117337944093 1504068971775419001729035)
                ·
                  refine ⟨2256103457663128502593553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1504068971775419001729035 2256103457663128502593553)
                  ·
                    refine ⟨1692077593247346376945165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2256103457663128502593553 1692077593247346376945165)
                    ·
                      refine ⟨634529097467754891354437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1692077593247346376945165 634529097467754891354437)
                      ·
                        rfl

theorem cell23_1235741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1235741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235741 prefixEnd_1235741 := by exact prefixLift 1235741
  have htrace : WordTrace (prefixWord ++ tailWord_1235741) baseStart_1235741 baseEnd_1235741 := by
    simpa [prefixWord, tailWord_1235741, baseEnd_1235741] using wordTrace_append hprefix tailTrace_1235741
  have hstable : (prefixWord ++ tailWord_1235741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235741).length < 2 ^ (prefixWord ++ tailWord_1235741).sum := by decide
  have hdescent : baseEnd_1235741 < baseStart_1235741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235753 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 3, 8]
def baseStart_1235753 : Nat := 118140960795 + 1235753 * 2 ^ 59
def prefixEnd_1235753 : Nat := 4983230072969 + 3 ^ 40 * 1235753 * 2
def baseEnd_1235753 : Nat := 211511753078536281468127

theorem tailTrace_1235753 : CollatzResearch.WordTrace tailWord_1235753 prefixEnd_1235753 211511753078536281468127 := by
  unfold tailWord_1235753
  simp only [CollatzResearch.WordTrace]
  refine ⟨45071614692085405654975913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30047743128056937103317275 45071614692085405654975913)
  ·
    refine ⟨33803711019064054241231935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45071614692085405654975913 33803711019064054241231935)
    ·
      refine ⟨50705566528596081361847903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33803711019064054241231935 50705566528596081361847903)
      ·
        refine ⟨76058349792894122042771855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50705566528596081361847903 76058349792894122042771855)
        ·
          refine ⟨114087524689341183064157783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76058349792894122042771855 114087524689341183064157783)
          ·
            refine ⟨171131287034011774596236675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114087524689341183064157783 171131287034011774596236675)
            ·
              refine ⟨256696930551017661894355013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171131287034011774596236675 256696930551017661894355013)
              ·
                refine ⟨48130674478315811605191565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 256696930551017661894355013 48130674478315811605191565)
                ·
                  refine ⟨18049002929368429351946837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48130674478315811605191565 18049002929368429351946837)
                  ·
                    refine ⟨211511753078536281468127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18049002929368429351946837 211511753078536281468127)
                    ·
                      rfl

theorem cell23_1235753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 8].length) (baseStart_1235753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235753 prefixEnd_1235753 := by exact prefixLift 1235753
  have htrace : WordTrace (prefixWord ++ tailWord_1235753) baseStart_1235753 baseEnd_1235753 := by
    simpa [prefixWord, tailWord_1235753, baseEnd_1235753] using wordTrace_append hprefix tailTrace_1235753
  have hstable : (prefixWord ++ tailWord_1235753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235753).length < 2 ^ (prefixWord ++ tailWord_1235753).sum := by decide
  have hdescent : baseEnd_1235753 < baseStart_1235753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235790 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_1235790 : Nat := 118140960795 + 1235790 * 2 ^ 59
def prefixEnd_1235790 : Nat := 4983230072969 + 3 ^ 40 * 1235790 * 2
def baseEnd_1235790 : Nat := 634554258019825199641711

theorem tailTrace_1235790 : CollatzResearch.WordTrace tailWord_1235790 prefixEnd_1235790 634554258019825199641711 := by
  unfold tailWord_1235790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5634120524118920121759103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30048642795300907316048549 5634120524118920121759103)
  ·
    refine ⟨8451180786178380182638655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5634120524118920121759103 8451180786178380182638655)
    ·
      refine ⟨12676771179267570273957983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8451180786178380182638655 12676771179267570273957983)
      ·
        refine ⟨19015156768901355410936975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12676771179267570273957983 19015156768901355410936975)
        ·
          refine ⟨28522735153352033116405463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19015156768901355410936975 28522735153352033116405463)
          ·
            refine ⟨42784102730028049674608195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28522735153352033116405463 42784102730028049674608195)
            ·
              refine ⟨64176154095042074511912293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42784102730028049674608195 64176154095042074511912293)
              ·
                refine ⟨12033028892820388970983555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64176154095042074511912293 12033028892820388970983555)
                ·
                  refine ⟨18049543339230583456475333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12033028892820388970983555 18049543339230583456475333)
                  ·
                    refine ⟨3384289376105734398089125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18049543339230583456475333 3384289376105734398089125)
                    ·
                      refine ⟨634554258019825199641711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3384289376105734398089125 634554258019825199641711)
                      ·
                        rfl

theorem cell23_1235790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_1235790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235790 prefixEnd_1235790 := by exact prefixLift 1235790
  have htrace : WordTrace (prefixWord ++ tailWord_1235790) baseStart_1235790 baseEnd_1235790 := by
    simpa [prefixWord, tailWord_1235790, baseEnd_1235790] using wordTrace_append hprefix tailTrace_1235790
  have hstable : (prefixWord ++ tailWord_1235790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235790).length < 2 ^ (prefixWord ++ tailWord_1235790).sum := by decide
  have hdescent : baseEnd_1235790 < baseStart_1235790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235794 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2]
def baseStart_1235794 : Nat := 118140960795 + 1235794 * 2 ^ 59
def prefixEnd_1235794 : Nat := 4983230072969 + 3 ^ 40 * 1235794 * 2
def baseEnd_1235794 : Nat := 634556311942443183991693

theorem tailTrace_1235794 : CollatzResearch.WordTrace tailWord_1235794 prefixEnd_1235794 634556311942443183991693 := by
  unfold tailWord_1235794
  simp only [CollatzResearch.WordTrace]
  refine ⟨11268277521234217414304609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30048740056624579771478957 11268277521234217414304609)
  ·
    refine ⟨8451208140925663060728457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11268277521234217414304609 8451208140925663060728457)
    ·
      refine ⟨6338406105694247295546343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8451208140925663060728457 6338406105694247295546343)
      ·
        refine ⟨9507609158541370943319515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6338406105694247295546343 9507609158541370943319515)
        ·
          refine ⟨14261413737812056414979273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9507609158541370943319515 14261413737812056414979273)
          ·
            refine ⟨10696060303359042311234455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14261413737812056414979273 10696060303359042311234455)
            ·
              refine ⟨16044090455038563466851683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10696060303359042311234455 16044090455038563466851683)
              ·
                refine ⟨24066135682557845200277525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16044090455038563466851683 24066135682557845200277525)
                ·
                  refine ⟨1128100110119898993763009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24066135682557845200277525 1128100110119898993763009)
                  ·
                    refine ⟨846075082589924245322257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1128100110119898993763009 846075082589924245322257)
                    ·
                      refine ⟨634556311942443183991693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 846075082589924245322257 634556311942443183991693)
                      ·
                        rfl

theorem cell23_1235794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_1235794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235794 prefixEnd_1235794 := by exact prefixLift 1235794
  have htrace : WordTrace (prefixWord ++ tailWord_1235794) baseStart_1235794 baseEnd_1235794 := by
    simpa [prefixWord, tailWord_1235794, baseEnd_1235794] using wordTrace_append hprefix tailTrace_1235794
  have hstable : (prefixWord ++ tailWord_1235794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235794).length < 2 ^ (prefixWord ++ tailWord_1235794).sum := by decide
  have hdescent : baseEnd_1235794 < baseStart_1235794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
