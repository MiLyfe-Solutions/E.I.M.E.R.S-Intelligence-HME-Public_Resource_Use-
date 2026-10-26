import V185TrunkScan23Chunk0394

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2335376 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 3]
def baseStart_2335376 : Nat := 118140960795 + 2335376 * 2 ^ 59
def prefixEnd_2335376 : Nat := 4983230072969 + 3 ^ 40 * 2335376 * 2
def baseEnd_2335376 : Nat := 1199170396974560064359807

theorem tailTrace_2335376 : CollatzResearch.WordTrace tailWord_2335376 prefixEnd_2335376 1199170396974560064359807 := by
  unfold tailWord_2335376
  simp only [CollatzResearch.WordTrace]
  refine ⟨42589080193669538655900991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56785440258226051541201321 42589080193669538655900991)
  ·
    refine ⟨63883620290504307983851487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42589080193669538655900991 63883620290504307983851487)
    ·
      refine ⟨95825430435756461975777231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63883620290504307983851487 95825430435756461975777231)
      ·
        refine ⟨143738145653634692963665847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95825430435756461975777231 143738145653634692963665847)
        ·
          refine ⟨215607218480452039445498771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143738145653634692963665847 215607218480452039445498771)
          ·
            refine ⟨323410827720678059168248157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215607218480452039445498771 323410827720678059168248157)
            ·
              refine ⟨121279060395254272188093059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 323410827720678059168248157 121279060395254272188093059)
              ·
                refine ⟨181918590592881408282139589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121279060395254272188093059 181918590592881408282139589)
                ·
                  refine ⟨34109735736165264052901173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181918590592881408282139589 34109735736165264052901173)
                  ·
                    refine ⟨3197787725265493504959485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34109735736165264052901173 3197787725265493504959485)
                    ·
                      refine ⟨1199170396974560064359807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3197787725265493504959485 1199170396974560064359807)
                      ·
                        rfl

theorem cell23_2335376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 3].length) (baseStart_2335376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335376 prefixEnd_2335376 := by exact prefixLift 2335376
  have htrace : WordTrace (prefixWord ++ tailWord_2335376) baseStart_2335376 baseEnd_2335376 := by
    simpa [prefixWord, tailWord_2335376, baseEnd_2335376] using wordTrace_append hprefix tailTrace_2335376
  have hstable : (prefixWord ++ tailWord_2335376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335376).length < 2 ^ (prefixWord ++ tailWord_2335376).sum := by decide
  have hdescent : baseEnd_2335376 < baseStart_2335376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335420 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 4, 3, 2]
def baseStart_2335420 : Nat := 118140960795 + 2335420 * 2 ^ 59
def prefixEnd_2335420 : Nat := 4983230072969 + 3 ^ 40 * 2335420 * 2
def baseEnd_2335420 : Nat := 1199192990123357892209605

theorem tailTrace_2335420 : CollatzResearch.WordTrace tailWord_2335420 prefixEnd_2335420 1199192990123357892209605 := by
  unfold tailWord_2335420
  simp only [CollatzResearch.WordTrace]
  refine ⟨42589882599589836413201857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56786510132786448550935809 42589882599589836413201857)
  ·
    refine ⟨31942411949692377309901393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42589882599589836413201857 31942411949692377309901393)
    ·
      refine ⟨23956808962269282982426045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31942411949692377309901393 23956808962269282982426045)
      ·
        refine ⟨8983803360850981118409767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23956808962269282982426045 8983803360850981118409767)
        ·
          refine ⟨13475705041276471677614651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8983803360850981118409767 13475705041276471677614651)
          ·
            refine ⟨20213557561914707516421977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13475705041276471677614651 20213557561914707516421977)
            ·
              refine ⟨15160168171436030637316483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20213557561914707516421977 15160168171436030637316483)
              ·
                refine ⟨22740252257154045955974725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15160168171436030637316483 22740252257154045955974725)
                ·
                  refine ⟨4263797298216383616745261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22740252257154045955974725 4263797298216383616745261)
                  ·
                    refine ⟨1598923986831143856279473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4263797298216383616745261 1598923986831143856279473)
                    ·
                      refine ⟨1199192990123357892209605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1598923986831143856279473 1199192990123357892209605)
                      ·
                        rfl

theorem cell23_2335420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_2335420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335420 prefixEnd_2335420 := by exact prefixLift 2335420
  have htrace : WordTrace (prefixWord ++ tailWord_2335420) baseStart_2335420 baseEnd_2335420 := by
    simpa [prefixWord, tailWord_2335420, baseEnd_2335420] using wordTrace_append hprefix tailTrace_2335420
  have hstable : (prefixWord ++ tailWord_2335420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335420).length < 2 ^ (prefixWord ++ tailWord_2335420).sum := by decide
  have hdescent : baseEnd_2335420 < baseStart_2335420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335450 : List Nat := [3, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4]
def baseStart_2335450 : Nat := 118140960795 + 2335450 * 2 ^ 59
def prefixEnd_2335450 : Nat := 4983230072969 + 3 ^ 40 * 2335450 * 2
def baseEnd_2335450 : Nat := 1199208394542992774834467

theorem tailTrace_2335450 : CollatzResearch.WordTrace tailWord_2335450 prefixEnd_2335450 1199208394542992774834467 := by
  unfold tailWord_2335450
  simp only [CollatzResearch.WordTrace]
  refine ⟨21295214847267746987498951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56787239592713991966663869 21295214847267746987498951)
  ·
    refine ⟨31942822270901620481248427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21295214847267746987498951 31942822270901620481248427)
    ·
      refine ⟨47914233406352430721872641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31942822270901620481248427 47914233406352430721872641)
      ·
        refine ⟨35935675054764323041404481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47914233406352430721872641 35935675054764323041404481)
        ·
          refine ⟨26951756291073242281053361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35935675054764323041404481 26951756291073242281053361)
          ·
            refine ⟨20213817218304931710790021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26951756291073242281053361 20213817218304931710790021)
            ·
              refine ⟨3790090728432174695773129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20213817218304931710790021 3790090728432174695773129)
              ·
                refine ⟨2842568046324131021829847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3790090728432174695773129 2842568046324131021829847)
                ·
                  refine ⟨4263852069486196532744771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2842568046324131021829847 4263852069486196532744771)
                  ·
                    refine ⟨6395778104229294799117157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4263852069486196532744771 6395778104229294799117157)
                    ·
                      refine ⟨1199208394542992774834467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6395778104229294799117157 1199208394542992774834467)
                      ·
                        rfl

theorem cell23_2335450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_2335450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335450 prefixEnd_2335450 := by exact prefixLift 2335450
  have htrace : WordTrace (prefixWord ++ tailWord_2335450) baseStart_2335450 baseEnd_2335450 := by
    simpa [prefixWord, tailWord_2335450, baseEnd_2335450] using wordTrace_append hprefix tailTrace_2335450
  have hstable : (prefixWord ++ tailWord_2335450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335450).length < 2 ^ (prefixWord ++ tailWord_2335450).sum := by decide
  have hdescent : baseEnd_2335450 < baseStart_2335450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335470 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_2335470 : Nat := 118140960795 + 2335470 * 2 ^ 59
def prefixEnd_2335470 : Nat := 4983230072969 + 3 ^ 40 * 2335470 * 2
def baseEnd_2335470 : Nat := 1199218664156082696584375

theorem tailTrace_2335470 : CollatzResearch.WordTrace tailWord_2335470 prefixEnd_2335470 1199218664156082696584375 := by
  unfold tailWord_2335470
  simp only [CollatzResearch.WordTrace]
  refine ⟨10647698606124816420715483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56787725899332354243815909 10647698606124816420715483)
  ·
    refine ⟨15971547909187224631073225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10647698606124816420715483 15971547909187224631073225)
    ·
      refine ⟨11978660931890418473304919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15971547909187224631073225 11978660931890418473304919)
      ·
        refine ⟨17967991397835627709957379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11978660931890418473304919 17967991397835627709957379)
        ·
          refine ⟨26951987096753441564936069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17967991397835627709957379 26951987096753441564936069)
          ·
            refine ⟨5053497580641270293425513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26951987096753441564936069 5053497580641270293425513)
            ·
              refine ⟨3790123185480952720069135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5053497580641270293425513 3790123185480952720069135)
              ·
                refine ⟨5685184778221429080103703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3790123185480952720069135 5685184778221429080103703)
                ·
                  refine ⟨8527777167332143620155555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5685184778221429080103703 8527777167332143620155555)
                  ·
                    refine ⟨12791665750998215430233333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8527777167332143620155555 12791665750998215430233333)
                    ·
                      refine ⟨1199218664156082696584375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12791665750998215430233333 1199218664156082696584375)
                      ·
                        rfl

theorem cell23_2335470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_2335470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335470 prefixEnd_2335470 := by exact prefixLift 2335470
  have htrace : WordTrace (prefixWord ++ tailWord_2335470) baseStart_2335470 baseEnd_2335470 := by
    simpa [prefixWord, tailWord_2335470, baseEnd_2335470] using wordTrace_append hprefix tailTrace_2335470
  have hstable : (prefixWord ++ tailWord_2335470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335470).length < 2 ^ (prefixWord ++ tailWord_2335470).sum := by decide
  have hdescent : baseEnd_2335470 < baseStart_2335470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335484 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 3, 2, 2]
def baseStart_2335484 : Nat := 118140960795 + 2335484 * 2 ^ 59
def prefixEnd_2335484 : Nat := 4983230072969 + 3 ^ 40 * 2335484 * 2
def baseEnd_2335484 : Nat := 1199225852885245641809311

theorem tailTrace_2335484 : CollatzResearch.WordTrace tailWord_2335484 prefixEnd_2335484 1199225852885245641809311 := by
  unfold tailWord_2335484
  simp only [CollatzResearch.WordTrace]
  refine ⟨42591049735473905878366753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56788066313965207837822337 42591049735473905878366753)
  ·
    refine ⟨31943287301605429408775065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42591049735473905878366753 31943287301605429408775065)
    ·
      refine ⟨23957465476204072056581299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31943287301605429408775065 23957465476204072056581299)
      ·
        refine ⟨35936198214306108084871949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23957465476204072056581299 35936198214306108084871949)
        ·
          refine ⟨13476074330364790531826981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35936198214306108084871949 13476074330364790531826981)
          ·
            refine ⟨2526763936943398224717559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13476074330364790531826981 2526763936943398224717559)
            ·
              refine ⟨3790145905415097337076339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2526763936943398224717559 3790145905415097337076339)
              ·
                refine ⟨5685218858122646005614509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3790145905415097337076339 5685218858122646005614509)
                ·
                  refine ⟨2131957071795992252105441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5685218858122646005614509 2131957071795992252105441)
                  ·
                    refine ⟨1598967803846994189079081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2131957071795992252105441 1598967803846994189079081)
                    ·
                      refine ⟨1199225852885245641809311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1598967803846994189079081 1199225852885245641809311)
                      ·
                        rfl

theorem cell23_2335484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_2335484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335484 prefixEnd_2335484 := by exact prefixLift 2335484
  have htrace : WordTrace (prefixWord ++ tailWord_2335484) baseStart_2335484 baseEnd_2335484 := by
    simpa [prefixWord, tailWord_2335484, baseEnd_2335484] using wordTrace_append hprefix tailTrace_2335484
  have hstable : (prefixWord ++ tailWord_2335484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335484).length < 2 ^ (prefixWord ++ tailWord_2335484).sum := by decide
  have hdescent : baseEnd_2335484 < baseStart_2335484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335490 : List Nat := [3, 4, 1, 1, 1, 3, 2, 8]
def baseStart_2335490 : Nat := 118140960795 + 2335490 * 2 ^ 59
def prefixEnd_2335490 : Nat := 4983230072969 + 3 ^ 40 * 2335490 * 2
def baseEnd_2335490 : Nat := 44415886435895282160529

theorem tailTrace_2335490 : CollatzResearch.WordTrace tailWord_2335490 prefixEnd_2335490 44415886435895282160529 := by
  unfold tailWord_2335490
  simp only [CollatzResearch.WordTrace]
  refine ⟨21295579577231518695362981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56788212205950716520967949 21295579577231518695362981)
  ·
    refine ⟨3992921170730909755380559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21295579577231518695362981 3992921170730909755380559)
    ·
      refine ⟨5989381756096364633070839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3992921170730909755380559 5989381756096364633070839)
      ·
        refine ⟨8984072634144546949606259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5989381756096364633070839 8984072634144546949606259)
        ·
          refine ⟨13476108951216820424409389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8984072634144546949606259 13476108951216820424409389)
          ·
            refine ⟨5053540856706307659153521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13476108951216820424409389 5053540856706307659153521)
            ·
              refine ⟨3790155642529730744365141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5053540856706307659153521 3790155642529730744365141)
              ·
                refine ⟨44415886435895282160529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3790155642529730744365141 44415886435895282160529)
                ·
                  rfl

theorem cell23_2335490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 8].length) (baseStart_2335490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335490 prefixEnd_2335490 := by exact prefixLift 2335490
  have htrace : WordTrace (prefixWord ++ tailWord_2335490) baseStart_2335490 baseEnd_2335490 := by
    simpa [prefixWord, tailWord_2335490, baseEnd_2335490] using wordTrace_append hprefix tailTrace_2335490
  have hstable : (prefixWord ++ tailWord_2335490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335490).length < 2 ^ (prefixWord ++ tailWord_2335490).sum := by decide
  have hdescent : baseEnd_2335490 < baseStart_2335490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335534 : List Nat := [4, 1, 3, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_2335534 : Nat := 118140960795 + 2335534 * 2 ^ 59
def prefixEnd_2335534 : Nat := 4983230072969 + 3 ^ 40 * 2335534 * 2
def baseEnd_2335534 : Nat := 1199251526917970446184081

theorem tailTrace_2335534 : CollatzResearch.WordTrace tailWord_2335534 prefixEnd_2335534 1199251526917970446184081 := by
  unfold tailWord_2335534
  simp only [CollatzResearch.WordTrace]
  refine ⟨10647990390095833787006707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56789282080511113530702437 10647990390095833787006707)
  ·
    refine ⟨15971985585143750680510061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10647990390095833787006707 15971985585143750680510061)
    ·
      refine ⟨5989494594428906505191273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15971985585143750680510061 5989494594428906505191273)
      ·
        refine ⟨4492120945821679878893455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5989494594428906505191273 4492120945821679878893455)
        ·
          refine ⟨6738181418732519818340183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4492120945821679878893455 6738181418732519818340183)
          ·
            refine ⟨10107272128098779727510275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6738181418732519818340183 10107272128098779727510275)
            ·
              refine ⟨15160908192148169591265413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10107272128098779727510275 15160908192148169591265413)
              ·
                refine ⟨2842670286027781798362265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15160908192148169591265413 2842670286027781798362265)
                ·
                  refine ⟨2132002714520836348771699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2842670286027781798362265 2132002714520836348771699)
                  ·
                    refine ⟨3198004071781254523157549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2132002714520836348771699 3198004071781254523157549)
                    ·
                      refine ⟨1199251526917970446184081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3198004071781254523157549 1199251526917970446184081)
                      ·
                        rfl

theorem cell23_2335534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_2335534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335534 prefixEnd_2335534 := by exact prefixLift 2335534
  have htrace : WordTrace (prefixWord ++ tailWord_2335534) baseStart_2335534 baseEnd_2335534 := by
    simpa [prefixWord, tailWord_2335534, baseEnd_2335534] using wordTrace_append hprefix tailTrace_2335534
  have hstable : (prefixWord ++ tailWord_2335534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335534).length < 2 ^ (prefixWord ++ tailWord_2335534).sum := by decide
  have hdescent : baseEnd_2335534 < baseStart_2335534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335543 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 3]
def baseStart_2335543 : Nat := 118140960795 + 2335543 * 2 ^ 59
def prefixEnd_2335543 : Nat := 4983230072969 + 3 ^ 40 * 2335543 * 2
def baseEnd_2335543 : Nat := 1199256148243860910971539

theorem tailTrace_2335543 : CollatzResearch.WordTrace tailWord_2335543 prefixEnd_2335543 1199256148243860910971539 := by
  unfold tailWord_2335543
  simp only [CollatzResearch.WordTrace]
  refine ⟨85184251377734064833131283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56789500918489376555420855 85184251377734064833131283)
  ·
    refine ⟨127776377066601097249696925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85184251377734064833131283 127776377066601097249696925)
    ·
      refine ⟨47916141399975411468636347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127776377066601097249696925 47916141399975411468636347)
      ·
        refine ⟨71874212099963117202954521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47916141399975411468636347 71874212099963117202954521)
        ·
          refine ⟨53905659074972337902215891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71874212099963117202954521 53905659074972337902215891)
          ·
            refine ⟨80858488612458506853323837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53905659074972337902215891 80858488612458506853323837)
            ·
              refine ⟨30321933229671940069996439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80858488612458506853323837 30321933229671940069996439)
              ·
                refine ⟨45482899844507910104994659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30321933229671940069996439 45482899844507910104994659)
                ·
                  refine ⟨68224349766761865157491989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45482899844507910104994659 68224349766761865157491989)
                  ·
                    refine ⟨3198016395316962429257437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68224349766761865157491989 3198016395316962429257437)
                    ·
                      refine ⟨1199256148243860910971539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3198016395316962429257437 1199256148243860910971539)
                      ·
                        rfl

theorem cell23_2335543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_2335543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335543 prefixEnd_2335543 := by exact prefixLift 2335543
  have htrace : WordTrace (prefixWord ++ tailWord_2335543) baseStart_2335543 baseEnd_2335543 := by
    simpa [prefixWord, tailWord_2335543, baseEnd_2335543] using wordTrace_append hprefix tailTrace_2335543
  have hstable : (prefixWord ++ tailWord_2335543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335543).length < 2 ^ (prefixWord ++ tailWord_2335543).sum := by decide
  have hdescent : baseEnd_2335543 < baseStart_2335543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335591 : List Nat := [1, 1, 5, 1, 2, 4, 1, 2, 2, 2, 2]
def baseStart_2335591 : Nat := 118140960795 + 2335591 * 2 ^ 59
def prefixEnd_2335591 : Nat := 4983230072969 + 3 ^ 40 * 2335591 * 2
def baseEnd_2335591 : Nat := 1199280795315276723171319

theorem tailTrace_2335591 : CollatzResearch.WordTrace tailWord_2335591 prefixEnd_2335591 1199280795315276723171319 := by
  unfold tailWord_2335591
  simp only [CollatzResearch.WordTrace]
  refine ⟨85186002081560169030878627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56790668054373446020585751 85186002081560169030878627)
  ·
    refine ⟨127779003122340253546317941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85186002081560169030878627 127779003122340253546317941)
    ·
      refine ⟨11979281542719398769967307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127779003122340253546317941 11979281542719398769967307)
      ·
        refine ⟨17968922314079098154950961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11979281542719398769967307 17968922314079098154950961)
        ·
          refine ⟨13476691735559323616213221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17968922314079098154950961 13476691735559323616213221)
          ·
            refine ⟨2526879700417373178039979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13476691735559323616213221 2526879700417373178039979)
            ·
              refine ⟨3790319550626059767059969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2526879700417373178039979 3790319550626059767059969)
              ·
                refine ⟨2842739662969544825294977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3790319550626059767059969 2842739662969544825294977)
                ·
                  refine ⟨2132054747227158618971233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2842739662969544825294977 2132054747227158618971233)
                  ·
                    refine ⟨1599041060420368964228425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2132054747227158618971233 1599041060420368964228425)
                    ·
                      refine ⟨1199280795315276723171319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1599041060420368964228425 1199280795315276723171319)
                      ·
                        rfl

theorem cell23_2335591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_2335591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335591 prefixEnd_2335591 := by exact prefixLift 2335591
  have htrace : WordTrace (prefixWord ++ tailWord_2335591) baseStart_2335591 baseEnd_2335591 := by
    simpa [prefixWord, tailWord_2335591, baseEnd_2335591] using wordTrace_append hprefix tailTrace_2335591
  have hstable : (prefixWord ++ tailWord_2335591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335591).length < 2 ^ (prefixWord ++ tailWord_2335591).sum := by decide
  have hdescent : baseEnd_2335591 < baseStart_2335591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335600 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 1, 7, 2]
def baseStart_2335600 : Nat := 118140960795 + 2335600 * 2 ^ 59
def prefixEnd_2335600 : Nat := 4983230072969 + 3 ^ 40 * 2335600 * 2
def baseEnd_2335600 : Nat := 1199285416641167187958777

theorem tailTrace_2335600 : CollatzResearch.WordTrace tailWord_2335600 prefixEnd_2335600 1199285416641167187958777 := by
  unfold tailWord_2335600
  simp only [CollatzResearch.WordTrace]
  refine ⟨42593165169263781783978127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56790886892351709045304169 42593165169263781783978127)
  ·
    refine ⟨63889747753895672675967191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42593165169263781783978127 63889747753895672675967191)
    ·
      refine ⟨95834621630843509013950787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63889747753895672675967191 95834621630843509013950787)
      ·
        refine ⟨143751932446265263520926181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95834621630843509013950787 143751932446265263520926181)
        ·
          refine ⟨26953487333674736910173659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143751932446265263520926181 26953487333674736910173659)
          ·
            refine ⟨40430231000512105365260489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26953487333674736910173659 40430231000512105365260489)
            ·
              refine ⟨30322673250384079023945367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40430231000512105365260489 30322673250384079023945367)
              ·
                refine ⟨45484009875576118535918051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30322673250384079023945367 45484009875576118535918051)
                ·
                  refine ⟨68226014813364177803877077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45484009875576118535918051 68226014813364177803877077)
                  ·
                    refine ⟨1599047222188222917278369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 68226014813364177803877077 1599047222188222917278369)
                    ·
                      refine ⟨1199285416641167187958777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1599047222188222917278369 1199285416641167187958777)
                      ·
                        rfl

theorem cell23_2335600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 7, 2].length) (baseStart_2335600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335600 prefixEnd_2335600 := by exact prefixLift 2335600
  have htrace : WordTrace (prefixWord ++ tailWord_2335600) baseStart_2335600 baseEnd_2335600 := by
    simpa [prefixWord, tailWord_2335600, baseEnd_2335600] using wordTrace_append hprefix tailTrace_2335600
  have hstable : (prefixWord ++ tailWord_2335600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335600).length < 2 ^ (prefixWord ++ tailWord_2335600).sum := by decide
  have hdescent : baseEnd_2335600 < baseStart_2335600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335603 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 5]
def baseStart_2335603 : Nat := 118140960795 + 2335603 * 2 ^ 59
def prefixEnd_2335603 : Nat := 4983230072969 + 3 ^ 40 * 2335603 * 2
def baseEnd_2335603 : Nat := 1199286957083130676221263

theorem tailTrace_2335603 : CollatzResearch.WordTrace tailWord_2335603 prefixEnd_2335603 1199286957083130676221263 := by
  unfold tailWord_2335603
  simp only [CollatzResearch.WordTrace]
  refine ⟨85186439757516695080315463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56790959838344463386876975 85186439757516695080315463)
  ·
    refine ⟨127779659636275042620473195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85186439757516695080315463 127779659636275042620473195)
    ·
      refine ⟨191669489454412563930709793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127779659636275042620473195 191669489454412563930709793)
      ·
        refine ⟨143752117090809422948032345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191669489454412563930709793 143752117090809422948032345)
        ·
          refine ⟨107814087818107067211024259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143752117090809422948032345 107814087818107067211024259)
          ·
            refine ⟨161721131727160600816536389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107814087818107067211024259 161721131727160600816536389)
            ·
              refine ⟨30322712198842612653100573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161721131727160600816536389 30322712198842612653100573)
              ·
                refine ⟨11371017074565979744912715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30322712198842612653100573 11371017074565979744912715)
                ·
                  refine ⟨17056525611848969617369073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11371017074565979744912715 17056525611848969617369073)
                  ·
                    refine ⟨12792394208886727213026805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17056525611848969617369073 12792394208886727213026805)
                    ·
                      refine ⟨1199286957083130676221263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12792394208886727213026805 1199286957083130676221263)
                      ·
                        rfl

theorem cell23_2335603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_2335603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335603 prefixEnd_2335603 := by exact prefixLift 2335603
  have htrace : WordTrace (prefixWord ++ tailWord_2335603) baseStart_2335603 baseEnd_2335603 := by
    simpa [prefixWord, tailWord_2335603, baseEnd_2335603] using wordTrace_append hprefix tailTrace_2335603
  have hstable : (prefixWord ++ tailWord_2335603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335603).length < 2 ^ (prefixWord ++ tailWord_2335603).sum := by decide
  have hdescent : baseEnd_2335603 < baseStart_2335603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335633 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 5]
def baseStart_2335633 : Nat := 118140960795 + 2335633 * 2 ^ 59
def prefixEnd_2335633 : Nat := 4983230072969 + 3 ^ 40 * 2335633 * 2
def baseEnd_2335633 : Nat := 1199302361502765558846125

theorem tailTrace_2335633 : CollatzResearch.WordTrace tailWord_2335633 prefixEnd_2335633 1199302361502765558846125 := by
  unfold tailWord_2335633
  simp only [CollatzResearch.WordTrace]
  refine ⟨85187533947408010203907553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56791689298272006802605035 85187533947408010203907553)
  ·
    refine ⟨63890650460556007652930665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85187533947408010203907553 63890650460556007652930665)
    ·
      refine ⟨47917987845417005739697999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63890650460556007652930665 47917987845417005739697999)
      ·
        refine ⟨71876981768125508609546999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47917987845417005739697999 71876981768125508609546999)
        ·
          refine ⟨107815472652188262914320499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71876981768125508609546999 107815472652188262914320499)
          ·
            refine ⟨161723208978282394371480749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107815472652188262914320499 161723208978282394371480749)
            ·
              refine ⟨60646203366855897889305281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161723208978282394371480749 60646203366855897889305281)
              ·
                refine ⟨45484652525141923416978961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60646203366855897889305281 45484652525141923416978961)
                ·
                  refine ⟨34113489393856442562734221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45484652525141923416978961 34113489393856442562734221)
                  ·
                    refine ⟨12792558522696165961025333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34113489393856442562734221 12792558522696165961025333)
                    ·
                      refine ⟨1199302361502765558846125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12792558522696165961025333 1199302361502765558846125)
                      ·
                        rfl

theorem cell23_2335633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_2335633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335633 prefixEnd_2335633 := by exact prefixLift 2335633
  have htrace : WordTrace (prefixWord ++ tailWord_2335633) baseStart_2335633 baseEnd_2335633 := by
    simpa [prefixWord, tailWord_2335633, baseEnd_2335633] using wordTrace_append hprefix tailTrace_2335633
  have hstable : (prefixWord ++ tailWord_2335633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335633).length < 2 ^ (prefixWord ++ tailWord_2335633).sum := by decide
  have hdescent : baseEnd_2335633 < baseStart_2335633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335647 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 4]
def baseStart_2335647 : Nat := 118140960795 + 2335647 * 2 ^ 59
def prefixEnd_2335647 : Nat := 4983230072969 + 3 ^ 40 * 2335647 * 2
def baseEnd_2335647 : Nat := 1199309550231928504071061

theorem tailTrace_2335647 : CollatzResearch.WordTrace tailWord_2335647 prefixEnd_2335647 1199309550231928504071061 := by
  unfold tailWord_2335647
  simp only [CollatzResearch.WordTrace]
  refine ⟨85188044569357290594917195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56792029712904860396611463 85188044569357290594917195)
  ·
    refine ⟨127782066854035935892375793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85188044569357290594917195 127782066854035935892375793)
    ·
      refine ⟨95836550140526951919281845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127782066854035935892375793 95836550140526951919281845)
      ·
        refine ⟨8984676575674401742432673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95836550140526951919281845 8984676575674401742432673)
        ·
          refine ⟨6738507431755801306824505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8984676575674401742432673 6738507431755801306824505)
          ·
            refine ⟨5053880573816850980118379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6738507431755801306824505 5053880573816850980118379)
            ·
              refine ⟨7580820860725276470177569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5053880573816850980118379 7580820860725276470177569)
              ·
                refine ⟨5685615645543957352633177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7580820860725276470177569 5685615645543957352633177)
                ·
                  refine ⟨4264211734157968014474883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5685615645543957352633177 4264211734157968014474883)
                  ·
                    refine ⟨6396317601236952021712325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4264211734157968014474883 6396317601236952021712325)
                    ·
                      refine ⟨1199309550231928504071061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6396317601236952021712325 1199309550231928504071061)
                      ·
                        rfl

theorem cell23_2335647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_2335647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335647 prefixEnd_2335647 := by exact prefixLift 2335647
  have htrace : WordTrace (prefixWord ++ tailWord_2335647) baseStart_2335647 baseEnd_2335647 := by
    simpa [prefixWord, tailWord_2335647, baseEnd_2335647] using wordTrace_append hprefix tailTrace_2335647
  have hstable : (prefixWord ++ tailWord_2335647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335647).length < 2 ^ (prefixWord ++ tailWord_2335647).sum := by decide
  have hdescent : baseEnd_2335647 < baseStart_2335647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335683 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 2, 9]
def baseStart_2335683 : Nat := 118140960795 + 2335683 * 2 ^ 59
def prefixEnd_2335683 : Nat := 4983230072969 + 3 ^ 40 * 2335683 * 2
def baseEnd_2335683 : Nat := 399776011845163454406965

theorem tailTrace_2335683 : CollatzResearch.WordTrace tailWord_2335683 prefixEnd_2335683 399776011845163454406965 := by
  unfold tailWord_2335683
  simp only [CollatzResearch.WordTrace]
  refine ⟨85189357597226868743227703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56792905064817912495485135 85189357597226868743227703)
  ·
    refine ⟨127784036395840303114841555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85189357597226868743227703 127784036395840303114841555)
    ·
      refine ⟨191676054593760454672262333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127784036395840303114841555 191676054593760454672262333)
      ·
        refine ⟨71878520472660170502098375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191676054593760454672262333 71878520472660170502098375)
        ·
          refine ⟨107817780708990255753147563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71878520472660170502098375 107817780708990255753147563)
          ·
            refine ⟨161726671063485383629721345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107817780708990255753147563 161726671063485383629721345)
            ·
              refine ⟨121295003297614037722291009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161726671063485383629721345 121295003297614037722291009)
              ·
                refine ⟨90971252473210528291718257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121295003297614037722291009 90971252473210528291718257)
                ·
                  refine ⟨68228439354907896218788693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90971252473210528291718257 68228439354907896218788693)
                  ·
                    refine ⟨399776011845163454406965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 68228439354907896218788693 399776011845163454406965)
                    ·
                      rfl

theorem cell23_2335683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 9].length) (baseStart_2335683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335683 prefixEnd_2335683 := by exact prefixLift 2335683
  have htrace : WordTrace (prefixWord ++ tailWord_2335683) baseStart_2335683 baseEnd_2335683 := by
    simpa [prefixWord, tailWord_2335683, baseEnd_2335683] using wordTrace_append hprefix tailTrace_2335683
  have hstable : (prefixWord ++ tailWord_2335683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335683).length < 2 ^ (prefixWord ++ tailWord_2335683).sum := by decide
  have hdescent : baseEnd_2335683 < baseStart_2335683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335732 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_2335732 : Nat := 118140960795 + 2335732 * 2 ^ 59
def prefixEnd_2335732 : Nat := 4983230072969 + 3 ^ 40 * 2335732 * 2
def baseEnd_2335732 : Nat := 1199353196087560671508171

theorem tailTrace_2335732 : CollatzResearch.WordTrace tailWord_2335732 prefixEnd_2335732 1199353196087560671508171 := by
  unfold tailWord_2335732
  simp only [CollatzResearch.WordTrace]
  refine ⟨42595572387024675055880725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56794096516032900074507633 42595572387024675055880725)
  ·
    refine ⟨1996667455641781643244409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42595572387024675055880725 1996667455641781643244409)
    ·
      refine ⟨1497500591731336232433307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1996667455641781643244409 1497500591731336232433307)
      ·
        refine ⟨2246250887597004348649961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1497500591731336232433307 2246250887597004348649961)
        ·
          refine ⟨1684688165697753261487471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2246250887597004348649961 1684688165697753261487471)
          ·
            refine ⟨2527032248546629892231207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1684688165697753261487471 2527032248546629892231207)
            ·
              refine ⟨3790548372819944838346811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2527032248546629892231207 3790548372819944838346811)
              ·
                refine ⟨5685822559229917257520217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3790548372819944838346811 5685822559229917257520217)
                ·
                  refine ⟨4264366919422437943140163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5685822559229917257520217 4264366919422437943140163)
                  ·
                    refine ⟨6396550379133656914710245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4264366919422437943140163 6396550379133656914710245)
                    ·
                      refine ⟨1199353196087560671508171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6396550379133656914710245 1199353196087560671508171)
                      ·
                        rfl

theorem cell23_2335732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_2335732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335732 prefixEnd_2335732 := by exact prefixLift 2335732
  have htrace : WordTrace (prefixWord ++ tailWord_2335732) baseStart_2335732 baseEnd_2335732 := by
    simpa [prefixWord, tailWord_2335732, baseEnd_2335732] using wordTrace_append hprefix tailTrace_2335732
  have hstable : (prefixWord ++ tailWord_2335732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335732).length < 2 ^ (prefixWord ++ tailWord_2335732).sum := by decide
  have hdescent : baseEnd_2335732 < baseStart_2335732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335737 : List Nat := [1, 2, 1, 3, 1, 3, 2, 4, 1, 1, 4]
def baseStart_2335737 : Nat := 118140960795 + 2335737 * 2 ^ 59
def prefixEnd_2335737 : Nat := 4983230072969 + 3 ^ 40 * 2335737 * 2
def baseEnd_2335737 : Nat := 1199355763490833151945647

theorem tailTrace_2335737 : CollatzResearch.WordTrace tailWord_2335737 prefixEnd_2335737 1199355763490833151945647 := by
  unfold tailWord_2335737
  simp only [CollatzResearch.WordTrace]
  refine ⟨85191327139031235965693465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56794218092687490643795643 85191327139031235965693465)
  ·
    refine ⟨63893495354273426974270099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85191327139031235965693465 63893495354273426974270099)
    ·
      refine ⟨95840243031410140461405149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63893495354273426974270099 95840243031410140461405149)
      ·
        refine ⟨35940091136778802673026931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95840243031410140461405149 35940091136778802673026931)
        ·
          refine ⟨53910136705168204009540397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35940091136778802673026931 53910136705168204009540397)
          ·
            refine ⟨20216301264438076503577649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53910136705168204009540397 20216301264438076503577649)
            ·
              refine ⟨15162225948328557377683237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20216301264438076503577649 15162225948328557377683237)
              ·
                refine ⟨2842917365311604508315607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15162225948328557377683237 2842917365311604508315607)
                ·
                  refine ⟨4264376047967406762473411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2842917365311604508315607 4264376047967406762473411)
                  ·
                    refine ⟨6396564071951110143710117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4264376047967406762473411 6396564071951110143710117)
                    ·
                      refine ⟨1199355763490833151945647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6396564071951110143710117 1199355763490833151945647)
                      ·
                        rfl

theorem cell23_2335737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_2335737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335737 prefixEnd_2335737 := by exact prefixLift 2335737
  have htrace : WordTrace (prefixWord ++ tailWord_2335737) baseStart_2335737 baseEnd_2335737 := by
    simpa [prefixWord, tailWord_2335737, baseEnd_2335737] using wordTrace_append hprefix tailTrace_2335737
  have hstable : (prefixWord ++ tailWord_2335737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335737).length < 2 ^ (prefixWord ++ tailWord_2335737).sum := by decide
  have hdescent : baseEnd_2335737 < baseStart_2335737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335754 : List Nat := [3, 1, 2, 2, 3, 2, 1, 3, 1, 1, 4]
def baseStart_2335754 : Nat := 118140960795 + 2335754 * 2 ^ 59
def prefixEnd_2335754 : Nat := 4983230072969 + 3 ^ 40 * 2335754 * 2
def baseEnd_2335754 : Nat := 1199364492661959585433069

theorem tailTrace_2335754 : CollatzResearch.WordTrace tailWord_2335754 prefixEnd_2335754 1199364492661959585433069 := by
  unfold tailWord_2335754
  simp only [CollatzResearch.WordTrace]
  refine ⟨21297986794992411967265579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56794631453313098579374877 21297986794992411967265579)
  ·
    refine ⟨31946980192488617950898369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21297986794992411967265579 31946980192488617950898369)
    ·
      refine ⟨23960235144366463463173777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31946980192488617950898369 23960235144366463463173777)
      ·
        refine ⟨17970176358274847597380333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23960235144366463463173777 17970176358274847597380333)
        ·
          refine ⟨6738816134353067849017625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17970176358274847597380333 6738816134353067849017625)
          ·
            refine ⟨5054112100764800886763219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6738816134353067849017625 5054112100764800886763219)
            ·
              refine ⟨7581168151147201330144829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5054112100764800886763219 7581168151147201330144829)
              ·
                refine ⟨2842938056680200498804311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7581168151147201330144829 2842938056680200498804311)
                ·
                  refine ⟨4264407085020300748206467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2842938056680200498804311 4264407085020300748206467)
                  ·
                    refine ⟨6396610627530451122309701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4264407085020300748206467 6396610627530451122309701)
                    ·
                      refine ⟨1199364492661959585433069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6396610627530451122309701 1199364492661959585433069)
                      ·
                        rfl

theorem cell23_2335754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_2335754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335754 prefixEnd_2335754 := by exact prefixLift 2335754
  have htrace : WordTrace (prefixWord ++ tailWord_2335754) baseStart_2335754 baseEnd_2335754 := by
    simpa [prefixWord, tailWord_2335754, baseEnd_2335754] using wordTrace_append hprefix tailTrace_2335754
  have hstable : (prefixWord ++ tailWord_2335754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335754).length < 2 ^ (prefixWord ++ tailWord_2335754).sum := by decide
  have hdescent : baseEnd_2335754 < baseStart_2335754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335804 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 4, 1, 3]
def baseStart_2335804 : Nat := 118140960795 + 2335804 * 2 ^ 59
def prefixEnd_2335804 : Nat := 4983230072969 + 3 ^ 40 * 2335804 * 2
def baseEnd_2335804 : Nat := 1199390166694684389807839

theorem tailTrace_2335804 : CollatzResearch.WordTrace tailWord_2335804 prefixEnd_2335804 1199390166694684389807839 := by
  unfold tailWord_2335804
  simp only [CollatzResearch.WordTrace]
  refine ⟨42596885414894253204191233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56795847219859004272254977 42596885414894253204191233)
  ·
    refine ⟨31947664061170689903143425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42596885414894253204191233 31947664061170689903143425)
    ·
      refine ⟨23960748045878017427357569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31947664061170689903143425 23960748045878017427357569)
      ·
        refine ⟨17970561034408513070518177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23960748045878017427357569 17970561034408513070518177)
        ·
          refine ⟨13477920775806384802888633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17970561034408513070518177 13477920775806384802888633)
          ·
            refine ⟨10108440581854788602166475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13477920775806384802888633 10108440581854788602166475)
            ·
              refine ⟨15162660872782182903249713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10108440581854788602166475 15162660872782182903249713)
              ·
                refine ⟨11371995654586637177437285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15162660872782182903249713 11371995654586637177437285)
                ·
                  refine ⟨2132249185234994470769491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11371995654586637177437285 2132249185234994470769491)
                  ·
                    refine ⟨3198373777852491706154237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2132249185234994470769491 3198373777852491706154237)
                    ·
                      refine ⟨1199390166694684389807839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3198373777852491706154237 1199390166694684389807839)
                      ·
                        rfl

theorem cell23_2335804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_2335804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335804 prefixEnd_2335804 := by exact prefixLift 2335804
  have htrace : WordTrace (prefixWord ++ tailWord_2335804) baseStart_2335804 baseEnd_2335804 := by
    simpa [prefixWord, tailWord_2335804, baseEnd_2335804] using wordTrace_append hprefix tailTrace_2335804
  have hstable : (prefixWord ++ tailWord_2335804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335804).length < 2 ^ (prefixWord ++ tailWord_2335804).sum := by decide
  have hdescent : baseEnd_2335804 < baseStart_2335804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335805 : List Nat := [1, 4, 1, 3, 1, 4, 1, 3, 1, 2, 2]
def baseStart_2335805 : Nat := 118140960795 + 2335805 * 2 ^ 59
def prefixEnd_2335805 : Nat := 4983230072969 + 3 ^ 40 * 2335805 * 2
def baseEnd_2335805 : Nat := 1199390680175338885895335

theorem tailTrace_2335805 : CollatzResearch.WordTrace tailWord_2335805 prefixEnd_2335805 1199390680175338885895335 := by
  unfold tailWord_2335805
  simp only [CollatzResearch.WordTrace]
  refine ⟨85193807302784883579168869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56795871535189922386112579 85193807302784883579168869)
  ·
    refine ⟨15973838869272165671094163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85193807302784883579168869 15973838869272165671094163)
    ·
      refine ⟨23960758303908248506641245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15973838869272165671094163 23960758303908248506641245)
      ·
        refine ⟨8985284363965593189990467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23960758303908248506641245 8985284363965593189990467)
        ·
          refine ⟨13477926545948389784985701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8985284363965593189990467 13477926545948389784985701)
          ·
            refine ⟨2527111227365323084684819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13477926545948389784985701 2527111227365323084684819)
            ·
              refine ⟨3790666841047984627027229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2527111227365323084684819 3790666841047984627027229)
              ·
                refine ⟨1421500065392994235135211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3790666841047984627027229 1421500065392994235135211)
                ·
                  refine ⟨2132250098089491352702817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421500065392994235135211 2132250098089491352702817)
                  ·
                    refine ⟨1599187573567118514527113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2132250098089491352702817 1599187573567118514527113)
                    ·
                      refine ⟨1199390680175338885895335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1599187573567118514527113 1199390680175338885895335)
                      ·
                        rfl

theorem cell23_2335805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_2335805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335805 prefixEnd_2335805 := by exact prefixLift 2335805
  have htrace : WordTrace (prefixWord ++ tailWord_2335805) baseStart_2335805 baseEnd_2335805 := by
    simpa [prefixWord, tailWord_2335805, baseEnd_2335805] using wordTrace_append hprefix tailTrace_2335805
  have hstable : (prefixWord ++ tailWord_2335805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335805).length < 2 ^ (prefixWord ++ tailWord_2335805).sum := by decide
  have hdescent : baseEnd_2335805 < baseStart_2335805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335821 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_2335821 : Nat := 118140960795 + 2335821 * 2 ^ 59
def prefixEnd_2335821 : Nat := 4983230072969 + 3 ^ 40 * 2335821 * 2
def baseEnd_2335821 : Nat := 1199398895865810823295261

theorem tailTrace_2335821 : CollatzResearch.WordTrace tailWord_2335821 prefixEnd_2335821 1199398895865810823295261 := by
  unfold tailWord_2335821
  simp only [CollatzResearch.WordTrace]
  refine ⟨85194390870726918311751317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56796260580484612207834211 85194390870726918311751317)
  ·
    refine ⟨3993487072065324295863343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85194390870726918311751317 3993487072065324295863343)
    ·
      refine ⟨5990230608097986443795015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3993487072065324295863343 5990230608097986443795015)
      ·
        refine ⟨8985345912146979665692523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5990230608097986443795015 8985345912146979665692523)
        ·
          refine ⟨13478018868220469498538785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8985345912146979665692523 13478018868220469498538785)
          ·
            refine ⟨10108514151165352123904089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13478018868220469498538785 10108514151165352123904089)
            ·
              refine ⟨7581385613374014092928067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10108514151165352123904089 7581385613374014092928067)
              ·
                refine ⟨11372078420061021139392101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7581385613374014092928067 11372078420061021139392101)
                ·
                  refine ⟨2132264703761441463636019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11372078420061021139392101 2132264703761441463636019)
                  ·
                    refine ⟨3198397055642162195454029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2132264703761441463636019 3198397055642162195454029)
                    ·
                      refine ⟨1199398895865810823295261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3198397055642162195454029 1199398895865810823295261)
                      ·
                        rfl

theorem cell23_2335821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_2335821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335821 prefixEnd_2335821 := by exact prefixLift 2335821
  have htrace : WordTrace (prefixWord ++ tailWord_2335821) baseStart_2335821 baseEnd_2335821 := by
    simpa [prefixWord, tailWord_2335821, baseEnd_2335821] using wordTrace_append hprefix tailTrace_2335821
  have hstable : (prefixWord ++ tailWord_2335821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335821).length < 2 ^ (prefixWord ++ tailWord_2335821).sum := by decide
  have hdescent : baseEnd_2335821 < baseStart_2335821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335844 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 1, 4, 2]
def baseStart_2335844 : Nat := 118140960795 + 2335844 * 2 ^ 59
def prefixEnd_2335844 : Nat := 4983230072969 + 3 ^ 40 * 2335844 * 2
def baseEnd_2335844 : Nat := 1199410705920864233307655

theorem tailTrace_2335844 : CollatzResearch.WordTrace tailWord_2335844 prefixEnd_2335844 1199410705920864233307655 := by
  unfold tailWord_2335844
  simp only [CollatzResearch.WordTrace]
  refine ⟨42597614874821796619919293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56796819833095728826559057 42597614874821796619919293)
  ·
    refine ⟨15974105578058173732469735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42597614874821796619919293 15974105578058173732469735)
    ·
      refine ⟨23961158367087260598704603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15974105578058173732469735 23961158367087260598704603)
      ·
        refine ⟨35941737550630890898056905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23961158367087260598704603 35941737550630890898056905)
        ·
          refine ⟨26956303162973168173542679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35941737550630890898056905 26956303162973168173542679)
          ·
            refine ⟨40434454744459752260314019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26956303162973168173542679 40434454744459752260314019)
            ·
              refine ⟨60651682116689628390471029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40434454744459752260314019 60651682116689628390471029)
              ·
                refine ⟨5686095198439652661606659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60651682116689628390471029 5686095198439652661606659)
                ·
                  refine ⟨8529142797659478992409989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5686095198439652661606659 8529142797659478992409989)
                  ·
                    refine ⟨1599214274561152311076873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8529142797659478992409989 1599214274561152311076873)
                    ·
                      refine ⟨1199410705920864233307655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1599214274561152311076873 1199410705920864233307655)
                      ·
                        rfl

theorem cell23_2335844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_2335844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335844 prefixEnd_2335844 := by exact prefixLift 2335844
  have htrace : WordTrace (prefixWord ++ tailWord_2335844) baseStart_2335844 baseEnd_2335844 := by
    simpa [prefixWord, tailWord_2335844, baseEnd_2335844] using wordTrace_append hprefix tailTrace_2335844
  have hstable : (prefixWord ++ tailWord_2335844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335844).length < 2 ^ (prefixWord ++ tailWord_2335844).sum := by decide
  have hdescent : baseEnd_2335844 < baseStart_2335844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335847 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_2335847 : Nat := 118140960795 + 2335847 * 2 ^ 59
def prefixEnd_2335847 : Nat := 4983230072969 + 3 ^ 40 * 2335847 * 2
def baseEnd_2335847 : Nat := 1199412246362827721570141

theorem tailTrace_2335847 : CollatzResearch.WordTrace tailWord_2335847 prefixEnd_2335847 1199412246362827721570141 := by
  unfold tailWord_2335847
  simp only [CollatzResearch.WordTrace]
  refine ⟨85195339168632724752197795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56796892779088483168131863 85195339168632724752197795)
  ·
    refine ⟨127793008752949087128296693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85195339168632724752197795 127793008752949087128296693)
    ·
      refine ⟨11980594570588976918277815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127793008752949087128296693 11980594570588976918277815)
      ·
        refine ⟨17970891855883465377416723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11980594570588976918277815 17970891855883465377416723)
        ·
          refine ⟨26956337783825198066125085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17970891855883465377416723 26956337783825198066125085)
          ·
            refine ⟨10108626668934449274796907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26956337783825198066125085 10108626668934449274796907)
            ·
              refine ⟨15162940003401673912195361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10108626668934449274796907 15162940003401673912195361)
              ·
                refine ⟨11372205002551255434146521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15162940003401673912195361 11372205002551255434146521)
                ·
                  refine ⟨8529153751913441575609891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11372205002551255434146521 8529153751913441575609891)
                  ·
                    refine ⟨12793730627870162363414837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8529153751913441575609891 12793730627870162363414837)
                    ·
                      refine ⟨1199412246362827721570141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12793730627870162363414837 1199412246362827721570141)
                      ·
                        rfl

theorem cell23_2335847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_2335847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335847 prefixEnd_2335847 := by exact prefixLift 2335847
  have htrace : WordTrace (prefixWord ++ tailWord_2335847) baseStart_2335847 baseEnd_2335847 := by
    simpa [prefixWord, tailWord_2335847, baseEnd_2335847] using wordTrace_append hprefix tailTrace_2335847
  have hstable : (prefixWord ++ tailWord_2335847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335847).length < 2 ^ (prefixWord ++ tailWord_2335847).sum := by decide
  have hdescent : baseEnd_2335847 < baseStart_2335847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335848 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 3, 3, 2]
def baseStart_2335848 : Nat := 118140960795 + 2335848 * 2 ^ 59
def prefixEnd_2335848 : Nat := 4983230072969 + 3 ^ 40 * 2335848 * 2
def baseEnd_2335848 : Nat := 1199412759843482217657637

theorem tailTrace_2335848 : CollatzResearch.WordTrace tailWord_2335848 prefixEnd_2335848 1199412759843482217657637 := by
  unfold tailWord_2335848
  simp only [CollatzResearch.WordTrace]
  refine ⟨42597687820814550961492099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56796917094419401281989465 42597687820814550961492099)
  ·
    refine ⟨63896531731221826442238149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42597687820814550961492099 63896531731221826442238149)
    ·
      refine ⟨11980599699604092457919653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63896531731221826442238149 11980599699604092457919653)
      ·
        refine ⟨2246362443675767335859935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11980599699604092457919653 2246362443675767335859935)
        ·
          refine ⟨3369543665513651003789903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2246362443675767335859935 3369543665513651003789903)
          ·
            refine ⟨5054315498270476505684855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3369543665513651003789903 5054315498270476505684855)
            ·
              refine ⟨7581473247405714758527283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5054315498270476505684855 7581473247405714758527283)
              ·
                refine ⟨11372209871108572137790925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7581473247405714758527283 11372209871108572137790925)
                ·
                  refine ⟨4264578701665714551671597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11372209871108572137790925 4264578701665714551671597)
                  ·
                    refine ⟨1599217013124642956876849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4264578701665714551671597 1599217013124642956876849)
                    ·
                      refine ⟨1199412759843482217657637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1599217013124642956876849 1199412759843482217657637)
                      ·
                        rfl

theorem cell23_2335848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_2335848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335848 prefixEnd_2335848 := by exact prefixLift 2335848
  have htrace : WordTrace (prefixWord ++ tailWord_2335848) baseStart_2335848 baseEnd_2335848 := by
    simpa [prefixWord, tailWord_2335848, baseEnd_2335848] using wordTrace_append hprefix tailTrace_2335848
  have hstable : (prefixWord ++ tailWord_2335848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335848).length < 2 ^ (prefixWord ++ tailWord_2335848).sum := by decide
  have hdescent : baseEnd_2335848 < baseStart_2335848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335904 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 2, 5, 2]
def baseStart_2335904 : Nat := 118140960795 + 2335904 * 2 ^ 59
def prefixEnd_2335904 : Nat := 4983230072969 + 3 ^ 40 * 2335904 * 2
def baseEnd_2335904 : Nat := 1199441514760133998557379

theorem tailTrace_2335904 : CollatzResearch.WordTrace tailWord_2335904 prefixEnd_2335904 1199441514760133998557379 := by
  unfold tailWord_2335904
  simp only [CollatzResearch.WordTrace]
  refine ⟨42598709064713111743511383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56798278752950815658015177 42598709064713111743511383)
  ·
    refine ⟨63898063597069667615267075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42598709064713111743511383 63898063597069667615267075)
    ·
      refine ⟨95847095395604501422900613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63898063597069667615267075 95847095395604501422900613)
      ·
        refine ⟨17971330386675844016793865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95847095395604501422900613 17971330386675844016793865)
        ·
          refine ⟨13478497790006883012595399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17971330386675844016793865 13478497790006883012595399)
          ·
            refine ⟨20217746685010324518893099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13478497790006883012595399 20217746685010324518893099)
            ·
              refine ⟨30326620027515486778339649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20217746685010324518893099 30326620027515486778339649)
              ·
                refine ⟨22744965020636615083754737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30326620027515486778339649 22744965020636615083754737)
                ·
                  refine ⟨17058723765477461312816053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22744965020636615083754737 17058723765477461312816053)
                  ·
                    refine ⟨1599255353013511998076505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17058723765477461312816053 1599255353013511998076505)
                    ·
                      refine ⟨1199441514760133998557379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1599255353013511998076505 1199441514760133998557379)
                      ·
                        rfl

theorem cell23_2335904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_2335904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335904 prefixEnd_2335904 := by exact prefixLift 2335904
  have htrace : WordTrace (prefixWord ++ tailWord_2335904) baseStart_2335904 baseEnd_2335904 := by
    simpa [prefixWord, tailWord_2335904, baseEnd_2335904] using wordTrace_append hprefix tailTrace_2335904
  have hstable : (prefixWord ++ tailWord_2335904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335904).length < 2 ^ (prefixWord ++ tailWord_2335904).sum := by decide
  have hdescent : baseEnd_2335904 < baseStart_2335904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335944 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 3, 4]
def baseStart_2335944 : Nat := 118140960795 + 2335944 * 2 ^ 59
def prefixEnd_2335944 : Nat := 4983230072969 + 3 ^ 40 * 2335944 * 2
def baseEnd_2335944 : Nat := 399820684662104614019065

theorem tailTrace_2335944 : CollatzResearch.WordTrace tailWord_2335944 prefixEnd_2335944 399820684662104614019065 := by
  unfold tailWord_2335944
  simp only [CollatzResearch.WordTrace]
  refine ⟨42599438524640655159239443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56799251366187540212319257 42599438524640655159239443)
  ·
    refine ⟨63899157786960982738859165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42599438524640655159239443 63899157786960982738859165)
    ·
      refine ⟨23962184170110368527072187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63899157786960982738859165 23962184170110368527072187)
      ·
        refine ⟨35943276255165552790608281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23962184170110368527072187 35943276255165552790608281)
        ·
          refine ⟨26957457191374164592956211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35943276255165552790608281 26957457191374164592956211)
          ·
            refine ⟨40436185787061246889434317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26957457191374164592956211 40436185787061246889434317)
            ·
              refine ⟨15163569670147967583537869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40436185787061246889434317 15163569670147967583537869)
              ·
                refine ⟨5686338626305487843826701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15163569670147967583537869 5686338626305487843826701)
                ·
                  refine ⟨2132376984864557941435013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5686338626305487843826701 2132376984864557941435013)
                  ·
                    refine ⟨399820684662104614019065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2132376984864557941435013 399820684662104614019065)
                    ·
                      rfl

theorem cell23_2335944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_2335944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335944 prefixEnd_2335944 := by exact prefixLift 2335944
  have htrace : WordTrace (prefixWord ++ tailWord_2335944) baseStart_2335944 baseEnd_2335944 := by
    simpa [prefixWord, tailWord_2335944, baseEnd_2335944] using wordTrace_append hprefix tailTrace_2335944
  have hstable : (prefixWord ++ tailWord_2335944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335944).length < 2 ^ (prefixWord ++ tailWord_2335944).sum := by decide
  have hdescent : baseEnd_2335944 < baseStart_2335944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335954 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_2335954 : Nat := 118140960795 + 2335954 * 2 ^ 59
def prefixEnd_2335954 : Nat := 4983230072969 + 3 ^ 40 * 2335954 * 2
def baseEnd_2335954 : Nat := 1199467188792858802932149

theorem tailTrace_2335954 : CollatzResearch.WordTrace tailWord_2335954 prefixEnd_2335954 1199467188792858802932149 := by
  unfold tailWord_2335954
  simp only [CollatzResearch.WordTrace]
  refine ⟨21299810444811270506585729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56799494519496721350895277 21299810444811270506585729)
  ·
    refine ⟨15974857833608452879939297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21299810444811270506585729 15974857833608452879939297)
    ·
      refine ⟨11981143375206339659954473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15974857833608452879939297 11981143375206339659954473)
      ·
        refine ⟨8985857531404754744965855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11981143375206339659954473 8985857531404754744965855)
        ·
          refine ⟨13478786297107132117448783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8985857531404754744965855 13478786297107132117448783)
          ·
            refine ⟨20218179445660698176173175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13478786297107132117448783 20218179445660698176173175)
            ·
              refine ⟨30327269168491047264259763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20218179445660698176173175 30327269168491047264259763)
              ·
                refine ⟨45490903752736570896389645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30327269168491047264259763 45490903752736570896389645)
                ·
                  refine ⟨17059088907276214086146117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45490903752736570896389645 17059088907276214086146117)
                  ·
                    refine ⟨3198579170114290141152397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17059088907276214086146117 3198579170114290141152397)
                    ·
                      refine ⟨1199467188792858802932149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3198579170114290141152397 1199467188792858802932149)
                      ·
                        rfl

theorem cell23_2335954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_2335954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335954 prefixEnd_2335954 := by exact prefixLift 2335954
  have htrace : WordTrace (prefixWord ++ tailWord_2335954) baseStart_2335954 baseEnd_2335954 := by
    simpa [prefixWord, tailWord_2335954, baseEnd_2335954] using wordTrace_append hprefix tailTrace_2335954
  have hstable : (prefixWord ++ tailWord_2335954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335954).length < 2 ^ (prefixWord ++ tailWord_2335954).sum := by decide
  have hdescent : baseEnd_2335954 < baseStart_2335954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335978 : List Nat := [3, 1, 3, 1, 1, 3, 3, 3, 1, 4]
def baseStart_2335978 : Nat := 118140960795 + 2335978 * 2 ^ 59
def prefixEnd_2335978 : Nat := 4983230072969 + 3 ^ 40 * 2335978 * 2
def baseEnd_2335978 : Nat := 399826504109522236344013

theorem tailTrace_2335978 : CollatzResearch.WordTrace tailWord_2335978 prefixEnd_2335978 399826504109522236344013 := by
  unfold tailWord_2335978
  simp only [CollatzResearch.WordTrace]
  refine ⟨21300029282789533531304147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56800078087438756083477725 21300029282789533531304147)
  ·
    refine ⟨31950043924184300296956221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21300029282789533531304147 31950043924184300296956221)
    ·
      refine ⟨11981266471569112611358583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31950043924184300296956221 11981266471569112611358583)
      ·
        refine ⟨17971899707353668917037875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11981266471569112611358583 17971899707353668917037875)
        ·
          refine ⟨26957849561030503375556813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17971899707353668917037875 26957849561030503375556813)
          ·
            refine ⟨10109193585386438765833805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26957849561030503375556813 10109193585386438765833805)
            ·
              refine ⟨3790947594519914537187677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10109193585386438765833805 3790947594519914537187677)
              ·
                refine ⟨1421605347944967951445379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3790947594519914537187677 1421605347944967951445379)
                ·
                  refine ⟨2132408021917451927168069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421605347944967951445379 2132408021917451927168069)
                  ·
                    refine ⟨399826504109522236344013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2132408021917451927168069 399826504109522236344013)
                    ·
                      rfl

theorem cell23_2335978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_2335978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335978 prefixEnd_2335978 := by exact prefixLift 2335978
  have htrace : WordTrace (prefixWord ++ tailWord_2335978) baseStart_2335978 baseEnd_2335978 := by
    simpa [prefixWord, tailWord_2335978, baseEnd_2335978] using wordTrace_append hprefix tailTrace_2335978
  have hstable : (prefixWord ++ tailWord_2335978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335978).length < 2 ^ (prefixWord ++ tailWord_2335978).sum := by decide
  have hdescent : baseEnd_2335978 < baseStart_2335978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335997 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_2335997 : Nat := 118140960795 + 2335997 * 2 ^ 59
def prefixEnd_2335997 : Nat := 4983230072969 + 3 ^ 40 * 2335997 * 2
def baseEnd_2335997 : Nat := 1199489268461002134694451

theorem tailTrace_2335997 : CollatzResearch.WordTrace tailWord_2335997 prefixEnd_2335997 1199489268461002134694451 := by
  unfold tailWord_2335997
  simp only [CollatzResearch.WordTrace]
  refine ⟨85200810118089300370158245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56800540078726200246772163 85200810118089300370158245)
  ·
    refine ⟨15975151897141743819404671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85200810118089300370158245 15975151897141743819404671)
    ·
      refine ⟨23962727845712615729107007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15975151897141743819404671 23962727845712615729107007)
      ·
        refine ⟨35944091768568923593660511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23962727845712615729107007 35944091768568923593660511)
        ·
          refine ⟨53916137652853385390490767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35944091768568923593660511 53916137652853385390490767)
          ·
            refine ⟨80874206479280078085736151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53916137652853385390490767 80874206479280078085736151)
            ·
              refine ⟨121311309718920117128604227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80874206479280078085736151 121311309718920117128604227)
              ·
                refine ⟨181966964578380175692906341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121311309718920117128604227 181966964578380175692906341)
                ·
                  refine ⟨34118805858446282942419939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181966964578380175692906341 34118805858446282942419939)
                  ·
                    refine ⟨51178208787669424413629909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34118805858446282942419939 51178208787669424413629909)
                    ·
                      refine ⟨1199489268461002134694451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51178208787669424413629909 1199489268461002134694451)
                      ·
                        rfl

theorem cell23_2335997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_2335997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335997 prefixEnd_2335997 := by exact prefixLift 2335997
  have htrace : WordTrace (prefixWord ++ tailWord_2335997) baseStart_2335997 baseEnd_2335997 := by
    simpa [prefixWord, tailWord_2335997, baseEnd_2335997] using wordTrace_append hprefix tailTrace_2335997
  have hstable : (prefixWord ++ tailWord_2335997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335997).length < 2 ^ (prefixWord ++ tailWord_2335997).sum := by decide
  have hdescent : baseEnd_2335997 < baseStart_2335997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336008 : List Nat := [2, 1, 3, 2, 4, 2, 2, 1, 6]
def baseStart_2336008 : Nat := 118140960795 + 2336008 * 2 ^ 59
def prefixEnd_2336008 : Nat := 4983230072969 + 3 ^ 40 * 2336008 * 2
def baseEnd_2336008 : Nat := 133277212972022399072989

theorem tailTrace_2336008 : CollatzResearch.WordTrace tailWord_2336008 prefixEnd_2336008 133277212972022399072989 := by
  unfold tailWord_2336008
  simp only [CollatzResearch.WordTrace]
  refine ⟨42600605660524724624404339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56800807547366299499205785 42600605660524724624404339)
  ·
    refine ⟨63900908490787086936606509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42600605660524724624404339 63900908490787086936606509)
    ·
      refine ⟨23962840684045157601227441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63900908490787086936606509 23962840684045157601227441)
      ·
        refine ⟨17972130513033868200920581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23962840684045157601227441 17972130513033868200920581)
        ·
          refine ⟨3369774471193850287672609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17972130513033868200920581 3369774471193850287672609)
          ·
            refine ⟨2527330853395387715754457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3369774471193850287672609 2527330853395387715754457)
            ·
              refine ⟨1895498140046540786815843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2527330853395387715754457 1895498140046540786815843)
              ·
                refine ⟨2843247210069811180223765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1895498140046540786815843 2843247210069811180223765)
                ·
                  refine ⟨133277212972022399072989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2843247210069811180223765 133277212972022399072989)
                  ·
                    rfl

theorem cell23_2336008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 6].length) (baseStart_2336008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336008 prefixEnd_2336008 := by exact prefixLift 2336008
  have htrace : WordTrace (prefixWord ++ tailWord_2336008) baseStart_2336008 baseEnd_2336008 := by
    simpa [prefixWord, tailWord_2336008, baseEnd_2336008] using wordTrace_append hprefix tailTrace_2336008
  have hstable : (prefixWord ++ tailWord_2336008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336008).length < 2 ^ (prefixWord ++ tailWord_2336008).sum := by decide
  have hdescent : baseEnd_2336008 < baseStart_2336008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336045 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_2336045 : Nat := 118140960795 + 2336045 * 2 ^ 59
def prefixEnd_2336045 : Nat := 4983230072969 + 3 ^ 40 * 2336045 * 2
def baseEnd_2336045 : Nat := 1199513915532417946894231

theorem tailTrace_2336045 : CollatzResearch.WordTrace tailWord_2336045 prefixEnd_2336045 1199513915532417946894231 := by
  unfold tailWord_2336045
  simp only [CollatzResearch.WordTrace]
  refine ⟨85202560821915404567905589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56801707214610269711937059 85202560821915404567905589)
  ·
    refine ⟨7987740077054569178241149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85202560821915404567905589 7987740077054569178241149)
    ·
      refine ⟨2995402528895463441840431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7987740077054569178241149 2995402528895463441840431)
      ·
        refine ⟨4493103793343195162760647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2995402528895463441840431 4493103793343195162760647)
        ·
          refine ⟨6739655690014792744140971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4493103793343195162760647 6739655690014792744140971)
          ·
            refine ⟨10109483535022189116211457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6739655690014792744140971 10109483535022189116211457)
            ·
              refine ⟨7582112651266641837158593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10109483535022189116211457 7582112651266641837158593)
              ·
                refine ⟨5686584488449981377868945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7582112651266641837158593 5686584488449981377868945)
                ·
                  refine ⟨4264938366337486033401709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5686584488449981377868945 4264938366337486033401709)
                  ·
                    refine ⟨1599351887376557262525641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4264938366337486033401709 1599351887376557262525641)
                    ·
                      refine ⟨1199513915532417946894231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1599351887376557262525641 1199513915532417946894231)
                      ·
                        rfl

theorem cell23_2336045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_2336045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336045 prefixEnd_2336045 := by exact prefixLift 2336045
  have htrace : WordTrace (prefixWord ++ tailWord_2336045) baseStart_2336045 baseEnd_2336045 := by
    simpa [prefixWord, tailWord_2336045, baseEnd_2336045] using wordTrace_append hprefix tailTrace_2336045
  have hstable : (prefixWord ++ tailWord_2336045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336045).length < 2 ^ (prefixWord ++ tailWord_2336045).sum := by decide
  have hdescent : baseEnd_2336045 < baseStart_2336045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336051 : List Nat := [1, 1, 1, 2, 5, 2, 1, 4, 2, 4]
def baseStart_2336051 : Nat := 118140960795 + 2336051 * 2 ^ 59
def prefixEnd_2336051 : Nat := 4983230072969 + 3 ^ 40 * 2336051 * 2
def baseEnd_2336051 : Nat := 399838998805448307806401

theorem tailTrace_2336051 : CollatzResearch.WordTrace tailWord_2336051 prefixEnd_2336051 399838998805448307806401 := by
  unfold tailWord_2336051
  simp only [CollatzResearch.WordTrace]
  refine ⟨85202779659893667592624007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56801853106595778395082671 85202779659893667592624007)
  ·
    refine ⟨127804169489840501388936011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85202779659893667592624007 127804169489840501388936011)
    ·
      refine ⟨191706254234760752083404017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127804169489840501388936011 191706254234760752083404017)
      ·
        refine ⟨143779690676070564062553013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191706254234760752083404017 143779690676070564062553013)
        ·
          refine ⟨13479346000881615380864345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 143779690676070564062553013 13479346000881615380864345)
          ·
            refine ⟨10109509500661211535648259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13479346000881615380864345 10109509500661211535648259)
            ·
              refine ⟨15164264250991817303472389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10109509500661211535648259 15164264250991817303472389)
              ·
                refine ⟨2843299547060965744401073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15164264250991817303472389 2843299547060965744401073)
                ·
                  refine ⟨2132474660295724308300805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2843299547060965744401073 2132474660295724308300805)
                  ·
                    refine ⟨399838998805448307806401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2132474660295724308300805 399838998805448307806401)
                    ·
                      rfl

theorem cell23_2336051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 4].length) (baseStart_2336051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336051 prefixEnd_2336051 := by exact prefixLift 2336051
  have htrace : WordTrace (prefixWord ++ tailWord_2336051) baseStart_2336051 baseEnd_2336051 := by
    simpa [prefixWord, tailWord_2336051, baseEnd_2336051] using wordTrace_append hprefix tailTrace_2336051
  have hstable : (prefixWord ++ tailWord_2336051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336051).length < 2 ^ (prefixWord ++ tailWord_2336051).sum := by decide
  have hdescent : baseEnd_2336051 < baseStart_2336051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336058 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2]
def baseStart_2336058 : Nat := 118140960795 + 2336058 * 2 ^ 59
def prefixEnd_2336058 : Nat := 4983230072969 + 3 ^ 40 * 2336058 * 2
def baseEnd_2336058 : Nat := 1199520590780926396031671

theorem tailTrace_2336058 : CollatzResearch.WordTrace tailWord_2336058 prefixEnd_2336058 1199520590780926396031671 := by
  unfold tailWord_2336058
  simp only [CollatzResearch.WordTrace]
  refine ⟨21300758742717076947032207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56802023313912205192085885 21300758742717076947032207)
  ·
    refine ⟨31951138114075615420548311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21300758742717076947032207 31951138114075615420548311)
    ·
      refine ⟨47926707171113423130822467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31951138114075615420548311 47926707171113423130822467)
      ·
        refine ⟨71890060756670134696233701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47926707171113423130822467 71890060756670134696233701)
        ·
          refine ⟨13479386391875650255543819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71890060756670134696233701 13479386391875650255543819)
          ·
            refine ⟨20219079587813475383315729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13479386391875650255543819 20219079587813475383315729)
            ·
              refine ⟨15164309690860106537486797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20219079587813475383315729 15164309690860106537486797)
              ·
                refine ⟨5686616134072539951557549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15164309690860106537486797 5686616134072539951557549)
                ·
                  refine ⟨2132481050277202481834081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5686616134072539951557549 2132481050277202481834081)
                  ·
                    refine ⟨1599360787707901861375561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2132481050277202481834081 1599360787707901861375561)
                    ·
                      refine ⟨1199520590780926396031671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1599360787707901861375561 1199520590780926396031671)
                      ·
                        rfl

theorem cell23_2336058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2].length) (baseStart_2336058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336058 prefixEnd_2336058 := by exact prefixLift 2336058
  have htrace : WordTrace (prefixWord ++ tailWord_2336058) baseStart_2336058 baseEnd_2336058 := by
    simpa [prefixWord, tailWord_2336058, baseEnd_2336058] using wordTrace_append hprefix tailTrace_2336058
  have hstable : (prefixWord ++ tailWord_2336058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336058).length < 2 ^ (prefixWord ++ tailWord_2336058).sum := by decide
  have hdescent : baseEnd_2336058 < baseStart_2336058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336068 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 1, 6]
def baseStart_2336068 : Nat := 118140960795 + 2336068 * 2 ^ 59
def prefixEnd_2336068 : Nat := 4983230072969 + 3 ^ 40 * 2336068 * 2
def baseEnd_2336068 : Nat := 399841908529157118968875

theorem tailTrace_2336068 : CollatzResearch.WordTrace tailWord_2336068 prefixEnd_2336068 399841908529157118968875 := by
  unfold tailWord_2336068
  simp only [CollatzResearch.WordTrace]
  refine ⟨42601699850416039747996429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56802266467221386330661905 42601699850416039747996429)
  ·
    refine ⟨15975637443906014905498661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42601699850416039747996429 15975637443906014905498661)
    ·
      refine ⟨2995432020732377794780999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15975637443906014905498661 2995432020732377794780999)
      ·
        refine ⟨4493148031098566692171499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2995432020732377794780999 4493148031098566692171499)
        ·
          refine ⟨6739722046647850038257249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4493148031098566692171499 6739722046647850038257249)
          ·
            refine ⟨5054791534985887528692937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6739722046647850038257249 5054791534985887528692937)
            ·
              refine ⟨3791093651239415646519703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5054791534985887528692937 3791093651239415646519703)
              ·
                refine ⟨5686640476859123469779555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3791093651239415646519703 5686640476859123469779555)
                ·
                  refine ⟨8529960715288685204669333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5686640476859123469779555 8529960715288685204669333)
                  ·
                    refine ⟨399841908529157118968875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8529960715288685204669333 399841908529157118968875)
                    ·
                      rfl

theorem cell23_2336068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_2336068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336068 prefixEnd_2336068 := by exact prefixLift 2336068
  have htrace : WordTrace (prefixWord ++ tailWord_2336068) baseStart_2336068 baseEnd_2336068 := by
    simpa [prefixWord, tailWord_2336068, baseEnd_2336068] using wordTrace_append hprefix tailTrace_2336068
  have hstable : (prefixWord ++ tailWord_2336068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336068).length < 2 ^ (prefixWord ++ tailWord_2336068).sum := by decide
  have hdescent : baseEnd_2336068 < baseStart_2336068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336071 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 4]
def baseStart_2336071 : Nat := 118140960795 + 2336071 * 2 ^ 59
def prefixEnd_2336071 : Nat := 4983230072969 + 3 ^ 40 * 2336071 * 2
def baseEnd_2336071 : Nat := 1199527266029434845169111

theorem tailTrace_2336071 : CollatzResearch.WordTrace tailWord_2336071 prefixEnd_2336071 1199527266029434845169111 := by
  unfold tailWord_2336071
  simp only [CollatzResearch.WordTrace]
  refine ⟨85203509119821211008352067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56802339413214140672234711 85203509119821211008352067)
  ·
    refine ⟨127805263679731816512528101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85203509119821211008352067 127805263679731816512528101)
    ·
      refine ⟨23963486939949715596099019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127805263679731816512528101 23963486939949715596099019)
      ·
        refine ⟨35945230409924573394148529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23963486939949715596099019 35945230409924573394148529)
        ·
          refine ⟨26958922807443430045611397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35945230409924573394148529 26958922807443430045611397)
          ·
            refine ⟨5054798026395643133552137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26958922807443430045611397 5054798026395643133552137)
            ·
              refine ⟨3791098519796732350164103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5054798026395643133552137 3791098519796732350164103)
              ·
                refine ⟨5686647779695098525246155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3791098519796732350164103 5686647779695098525246155)
                ·
                  refine ⟨8529971669542647787869233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5686647779695098525246155 8529971669542647787869233)
                  ·
                    refine ⟨6397478752156985840901925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8529971669542647787869233 6397478752156985840901925)
                    ·
                      refine ⟨1199527266029434845169111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6397478752156985840901925 1199527266029434845169111)
                      ·
                        rfl

theorem cell23_2336071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_2336071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336071 prefixEnd_2336071 := by exact prefixLift 2336071
  have htrace : WordTrace (prefixWord ++ tailWord_2336071) baseStart_2336071 baseEnd_2336071 := by
    simpa [prefixWord, tailWord_2336071, baseEnd_2336071] using wordTrace_append hprefix tailTrace_2336071
  have hstable : (prefixWord ++ tailWord_2336071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336071).length < 2 ^ (prefixWord ++ tailWord_2336071).sum := by decide
  have hdescent : baseEnd_2336071 < baseStart_2336071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336108 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 3]
def baseStart_2336108 : Nat := 118140960795 + 2336108 * 2 ^ 59
def prefixEnd_2336108 : Nat := 4983230072969 + 3 ^ 40 * 2336108 * 2
def baseEnd_2336108 : Nat := 1199546264813651200406441

theorem tailTrace_2336108 : CollatzResearch.WordTrace tailWord_2336108 prefixEnd_2336108 1199546264813651200406441 := by
  unfold tailWord_2336108
  simp only [CollatzResearch.WordTrace]
  refine ⟨42602429310343583163724489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56803239080458110884965985 42602429310343583163724489)
  ·
    refine ⟨31951821982757687372793367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42602429310343583163724489 31951821982757687372793367)
    ·
      refine ⟨47927732974136531059190051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31951821982757687372793367 47927732974136531059190051)
      ·
        refine ⟨71891599461204796588785077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47927732974136531059190051 71891599461204796588785077)
        ·
          refine ⟨6739837449487949680198601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71891599461204796588785077 6739837449487949680198601)
          ·
            refine ⟨5054878087115962260148951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6739837449487949680198601 5054878087115962260148951)
            ·
              refine ⟨7582317130673943390223427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5054878087115962260148951 7582317130673943390223427)
              ·
                refine ⟨11373475696010915085335141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7582317130673943390223427 11373475696010915085335141)
                ·
                  refine ⟨2132526693002046578500339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11373475696010915085335141 2132526693002046578500339)
                  ·
                    refine ⟨3198790039503069867750509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2132526693002046578500339 3198790039503069867750509)
                    ·
                      refine ⟨1199546264813651200406441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3198790039503069867750509 1199546264813651200406441)
                      ·
                        rfl

theorem cell23_2336108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 3].length) (baseStart_2336108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336108 prefixEnd_2336108 := by exact prefixLift 2336108
  have htrace : WordTrace (prefixWord ++ tailWord_2336108) baseStart_2336108 baseEnd_2336108 := by
    simpa [prefixWord, tailWord_2336108, baseEnd_2336108] using wordTrace_append hprefix tailTrace_2336108
  have hstable : (prefixWord ++ tailWord_2336108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336108).length < 2 ^ (prefixWord ++ tailWord_2336108).sum := by decide
  have hdescent : baseEnd_2336108 < baseStart_2336108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336124 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 2, 6]
def baseStart_2336124 : Nat := 118140960795 + 2336124 * 2 ^ 59
def prefixEnd_2336124 : Nat := 4983230072969 + 3 ^ 40 * 2336124 * 2
def baseEnd_2336124 : Nat := 399851493501374379268789

theorem tailTrace_2336124 : CollatzResearch.WordTrace tailWord_2336124 prefixEnd_2336124 399851493501374379268789 := by
  unfold tailWord_2336124
  simp only [CollatzResearch.WordTrace]
  refine ⟨42602721094314600530015713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56803628125752800706687617 42602721094314600530015713)
  ·
    refine ⟨31952040820735950397511785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42602721094314600530015713 31952040820735950397511785)
    ·
      refine ⟨23964030615551962798133839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31952040820735950397511785 23964030615551962798133839)
      ·
        refine ⟨35946045923327944197200759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23964030615551962798133839 35946045923327944197200759)
        ·
          refine ⟨53919068884991916295801139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35946045923327944197200759 53919068884991916295801139)
          ·
            refine ⟨80878603327487874443701709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53919068884991916295801139 80878603327487874443701709)
            ·
              refine ⟨30329476247807952916388141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80878603327487874443701709 30329476247807952916388141)
              ·
                refine ⟨11373553592927982343645553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30329476247807952916388141 11373553592927982343645553)
                ·
                  refine ⟨8530165194695986757734165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11373553592927982343645553 8530165194695986757734165)
                  ·
                    refine ⟨399851493501374379268789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8530165194695986757734165 399851493501374379268789)
                    ·
                      rfl

theorem cell23_2336124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_2336124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336124 prefixEnd_2336124 := by exact prefixLift 2336124
  have htrace : WordTrace (prefixWord ++ tailWord_2336124) baseStart_2336124 baseEnd_2336124 := by
    simpa [prefixWord, tailWord_2336124, baseEnd_2336124] using wordTrace_append hprefix tailTrace_2336124
  have hstable : (prefixWord ++ tailWord_2336124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336124).length < 2 ^ (prefixWord ++ tailWord_2336124).sum := by decide
  have hdescent : baseEnd_2336124 < baseStart_2336124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336125 : List Nat := [1, 4, 1, 1, 2, 2, 5, 1, 2, 1, 3]
def baseStart_2336125 : Nat := 118140960795 + 2336125 * 2 ^ 59
def prefixEnd_2336125 : Nat := 4983230072969 + 3 ^ 40 * 2336125 * 2
def baseEnd_2336125 : Nat := 1199554993984777633893863

theorem tailTrace_2336125 : CollatzResearch.WordTrace tailWord_2336125 prefixEnd_2336125 1199554993984777633893863 := by
  unfold tailWord_2336125
  simp only [CollatzResearch.WordTrace]
  refine ⟨85205478661625578230817829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56803652441083718820545219 85205478661625578230817829)
  ·
    refine ⟨15976027249054795918278343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85205478661625578230817829 15976027249054795918278343)
    ·
      refine ⟨23964040873582193877417515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15976027249054795918278343 23964040873582193877417515)
      ·
        refine ⟨35946061310373290816126273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23964040873582193877417515 35946061310373290816126273)
        ·
          refine ⟨26959545982779968112094705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35946061310373290816126273 26959545982779968112094705)
          ·
            refine ⟨20219659487084976084071029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26959545982779968112094705 20219659487084976084071029)
            ·
              refine ⟨1895593076914216507881659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20219659487084976084071029 1895593076914216507881659)
              ·
                refine ⟨2843389615371324761822489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1895593076914216507881659 2843389615371324761822489)
                ·
                  refine ⟨2132542211528493571366867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2843389615371324761822489 2132542211528493571366867)
                  ·
                    refine ⟨3198813317292740357050301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2132542211528493571366867 3198813317292740357050301)
                    ·
                      refine ⟨1199554993984777633893863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3198813317292740357050301 1199554993984777633893863)
                      ·
                        rfl

theorem cell23_2336125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_2336125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336125 prefixEnd_2336125 := by exact prefixLift 2336125
  have htrace : WordTrace (prefixWord ++ tailWord_2336125) baseStart_2336125 baseEnd_2336125 := by
    simpa [prefixWord, tailWord_2336125, baseEnd_2336125] using wordTrace_append hprefix tailTrace_2336125
  have hstable : (prefixWord ++ tailWord_2336125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336125).length < 2 ^ (prefixWord ++ tailWord_2336125).sum := by decide
  have hdescent : baseEnd_2336125 < baseStart_2336125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336135 : List Nat := [1, 1, 4, 2, 2, 3, 2, 2, 1, 3, 2]
def baseStart_2336135 : Nat := 118140960795 + 2336135 * 2 ^ 59
def prefixEnd_2336135 : Nat := 4983230072969 + 3 ^ 40 * 2336135 * 2
def baseEnd_2336135 : Nat := 1199560128791322594768817

theorem tailTrace_2336135 : CollatzResearch.WordTrace tailWord_2336135 prefixEnd_2336135 1199560128791322594768817 := by
  unfold tailWord_2336135
  simp only [CollatzResearch.WordTrace]
  refine ⟨85205843391589349938681859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56803895594392899959121239 85205843391589349938681859)
  ·
    refine ⟨127808765087384024908022789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85205843391589349938681859 127808765087384024908022789)
    ·
      refine ⟨23964143453884504670254273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127808765087384024908022789 23964143453884504670254273)
      ·
        refine ⟨17973107590413378502690705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23964143453884504670254273 17973107590413378502690705)
        ·
          refine ⟨13479830692810033877018029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17973107590413378502690705 13479830692810033877018029)
          ·
            refine ⟨5054936509803762703881761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13479830692810033877018029 5054936509803762703881761)
            ·
              refine ⟨3791202382352822027911321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5054936509803762703881761 3791202382352822027911321)
              ·
                refine ⟨2843401786764616520933491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3791202382352822027911321 2843401786764616520933491)
                ·
                  refine ⟨4265102680146924781400237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2843401786764616520933491 4265102680146924781400237)
                  ·
                    refine ⟨1599413505055096793025089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4265102680146924781400237 1599413505055096793025089)
                    ·
                      refine ⟨1199560128791322594768817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1599413505055096793025089 1199560128791322594768817)
                      ·
                        rfl

theorem cell23_2336135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_2336135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336135 prefixEnd_2336135 := by exact prefixLift 2336135
  have htrace : WordTrace (prefixWord ++ tailWord_2336135) baseStart_2336135 baseEnd_2336135 := by
    simpa [prefixWord, tailWord_2336135, baseEnd_2336135] using wordTrace_append hprefix tailTrace_2336135
  have hstable : (prefixWord ++ tailWord_2336135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336135).length < 2 ^ (prefixWord ++ tailWord_2336135).sum := by decide
  have hdescent : baseEnd_2336135 < baseStart_2336135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336164 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_2336164 : Nat := 118140960795 + 2336164 * 2 ^ 59
def prefixEnd_2336164 : Nat := 4983230072969 + 3 ^ 40 * 2336164 * 2
def baseEnd_2336164 : Nat := 1199575019730302981306183

theorem tailTrace_2336164 : CollatzResearch.WordTrace tailWord_2336164 prefixEnd_2336164 1199575019730302981306183 := by
  unfold tailWord_2336164
  simp only [CollatzResearch.WordTrace]
  refine ⟨42603450554242143945743773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56804600738989525260991697 42603450554242143945743773)
  ·
    refine ⟨15976293957840803979653915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42603450554242143945743773 15976293957840803979653915)
    ·
      refine ⟨23964440936761205969480873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15976293957840803979653915 23964440936761205969480873)
      ·
        refine ⟨17973330702570904477110655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23964440936761205969480873 17973330702570904477110655)
        ·
          refine ⟨26959996053856356715665983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17973330702570904477110655 26959996053856356715665983)
          ·
            refine ⟨40439994080784535073498975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26959996053856356715665983 40439994080784535073498975)
            ·
              refine ⟨60659991121176802610248463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40439994080784535073498975 60659991121176802610248463)
              ·
                refine ⟨90989986681765203915372695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60659991121176802610248463 90989986681765203915372695)
                ·
                  refine ⟨136484980022647805873059043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90989986681765203915372695 136484980022647805873059043)
                  ·
                    refine ⟨204727470033971708809588565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 136484980022647805873059043 204727470033971708809588565)
                    ·
                      refine ⟨1199575019730302981306183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 204727470033971708809588565 1199575019730302981306183)
                      ·
                        rfl

theorem cell23_2336164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_2336164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336164 prefixEnd_2336164 := by exact prefixLift 2336164
  have htrace : WordTrace (prefixWord ++ tailWord_2336164) baseStart_2336164 baseEnd_2336164 := by
    simpa [prefixWord, tailWord_2336164, baseEnd_2336164] using wordTrace_append hprefix tailTrace_2336164
  have hstable : (prefixWord ++ tailWord_2336164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336164).length < 2 ^ (prefixWord ++ tailWord_2336164).sum := by decide
  have hdescent : baseEnd_2336164 < baseStart_2336164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336184 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 3, 7]
def baseStart_2336184 : Nat := 118140960795 + 2336184 * 2 ^ 59
def prefixEnd_2336184 : Nat := 4983230072969 + 3 ^ 40 * 2336184 * 2
def baseEnd_2336184 : Nat := 399861763114464301018697

theorem tailTrace_2336184 : CollatzResearch.WordTrace tailWord_2336184 prefixEnd_2336184 399861763114464301018697 := by
  unfold tailWord_2336184
  simp only [CollatzResearch.WordTrace]
  refine ⟨42603815284205915653607803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56805087045607887538143737 42603815284205915653607803)
  ·
    refine ⟨63905722926308873480411705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42603815284205915653607803 63905722926308873480411705)
    ·
      refine ⟨47929292194731655110308779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63905722926308873480411705 47929292194731655110308779)
      ·
        refine ⟨71893938292097482665463169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47929292194731655110308779 71893938292097482665463169)
        ·
          refine ⟨53920453719073111999097377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71893938292097482665463169 53920453719073111999097377)
          ·
            refine ⟨40440340289304833999323033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53920453719073111999097377 40440340289304833999323033)
            ·
              refine ⟨30330255216978625499492275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40440340289304833999323033 30330255216978625499492275)
              ·
                refine ⟨45495382825467938249238413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30330255216978625499492275 45495382825467938249238413)
                ·
                  refine ⟨17060768559550476843464405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45495382825467938249238413 17060768559550476843464405)
                  ·
                    refine ⟨399861763114464301018697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17060768559550476843464405 399861763114464301018697)
                    ·
                      rfl

theorem cell23_2336184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_2336184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336184 prefixEnd_2336184 := by exact prefixLift 2336184
  have htrace : WordTrace (prefixWord ++ tailWord_2336184) baseStart_2336184 baseEnd_2336184 := by
    simpa [prefixWord, tailWord_2336184, baseEnd_2336184] using wordTrace_append hprefix tailTrace_2336184
  have hstable : (prefixWord ++ tailWord_2336184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336184).length < 2 ^ (prefixWord ++ tailWord_2336184).sum := by decide
  have hdescent : baseEnd_2336184 < baseStart_2336184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336248 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 3, 4]
def baseStart_2336248 : Nat := 118140960795 + 2336248 * 2 ^ 59
def prefixEnd_2336248 : Nat := 4983230072969 + 3 ^ 40 * 2336248 * 2
def baseEnd_2336248 : Nat := 399872717368426884218599

theorem tailTrace_2336248 : CollatzResearch.WordTrace tailWord_2336248 prefixEnd_2336248 399872717368426884218599 := by
  unfold tailWord_2336248
  simp only [CollatzResearch.WordTrace]
  refine ⟨42604982420089985118772699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56806643226786646825030265 42604982420089985118772699)
  ·
    refine ⟨63907473630134977678159049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42604982420089985118772699 63907473630134977678159049)
    ·
      refine ⟨47930605222601233258619287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63907473630134977678159049 47930605222601233258619287)
      ·
        refine ⟨71895907833901849887928931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47930605222601233258619287 71895907833901849887928931)
        ·
          refine ⟨107843861750852774831893397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71895907833901849887928931 107843861750852774831893397)
          ·
            refine ⟨5055181019571223820245003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107843861750852774831893397 5055181019571223820245003)
            ·
              refine ⟨7582771529356835730367505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5055181019571223820245003 7582771529356835730367505)
              ·
                refine ⟨5687078647017626797775629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7582771529356835730367505 5687078647017626797775629)
                ·
                  refine ⟨2132654492631610049165861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5687078647017626797775629 2132654492631610049165861)
                  ·
                    refine ⟨399872717368426884218599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2132654492631610049165861 399872717368426884218599)
                    ·
                      rfl

theorem cell23_2336248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_2336248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336248 prefixEnd_2336248 := by exact prefixLift 2336248
  have htrace : WordTrace (prefixWord ++ tailWord_2336248) baseStart_2336248 baseEnd_2336248 := by
    simpa [prefixWord, tailWord_2336248, baseEnd_2336248] using wordTrace_append hprefix tailTrace_2336248
  have hstable : (prefixWord ++ tailWord_2336248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336248).length < 2 ^ (prefixWord ++ tailWord_2336248).sum := by decide
  have hdescent : baseEnd_2336248 < baseStart_2336248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336265 : List Nat := [1, 2, 1, 1, 3, 1, 6, 3, 1, 4]
def baseStart_2336265 : Nat := 118140960795 + 2336265 * 2 ^ 59
def prefixEnd_2336265 : Nat := 4983230072969 + 3 ^ 40 * 2336265 * 2
def baseEnd_2336265 : Nat := 399875627092135695381073

theorem tailTrace_2336265 : CollatzResearch.WordTrace tailWord_2336265 prefixEnd_2336265 399875627092135695381073 := by
  unfold tailWord_2336265
  simp only [CollatzResearch.WordTrace]
  refine ⟨85210584881118382140914249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56807056587412254760609499 85210584881118382140914249)
  ·
    refine ⟨63907938660838786605685687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85210584881118382140914249 63907938660838786605685687)
    ·
      refine ⟨95861907991258179908528531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63907938660838786605685687 95861907991258179908528531)
      ·
        refine ⟨143792861986887269862792797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95861907991258179908528531 143792861986887269862792797)
        ·
          refine ⟨53922323245082726198547299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143792861986887269862792797 53922323245082726198547299)
          ·
            refine ⟨80883484867624089297820949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53922323245082726198547299 80883484867624089297820949)
            ·
              refine ⟨3791413353169879185835357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80883484867624089297820949 3791413353169879185835357)
              ·
                refine ⟨1421780007438704694688259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3791413353169879185835357 1421780007438704694688259)
                ·
                  refine ⟨2132670011158057042032389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421780007438704694688259 2132670011158057042032389)
                  ·
                    refine ⟨399875627092135695381073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2132670011158057042032389 399875627092135695381073)
                    ·
                      rfl

theorem cell23_2336265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 1, 4].length) (baseStart_2336265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336265 prefixEnd_2336265 := by exact prefixLift 2336265
  have htrace : WordTrace (prefixWord ++ tailWord_2336265) baseStart_2336265 baseEnd_2336265 := by
    simpa [prefixWord, tailWord_2336265, baseEnd_2336265] using wordTrace_append hprefix tailTrace_2336265
  have hstable : (prefixWord ++ tailWord_2336265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336265).length < 2 ^ (prefixWord ++ tailWord_2336265).sum := by decide
  have hdescent : baseEnd_2336265 < baseStart_2336265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336355 : List Nat := [1, 1, 1, 5, 1, 4, 1, 3, 2, 4]
def baseStart_2336355 : Nat := 118140960795 + 2336355 * 2 ^ 59
def prefixEnd_2336355 : Nat := 4983230072969 + 3 ^ 40 * 2336355 * 2
def baseEnd_2336355 : Nat := 399891031511770578005935

theorem tailTrace_2336355 : CollatzResearch.WordTrace tailWord_2336355 prefixEnd_2336355 399891031511770578005935 := by
  unfold tailWord_2336355
  simp only [CollatzResearch.WordTrace]
  refine ⟨85213867450792327511690519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56809244967194885007793679 85213867450792327511690519)
  ·
    refine ⟨127820801176188491267535779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85213867450792327511690519 127820801176188491267535779)
    ·
      refine ⟨191731201764282736901303669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127820801176188491267535779 191731201764282736901303669)
      ·
        refine ⟨17974800165401506584497219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 191731201764282736901303669 17974800165401506584497219)
        ·
          refine ⟨26962200248102259876745829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17974800165401506584497219 26962200248102259876745829)
          ·
            refine ⟨5055412546519173726889843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26962200248102259876745829 5055412546519173726889843)
            ·
              refine ⟨7583118819778760590334765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5055412546519173726889843 7583118819778760590334765)
              ·
                refine ⟨2843669557417035221375537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7583118819778760590334765 2843669557417035221375537)
                ·
                  refine ⟨2132752168062776416031653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2843669557417035221375537 2132752168062776416031653)
                  ·
                    refine ⟨399891031511770578005935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2132752168062776416031653 399891031511770578005935)
                    ·
                      rfl

theorem cell23_2336355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 4].length) (baseStart_2336355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336355 prefixEnd_2336355 := by exact prefixLift 2336355
  have htrace : WordTrace (prefixWord ++ tailWord_2336355) baseStart_2336355 baseEnd_2336355 := by
    simpa [prefixWord, tailWord_2336355, baseEnd_2336355] using wordTrace_append hprefix tailTrace_2336355
  have hstable : (prefixWord ++ tailWord_2336355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336355).length < 2 ^ (prefixWord ++ tailWord_2336355).sum := by decide
  have hdescent : baseEnd_2336355 < baseStart_2336355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336362 : List Nat := [3, 1, 3, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_2336362 : Nat := 118140960795 + 2336362 * 2 ^ 59
def prefixEnd_2336362 : Nat := 4983230072969 + 3 ^ 40 * 2336362 * 2
def baseEnd_2336362 : Nat := 1199676688899893206630273

theorem tailTrace_2336362 : CollatzResearch.WordTrace tailWord_2336362 prefixEnd_2336362 1199676688899893206630273 := by
  unfold tailWord_2336362
  simp only [CollatzResearch.WordTrace]
  refine ⟨21303530690441741926798835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56809415174511311804796893 21303530690441741926798835)
  ·
    refine ⟨31955296035662612890198253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21303530690441741926798835 31955296035662612890198253)
    ·
      refine ⟨11983236013373479833824345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31955296035662612890198253 11983236013373479833824345)
      ·
        refine ⟨8987427010030109875368259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11983236013373479833824345 8987427010030109875368259)
        ·
          refine ⟨13481140515045164813052389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8987427010030109875368259 13481140515045164813052389)
          ·
            refine ⟨2527713846570968402447323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13481140515045164813052389 2527713846570968402447323)
            ·
              refine ⟨3791570769856452603670985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2527713846570968402447323 3791570769856452603670985)
              ·
                refine ⟨2843678077392339452753239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3791570769856452603670985 2843678077392339452753239)
                ·
                  refine ⟨4265517116088509179129859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2843678077392339452753239 4265517116088509179129859)
                  ·
                    refine ⟨6398275674132763768694789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4265517116088509179129859 6398275674132763768694789)
                    ·
                      refine ⟨1199676688899893206630273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6398275674132763768694789 1199676688899893206630273)
                      ·
                        rfl

theorem cell23_2336362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_2336362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336362 prefixEnd_2336362 := by exact prefixLift 2336362
  have htrace : WordTrace (prefixWord ++ tailWord_2336362) baseStart_2336362 baseEnd_2336362 := by
    simpa [prefixWord, tailWord_2336362, baseEnd_2336362] using wordTrace_append hprefix tailTrace_2336362
  have hstable : (prefixWord ++ tailWord_2336362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336362).length < 2 ^ (prefixWord ++ tailWord_2336362).sum := by decide
  have hdescent : baseEnd_2336362 < baseStart_2336362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336398 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 2, 7]
def baseStart_2336398 : Nat := 118140960795 + 2336398 * 2 ^ 59
def prefixEnd_2336398 : Nat := 4983230072969 + 3 ^ 40 * 2336398 * 2
def baseEnd_2336398 : Nat := 399898391401151688593369

theorem tailTrace_2336398 : CollatzResearch.WordTrace tailWord_2336398 prefixEnd_2336398 399898391401151688593369 := by
  unfold tailWord_2336398
  simp only [CollatzResearch.WordTrace]
  refine ⟨10651929473704568231938231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56810290526424363903670565 10651929473704568231938231)
  ·
    refine ⟨15977894210556852347907347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10651929473704568231938231 15977894210556852347907347)
    ·
      refine ⟨23966841315835278521861021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15977894210556852347907347 23966841315835278521861021)
      ·
        refine ⟨8987565493438229445697883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23966841315835278521861021 8987565493438229445697883)
        ·
          refine ⟨13481348240157344168546825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8987565493438229445697883 13481348240157344168546825)
          ·
            refine ⟨10111011180118008126410119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13481348240157344168546825 10111011180118008126410119)
            ·
              refine ⟨15166516770177012189615179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10111011180118008126410119 15166516770177012189615179)
              ·
                refine ⟨22749775155265518284422769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15166516770177012189615179 22749775155265518284422769)
                ·
                  refine ⟨17062331366449138713317077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22749775155265518284422769 17062331366449138713317077)
                  ·
                    refine ⟨399898391401151688593369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17062331366449138713317077 399898391401151688593369)
                    ·
                      rfl

theorem cell23_2336398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_2336398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336398 prefixEnd_2336398 := by exact prefixLift 2336398
  have htrace : WordTrace (prefixWord ++ tailWord_2336398) baseStart_2336398 baseEnd_2336398 := by
    simpa [prefixWord, tailWord_2336398, baseEnd_2336398] using wordTrace_append hprefix tailTrace_2336398
  have hstable : (prefixWord ++ tailWord_2336398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336398).length < 2 ^ (prefixWord ++ tailWord_2336398).sum := by decide
  have hdescent : baseEnd_2336398 < baseStart_2336398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336402 : List Nat := [3, 2, 3, 1, 4, 1, 1, 8]
def baseStart_2336402 : Nat := 118140960795 + 2336402 * 2 ^ 59
def prefixEnd_2336402 : Nat := 4983230072969 + 3 ^ 40 * 2336402 * 2
def baseEnd_2336402 : Nat := 44433230671336038893707

theorem tailTrace_2336402 : CollatzResearch.WordTrace tailWord_2336402 prefixEnd_2336402 44433230671336038893707 := by
  unfold tailWord_2336402
  simp only [CollatzResearch.WordTrace]
  refine ⟨21303895420405513634662865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56810387787748036359100973 21303895420405513634662865)
  ·
    refine ⟨15977921565304135225997149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21303895420405513634662865 15977921565304135225997149)
    ·
      refine ⟨5991720586989050709748931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15977921565304135225997149 5991720586989050709748931)
      ·
        refine ⟨8987580880483576064623397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5991720586989050709748931 8987580880483576064623397)
        ·
          refine ⟨1685171415090670512116887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8987580880483576064623397 1685171415090670512116887)
          ·
            refine ⟨2527757122636005768175331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1685171415090670512116887 2527757122636005768175331)
            ·
              refine ⟨3791635683954008652262997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2527757122636005768175331 3791635683954008652262997)
              ·
                refine ⟨44433230671336038893707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3791635683954008652262997 44433230671336038893707)
                ·
                  rfl

theorem cell23_2336402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 8].length) (baseStart_2336402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336402 prefixEnd_2336402 := by exact prefixLift 2336402
  have htrace : WordTrace (prefixWord ++ tailWord_2336402) baseStart_2336402 baseEnd_2336402 := by
    simpa [prefixWord, tailWord_2336402, baseEnd_2336402] using wordTrace_append hprefix tailTrace_2336402
  have hstable : (prefixWord ++ tailWord_2336402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336402).length < 2 ^ (prefixWord ++ tailWord_2336402).sum := by decide
  have hdescent : baseEnd_2336402 < baseStart_2336402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336412 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_2336412 : Nat := 118140960795 + 2336412 * 2 ^ 59
def prefixEnd_2336412 : Nat := 4983230072969 + 3 ^ 40 * 2336412 * 2
def baseEnd_2336412 : Nat := 1199702362932618011005043

theorem tailTrace_2336412 : CollatzResearch.WordTrace tailWord_2336412 prefixEnd_2336412 1199702362932618011005043 := by
  unfold tailWord_2336412
  simp only [CollatzResearch.WordTrace]
  refine ⟨42607973205792913123257745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56810630941057217497676993 42607973205792913123257745)
  ·
    refine ⟨31955979904344684842443309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42607973205792913123257745 31955979904344684842443309)
    ·
      refine ⟨11983492464129256815916241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31955979904344684842443309 11983492464129256815916241)
      ·
        refine ⟨8987619348096942611937181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11983492464129256815916241 8987619348096942611937181)
        ·
          refine ⟨3370357255536353479476443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8987619348096942611937181 3370357255536353479476443)
          ·
            refine ⟨5055535883304530219214665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3370357255536353479476443 5055535883304530219214665)
            ·
              refine ⟨3791651912478397664410999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5055535883304530219214665 3791651912478397664410999)
              ·
                refine ⟨5687477868717596496616499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3791651912478397664410999 5687477868717596496616499)
                ·
                  refine ⟨8531216803076394744924749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5687477868717596496616499 8531216803076394744924749)
                  ·
                    refine ⟨3199206301153648029346781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8531216803076394744924749 3199206301153648029346781)
                    ·
                      refine ⟨1199702362932618011005043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3199206301153648029346781 1199702362932618011005043)
                      ·
                        rfl

theorem cell23_2336412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_2336412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336412 prefixEnd_2336412 := by exact prefixLift 2336412
  have htrace : WordTrace (prefixWord ++ tailWord_2336412) baseStart_2336412 baseEnd_2336412 := by
    simpa [prefixWord, tailWord_2336412, baseEnd_2336412] using wordTrace_append hprefix tailTrace_2336412
  have hstable : (prefixWord ++ tailWord_2336412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336412).length < 2 ^ (prefixWord ++ tailWord_2336412).sum := by decide
  have hdescent : baseEnd_2336412 < baseStart_2336412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336435 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 1, 4, 2]
def baseStart_2336435 : Nat := 118140960795 + 2336435 * 2 ^ 59
def prefixEnd_2336435 : Nat := 4983230072969 + 3 ^ 40 * 2336435 * 2
def baseEnd_2336435 : Nat := 1199714172987671421017437

theorem tailTrace_2336435 : CollatzResearch.WordTrace tailWord_2336435 prefixEnd_2336435 1199714172987671421017437 := by
  unfold tailWord_2336435
  simp only [CollatzResearch.WordTrace]
  refine ⟨85216785290502501174602759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56811190193668334116401839 85216785290502501174602759)
  ·
    refine ⟨127825177935753751761904139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85216785290502501174602759 127825177935753751761904139)
    ·
      refine ⟨191737766903630627642856209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127825177935753751761904139 191737766903630627642856209)
      ·
        refine ⟨143803325177722970732142157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191737766903630627642856209 143803325177722970732142157)
        ·
          refine ⟨53926246941646114024553309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143803325177722970732142157 53926246941646114024553309)
          ·
            refine ⟨20222342603117292759207491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53926246941646114024553309 20222342603117292759207491)
            ·
              refine ⟨30333513904675939138811237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20222342603117292759207491 30333513904675939138811237)
              ·
                refine ⟨5687533857126738588527107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30333513904675939138811237 5687533857126738588527107)
                ·
                  refine ⟨8531300785690107882790661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5687533857126738588527107 8531300785690107882790661)
                  ·
                    refine ⟨1599618897316895228023249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8531300785690107882790661 1599618897316895228023249)
                    ·
                      refine ⟨1199714172987671421017437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1599618897316895228023249 1199714172987671421017437)
                      ·
                        rfl

theorem cell23_2336435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 4, 2].length) (baseStart_2336435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336435 prefixEnd_2336435 := by exact prefixLift 2336435
  have htrace : WordTrace (prefixWord ++ tailWord_2336435) baseStart_2336435 baseEnd_2336435 := by
    simpa [prefixWord, tailWord_2336435, baseEnd_2336435] using wordTrace_append hprefix tailTrace_2336435
  have hstable : (prefixWord ++ tailWord_2336435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336435).length < 2 ^ (prefixWord ++ tailWord_2336435).sum := by decide
  have hdescent : baseEnd_2336435 < baseStart_2336435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336439 : List Nat := [1, 1, 3, 1, 5, 1, 4, 1, 1, 3, 2]
def baseStart_2336439 : Nat := 118140960795 + 2336439 * 2 ^ 59
def prefixEnd_2336439 : Nat := 4983230072969 + 3 ^ 40 * 2336439 * 2
def baseEnd_2336439 : Nat := 1199716226910289405367419

theorem tailTrace_2336439 : CollatzResearch.WordTrace tailWord_2336439 prefixEnd_2336439 1199716226910289405367419 := by
  unfold tailWord_2336439
  simp only [CollatzResearch.WordTrace]
  refine ⟨85216931182488009857748371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56811287454992006571832247 85216931182488009857748371)
  ·
    refine ⟨127825396773732014786622557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85216931182488009857748371 127825396773732014786622557)
    ·
      refine ⟨47934523790149505544983459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127825396773732014786622557 47934523790149505544983459)
      ·
        refine ⟨71901785685224258317475189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47934523790149505544983459 71901785685224258317475189)
        ·
          refine ⟨6740792407989774217263299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71901785685224258317475189 6740792407989774217263299)
          ·
            refine ⟨10111188611984661325894949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6740792407989774217263299 10111188611984661325894949)
            ·
              refine ⟨1895847864747123998605303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10111188611984661325894949 1895847864747123998605303)
              ·
                refine ⟨2843771797120685997907955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1895847864747123998605303 2843771797120685997907955)
                ·
                  refine ⟨4265657695681028996861933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2843771797120685997907955 4265657695681028996861933)
                  ·
                    refine ⟨1599621635880385873823225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4265657695681028996861933 1599621635880385873823225)
                    ·
                      refine ⟨1199716226910289405367419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1599621635880385873823225 1199716226910289405367419)
                      ·
                        rfl

theorem cell23_2336439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 1, 3, 2].length) (baseStart_2336439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336439 prefixEnd_2336439 := by exact prefixLift 2336439
  have htrace : WordTrace (prefixWord ++ tailWord_2336439) baseStart_2336439 baseEnd_2336439 := by
    simpa [prefixWord, tailWord_2336439, baseEnd_2336439] using wordTrace_append hprefix tailTrace_2336439
  have hstable : (prefixWord ++ tailWord_2336439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336439).length < 2 ^ (prefixWord ++ tailWord_2336439).sum := by decide
  have hdescent : baseEnd_2336439 < baseStart_2336439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336448 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 4]
def baseStart_2336448 : Nat := 118140960795 + 2336448 * 2 ^ 59
def prefixEnd_2336448 : Nat := 4983230072969 + 3 ^ 40 * 2336448 * 2
def baseEnd_2336448 : Nat := 1199720848236179870154877

theorem tailTrace_2336448 : CollatzResearch.WordTrace tailWord_2336448 prefixEnd_2336448 1199720848236179870154877 := by
  unfold tailWord_2336448
  simp only [CollatzResearch.WordTrace]
  refine ⟨42608629719727702197412999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56811506292970269596550665 42608629719727702197412999)
  ·
    refine ⟨63912944579591553296119499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42608629719727702197412999 63912944579591553296119499)
    ·
      refine ⟨95869416869387329944179249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63912944579591553296119499 95869416869387329944179249)
      ·
        refine ⟨71902062652040497458134437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95869416869387329944179249 71902062652040497458134437)
        ·
          refine ⟨13481636747257593273400207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71902062652040497458134437 13481636747257593273400207)
          ·
            refine ⟨20222455120886389910100311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13481636747257593273400207 20222455120886389910100311)
            ·
              refine ⟨30333682681329584865150467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20222455120886389910100311 30333682681329584865150467)
              ·
                refine ⟨45500524021994377297725701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30333682681329584865150467 45500524021994377297725701)
                ·
                  refine ⟨8531348254123945743323569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45500524021994377297725701 8531348254123945743323569)
                  ·
                    refine ⟨6398511190592959307492677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8531348254123945743323569 6398511190592959307492677)
                    ·
                      refine ⟨1199720848236179870154877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6398511190592959307492677 1199720848236179870154877)
                      ·
                        rfl

theorem cell23_2336448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_2336448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336448 prefixEnd_2336448 := by exact prefixLift 2336448
  have htrace : WordTrace (prefixWord ++ tailWord_2336448) baseStart_2336448 baseEnd_2336448 := by
    simpa [prefixWord, tailWord_2336448, baseEnd_2336448] using wordTrace_append hprefix tailTrace_2336448
  have hstable : (prefixWord ++ tailWord_2336448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336448).length < 2 ^ (prefixWord ++ tailWord_2336448).sum := by decide
  have hdescent : baseEnd_2336448 < baseStart_2336448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336562 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3]
def baseStart_2336562 : Nat := 118140960795 + 2336562 * 2 ^ 59
def prefixEnd_2336562 : Nat := 4983230072969 + 3 ^ 40 * 2336562 * 2
def baseEnd_2336562 : Nat := 1199779385030792424129353

theorem tailTrace_2336562 : CollatzResearch.WordTrace tailWord_2336562 prefixEnd_2336562 1199779385030792424129353 := by
  unfold tailWord_2336562
  simp only [CollatzResearch.WordTrace]
  refine ⟨21305354340260600466118985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56814278240694934576317293 21305354340260600466118985)
  ·
    refine ⟨15979015755195450349589239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21305354340260600466118985 15979015755195450349589239)
    ·
      refine ⟨23968523632793175524383859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15979015755195450349589239 23968523632793175524383859)
      ·
        refine ⟨35952785449189763286575789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23968523632793175524383859 35952785449189763286575789)
        ·
          refine ⟨13482294543446161232465921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35952785449189763286575789 13482294543446161232465921)
          ·
            refine ⟨10111720907584620924349441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13482294543446161232465921 10111720907584620924349441)
            ·
              refine ⟨7583790680688465693262081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10111720907584620924349441 7583790680688465693262081)
              ·
                refine ⟨5687843010516349269946561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7583790680688465693262081 5687843010516349269946561)
                ·
                  refine ⟨4265882257887261952459921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5687843010516349269946561 4265882257887261952459921)
                  ·
                    refine ⟨3199411693415446464344941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4265882257887261952459921 3199411693415446464344941)
                    ·
                      refine ⟨1199779385030792424129353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3199411693415446464344941 1199779385030792424129353)
                      ·
                        rfl

theorem cell23_2336562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_2336562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336562 prefixEnd_2336562 := by exact prefixLift 2336562
  have htrace : WordTrace (prefixWord ++ tailWord_2336562) baseStart_2336562 baseEnd_2336562 := by
    simpa [prefixWord, tailWord_2336562, baseEnd_2336562] using wordTrace_append hprefix tailTrace_2336562
  have hstable : (prefixWord ++ tailWord_2336562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336562).length < 2 ^ (prefixWord ++ tailWord_2336562).sum := by decide
  have hdescent : baseEnd_2336562 < baseStart_2336562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336602 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2]
def baseStart_2336602 : Nat := 118140960795 + 2336602 * 2 ^ 59
def prefixEnd_2336602 : Nat := 4983230072969 + 3 ^ 40 * 2336602 * 2
def baseEnd_2336602 : Nat := 1199799924256972267629169

theorem tailTrace_2336602 : CollatzResearch.WordTrace tailWord_2336602 prefixEnd_2336602 1199799924256972267629169 := by
  unfold tailWord_2336602
  simp only [CollatzResearch.WordTrace]
  refine ⟨21305719070224372173983015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56815250853931659130621373 21305719070224372173983015)
  ·
    refine ⟨31958578605336558260974523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21305719070224372173983015 31958578605336558260974523)
    ·
      refine ⟨47937867908004837391461785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31958578605336558260974523 47937867908004837391461785)
      ·
        refine ⟨35953400931003628043596339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47937867908004837391461785 35953400931003628043596339)
        ·
          refine ⟨53930101396505442065394509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35953400931003628043596339 53930101396505442065394509)
          ·
            refine ⟨20223788023689540774522941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53930101396505442065394509 20223788023689540774522941)
            ·
              refine ⟨7583920508883577790446103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20223788023689540774522941 7583920508883577790446103)
              ·
                refine ⟨11375880763325366685669155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7583920508883577790446103 11375880763325366685669155)
                ·
                  refine ⟨17063821144988050028503733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11375880763325366685669155 17063821144988050028503733)
                  ·
                    refine ⟨1599733232342629690172225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17063821144988050028503733 1599733232342629690172225)
                    ·
                      refine ⟨1199799924256972267629169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1599733232342629690172225 1199799924256972267629169)
                      ·
                        rfl

theorem cell23_2336602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_2336602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336602 prefixEnd_2336602 := by exact prefixLift 2336602
  have htrace : WordTrace (prefixWord ++ tailWord_2336602) baseStart_2336602 baseEnd_2336602 := by
    simpa [prefixWord, tailWord_2336602, baseEnd_2336602] using wordTrace_append hprefix tailTrace_2336602
  have hstable : (prefixWord ++ tailWord_2336602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336602).length < 2 ^ (prefixWord ++ tailWord_2336602).sum := by decide
  have hdescent : baseEnd_2336602 < baseStart_2336602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336645 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 1, 1, 6]
def baseStart_2336645 : Nat := 118140960795 + 2336645 * 2 ^ 59
def prefixEnd_2336645 : Nat := 4983230072969 + 3 ^ 40 * 2336645 * 2
def baseEnd_2336645 : Nat := 1199822003925115599391471

theorem tailTrace_2336645 : CollatzResearch.WordTrace tailWord_2336645 prefixEnd_2336645 1199822003925115599391471 := by
  unfold tailWord_2336645
  simp only [CollatzResearch.WordTrace]
  refine ⟨85224444619741707039747389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56816296413161138026498259 85224444619741707039747389)
  ·
    refine ⟨31959166732403140139905271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85224444619741707039747389 31959166732403140139905271)
    ·
      refine ⟨47938750098604710209857907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31959166732403140139905271 47938750098604710209857907)
      ·
        refine ⟨71908125147907065314786861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47938750098604710209857907 71908125147907065314786861)
        ·
          refine ⟨26965546930465149493045073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71908125147907065314786861 26965546930465149493045073)
          ·
            refine ⟨20224160197848862119783805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26965546930465149493045073 20224160197848862119783805)
            ·
              refine ⟨7584060074193323294918927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20224160197848862119783805 7584060074193323294918927)
              ·
                refine ⟨11376090111289984942378391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7584060074193323294918927 11376090111289984942378391)
                ·
                  refine ⟨17064135166934977413567587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11376090111289984942378391 17064135166934977413567587)
                  ·
                    refine ⟨25596202750402466120351381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17064135166934977413567587 25596202750402466120351381)
                    ·
                      refine ⟨1199822003925115599391471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25596202750402466120351381 1199822003925115599391471)
                      ·
                        rfl

theorem cell23_2336645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_2336645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336645 prefixEnd_2336645 := by exact prefixLift 2336645
  have htrace : WordTrace (prefixWord ++ tailWord_2336645) baseStart_2336645 baseEnd_2336645 := by
    simpa [prefixWord, tailWord_2336645, baseEnd_2336645] using wordTrace_append hprefix tailTrace_2336645
  have hstable : (prefixWord ++ tailWord_2336645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336645).length < 2 ^ (prefixWord ++ tailWord_2336645).sum := by decide
  have hdescent : baseEnd_2336645 < baseStart_2336645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336649 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 3, 2, 2]
def baseStart_2336649 : Nat := 118140960795 + 2336649 * 2 ^ 59
def prefixEnd_2336649 : Nat := 4983230072969 + 3 ^ 40 * 2336649 * 2
def baseEnd_2336649 : Nat := 1199824057847733583741453

theorem tailTrace_2336649 : CollatzResearch.WordTrace tailWord_2336649 prefixEnd_2336649 1199824057847733583741453 := by
  unfold tailWord_2336649
  simp only [CollatzResearch.WordTrace]
  refine ⟨85224590511727215722893001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56816393674484810481928667 85224590511727215722893001)
  ·
    refine ⟨63918442883795411792169751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85224590511727215722893001 63918442883795411792169751)
    ·
      refine ⟨95877664325693117688254627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63918442883795411792169751 95877664325693117688254627)
      ·
        refine ⟨143816496488539676532381941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95877664325693117688254627 143816496488539676532381941)
        ·
          refine ⟨13482796545800594674910807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 143816496488539676532381941 13482796545800594674910807)
          ·
            refine ⟨20224194818700892012366211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13482796545800594674910807 20224194818700892012366211)
            ·
              refine ⟨30336292228051338018549317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20224194818700892012366211 30336292228051338018549317)
              ·
                refine ⟨5688054792759625878477997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30336292228051338018549317 5688054792759625878477997)
                ·
                  refine ⟨2133020547284859704429249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5688054792759625878477997 2133020547284859704429249)
                  ·
                    refine ⟨1599765410463644778321937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2133020547284859704429249 1599765410463644778321937)
                    ·
                      refine ⟨1199824057847733583741453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1599765410463644778321937 1199824057847733583741453)
                      ·
                        rfl

theorem cell23_2336649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 2, 2].length) (baseStart_2336649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336649 prefixEnd_2336649 := by exact prefixLift 2336649
  have htrace : WordTrace (prefixWord ++ tailWord_2336649) baseStart_2336649 baseEnd_2336649 := by
    simpa [prefixWord, tailWord_2336649, baseEnd_2336649] using wordTrace_append hprefix tailTrace_2336649
  have hstable : (prefixWord ++ tailWord_2336649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336649).length < 2 ^ (prefixWord ++ tailWord_2336649).sum := by decide
  have hdescent : baseEnd_2336649 < baseStart_2336649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336669 : List Nat := [1, 4, 2, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_2336669 : Nat := 118140960795 + 2336669 * 2 ^ 59
def prefixEnd_2336669 : Nat := 4983230072969 + 3 ^ 40 * 2336669 * 2
def baseEnd_2336669 : Nat := 1199834327460823505491361

theorem tailTrace_2336669 : CollatzResearch.WordTrace tailWord_2336669 prefixEnd_2336669 1199834327460823505491361 := by
  unfold tailWord_2336669
  simp only [CollatzResearch.WordTrace]
  refine ⟨85225319971654759138621061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56816879981103172759080707 85225319971654759138621061)
  ·
    refine ⟨15979747494685267338491449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85225319971654759138621061 15979747494685267338491449)
    ·
      refine ⟨11984810621013950503868587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15979747494685267338491449 11984810621013950503868587)
      ·
        refine ⟨17977215931520925755802881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11984810621013950503868587 17977215931520925755802881)
        ·
          refine ⟨13482911948640694316852161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17977215931520925755802881 13482911948640694316852161)
          ·
            refine ⟨10112183961480520737639121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13482911948640694316852161 10112183961480520737639121)
            ·
              refine ⟨7584137971110390553229341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10112183961480520737639121 7584137971110390553229341)
              ·
                refine ⟨2844051739166396457461003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7584137971110390553229341 2844051739166396457461003)
                ·
                  refine ⟨4266077608749594686191505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844051739166396457461003 4266077608749594686191505)
                  ·
                    refine ⟨3199558206562196014643629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4266077608749594686191505 3199558206562196014643629)
                    ·
                      refine ⟨1199834327460823505491361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3199558206562196014643629 1199834327460823505491361)
                      ·
                        rfl

theorem cell23_2336669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_2336669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336669 prefixEnd_2336669 := by exact prefixLift 2336669
  have htrace : WordTrace (prefixWord ++ tailWord_2336669) baseStart_2336669 baseEnd_2336669 := by
    simpa [prefixWord, tailWord_2336669, baseEnd_2336669] using wordTrace_append hprefix tailTrace_2336669
  have hstable : (prefixWord ++ tailWord_2336669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336669).length < 2 ^ (prefixWord ++ tailWord_2336669).sum := by decide
  have hdescent : baseEnd_2336669 < baseStart_2336669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336709 : List Nat := [1, 3, 1, 1, 1, 1, 1, 8, 1, 3, 2]
def baseStart_2336709 : Nat := 118140960795 + 2336709 * 2 ^ 59
def prefixEnd_2336709 : Nat := 4983230072969 + 3 ^ 40 * 2336709 * 2
def baseEnd_2336709 : Nat := 1199854866687003348991177

theorem tailTrace_2336709 : CollatzResearch.WordTrace tailWord_2336709 prefixEnd_2336709 1199854866687003348991177 := by
  unfold tailWord_2336709
  simp only [CollatzResearch.WordTrace]
  refine ⟨85226778891509845970077181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56817852594339897313384787 85226778891509845970077181)
  ·
    refine ⟨31960042084316192238778943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85226778891509845970077181 31960042084316192238778943)
    ·
      refine ⟨47940063126474288358168415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31960042084316192238778943 47940063126474288358168415)
      ·
        refine ⟨71910094689711432537252623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47940063126474288358168415 71910094689711432537252623)
        ·
          refine ⟨107865142034567148805878935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71910094689711432537252623 107865142034567148805878935)
          ·
            refine ⟨161797713051850723208818403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107865142034567148805878935 161797713051850723208818403)
            ·
              refine ⟨242696569577776084813227605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161797713051850723208818403 242696569577776084813227605)
              ·
                refine ⟨2844100424739563493905011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 242696569577776084813227605 2844100424739563493905011)
                ·
                  refine ⟨4266150637109345240857517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844100424739563493905011 4266150637109345240857517)
                  ·
                    refine ⟨1599806488916004465321569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4266150637109345240857517 1599806488916004465321569)
                    ·
                      refine ⟨1199854866687003348991177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1599806488916004465321569 1199854866687003348991177)
                      ·
                        rfl

theorem cell23_2336709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 3, 2].length) (baseStart_2336709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336709 prefixEnd_2336709 := by exact prefixLift 2336709
  have htrace : WordTrace (prefixWord ++ tailWord_2336709) baseStart_2336709 baseEnd_2336709 := by
    simpa [prefixWord, tailWord_2336709, baseEnd_2336709] using wordTrace_append hprefix tailTrace_2336709
  have hstable : (prefixWord ++ tailWord_2336709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336709).length < 2 ^ (prefixWord ++ tailWord_2336709).sum := by decide
  have hdescent : baseEnd_2336709 < baseStart_2336709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336733 : List Nat := [1, 4, 3, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_2336733 : Nat := 118140960795 + 2336733 * 2 ^ 59
def prefixEnd_2336733 : Nat := 4983230072969 + 3 ^ 40 * 2336733 * 2
def baseEnd_2336733 : Nat := 1199867190222711255091067

theorem tailTrace_2336733 : CollatzResearch.WordTrace tailWord_2336733 prefixEnd_2336733 1199867190222711255091067 := by
  unfold tailWord_2336733
  simp only [CollatzResearch.WordTrace]
  refine ⟨85227654243422898068950853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56818436162281932045967235 85227654243422898068950853)
  ·
    refine ⟨15980185170641793387928285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85227654243422898068950853 15980185170641793387928285)
    ·
      refine ⟨5992569438990672520473107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15980185170641793387928285 5992569438990672520473107)
      ·
        refine ⟨8988854158486008780709661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5992569438990672520473107 8988854158486008780709661)
        ·
          refine ⟨3370820309432253292766123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8988854158486008780709661 3370820309432253292766123)
          ·
            refine ⟨5056230464148379939149185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3370820309432253292766123 5056230464148379939149185)
            ·
              refine ⟨3792172848111284954361889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5056230464148379939149185 3792172848111284954361889)
              ·
                refine ⟨2844129636083463715771417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3792172848111284954361889 2844129636083463715771417)
                ·
                  refine ⟨2133097227062597786828563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2844129636083463715771417 2133097227062597786828563)
                  ·
                    refine ⟨3199645840593896680242845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2133097227062597786828563 3199645840593896680242845)
                    ·
                      refine ⟨1199867190222711255091067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3199645840593896680242845 1199867190222711255091067)
                      ·
                        rfl

theorem cell23_2336733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_2336733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336733 prefixEnd_2336733 := by exact prefixLift 2336733
  have htrace : WordTrace (prefixWord ++ tailWord_2336733) baseStart_2336733 baseEnd_2336733 := by
    simpa [prefixWord, tailWord_2336733, baseEnd_2336733] using wordTrace_append hprefix tailTrace_2336733
  have hstable : (prefixWord ++ tailWord_2336733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336733).length < 2 ^ (prefixWord ++ tailWord_2336733).sum := by decide
  have hdescent : baseEnd_2336733 < baseStart_2336733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336779 : List Nat := [1, 1, 1, 1, 6, 1, 4, 3, 5]
def baseStart_2336779 : Nat := 118140960795 + 2336779 * 2 ^ 59
def prefixEnd_2336779 : Nat := 4983230072969 + 3 ^ 40 * 2336779 * 2
def baseEnd_2336779 : Nat := 133321201148090897235095

theorem tailTrace_2336779 : CollatzResearch.WordTrace tailWord_2336779 prefixEnd_2336779 133321201148090897235095 := by
  unfold tailWord_2336779
  simp only [CollatzResearch.WordTrace]
  refine ⟨85229332001256247925125391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56819554667504165283416927 85229332001256247925125391)
  ·
    refine ⟨127843998001884371887688087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85229332001256247925125391 127843998001884371887688087)
    ·
      refine ⟨191765997002826557831532131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127843998001884371887688087 191765997002826557831532131)
      ·
        refine ⟨287648995504239836747298197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191765997002826557831532131 287648995504239836747298197)
        ·
          refine ⟨13483546664261242347529603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 287648995504239836747298197 13483546664261242347529603)
          ·
            refine ⟨20225319996391863521294405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13483546664261242347529603 20225319996391863521294405)
            ·
              refine ⟨3792247499323474410242701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20225319996391863521294405 3792247499323474410242701)
              ·
                refine ⟨1422092812246302903841013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3792247499323474410242701 1422092812246302903841013)
                ·
                  refine ⟨133321201148090897235095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1422092812246302903841013 133321201148090897235095)
                  ·
                    rfl

theorem cell23_2336779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 5].length) (baseStart_2336779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336779 prefixEnd_2336779 := by exact prefixLift 2336779
  have htrace : WordTrace (prefixWord ++ tailWord_2336779) baseStart_2336779 baseEnd_2336779 := by
    simpa [prefixWord, tailWord_2336779, baseEnd_2336779] using wordTrace_append hprefix tailTrace_2336779
  have hstable : (prefixWord ++ tailWord_2336779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336779).length < 2 ^ (prefixWord ++ tailWord_2336779).sum := by decide
  have hdescent : baseEnd_2336779 < baseStart_2336779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336792 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 4, 5]
def baseStart_2336792 : Nat := 118140960795 + 2336792 * 2 ^ 59
def prefixEnd_2336792 : Nat := 4983230072969 + 3 ^ 40 * 2336792 * 2
def baseEnd_2336792 : Nat := 399965828527108841417765

theorem tailTrace_2336792 : CollatzResearch.WordTrace tailWord_2336792 prefixEnd_2336792 399965828527108841417765 := by
  unfold tailWord_2336792
  simp only [CollatzResearch.WordTrace]
  refine ⟨42614903075104575572674315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56819870766806100763565753 42614903075104575572674315)
  ·
    refine ⟨63922354612656863359011473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42614903075104575572674315 63922354612656863359011473)
    ·
      refine ⟨47941765959492647519258605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63922354612656863359011473 47941765959492647519258605)
      ·
        refine ⟨17978162234809742819721977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47941765959492647519258605 17978162234809742819721977)
        ·
          refine ⟨13483621676107307114791483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17978162234809742819721977 13483621676107307114791483)
          ·
            refine ⟨20225432514160960672187225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13483621676107307114791483 20225432514160960672187225)
            ·
              refine ⟨15169074385620720504140419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20225432514160960672187225 15169074385620720504140419)
              ·
                refine ⟨22753611578431080756210629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15169074385620720504140419 22753611578431080756210629)
                ·
                  refine ⟨4266302170955827641789493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22753611578431080756210629 4266302170955827641789493)
                  ·
                    refine ⟨399965828527108841417765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4266302170955827641789493 399965828527108841417765)
                    ·
                      rfl

theorem cell23_2336792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_2336792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336792 prefixEnd_2336792 := by exact prefixLift 2336792
  have htrace : WordTrace (prefixWord ++ tailWord_2336792) baseStart_2336792 baseEnd_2336792 := by
    simpa [prefixWord, tailWord_2336792, baseEnd_2336792] using wordTrace_append hprefix tailTrace_2336792
  have hstable : (prefixWord ++ tailWord_2336792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336792).length < 2 ^ (prefixWord ++ tailWord_2336792).sum := by decide
  have hdescent : baseEnd_2336792 < baseStart_2336792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336802 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_2336802 : Nat := 118140960795 + 2336802 * 2 ^ 59
def prefixEnd_2336802 : Nat := 4983230072969 + 3 ^ 40 * 2336802 * 2
def baseEnd_2336802 : Nat := 1199902620387871485128249

theorem tailTrace_2336802 : CollatzResearch.WordTrace tailWord_2336802 prefixEnd_2336802 1199902620387871485128249 := by
  unfold tailWord_2336802
  simp only [CollatzResearch.WordTrace]
  refine ⟨21307542720043230713303165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56820113920115281902141773 21307542720043230713303165)
  ·
    refine ⟨7990328520016211517488687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21307542720043230713303165 7990328520016211517488687)
    ·
      refine ⟨11985492780024317276233031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7990328520016211517488687 11985492780024317276233031)
      ·
        refine ⟨17978239170036475914349547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11985492780024317276233031 17978239170036475914349547)
        ·
          refine ⟨26967358755054713871524321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17978239170036475914349547 26967358755054713871524321)
          ·
            refine ⟨20225519066291035403643241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26967358755054713871524321 20225519066291035403643241)
            ·
              refine ⟨15169139299718276552732431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20225519066291035403643241 15169139299718276552732431)
              ·
                refine ⟨22753708949577414829098647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15169139299718276552732431 22753708949577414829098647)
                ·
                  refine ⟨34130563424366122243647971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22753708949577414829098647 34130563424366122243647971)
                  ·
                    refine ⟨51195845136549183365471957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34130563424366122243647971 51195845136549183365471957)
                    ·
                      refine ⟨1199902620387871485128249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51195845136549183365471957 1199902620387871485128249)
                      ·
                        rfl

theorem cell23_2336802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_2336802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336802 prefixEnd_2336802 := by exact prefixLift 2336802
  have htrace : WordTrace (prefixWord ++ tailWord_2336802) baseStart_2336802 baseEnd_2336802 := by
    simpa [prefixWord, tailWord_2336802, baseEnd_2336802] using wordTrace_append hprefix tailTrace_2336802
  have hstable : (prefixWord ++ tailWord_2336802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336802).length < 2 ^ (prefixWord ++ tailWord_2336802).sum := by decide
  have hdescent : baseEnd_2336802 < baseStart_2336802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336807 : List Nat := [1, 1, 7, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_2336807 : Nat := 118140960795 + 2336807 * 2 ^ 59
def prefixEnd_2336807 : Nat := 4983230072969 + 3 ^ 40 * 2336807 * 2
def baseEnd_2336807 : Nat := 1199905187791143965565727

theorem tailTrace_2336807 : CollatzResearch.WordTrace tailWord_2336807 prefixEnd_2336807 1199905187791143965565727 := by
  unfold tailWord_2336807
  simp only [CollatzResearch.WordTrace]
  refine ⟨85230353245154808707144675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56820235496769872471429783 85230353245154808707144675)
  ·
    refine ⟨127845529867732213060717013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85230353245154808707144675 127845529867732213060717013)
    ·
      refine ⟨2996379606274973743610555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 127845529867732213060717013 2996379606274973743610555)
      ·
        refine ⟨4494569409412460615415833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2996379606274973743610555 4494569409412460615415833)
        ·
          refine ⟨3370927057059345461561875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4494569409412460615415833 3370927057059345461561875)
          ·
            refine ⟨5056390585589018192342813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3370927057059345461561875 5056390585589018192342813)
            ·
              refine ⟨1896146469595881822128555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5056390585589018192342813 1896146469595881822128555)
              ·
                refine ⟨2844219704393822733192833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896146469595881822128555 2844219704393822733192833)
                ·
                  refine ⟨2133164778295367049894625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2844219704393822733192833 2133164778295367049894625)
                  ·
                    refine ⟨1599873583721525287420969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2133164778295367049894625 1599873583721525287420969)
                    ·
                      refine ⟨1199905187791143965565727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1599873583721525287420969 1199905187791143965565727)
                      ·
                        rfl

theorem cell23_2336807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_2336807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336807 prefixEnd_2336807 := by exact prefixLift 2336807
  have htrace : WordTrace (prefixWord ++ tailWord_2336807) baseStart_2336807 baseEnd_2336807 := by
    simpa [prefixWord, tailWord_2336807, baseEnd_2336807] using wordTrace_append hprefix tailTrace_2336807
  have hstable : (prefixWord ++ tailWord_2336807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336807).length < 2 ^ (prefixWord ++ tailWord_2336807).sum := by decide
  have hdescent : baseEnd_2336807 < baseStart_2336807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336812 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 4]
def baseStart_2336812 : Nat := 118140960795 + 2336812 * 2 ^ 59
def prefixEnd_2336812 : Nat := 4983230072969 + 3 ^ 40 * 2336812 * 2
def baseEnd_2336812 : Nat := 1199907755194416446003203

theorem tailTrace_2336812 : CollatzResearch.WordTrace tailWord_2336812 prefixEnd_2336812 1199907755194416446003203 := by
  unfold tailWord_2336812
  simp only [CollatzResearch.WordTrace]
  refine ⟨42615267805068347280538345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56820357073424463040717793 42615267805068347280538345)
  ·
    refine ⟨31961450853801260460403759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42615267805068347280538345 31961450853801260460403759)
    ·
      refine ⟨47942176280701890690605639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31961450853801260460403759 47942176280701890690605639)
      ·
        refine ⟨71913264421052836035908459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47942176280701890690605639 71913264421052836035908459)
        ·
          refine ⟨107869896631579254053862689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71913264421052836035908459 107869896631579254053862689)
          ·
            refine ⟨80902422473684440540397017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107869896631579254053862689 80902422473684440540397017)
            ·
              refine ⟨60676816855263330405297763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80902422473684440540397017 60676816855263330405297763)
              ·
                refine ⟨91015225282894995607946645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60676816855263330405297763 91015225282894995607946645)
                ·
                  refine ⟨4266338685135702919122499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91015225282894995607946645 4266338685135702919122499)
                  ·
                    refine ⟨6399508027703554378683749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4266338685135702919122499 6399508027703554378683749)
                    ·
                      refine ⟨1199907755194416446003203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6399508027703554378683749 1199907755194416446003203)
                      ·
                        rfl

theorem cell23_2336812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_2336812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336812 prefixEnd_2336812 := by exact prefixLift 2336812
  have htrace : WordTrace (prefixWord ++ tailWord_2336812) baseStart_2336812 baseEnd_2336812 := by
    simpa [prefixWord, tailWord_2336812, baseEnd_2336812] using wordTrace_append hprefix tailTrace_2336812
  have hstable : (prefixWord ++ tailWord_2336812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336812).length < 2 ^ (prefixWord ++ tailWord_2336812).sum := by decide
  have hdescent : baseEnd_2336812 < baseStart_2336812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336829 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_2336829 : Nat := 118140960795 + 2336829 * 2 ^ 59
def prefixEnd_2336829 : Nat := 4983230072969 + 3 ^ 40 * 2336829 * 2
def baseEnd_2336829 : Nat := 1199916484365542879490625

theorem tailTrace_2336829 : CollatzResearch.WordTrace tailWord_2336829 prefixEnd_2336829 1199916484365542879490625 := by
  unfold tailWord_2336829
  simp only [CollatzResearch.WordTrace]
  refine ⟨85231155651075106464445541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56820770434050070976297027 85231155651075106464445541)
  ·
    refine ⟨15980841684576582462083539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85231155651075106464445541 15980841684576582462083539)
    ·
      refine ⟨23971262526864873693125309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15980841684576582462083539 23971262526864873693125309)
      ·
        refine ⟨8989223447574327634921991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23971262526864873693125309 8989223447574327634921991)
        ·
          refine ⟨13483835171361491452382987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8989223447574327634921991 13483835171361491452382987)
          ·
            refine ⟨20225752757042237178574481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13483835171361491452382987 20225752757042237178574481)
            ·
              refine ⟨15169314567781677883930861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20225752757042237178574481 15169314567781677883930861)
              ·
                refine ⟨5688492962918129206474073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15169314567781677883930861 5688492962918129206474073)
                ·
                  refine ⟨4266369722188596904855555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5688492962918129206474073 4266369722188596904855555)
                  ·
                    refine ⟨6399554583282895357283333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4266369722188596904855555 6399554583282895357283333)
                    ·
                      refine ⟨1199916484365542879490625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6399554583282895357283333 1199916484365542879490625)
                      ·
                        rfl

theorem cell23_2336829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_2336829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336829 prefixEnd_2336829 := by exact prefixLift 2336829
  have htrace : WordTrace (prefixWord ++ tailWord_2336829) baseStart_2336829 baseEnd_2336829 := by
    simpa [prefixWord, tailWord_2336829, baseEnd_2336829] using wordTrace_append hprefix tailTrace_2336829
  have hstable : (prefixWord ++ tailWord_2336829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336829).length < 2 ^ (prefixWord ++ tailWord_2336829).sum := by decide
  have hdescent : baseEnd_2336829 < baseStart_2336829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336830 : List Nat := [4, 2, 1, 3, 3, 1, 1, 3, 5]
def baseStart_2336830 : Nat := 118140960795 + 2336830 * 2 ^ 59
def prefixEnd_2336830 : Nat := 4983230072969 + 3 ^ 40 * 2336830 * 2
def baseEnd_2336830 : Nat := 133324110871799708397569

theorem tailTrace_2336830 : CollatzResearch.WordTrace tailWord_2336830 prefixEnd_2336830 133324110871799708397569 := by
  unfold tailWord_2336830
  simp only [CollatzResearch.WordTrace]
  refine ⟨10653899015508935454403993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56820794749380989090154629 10653899015508935454403993)
  ·
    refine ⟨7990424261631701590802995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10653899015508935454403993 7990424261631701590802995)
    ·
      refine ⟨11985636392447552386204493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7990424261631701590802995 11985636392447552386204493)
      ·
        refine ⟨4494613647167832144826685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11985636392447552386204493 4494613647167832144826685)
        ·
          refine ⟨1685480117687937054310007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4494613647167832144826685 1685480117687937054310007)
          ·
            refine ⟨2528220176531905581465011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1685480117687937054310007 2528220176531905581465011)
            ·
              refine ⟨3792330264797858372197517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2528220176531905581465011 3792330264797858372197517)
              ·
                refine ⟨1422123849299196889574069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3792330264797858372197517 1422123849299196889574069)
                ·
                  refine ⟨133324110871799708397569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1422123849299196889574069 133324110871799708397569)
                  ·
                    rfl

theorem cell23_2336830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_2336830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336830 prefixEnd_2336830 := by exact prefixLift 2336830
  have htrace : WordTrace (prefixWord ++ tailWord_2336830) baseStart_2336830 baseEnd_2336830 := by
    simpa [prefixWord, tailWord_2336830, baseEnd_2336830] using wordTrace_append hprefix tailTrace_2336830
  have hstable : (prefixWord ++ tailWord_2336830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336830).length < 2 ^ (prefixWord ++ tailWord_2336830).sum := by decide
  have hdescent : baseEnd_2336830 < baseStart_2336830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336856 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 3, 4]
def baseStart_2336856 : Nat := 118140960795 + 2336856 * 2 ^ 59
def prefixEnd_2336856 : Nat := 4983230072969 + 3 ^ 40 * 2336856 * 2
def baseEnd_2336856 : Nat := 399976782781071424617667

theorem tailTrace_2336856 : CollatzResearch.WordTrace tailWord_2336856 prefixEnd_2336856 399976782781071424617667 := by
  unfold tailWord_2336856
  simp only [CollatzResearch.WordTrace]
  refine ⟨42616070210988645037839211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56821426947984860050452281 42616070210988645037839211)
  ·
    refine ⟨63924105316482967556758817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42616070210988645037839211 63924105316482967556758817)
    ·
      refine ⟨47943078987362225667569113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63924105316482967556758817 47943078987362225667569113)
      ·
        refine ⟨35957309240521669250676835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47943078987362225667569113 35957309240521669250676835)
        ·
          refine ⟨53935963860782503876015253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35957309240521669250676835 53935963860782503876015253)
          ·
            refine ⟨2528248305974179869188215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53935963860782503876015253 2528248305974179869188215)
            ·
              refine ⟨3792372458961269803782323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2528248305974179869188215 3792372458961269803782323)
              ·
                refine ⟨5688558688441904705673485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3792372458961269803782323 5688558688441904705673485)
                ·
                  refine ⟨2133209508165714264627557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5688558688441904705673485 2133209508165714264627557)
                  ·
                    refine ⟨399976782781071424617667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2133209508165714264627557 399976782781071424617667)
                    ·
                      rfl

theorem cell23_2336856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_2336856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336856 prefixEnd_2336856 := by exact prefixLift 2336856
  have htrace : WordTrace (prefixWord ++ tailWord_2336856) baseStart_2336856 baseEnd_2336856 := by
    simpa [prefixWord, tailWord_2336856, baseEnd_2336856] using wordTrace_append hprefix tailTrace_2336856
  have hstable : (prefixWord ++ tailWord_2336856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336856).length < 2 ^ (prefixWord ++ tailWord_2336856).sum := by decide
  have hdescent : baseEnd_2336856 < baseStart_2336856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336869 : List Nat := [1, 3, 1, 3, 2, 3, 1, 3, 6]
def baseStart_2336869 : Nat := 118140960795 + 2336869 * 2 ^ 59
def prefixEnd_2336869 : Nat := 4983230072969 + 3 ^ 40 * 2336869 * 2
def baseEnd_2336869 : Nat := 133326335954635858110049

theorem tailTrace_2336869 : CollatzResearch.WordTrace tailWord_2336869 prefixEnd_2336869 133326335954635858110049 := by
  unfold tailWord_2336869
  simp only [CollatzResearch.WordTrace]
  refine ⟨85232614570930193295901661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56821743047286795530601107 85232614570930193295901661)
  ·
    refine ⟨31962230464098822485963123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85232614570930193295901661 31962230464098822485963123)
    ·
      refine ⟨47943345696148233728944685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31962230464098822485963123 47943345696148233728944685)
      ·
        refine ⟨17978754636055587648354257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47943345696148233728944685 17978754636055587648354257)
        ·
          refine ⟨13484065977041690736265693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17978754636055587648354257 13484065977041690736265693)
          ·
            refine ⟨5056524741390634026099635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13484065977041690736265693 5056524741390634026099635)
            ·
              refine ⟨7584787112085951039149453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5056524741390634026099635 7584787112085951039149453)
              ·
                refine ⟨2844295167032231639681045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7584787112085951039149453 2844295167032231639681045)
                ·
                  refine ⟨133326335954635858110049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2844295167032231639681045 133326335954635858110049)
                  ·
                    rfl

theorem cell23_2336869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 6].length) (baseStart_2336869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336869 prefixEnd_2336869 := by exact prefixLift 2336869
  have htrace : WordTrace (prefixWord ++ tailWord_2336869) baseStart_2336869 baseEnd_2336869 := by
    simpa [prefixWord, tailWord_2336869, baseEnd_2336869] using wordTrace_append hprefix tailTrace_2336869
  have hstable : (prefixWord ++ tailWord_2336869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336869).length < 2 ^ (prefixWord ++ tailWord_2336869).sum := by decide
  have hdescent : baseEnd_2336869 < baseStart_2336869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336912 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 3, 6]
def baseStart_2336912 : Nat := 118140960795 + 2336912 * 2 ^ 59
def prefixEnd_2336912 : Nat := 4983230072969 + 3 ^ 40 * 2336912 * 2
def baseEnd_2336912 : Nat := 399986367753288684917581

theorem tailTrace_2336912 : CollatzResearch.WordTrace tailWord_2336912 prefixEnd_2336912 399986367753288684917581 := by
  unfold tailWord_2336912
  simp only [CollatzResearch.WordTrace]
  refine ⟨42617091454887205819858495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56822788606516274426477993 42617091454887205819858495)
  ·
    refine ⟨63925637182330808729787743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42617091454887205819858495 63925637182330808729787743)
    ·
      refine ⟨95888455773496213094681615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63925637182330808729787743 95888455773496213094681615)
      ·
        refine ⟨143832683660244319642022423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95888455773496213094681615 143832683660244319642022423)
        ·
          refine ⟨215749025490366479463033635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143832683660244319642022423 215749025490366479463033635)
          ·
            refine ⟨323623538235549719194550453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215749025490366479463033635 323623538235549719194550453)
            ·
              refine ⟨30339706709582786174489105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 323623538235549719194550453 30339706709582786174489105)
              ·
                refine ⟨22754780032187089630866829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30339706709582786174489105 22754780032187089630866829)
                ·
                  refine ⟨8533042512070158611575061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22754780032187089630866829 8533042512070158611575061)
                  ·
                    refine ⟨399986367753288684917581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8533042512070158611575061 399986367753288684917581)
                    ·
                      rfl

theorem cell23_2336912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 3, 6].length) (baseStart_2336912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336912 prefixEnd_2336912 := by exact prefixLift 2336912
  have htrace : WordTrace (prefixWord ++ tailWord_2336912) baseStart_2336912 baseEnd_2336912 := by
    simpa [prefixWord, tailWord_2336912, baseEnd_2336912] using wordTrace_append hprefix tailTrace_2336912
  have hstable : (prefixWord ++ tailWord_2336912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336912).length < 2 ^ (prefixWord ++ tailWord_2336912).sum := by decide
  have hdescent : baseEnd_2336912 < baseStart_2336912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336929 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 1, 6]
def baseStart_2336929 : Nat := 118140960795 + 2336929 * 2 ^ 59
def prefixEnd_2336929 : Nat := 4983230072969 + 3 ^ 40 * 2336929 * 2
def baseEnd_2336929 : Nat := 399989277476997496080055

theorem tailTrace_2336929 : CollatzResearch.WordTrace tailWord_2336929 prefixEnd_2336929 399989277476997496080055 := by
  unfold tailWord_2336929
  simp only [CollatzResearch.WordTrace]
  refine ⟨85234802950712823543085841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56823201967141882362057227 85234802950712823543085841)
  ·
    refine ⟨63926102213034617657314381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85234802950712823543085841 63926102213034617657314381)
    ·
      refine ⟨23972288329887981621492893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63926102213034617657314381 23972288329887981621492893)
      ·
        refine ⟨8989608123707993108059835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23972288329887981621492893 8989608123707993108059835)
        ·
          refine ⟨13484412185561989662089753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8989608123707993108059835 13484412185561989662089753)
          ·
            refine ⟨10113309139171492246567315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13484412185561989662089753 10113309139171492246567315)
            ·
              refine ⟨15169963708757238369850973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10113309139171492246567315 15169963708757238369850973)
              ·
                refine ⟨5688736390783964388694115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15169963708757238369850973 5688736390783964388694115)
                ·
                  refine ⟨8533104586175946583041173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5688736390783964388694115 8533104586175946583041173)
                  ·
                    refine ⟨399989277476997496080055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8533104586175946583041173 399989277476997496080055)
                    ·
                      rfl

theorem cell23_2336929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_2336929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336929 prefixEnd_2336929 := by exact prefixLift 2336929
  have htrace : WordTrace (prefixWord ++ tailWord_2336929) baseStart_2336929 baseEnd_2336929 := by
    simpa [prefixWord, tailWord_2336929, baseEnd_2336929] using wordTrace_append hprefix tailTrace_2336929
  have hstable : (prefixWord ++ tailWord_2336929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336929).length < 2 ^ (prefixWord ++ tailWord_2336929).sum := by decide
  have hdescent : baseEnd_2336929 < baseStart_2336929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336970 : List Nat := [3, 1, 2, 1, 3, 1, 1, 6, 1, 2, 2]
def baseStart_2336970 : Nat := 118140960795 + 2336970 * 2 ^ 59
def prefixEnd_2336970 : Nat := 4983230072969 + 3 ^ 40 * 2336970 * 2
def baseEnd_2336970 : Nat := 1199988885137826827827477

theorem tailTrace_2336970 : CollatzResearch.WordTrace tailWord_2336970 prefixEnd_2336970 1199988885137826827827477 := by
  unfold tailWord_2336970
  simp only [CollatzResearch.WordTrace]
  refine ⟨21309074585891071886332091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56824198895709525030218909 21309074585891071886332091)
  ·
    refine ⟨31963611878836607829498137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21309074585891071886332091 31963611878836607829498137)
    ·
      refine ⟨23972708909127455872123603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31963611878836607829498137 23972708909127455872123603)
      ·
        refine ⟨35959063363691183808185405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23972708909127455872123603 35959063363691183808185405)
        ·
          refine ⟨13484648761384193928069527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35959063363691183808185405 13484648761384193928069527)
          ·
            refine ⟨20226973142076290892104291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13484648761384193928069527 20226973142076290892104291)
            ·
              refine ⟨30340459713114436338156437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20226973142076290892104291 30340459713114436338156437)
              ·
                refine ⟨1422209049052239203351083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30340459713114436338156437 1422209049052239203351083)
                ·
                  refine ⟨2133313573578358805026625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1422209049052239203351083 2133313573578358805026625)
                  ·
                    refine ⟨1599985180183769103769969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2133313573578358805026625 1599985180183769103769969)
                    ·
                      refine ⟨1199988885137826827827477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1599985180183769103769969 1199988885137826827827477)
                      ·
                        rfl

theorem cell23_2336970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_2336970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336970 prefixEnd_2336970 := by exact prefixLift 2336970
  have htrace : WordTrace (prefixWord ++ tailWord_2336970) baseStart_2336970 baseEnd_2336970 := by
    simpa [prefixWord, tailWord_2336970, baseEnd_2336970] using wordTrace_append hprefix tailTrace_2336970
  have hstable : (prefixWord ++ tailWord_2336970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336970).length < 2 ^ (prefixWord ++ tailWord_2336970).sum := by decide
  have hdescent : baseEnd_2336970 < baseStart_2336970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2336986 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3]
def baseStart_2336986 : Nat := 118140960795 + 2336986 * 2 ^ 59
def prefixEnd_2336986 : Nat := 4983230072969 + 3 ^ 40 * 2336986 * 2
def baseEnd_2336986 : Nat := 1199997100828298765227403

theorem tailTrace_2336986 : CollatzResearch.WordTrace tailWord_2336986 prefixEnd_2336986 1199997100828298765227403 := by
  unfold tailWord_2336986
  simp only [CollatzResearch.WordTrace]
  refine ⟨21309220477876580569477703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56824587941004214851940541 21309220477876580569477703)
  ·
    refine ⟨31963830716814870854216555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21309220477876580569477703 31963830716814870854216555)
    ·
      refine ⟨47945746075222306281324833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31963830716814870854216555 47945746075222306281324833)
      ·
        refine ⟨35959309556416729710993625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47945746075222306281324833 35959309556416729710993625)
        ·
          refine ⟨26969482167312547283245219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35959309556416729710993625 26969482167312547283245219)
          ·
            refine ⟨40454223250968820924867829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26969482167312547283245219 40454223250968820924867829)
            ·
              refine ⟨3792583429778326961706359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40454223250968820924867829 3792583429778326961706359)
              ·
                refine ⟨5688875144667490442559539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3792583429778326961706359 5688875144667490442559539)
                ·
                  refine ⟨8533312717001235663839309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5688875144667490442559539 8533312717001235663839309)
                  ·
                    refine ⟨3199992268875463373939741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8533312717001235663839309 3199992268875463373939741)
                    ·
                      refine ⟨1199997100828298765227403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3199992268875463373939741 1199997100828298765227403)
                      ·
                        rfl

theorem cell23_2336986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_2336986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2336986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2336986 prefixEnd_2336986 := by exact prefixLift 2336986
  have htrace : WordTrace (prefixWord ++ tailWord_2336986) baseStart_2336986 baseEnd_2336986 := by
    simpa [prefixWord, tailWord_2336986, baseEnd_2336986] using wordTrace_append hprefix tailTrace_2336986
  have hstable : (prefixWord ++ tailWord_2336986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2336986).length < 2 ^ (prefixWord ++ tailWord_2336986).sum := by decide
  have hdescent : baseEnd_2336986 < baseStart_2336986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2336986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337039 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 4]
def baseStart_2337039 : Nat := 118140960795 + 2337039 * 2 ^ 59
def prefixEnd_2337039 : Nat := 4983230072969 + 3 ^ 40 * 2337039 * 2
def baseEnd_2337039 : Nat := 1200024315302987057864659

theorem tailTrace_2337039 : CollatzResearch.WordTrace tailWord_2337039 prefixEnd_2337039 1200024315302987057864659 := by
  unfold tailWord_2337039
  simp only [CollatzResearch.WordTrace]
  refine ⟨85238814980314312329590171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56825876653542874886393447 85238814980314312329590171)
  ·
    refine ⟨127858222470471468494385257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85238814980314312329590171 127858222470471468494385257)
    ·
      refine ⟨95893666852853601370788943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127858222470471468494385257 95893666852853601370788943)
      ·
        refine ⟨143840500279280402056183415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95893666852853601370788943 143840500279280402056183415)
        ·
          refine ⟨215760750418920603084275123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143840500279280402056183415 215760750418920603084275123)
          ·
            refine ⟨323641125628380904626412685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215760750418920603084275123 323641125628380904626412685)
            ·
              refine ⟨121365422110642839234904757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 323641125628380904626412685 121365422110642839234904757)
              ·
                refine ⟨11378008322872766178272321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121365422110642839234904757 11378008322872766178272321)
                ·
                  refine ⟨8533506242154574633704241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11378008322872766178272321 8533506242154574633704241)
                  ·
                    refine ⟨6400129681615930975278181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8533506242154574633704241 6400129681615930975278181)
                    ·
                      refine ⟨1200024315302987057864659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6400129681615930975278181 1200024315302987057864659)
                      ·
                        rfl

theorem cell23_2337039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_2337039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337039 prefixEnd_2337039 := by exact prefixLift 2337039
  have htrace : WordTrace (prefixWord ++ tailWord_2337039) baseStart_2337039 baseEnd_2337039 := by
    simpa [prefixWord, tailWord_2337039, baseEnd_2337039] using wordTrace_append hprefix tailTrace_2337039
  have hstable : (prefixWord ++ tailWord_2337039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337039).length < 2 ^ (prefixWord ++ tailWord_2337039).sum := by decide
  have hdescent : baseEnd_2337039 < baseStart_2337039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337129 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 1, 3, 6]
def baseStart_2337129 : Nat := 118140960795 + 2337129 * 2 ^ 59
def prefixEnd_2337129 : Nat := 4983230072969 + 3 ^ 40 * 2337129 * 2
def baseEnd_2337129 : Nat := 1200070528561891705739245

theorem tailTrace_2337129 : CollatzResearch.WordTrace tailWord_2337129 prefixEnd_2337129 1200070528561891705739245 := by
  unfold tailWord_2337129
  simp only [CollatzResearch.WordTrace]
  refine ⟨85242097549988257700366441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56828065033325505133577627 85242097549988257700366441)
  ·
    refine ⟨63931573162491193275274831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85242097549988257700366441 63931573162491193275274831)
    ·
      refine ⟨95897359743736789912912247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63931573162491193275274831 95897359743736789912912247)
      ·
        refine ⟨143846039615605184869368371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95897359743736789912912247 143846039615605184869368371)
        ·
          refine ⟨215769059423407777304052557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143846039615605184869368371 215769059423407777304052557)
          ·
            refine ⟨80913397283777916489019709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215769059423407777304052557 80913397283777916489019709)
            ·
              refine ⟨30342523981416718683382391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80913397283777916489019709 30342523981416718683382391)
              ·
                refine ⟨45513785972125078025073587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30342523981416718683382391 45513785972125078025073587)
                ·
                  refine ⟨68270678958187617037610381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45513785972125078025073587 68270678958187617037610381)
                  ·
                    refine ⟨25601504609320356389103893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68270678958187617037610381 25601504609320356389103893)
                    ·
                      refine ⟨1200070528561891705739245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25601504609320356389103893 1200070528561891705739245)
                      ·
                        rfl

theorem cell23_2337129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_2337129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337129 prefixEnd_2337129 := by exact prefixLift 2337129
  have htrace : WordTrace (prefixWord ++ tailWord_2337129) baseStart_2337129 baseEnd_2337129 := by
    simpa [prefixWord, tailWord_2337129, baseEnd_2337129] using wordTrace_append hprefix tailTrace_2337129
  have hstable : (prefixWord ++ tailWord_2337129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337129).length < 2 ^ (prefixWord ++ tailWord_2337129).sum := by decide
  have hdescent : baseEnd_2337129 < baseStart_2337129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337133 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 4, 4, 2]
def baseStart_2337133 : Nat := 118140960795 + 2337133 * 2 ^ 59
def prefixEnd_2337133 : Nat := 4983230072969 + 3 ^ 40 * 2337133 * 2
def baseEnd_2337133 : Nat := 1200072582484509690089227

theorem tailTrace_2337133 : CollatzResearch.WordTrace tailWord_2337133 prefixEnd_2337133 1200072582484509690089227 := by
  unfold tailWord_2337133
  simp only [CollatzResearch.WordTrace]
  refine ⟨85242243441973766383512053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56828162294649177589008035 85242243441973766383512053)
  ·
    refine ⟨7991460322685040598454255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85242243441973766383512053 7991460322685040598454255)
    ·
      refine ⟨11987190484027560897681383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7991460322685040598454255 11987190484027560897681383)
      ·
        refine ⟨17980785726041341346522075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11987190484027560897681383 17980785726041341346522075)
        ·
          refine ⟨26971178589062012019783113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17980785726041341346522075 26971178589062012019783113)
          ·
            refine ⟨20228383941796509014837335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26971178589062012019783113 20228383941796509014837335)
            ·
              refine ⟨30342575912694763522256003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20228383941796509014837335 30342575912694763522256003)
              ·
                refine ⟨45513863869042145283384005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30342575912694763522256003 45513863869042145283384005)
                ·
                  refine ⟨8533849475445402240634501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45513863869042145283384005 8533849475445402240634501)
                  ·
                    refine ⟨1600096776646012920118969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8533849475445402240634501 1600096776646012920118969)
                    ·
                      refine ⟨1200072582484509690089227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1600096776646012920118969 1200072582484509690089227)
                      ·
                        rfl

theorem cell23_2337133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_2337133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337133 prefixEnd_2337133 := by exact prefixLift 2337133
  have htrace : WordTrace (prefixWord ++ tailWord_2337133) baseStart_2337133 baseEnd_2337133 := by
    simpa [prefixWord, tailWord_2337133, baseEnd_2337133] using wordTrace_append hprefix tailTrace_2337133
  have hstable : (prefixWord ++ tailWord_2337133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337133).length < 2 ^ (prefixWord ++ tailWord_2337133).sum := by decide
  have hdescent : baseEnd_2337133 < baseStart_2337133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337139 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 8]
def baseStart_2337139 : Nat := 118140960795 + 2337139 * 2 ^ 59
def prefixEnd_2337139 : Nat := 4983230072969 + 3 ^ 40 * 2337139 * 2
def baseEnd_2337139 : Nat := 133341740374270740734911

theorem tailTrace_2337139 : CollatzResearch.WordTrace tailWord_2337139 prefixEnd_2337139 133341740374270740734911 := by
  unfold tailWord_2337139
  simp only [CollatzResearch.WordTrace]
  refine ⟨85242462279952029408230471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56828308186634686272153647 85242462279952029408230471)
  ·
    refine ⟨127863693419928044112345707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85242462279952029408230471 127863693419928044112345707)
    ·
      refine ⟨191795540129892066168518561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127863693419928044112345707 191795540129892066168518561)
      ·
        refine ⟨143846655097419049626388921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191795540129892066168518561 143846655097419049626388921)
        ·
          refine ⟨107884991323064287219791691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143846655097419049626388921 107884991323064287219791691)
          ·
            refine ⟨161827486984596430829687537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107884991323064287219791691 161827486984596430829687537)
            ·
              refine ⟨121370615238447323122265653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161827486984596430829687537 121370615238447323122265653)
              ·
                refine ⟨11378495178604436542712405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121370615238447323122265653 11378495178604436542712405)
                ·
                  refine ⟨133341740374270740734911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11378495178604436542712405 133341740374270740734911)
                  ·
                    rfl

theorem cell23_2337139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 8].length) (baseStart_2337139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337139 prefixEnd_2337139 := by exact prefixLift 2337139
  have htrace : WordTrace (prefixWord ++ tailWord_2337139) baseStart_2337139 baseEnd_2337139 := by
    simpa [prefixWord, tailWord_2337139, baseEnd_2337139] using wordTrace_append hprefix tailTrace_2337139
  have hstable : (prefixWord ++ tailWord_2337139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337139).length < 2 ^ (prefixWord ++ tailWord_2337139).sum := by decide
  have hdescent : baseEnd_2337139 < baseStart_2337139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337153 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_2337153 : Nat := 118140960795 + 2337153 * 2 ^ 59
def prefixEnd_2337153 : Nat := 4983230072969 + 3 ^ 40 * 2337153 * 2
def baseEnd_2337153 : Nat := 1200082852097599611839135

theorem tailTrace_2337153 : CollatzResearch.WordTrace tailWord_2337153 prefixEnd_2337153 1200082852097599611839135 := by
  unfold tailWord_2337153
  simp only [CollatzResearch.WordTrace]
  refine ⟨85242972901901309799240113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56828648601267539866160075 85242972901901309799240113)
  ·
    refine ⟨63932229676425982349430085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85242972901901309799240113 63932229676425982349430085)
    ·
      refine ⟨11987293064329871690518141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63932229676425982349430085 11987293064329871690518141)
      ·
        refine ⟨4495234899123701883944303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11987293064329871690518141 4495234899123701883944303)
        ·
          refine ⟨6742852348685552825916455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4495234899123701883944303 6742852348685552825916455)
          ·
            refine ⟨10114278523028329238874683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6742852348685552825916455 10114278523028329238874683)
            ·
              refine ⟨15171417784542493858312025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10114278523028329238874683 15171417784542493858312025)
              ·
                refine ⟨11378563338406870393734019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15171417784542493858312025 11378563338406870393734019)
                ·
                  refine ⟨17067845007610305590601029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11378563338406870393734019 17067845007610305590601029)
                  ·
                    refine ⟨3200220938926932298237693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17067845007610305590601029 3200220938926932298237693)
                    ·
                      refine ⟨1200082852097599611839135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3200220938926932298237693 1200082852097599611839135)
                      ·
                        rfl

theorem cell23_2337153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_2337153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337153 prefixEnd_2337153 := by exact prefixLift 2337153
  have htrace : WordTrace (prefixWord ++ tailWord_2337153) baseStart_2337153 baseEnd_2337153 := by
    simpa [prefixWord, tailWord_2337153, baseEnd_2337153] using wordTrace_append hprefix tailTrace_2337153
  have hstable : (prefixWord ++ tailWord_2337153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337153).length < 2 ^ (prefixWord ++ tailWord_2337153).sum := by decide
  have hdescent : baseEnd_2337153 < baseStart_2337153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337216 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 1, 6]
def baseStart_2337216 : Nat := 118140960795 + 2337216 * 2 ^ 59
def prefixEnd_2337216 : Nat := 4983230072969 + 3 ^ 40 * 2337216 * 2
def baseEnd_2337216 : Nat := 400038400459610955117115

theorem tailTrace_2337216 : CollatzResearch.WordTrace tailWord_2337216 prefixEnd_2337216 400038400459610955117115 := by
  unfold tailWord_2337216
  simp only [CollatzResearch.WordTrace]
  refine ⟨42622635350336535779391751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56830180467115381039189001 42622635350336535779391751)
  ·
    refine ⟨63933953025504803669087627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42622635350336535779391751 63933953025504803669087627)
    ·
      refine ⟨95900929538257205503631441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63933953025504803669087627 95900929538257205503631441)
      ·
        refine ⟨71925697153692904127723581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95900929538257205503631441 71925697153692904127723581)
        ·
          refine ⟨26972136432634839047896343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71925697153692904127723581 26972136432634839047896343)
          ·
            refine ⟨40458204648952258571844515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26972136432634839047896343 40458204648952258571844515)
            ·
              refine ⟨60687306973428387857766773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40458204648952258571844515 60687306973428387857766773)
              ·
                refine ⟨5689435028758911361665635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60687306973428387857766773 5689435028758911361665635)
                ·
                  refine ⟨8534152543138367042498453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5689435028758911361665635 8534152543138367042498453)
                  ·
                    refine ⟨400038400459610955117115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8534152543138367042498453 400038400459610955117115)
                    ·
                      rfl

theorem cell23_2337216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 1, 6].length) (baseStart_2337216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337216 prefixEnd_2337216 := by exact prefixLift 2337216
  have htrace : WordTrace (prefixWord ++ tailWord_2337216) baseStart_2337216 baseEnd_2337216 := by
    simpa [prefixWord, tailWord_2337216, baseEnd_2337216] using wordTrace_append hprefix tailTrace_2337216
  have hstable : (prefixWord ++ tailWord_2337216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337216).length < 2 ^ (prefixWord ++ tailWord_2337216).sum := by decide
  have hdescent : baseEnd_2337216 < baseStart_2337216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337220 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 3, 5]
def baseStart_2337220 : Nat := 118140960795 + 2337220 * 2 ^ 59
def prefixEnd_2337220 : Nat := 4983230072969 + 3 ^ 40 * 2337220 * 2
def baseEnd_2337220 : Nat := 400039085100483616567109

theorem tailTrace_2337220 : CollatzResearch.WordTrace tailWord_2337220 prefixEnd_2337220 400039085100483616567109 := by
  unfold tailWord_2337220
  simp only [CollatzResearch.WordTrace]
  refine ⟨42622708296329290120964557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56830277728439053494619409 42622708296329290120964557)
  ·
    refine ⟨15983515611123483795361709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42622708296329290120964557 15983515611123483795361709)
    ·
      refine ⟨5993818354171306423260641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15983515611123483795361709 5993818354171306423260641)
      ·
        refine ⟨4495363765628479817445481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5993818354171306423260641 4495363765628479817445481)
        ·
          refine ⟨3371522824221359863084111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4495363765628479817445481 3371522824221359863084111)
          ·
            refine ⟨5057284236332039794626167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3371522824221359863084111 5057284236332039794626167)
            ·
              refine ⟨7585926354498059691939251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5057284236332039794626167 7585926354498059691939251)
              ·
                refine ⟨11378889531747089537908877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7585926354498059691939251 11378889531747089537908877)
                ·
                  refine ⟨4267083574405158576715829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11378889531747089537908877 4267083574405158576715829)
                  ·
                    refine ⟨400039085100483616567109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4267083574405158576715829 400039085100483616567109)
                    ·
                      rfl

theorem cell23_2337220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_2337220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337220 prefixEnd_2337220 := by exact prefixLift 2337220
  have htrace : WordTrace (prefixWord ++ tailWord_2337220) baseStart_2337220 baseEnd_2337220 := by
    simpa [prefixWord, tailWord_2337220, baseEnd_2337220] using wordTrace_append hprefix tailTrace_2337220
  have hstable : (prefixWord ++ tailWord_2337220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337220).length < 2 ^ (prefixWord ++ tailWord_2337220).sum := by decide
  have hdescent : baseEnd_2337220 < baseStart_2337220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337223 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_2337223 : Nat := 118140960795 + 2337223 * 2 ^ 59
def prefixEnd_2337223 : Nat := 4983230072969 + 3 ^ 40 * 2337223 * 2
def baseEnd_2337223 : Nat := 1200118795743414337963813

theorem tailTrace_2337223 : CollatzResearch.WordTrace tailWord_2337223 prefixEnd_2337223 1200118795743414337963813 := by
  unfold tailWord_2337223
  simp only [CollatzResearch.WordTrace]
  refine ⟨85245526011647711754288323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56830350674431807836192215 85245526011647711754288323)
  ·
    refine ⟨127868289017471567631432485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85245526011647711754288323 127868289017471567631432485)
    ·
      refine ⟨23975304190775918930893591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127868289017471567631432485 23975304190775918930893591)
      ·
        refine ⟨35962956286163878396340387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23975304190775918930893591 35962956286163878396340387)
        ·
          refine ⟨53944434429245817594510581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35962956286163878396340387 53944434429245817594510581)
          ·
            refine ⟨5057290727741795399485367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53944434429245817594510581 5057290727741795399485367)
            ·
              refine ⟨7585936091612693099228051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5057290727741795399485367 7585936091612693099228051)
              ·
                refine ⟨11378904137419039648842077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7585936091612693099228051 11378904137419039648842077)
                ·
                  refine ⟨4267089051532139868315779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11378904137419039648842077 4267089051532139868315779)
                  ·
                    refine ⟨6400633577298209802473669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4267089051532139868315779 6400633577298209802473669)
                    ·
                      refine ⟨1200118795743414337963813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6400633577298209802473669 1200118795743414337963813)
                      ·
                        rfl

theorem cell23_2337223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_2337223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337223 prefixEnd_2337223 := by exact prefixLift 2337223
  have htrace : WordTrace (prefixWord ++ tailWord_2337223) baseStart_2337223 baseEnd_2337223 := by
    simpa [prefixWord, tailWord_2337223, baseEnd_2337223] using wordTrace_append hprefix tailTrace_2337223
  have hstable : (prefixWord ++ tailWord_2337223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337223).length < 2 ^ (prefixWord ++ tailWord_2337223).sum := by decide
  have hdescent : baseEnd_2337223 < baseStart_2337223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337251 : List Nat := [1, 1, 1, 6, 3, 2, 2, 2, 1, 1, 3]
def baseStart_2337251 : Nat := 118140960795 + 2337251 * 2 ^ 59
def prefixEnd_2337251 : Nat := 4983230072969 + 3 ^ 40 * 2337251 * 2
def baseEnd_2337251 : Nat := 1200133173201740228413685

theorem tailTrace_2337251 : CollatzResearch.WordTrace tailWord_2337251 prefixEnd_2337251 1200133173201740228413685 := by
  unfold tailWord_2337251
  simp only [CollatzResearch.WordTrace]
  refine ⟨85246547255546272536307607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56831031503697515024205071 85246547255546272536307607)
  ·
    refine ⟨127869820883319408804461411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85246547255546272536307607 127869820883319408804461411)
    ·
      refine ⟨191804731324979113206692117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127869820883319408804461411 191804731324979113206692117)
      ·
        refine ⟨8990846780858395931563693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 191804731324979113206692117 8990846780858395931563693)
        ·
          refine ⟨3371567542821898474336385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8990846780858395931563693 3371567542821898474336385)
          ·
            refine ⟨2528675657116423855752289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3371567542821898474336385 2528675657116423855752289)
            ·
              refine ⟨1896506742837317891814217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2528675657116423855752289 1896506742837317891814217)
              ·
                refine ⟨1422380057127988418860663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1896506742837317891814217 1422380057127988418860663)
                ·
                  refine ⟨2133570085691982628290995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1422380057127988418860663 2133570085691982628290995)
                  ·
                    refine ⟨3200355128537973942436493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2133570085691982628290995 3200355128537973942436493)
                    ·
                      refine ⟨1200133173201740228413685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3200355128537973942436493 1200133173201740228413685)
                      ·
                        rfl

theorem cell23_2337251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_2337251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337251 prefixEnd_2337251 := by exact prefixLift 2337251
  have htrace : WordTrace (prefixWord ++ tailWord_2337251) baseStart_2337251 baseEnd_2337251 := by
    simpa [prefixWord, tailWord_2337251, baseEnd_2337251] using wordTrace_append hprefix tailTrace_2337251
  have hstable : (prefixWord ++ tailWord_2337251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337251).length < 2 ^ (prefixWord ++ tailWord_2337251).sum := by decide
  have hdescent : baseEnd_2337251 < baseStart_2337251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337270 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_2337270 : Nat := 118140960795 + 2337270 * 2 ^ 59
def prefixEnd_2337270 : Nat := 4983230072969 + 3 ^ 40 * 2337270 * 2
def baseEnd_2337270 : Nat := 1200142929334175654076097

theorem tailTrace_2337270 : CollatzResearch.WordTrace tailWord_2337270 prefixEnd_2337270 1200142929334175654076097 := by
  unfold tailWord_2337270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5327952515154839923828079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56831493494984959187499509 5327952515154839923828079)
  ·
    refine ⟨7991928772732259885742119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5327952515154839923828079 7991928772732259885742119)
    ·
      refine ⟨11987893159098389828613179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7991928772732259885742119 11987893159098389828613179)
      ·
        refine ⟨17981839738647584742919769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11987893159098389828613179 17981839738647584742919769)
        ·
          refine ⟨13486379803985688557189827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17981839738647584742919769 13486379803985688557189827)
          ·
            refine ⟨20229569705978532835784741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13486379803985688557189827 20229569705978532835784741)
            ·
              refine ⟨3793044319870974906709639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20229569705978532835784741 3793044319870974906709639)
              ·
                refine ⟨5689566479806462360064459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3793044319870974906709639 5689566479806462360064459)
                ·
                  refine ⟨8534349719709693540096689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5689566479806462360064459 8534349719709693540096689)
                  ·
                    refine ⟨6400762289782270155072517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8534349719709693540096689 6400762289782270155072517)
                    ·
                      refine ⟨1200142929334175654076097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6400762289782270155072517 1200142929334175654076097)
                      ·
                        rfl

theorem cell23_2337270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_2337270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337270 prefixEnd_2337270 := by exact prefixLift 2337270
  have htrace : WordTrace (prefixWord ++ tailWord_2337270) baseStart_2337270 baseEnd_2337270 := by
    simpa [prefixWord, tailWord_2337270, baseEnd_2337270] using wordTrace_append hprefix tailTrace_2337270
  have hstable : (prefixWord ++ tailWord_2337270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337270).length < 2 ^ (prefixWord ++ tailWord_2337270).sum := by decide
  have hdescent : baseEnd_2337270 < baseStart_2337270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337273 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 1, 3, 3]
def baseStart_2337273 : Nat := 118140960795 + 2337273 * 2 ^ 59
def prefixEnd_2337273 : Nat := 4983230072969 + 3 ^ 40 * 2337273 * 2
def baseEnd_2337273 : Nat := 1200144469776139142338583

theorem tailTrace_2337273 : CollatzResearch.WordTrace tailWord_2337273 prefixEnd_2337273 1200144469776139142338583 := by
  unfold tailWord_2337273
  simp only [CollatzResearch.WordTrace]
  refine ⟨85247349661466570293608473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56831566440977713529072315 85247349661466570293608473)
  ·
    refine ⟨63935512246099927720206355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85247349661466570293608473 63935512246099927720206355)
    ·
      refine ⟨95903268369149891580309533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63935512246099927720206355 95903268369149891580309533)
      ·
        refine ⟨35963725638431209342616075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95903268369149891580309533 35963725638431209342616075)
        ·
          refine ⟨53945588457646814013924113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35963725638431209342616075 53945588457646814013924113)
          ·
            refine ⟨40459191343235110510443085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53945588457646814013924113 40459191343235110510443085)
            ·
              refine ⟨15172196753713166441416157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40459191343235110510443085 15172196753713166441416157)
              ·
                refine ⟨5689573782642437415531059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15172196753713166441416157 5689573782642437415531059)
                ·
                  refine ⟨8534360673963656123296589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5689573782642437415531059 8534360673963656123296589)
                  ·
                    refine ⟨3200385252736371046236221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8534360673963656123296589 3200385252736371046236221)
                    ·
                      refine ⟨1200144469776139142338583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3200385252736371046236221 1200144469776139142338583)
                      ·
                        rfl

theorem cell23_2337273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_2337273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337273 prefixEnd_2337273 := by exact prefixLift 2337273
  have htrace : WordTrace (prefixWord ++ tailWord_2337273) baseStart_2337273 baseEnd_2337273 := by
    simpa [prefixWord, tailWord_2337273, baseEnd_2337273] using wordTrace_append hprefix tailTrace_2337273
  have hstable : (prefixWord ++ tailWord_2337273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337273).length < 2 ^ (prefixWord ++ tailWord_2337273).sum := by decide
  have hdescent : baseEnd_2337273 < baseStart_2337273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337276 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 4, 7]
def baseStart_2337276 : Nat := 118140960795 + 2337276 * 2 ^ 59
def prefixEnd_2337276 : Nat := 4983230072969 + 3 ^ 40 * 2337276 * 2
def baseEnd_2337276 : Nat := 400048670072700876867023

theorem tailTrace_2337276 : CollatzResearch.WordTrace tailWord_2337276 prefixEnd_2337276 400048670072700876867023 := by
  unfold tailWord_2337276
  simp only [CollatzResearch.WordTrace]
  refine ⟨42623729540227850902983841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56831639386970467870645121 42623729540227850902983841)
  ·
    refine ⟨31967797155170888177237881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42623729540227850902983841 31967797155170888177237881)
    ·
      refine ⟨23975847866378166132928411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31967797155170888177237881 23975847866378166132928411)
      ·
        refine ⟨35963771799567249199392617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23975847866378166132928411 35963771799567249199392617)
        ·
          refine ⟨26972828849675436899544463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35963771799567249199392617 26972828849675436899544463)
          ·
            refine ⟨40459243274513155349316695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26972828849675436899544463 40459243274513155349316695)
            ·
              refine ⟨60688864911769733023975043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40459243274513155349316695 60688864911769733023975043)
              ·
                refine ⟨91033297367654599535962565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60688864911769733023975043 91033297367654599535962565)
                ·
                  refine ⟨17068743256435237412992981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91033297367654599535962565 17068743256435237412992981)
                  ·
                    refine ⟨400048670072700876867023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17068743256435237412992981 400048670072700876867023)
                    ·
                      rfl

theorem cell23_2337276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_2337276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337276 prefixEnd_2337276 := by exact prefixLift 2337276
  have htrace : WordTrace (prefixWord ++ tailWord_2337276) baseStart_2337276 baseEnd_2337276 := by
    simpa [prefixWord, tailWord_2337276, baseEnd_2337276] using wordTrace_append hprefix tailTrace_2337276
  have hstable : (prefixWord ++ tailWord_2337276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337276).length < 2 ^ (prefixWord ++ tailWord_2337276).sum := by decide
  have hdescent : baseEnd_2337276 < baseStart_2337276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337290 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 4, 1, 3]
def baseStart_2337290 : Nat := 118140960795 + 2337290 * 2 ^ 59
def prefixEnd_2337290 : Nat := 4983230072969 + 3 ^ 40 * 2337290 * 2
def baseEnd_2337290 : Nat := 1200153198947265575826005

theorem tailTrace_2337290 : CollatzResearch.WordTrace tailWord_2337290 prefixEnd_2337290 1200153198947265575826005 := by
  unfold tailWord_2337290
  simp only [CollatzResearch.WordTrace]
  refine ⟨21311992425601245549244331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56831979801603321464651549 21311992425601245549244331)
  ·
    refine ⟨31967988638401868323866497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21311992425601245549244331 31967988638401868323866497)
    ·
      refine ⟨23975991478801401242899873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31967988638401868323866497 23975991478801401242899873)
      ·
        refine ⟨17981993609101050932174905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23975991478801401242899873 17981993609101050932174905)
        ·
          refine ⟨13486495206825788199131179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17981993609101050932174905 13486495206825788199131179)
          ·
            refine ⟨20229742810238682298696769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13486495206825788199131179 20229742810238682298696769)
            ·
              refine ⟨15172307107679011724022577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20229742810238682298696769 15172307107679011724022577)
              ·
                refine ⟨11379230330759258793016933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15172307107679011724022577 11379230330759258793016933)
                ·
                  refine ⟨2133605687017361023690675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11379230330759258793016933 2133605687017361023690675)
                  ·
                    refine ⟨3200408530526041535536013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2133605687017361023690675 3200408530526041535536013)
                    ·
                      refine ⟨1200153198947265575826005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3200408530526041535536013 1200153198947265575826005)
                      ·
                        rfl

theorem cell23_2337290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_2337290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337290 prefixEnd_2337290 := by exact prefixLift 2337290
  have htrace : WordTrace (prefixWord ++ tailWord_2337290) baseStart_2337290 baseEnd_2337290 := by
    simpa [prefixWord, tailWord_2337290, baseEnd_2337290] using wordTrace_append hprefix tailTrace_2337290
  have hstable : (prefixWord ++ tailWord_2337290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337290).length < 2 ^ (prefixWord ++ tailWord_2337290).sum := by decide
  have hdescent : baseEnd_2337290 < baseStart_2337290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337294 : List Nat := [4, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3]
def baseStart_2337294 : Nat := 118140960795 + 2337294 * 2 ^ 59
def prefixEnd_2337294 : Nat := 4983230072969 + 3 ^ 40 * 2337294 * 2
def baseEnd_2337294 : Nat := 1200155252869883560175987

theorem tailTrace_2337294 : CollatzResearch.WordTrace tailWord_2337294 prefixEnd_2337294 1200155252869883560175987 := by
  unfold tailWord_2337294
  simp only [CollatzResearch.WordTrace]
  refine ⟨10656014449298811360015367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56832077062926993920081957 10656014449298811360015367)
  ·
    refine ⟨15984021673948217040023051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10656014449298811360015367 15984021673948217040023051)
    ·
      refine ⟨23976032510922325560034577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15984021673948217040023051 23976032510922325560034577)
      ·
        refine ⟨17982024383191744170025933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23976032510922325560034577 17982024383191744170025933)
        ·
          refine ⟨6743259143696904063759725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17982024383191744170025933 6743259143696904063759725)
          ·
            refine ⟨2528722178886339023909897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6743259143696904063759725 2528722178886339023909897)
            ·
              refine ⟨1896541634164754267932423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2528722178886339023909897 1896541634164754267932423)
              ·
                refine ⟨2844812451247131401898635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896541634164754267932423 2844812451247131401898635)
                ·
                  refine ⟨4267218676870697102847953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844812451247131401898635 4267218676870697102847953)
                  ·
                    refine ⟨3200414007653022827135965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4267218676870697102847953 3200414007653022827135965)
                    ·
                      refine ⟨1200155252869883560175987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3200414007653022827135965 1200155252869883560175987)
                      ·
                        rfl

theorem cell23_2337294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_2337294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337294 prefixEnd_2337294 := by exact prefixLift 2337294
  have htrace : WordTrace (prefixWord ++ tailWord_2337294) baseStart_2337294 baseEnd_2337294 := by
    simpa [prefixWord, tailWord_2337294, baseEnd_2337294] using wordTrace_append hprefix tailTrace_2337294
  have hstable : (prefixWord ++ tailWord_2337294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337294).length < 2 ^ (prefixWord ++ tailWord_2337294).sum := by decide
  have hdescent : baseEnd_2337294 < baseStart_2337294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337333 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_2337333 : Nat := 118140960795 + 2337333 * 2 ^ 59
def prefixEnd_2337333 : Nat := 4983230072969 + 3 ^ 40 * 2337333 * 2
def baseEnd_2337333 : Nat := 1200175278615408907588307

theorem tailTrace_2337333 : CollatzResearch.WordTrace tailWord_2337333 prefixEnd_2337333 1200175278615408907588307 := by
  unfold tailWord_2337333
  simp only [CollatzResearch.WordTrace]
  refine ⟨85249538041249200540792653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56833025360832800360528435 85249538041249200540792653)
  ·
    refine ⟨31968576765468450202797245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85249538041249200540792653 31968576765468450202797245)
    ·
      refine ⟨11988216287050668826048967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31968576765468450202797245 11988216287050668826048967)
      ·
        refine ⟨17982324430576003239073451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11988216287050668826048967 17982324430576003239073451)
        ·
          refine ⟨26973486645864004858610177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17982324430576003239073451 26973486645864004858610177)
          ·
            refine ⟨20230114984398003643957633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26973486645864004858610177 20230114984398003643957633)
            ·
              refine ⟨15172586238298502732968225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20230114984398003643957633 15172586238298502732968225)
              ·
                refine ⟨11379439678723877049726169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15172586238298502732968225 11379439678723877049726169)
                ·
                  refine ⟨8534579759042907787294627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11379439678723877049726169 8534579759042907787294627)
                  ·
                    refine ⟨12801869638564361680941941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8534579759042907787294627 12801869638564361680941941)
                    ·
                      refine ⟨1200175278615408907588307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12801869638564361680941941 1200175278615408907588307)
                      ·
                        rfl

theorem cell23_2337333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_2337333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337333 prefixEnd_2337333 := by exact prefixLift 2337333
  have htrace : WordTrace (prefixWord ++ tailWord_2337333) baseStart_2337333 baseEnd_2337333 := by
    simpa [prefixWord, tailWord_2337333, baseEnd_2337333] using wordTrace_append hprefix tailTrace_2337333
  have hstable : (prefixWord ++ tailWord_2337333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337333).length < 2 ^ (prefixWord ++ tailWord_2337333).sum := by decide
  have hdescent : baseEnd_2337333 < baseStart_2337333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337334 : List Nat := [5, 1, 2, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_2337334 : Nat := 118140960795 + 2337334 * 2 ^ 59
def prefixEnd_2337334 : Nat := 4983230072969 + 3 ^ 40 * 2337334 * 2
def baseEnd_2337334 : Nat := 1200175792096063403675803

theorem tailTrace_2337334 : CollatzResearch.WordTrace tailWord_2337334 prefixEnd_2337334 1200175792096063403675803 := by
  unfold tailWord_2337334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5328098407140348606973691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56833049676163718474386037 5328098407140348606973691)
  ·
    refine ⟨7992147610710522910460537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5328098407140348606973691 7992147610710522910460537)
    ·
      refine ⟨5994110708032892182845403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7992147610710522910460537 5994110708032892182845403)
      ·
        refine ⟨8991166062049338274268105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5994110708032892182845403 8991166062049338274268105)
        ·
          refine ⟨6743374546537003705701079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8991166062049338274268105 6743374546537003705701079)
          ·
            refine ⟨10115061819805505558551619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6743374546537003705701079 10115061819805505558551619)
            ·
              refine ⟨15172592729708258337827429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10115061819805505558551619 15172592729708258337827429)
              ·
                refine ⟨2844861136820298438342643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15172592729708258337827429 2844861136820298438342643)
                ·
                  refine ⟨4267291705230447657513965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844861136820298438342643 4267291705230447657513965)
                  ·
                    refine ⟨1600234389461417871567737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4267291705230447657513965 1600234389461417871567737)
                    ·
                      refine ⟨1200175792096063403675803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1600234389461417871567737 1200175792096063403675803)
                      ·
                        rfl

theorem cell23_2337334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_2337334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337334 prefixEnd_2337334 := by exact prefixLift 2337334
  have htrace : WordTrace (prefixWord ++ tailWord_2337334) baseStart_2337334 baseEnd_2337334 := by
    simpa [prefixWord, tailWord_2337334, baseEnd_2337334] using wordTrace_append hprefix tailTrace_2337334
  have hstable : (prefixWord ++ tailWord_2337334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337334).length < 2 ^ (prefixWord ++ tailWord_2337334).sum := by decide
  have hdescent : baseEnd_2337334 < baseStart_2337334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337383 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 6, 5]
def baseStart_2337383 : Nat := 118140960795 + 2337383 * 2 ^ 59
def prefixEnd_2337383 : Nat := 4983230072969 + 3 ^ 40 * 2337383 * 2
def baseEnd_2337383 : Nat := 400066984216044570654359

theorem tailTrace_2337383 : CollatzResearch.WordTrace tailWord_2337383 prefixEnd_2337383 400066984216044570654359 := by
  unfold tailWord_2337383
  simp only [CollatzResearch.WordTrace]
  refine ⟨85251361691068059080112803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56834241127378706053408535 85251361691068059080112803)
  ·
    refine ⟨127877042536602088620169205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85251361691068059080112803 127877042536602088620169205)
    ·
      refine ⟨11988472737806445808140863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127877042536602088620169205 11988472737806445808140863)
      ·
        refine ⟨17982709106709668712211295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11988472737806445808140863 17982709106709668712211295)
        ·
          refine ⟨26974063660064503068316943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17982709106709668712211295 26974063660064503068316943)
          ·
            refine ⟨40461095490096754602475415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26974063660064503068316943 40461095490096754602475415)
            ·
              refine ⟨60691643235145131903713123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40461095490096754602475415 60691643235145131903713123)
              ·
                refine ⟨91037464852717697855569685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60691643235145131903713123 91037464852717697855569685)
                ·
                  refine ⟨4267381164971142086979829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91037464852717697855569685 4267381164971142086979829)
                  ·
                    refine ⟨400066984216044570654359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4267381164971142086979829 400066984216044570654359)
                    ·
                      rfl

theorem cell23_2337383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_2337383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337383 prefixEnd_2337383 := by exact prefixLift 2337383
  have htrace : WordTrace (prefixWord ++ tailWord_2337383) baseStart_2337383 baseEnd_2337383 := by
    simpa [prefixWord, tailWord_2337383, baseEnd_2337383] using wordTrace_append hprefix tailTrace_2337383
  have hstable : (prefixWord ++ tailWord_2337383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337383).length < 2 ^ (prefixWord ++ tailWord_2337383).sum := by decide
  have hdescent : baseEnd_2337383 < baseStart_2337383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337454 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_2337454 : Nat := 118140960795 + 2337454 * 2 ^ 59
def prefixEnd_2337454 : Nat := 4983230072969 + 3 ^ 40 * 2337454 * 2
def baseEnd_2337454 : Nat := 1200237409774602934175251

theorem tailTrace_2337454 : CollatzResearch.WordTrace tailWord_2337454 prefixEnd_2337454 1200237409774602934175251 := by
  unfold tailWord_2337454
  simp only [CollatzResearch.WordTrace]
  refine ⟨10656743909226354775743427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56835967515873892137298277 10656743909226354775743427)
  ·
    refine ⟨15985115863839532163615141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10656743909226354775743427 15985115863839532163615141)
    ·
      refine ⟨2997209224469912280677839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15985115863839532163615141 2997209224469912280677839)
      ·
        refine ⟨4495813836704868421016759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2997209224469912280677839 4495813836704868421016759)
        ·
          refine ⟨6743720755057302631525139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4495813836704868421016759 6743720755057302631525139)
          ·
            refine ⟨10115581132585953947287709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6743720755057302631525139 10115581132585953947287709)
            ·
              refine ⟨3793342924719732730232891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10115581132585953947287709 3793342924719732730232891)
              ·
                refine ⟨5690014387079599095349337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3793342924719732730232891 5690014387079599095349337)
                ·
                  refine ⟨4267510790309699321512003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5690014387079599095349337 4267510790309699321512003)
                  ·
                    refine ⟨6401266185464548982268005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4267510790309699321512003 6401266185464548982268005)
                    ·
                      refine ⟨1200237409774602934175251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6401266185464548982268005 1200237409774602934175251)
                      ·
                        rfl

theorem cell23_2337454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_2337454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337454 prefixEnd_2337454 := by exact prefixLift 2337454
  have htrace : WordTrace (prefixWord ++ tailWord_2337454) baseStart_2337454 baseEnd_2337454 := by
    simpa [prefixWord, tailWord_2337454, baseEnd_2337454] using wordTrace_append hprefix tailTrace_2337454
  have hstable : (prefixWord ++ tailWord_2337454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337454).length < 2 ^ (prefixWord ++ tailWord_2337454).sum := by decide
  have hdescent : baseEnd_2337454 < baseStart_2337454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337507 : List Nat := [1, 1, 1, 7, 1, 1, 1, 4, 1, 5]
def baseStart_2337507 : Nat := 118140960795 + 2337507 * 2 ^ 59
def prefixEnd_2337507 : Nat := 4983230072969 + 3 ^ 40 * 2337507 * 2
def baseEnd_2337507 : Nat := 400088208083097075604169

theorem tailTrace_2337507 : CollatzResearch.WordTrace tailWord_2337507 prefixEnd_2337507 400088208083097075604169 := by
  unfold tailWord_2337507
  simp only [CollatzResearch.WordTrace]
  refine ⟨85255884342618828257626775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56837256228412552171751183 85255884342618828257626775)
  ·
    refine ⟨127883826513928242386440163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85255884342618828257626775 127883826513928242386440163)
    ·
      refine ⟨191825739770892363579660245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127883826513928242386440163 191825739770892363579660245)
      ·
        refine ⟨4495915775880289771398287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 191825739770892363579660245 4495915775880289771398287)
        ·
          refine ⟨6743873663820434657097431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4495915775880289771398287 6743873663820434657097431)
          ·
            refine ⟨10115810495730651985646147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6743873663820434657097431 10115810495730651985646147)
            ·
              refine ⟨15173715743595977978469221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10115810495730651985646147 15173715743595977978469221)
              ·
                refine ⟨2845071701924245870962979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15173715743595977978469221 2845071701924245870962979)
                ·
                  refine ⟨4267607552886368806444469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2845071701924245870962979 4267607552886368806444469)
                  ·
                    refine ⟨400088208083097075604169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4267607552886368806444469 400088208083097075604169)
                    ·
                      rfl

theorem cell23_2337507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 5].length) (baseStart_2337507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337507 prefixEnd_2337507 := by exact prefixLift 2337507
  have htrace : WordTrace (prefixWord ++ tailWord_2337507) baseStart_2337507 baseEnd_2337507 := by
    simpa [prefixWord, tailWord_2337507, baseEnd_2337507] using wordTrace_append hprefix tailTrace_2337507
  have hstable : (prefixWord ++ tailWord_2337507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337507).length < 2 ^ (prefixWord ++ tailWord_2337507).sum := by decide
  have hdescent : baseEnd_2337507 < baseStart_2337507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337520 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 6, 4]
def baseStart_2337520 : Nat := 118140960795 + 2337520 * 2 ^ 59
def prefixEnd_2337520 : Nat := 4983230072969 + 3 ^ 40 * 2337520 * 2
def baseEnd_2337520 : Nat := 400090433165933225316649

theorem tailTrace_2337520 : CollatzResearch.WordTrace tailWord_2337520 prefixEnd_2337520 400090433165933225316649 := by
  unfold tailWord_2337520
  simp only [CollatzResearch.WordTrace]
  refine ⟨42628179245785865738925007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56837572327714487651900009 42628179245785865738925007)
  ·
    refine ⟨63942268868678798608387511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42628179245785865738925007 63942268868678798608387511)
    ·
      refine ⟨95913403303018197912581267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63942268868678798608387511 95913403303018197912581267)
      ·
        refine ⟨143870104954527296868871901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95913403303018197912581267 143870104954527296868871901)
        ·
          refine ⟨53951289357947736325826963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143870104954527296868871901 53951289357947736325826963)
          ·
            refine ⟨80926934036921604488740445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53951289357947736325826963 80926934036921604488740445)
            ·
              refine ⟨30347600263845601683277667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80926934036921604488740445 30347600263845601683277667)
              ·
                refine ⟨45521400395768402524916501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30347600263845601683277667 45521400395768402524916501)
                ·
                  refine ⟨2133815643551643868355461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45521400395768402524916501 2133815643551643868355461)
                  ·
                    refine ⟨400090433165933225316649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2133815643551643868355461 400090433165933225316649)
                    ·
                      rfl

theorem cell23_2337520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 6, 4].length) (baseStart_2337520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337520 prefixEnd_2337520 := by exact prefixLift 2337520
  have htrace : WordTrace (prefixWord ++ tailWord_2337520) baseStart_2337520 baseEnd_2337520 := by
    simpa [prefixWord, tailWord_2337520, baseEnd_2337520] using wordTrace_append hprefix tailTrace_2337520
  have hstable : (prefixWord ++ tailWord_2337520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337520).length < 2 ^ (prefixWord ++ tailWord_2337520).sum := by decide
  have hdescent : baseEnd_2337520 < baseStart_2337520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337530 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5]
def baseStart_2337530 : Nat := 118140960795 + 2337530 * 2 ^ 59
def prefixEnd_2337530 : Nat := 4983230072969 + 3 ^ 40 * 2337530 * 2
def baseEnd_2337530 : Nat := 1200276434304344636824901

theorem tailTrace_2337530 : CollatzResearch.WordTrace tailWord_2337530 prefixEnd_2337530 1200276434304344636824901 := by
  unfold tailWord_2337530
  simp only [CollatzResearch.WordTrace]
  refine ⟨21314180805383875796428511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56837815481023668790476029 21314180805383875796428511)
  ·
    refine ⟨31971271208075813694642767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21314180805383875796428511 31971271208075813694642767)
    ·
      refine ⟨47956906812113720541964151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31971271208075813694642767 47956906812113720541964151)
      ·
        refine ⟨71935360218170580812946227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47956906812113720541964151 71935360218170580812946227)
        ·
          refine ⟨107903040327255871219419341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71935360218170580812946227 107903040327255871219419341)
          ·
            refine ⟨40463640122720951707282253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107903040327255871219419341 40463640122720951707282253)
            ·
              refine ⟨15173865046020356890230845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40463640122720951707282253 15173865046020356890230845)
              ·
                refine ⟨5690199392257633833836567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15173865046020356890230845 5690199392257633833836567)
                ·
                  refine ⟨8535299088386450750754851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5690199392257633833836567 8535299088386450750754851)
                  ·
                    refine ⟨12802948632579676126132277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8535299088386450750754851 12802948632579676126132277)
                    ·
                      refine ⟨1200276434304344636824901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12802948632579676126132277 1200276434304344636824901)
                      ·
                        rfl

theorem cell23_2337530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_2337530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337530 prefixEnd_2337530 := by exact prefixLift 2337530
  have htrace : WordTrace (prefixWord ++ tailWord_2337530) baseStart_2337530 baseEnd_2337530 := by
    simpa [prefixWord, tailWord_2337530, baseEnd_2337530] using wordTrace_append hprefix tailTrace_2337530
  have hstable : (prefixWord ++ tailWord_2337530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337530).length < 2 ^ (prefixWord ++ tailWord_2337530).sum := by decide
  have hdescent : baseEnd_2337530 < baseStart_2337530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337537 : List Nat := [1, 2, 4, 1, 1, 1, 1, 6, 2, 4]
def baseStart_2337537 : Nat := 118140960795 + 2337537 * 2 ^ 59
def prefixEnd_2337537 : Nat := 4983230072969 + 3 ^ 40 * 2337537 * 2
def baseEnd_2337537 : Nat := 400093342889642036479123

theorem tailTrace_2337537 : CollatzResearch.WordTrace tailWord_2337537 prefixEnd_2337537 400093342889642036479123 := by
  unfold tailWord_2337537
  simp only [CollatzResearch.WordTrace]
  refine ⟨85256978532510143381218865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56837985688340095587479243 85256978532510143381218865)
  ·
    refine ⟨63942733899382607535914149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85256978532510143381218865 63942733899382607535914149)
    ·
      refine ⟨11989262606134238912983903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63942733899382607535914149 11989262606134238912983903)
      ·
        refine ⟨17983893909201358369475855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11989262606134238912983903 17983893909201358369475855)
        ·
          refine ⟨26975840863802037554213783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17983893909201358369475855 26975840863802037554213783)
          ·
            refine ⟨40463761295703056331320675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26975840863802037554213783 40463761295703056331320675)
            ·
              refine ⟨60695641943554584496981013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40463761295703056331320675 60695641943554584496981013)
              ·
                refine ⟨2845108216104121148295985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60695641943554584496981013 2845108216104121148295985)
                ·
                  refine ⟨2133831162078090861221989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2845108216104121148295985 2133831162078090861221989)
                  ·
                    refine ⟨400093342889642036479123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2133831162078090861221989 400093342889642036479123)
                    ·
                      rfl

theorem cell23_2337537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_2337537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337537 prefixEnd_2337537 := by exact prefixLift 2337537
  have htrace : WordTrace (prefixWord ++ tailWord_2337537) baseStart_2337537 baseEnd_2337537 := by
    simpa [prefixWord, tailWord_2337537, baseEnd_2337537] using wordTrace_append hprefix tailTrace_2337537
  have hstable : (prefixWord ++ tailWord_2337537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337537).length < 2 ^ (prefixWord ++ tailWord_2337537).sum := by decide
  have hdescent : baseEnd_2337537 < baseStart_2337537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337540 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_2337540 : Nat := 118140960795 + 2337540 * 2 ^ 59
def prefixEnd_2337540 : Nat := 4983230072969 + 3 ^ 40 * 2337540 * 2
def baseEnd_2337540 : Nat := 1200281569110889597699855

theorem tailTrace_2337540 : CollatzResearch.WordTrace tailWord_2337540 prefixEnd_2337540 1200281569110889597699855 := by
  unfold tailWord_2337540
  simp only [CollatzResearch.WordTrace]
  refine ⟨42628543975749637446789037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56838058634332849929052049 42628543975749637446789037)
  ·
    refine ⟨15985703990906114042545889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42628543975749637446789037 15985703990906114042545889)
    ·
      refine ⟨11989277993179585531909417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15985703990906114042545889 11989277993179585531909417)
      ·
        refine ⟨8991958494884689148932063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11989277993179585531909417 8991958494884689148932063)
        ·
          refine ⟨13487937742327033723398095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8991958494884689148932063 13487937742327033723398095)
          ·
            refine ⟨20231906613490550585097143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13487937742327033723398095 20231906613490550585097143)
            ·
              refine ⟨30347859920235825877645715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20231906613490550585097143 30347859920235825877645715)
              ·
                refine ⟨45521789880353738816468573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30347859920235825877645715 45521789880353738816468573)
                ·
                  refine ⟨17070671205132652056175715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45521789880353738816468573 17070671205132652056175715)
                  ·
                    refine ⟨25606006807698978084263573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17070671205132652056175715 25606006807698978084263573)
                    ·
                      refine ⟨1200281569110889597699855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25606006807698978084263573 1200281569110889597699855)
                      ·
                        rfl

theorem cell23_2337540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_2337540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337540 prefixEnd_2337540 := by exact prefixLift 2337540
  have htrace : WordTrace (prefixWord ++ tailWord_2337540) baseStart_2337540 baseEnd_2337540 := by
    simpa [prefixWord, tailWord_2337540, baseEnd_2337540] using wordTrace_append hprefix tailTrace_2337540
  have hstable : (prefixWord ++ tailWord_2337540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337540).length < 2 ^ (prefixWord ++ tailWord_2337540).sum := by decide
  have hdescent : baseEnd_2337540 < baseStart_2337540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337564 : List Nat := [2, 2, 3, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_2337564 : Nat := 118140960795 + 2337564 * 2 ^ 59
def prefixEnd_2337564 : Nat := 4983230072969 + 3 ^ 40 * 2337564 * 2
def baseEnd_2337564 : Nat := 1200293892646597503799745

theorem tailTrace_2337564 : CollatzResearch.WordTrace tailWord_2337564 prefixEnd_2337564 1200293892646597503799745 := by
  unfold tailWord_2337564
  simp only [CollatzResearch.WordTrace]
  refine ⟨42628981651706163496225873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56838642202274884661634497 42628981651706163496225873)
  ·
    refine ⟨31971736238779622622169405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42628981651706163496225873 31971736238779622622169405)
    ·
      refine ⟨11989401089542358483313527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31971736238779622622169405 11989401089542358483313527)
      ·
        refine ⟨17984101634313537724970291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11989401089542358483313527 17984101634313537724970291)
        ·
          refine ⟨26976152451470306587455437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17984101634313537724970291 26976152451470306587455437)
          ·
            refine ⟨10116057169301364970295789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26976152451470306587455437 10116057169301364970295789)
            ·
              refine ⟨3793521438488011863860921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10116057169301364970295789 3793521438488011863860921)
              ·
                refine ⟨2845141078866008897895691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3793521438488011863860921 2845141078866008897895691)
                ·
                  refine ⟨4267711618299013346843537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2845141078866008897895691 4267711618299013346843537)
                  ·
                    refine ⟨3200783713724260010132653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4267711618299013346843537 3200783713724260010132653)
                    ·
                      refine ⟨1200293892646597503799745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3200783713724260010132653 1200293892646597503799745)
                      ·
                        rfl

theorem cell23_2337564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_2337564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337564 prefixEnd_2337564 := by exact prefixLift 2337564
  have htrace : WordTrace (prefixWord ++ tailWord_2337564) baseStart_2337564 baseEnd_2337564 := by
    simpa [prefixWord, tailWord_2337564, baseEnd_2337564] using wordTrace_append hprefix tailTrace_2337564
  have hstable : (prefixWord ++ tailWord_2337564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337564).length < 2 ^ (prefixWord ++ tailWord_2337564).sum := by decide
  have hdescent : baseEnd_2337564 < baseStart_2337564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337578 : List Nat := [3, 1, 4, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_2337578 : Nat := 118140960795 + 2337578 * 2 ^ 59
def prefixEnd_2337578 : Nat := 4983230072969 + 3 ^ 40 * 2337578 * 2
def baseEnd_2337578 : Nat := 1200301081375760449024681

theorem tailTrace_2337578 : CollatzResearch.WordTrace tailWord_2337578 prefixEnd_2337578 1200301081375760449024681 := by
  unfold tailWord_2337578
  simp only [CollatzResearch.WordTrace]
  refine ⟨21314618481340401845865347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56838982616907738255640925 21314618481340401845865347)
  ·
    refine ⟨31971927722010602768798021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21314618481340401845865347 31971927722010602768798021)
    ·
      refine ⟨5994736447876988019149629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31971927722010602768798021 5994736447876988019149629)
      ·
        refine ⟨2248026167953870507181111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5994736447876988019149629 2248026167953870507181111)
        ·
          refine ⟨3372039251930805760771667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2248026167953870507181111 3372039251930805760771667)
          ·
            refine ⟨5058058877896208641157501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3372039251930805760771667 5058058877896208641157501)
            ·
              refine ⟨1896772079211078240434063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5058058877896208641157501 1896772079211078240434063)
              ·
                refine ⟨2845158118816617360651095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896772079211078240434063 2845158118816617360651095)
                ·
                  refine ⟨4267737178224926040976643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2845158118816617360651095 4267737178224926040976643)
                  ·
                    refine ⟨6401605767337389061464965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4267737178224926040976643 6401605767337389061464965)
                    ·
                      refine ⟨1200301081375760449024681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6401605767337389061464965 1200301081375760449024681)
                      ·
                        rfl

theorem cell23_2337578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_2337578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337578 prefixEnd_2337578 := by exact prefixLift 2337578
  have htrace : WordTrace (prefixWord ++ tailWord_2337578) baseStart_2337578 baseEnd_2337578 := by
    simpa [prefixWord, tailWord_2337578, baseEnd_2337578] using wordTrace_append hprefix tailTrace_2337578
  have hstable : (prefixWord ++ tailWord_2337578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337578).length < 2 ^ (prefixWord ++ tailWord_2337578).sum := by decide
  have hdescent : baseEnd_2337578 < baseStart_2337578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337601 : List Nat := [1, 2, 5, 3, 2, 1, 1, 8]
def baseStart_2337601 : Nat := 118140960795 + 2337601 * 2 ^ 59
def prefixEnd_2337601 : Nat := 4983230072969 + 3 ^ 40 * 2337601 * 2
def baseEnd_2337601 : Nat := 44456033015956068853225

theorem tailTrace_2337601 : CollatzResearch.WordTrace tailWord_2337601 prefixEnd_2337601 44456033015956068853225 := by
  unfold tailWord_2337601
  simp only [CollatzResearch.WordTrace]
  refine ⟨85259312804278282311548657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56839541869518854874365771 85259312804278282311548657)
  ·
    refine ⟨63944484603208711733661493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85259312804278282311548657 63944484603208711733661493)
    ·
      refine ⟨5994795431550816725030765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63944484603208711733661493 5994795431550816725030765)
      ·
        refine ⟨2248048286831556271886537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5994795431550816725030765 2248048286831556271886537)
        ·
          refine ⟨1686036215123667203914903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2248048286831556271886537 1686036215123667203914903)
          ·
            refine ⟨2529054322685500805872355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686036215123667203914903 2529054322685500805872355)
            ·
              refine ⟨3793581484028251208808533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529054322685500805872355 3793581484028251208808533)
              ·
                refine ⟨44456033015956068853225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3793581484028251208808533 44456033015956068853225)
                ·
                  rfl

theorem cell23_2337601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 8].length) (baseStart_2337601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337601 prefixEnd_2337601 := by exact prefixLift 2337601
  have htrace : WordTrace (prefixWord ++ tailWord_2337601) baseStart_2337601 baseEnd_2337601 := by
    simpa [prefixWord, tailWord_2337601, baseEnd_2337601] using wordTrace_append hprefix tailTrace_2337601
  have hstable : (prefixWord ++ tailWord_2337601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337601).length < 2 ^ (prefixWord ++ tailWord_2337601).sum := by decide
  have hdescent : baseEnd_2337601 < baseStart_2337601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337651 : List Nat := [1, 1, 1, 2, 2, 1, 7, 2, 2, 2, 2]
def baseStart_2337651 : Nat := 118140960795 + 2337651 * 2 ^ 59
def prefixEnd_2337651 : Nat := 4983230072969 + 3 ^ 40 * 2337651 * 2
def baseEnd_2337651 : Nat := 1200338565463538663411845

theorem tailTrace_2337651 : CollatzResearch.WordTrace tailWord_2337651 prefixEnd_2337651 1200338565463538663411845 := by
  unfold tailWord_2337651
  simp only [CollatzResearch.WordTrace]
  refine ⟨85261136454097140850868807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56840757636064760567245871 85261136454097140850868807)
  ·
    refine ⟨127891704681145711276303211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85261136454097140850868807 127891704681145711276303211)
    ·
      refine ⟨191837557021718566914454817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127891704681145711276303211 191837557021718566914454817)
      ·
        refine ⟨143878167766288925185841113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191837557021718566914454817 143878167766288925185841113)
        ·
          refine ⟨107908625824716693889380835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143878167766288925185841113 107908625824716693889380835)
          ·
            refine ⟨161862938737075040834071253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107908625824716693889380835 161862938737075040834071253)
            ·
              refine ⟨3793662626650196269548545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 161862938737075040834071253 3793662626650196269548545)
              ·
                refine ⟨2845246969987647202161409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3793662626650196269548545 2845246969987647202161409)
                ·
                  refine ⟨2133935227490735401621057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2845246969987647202161409 2133935227490735401621057)
                  ·
                    refine ⟨1600451420618051551215793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2133935227490735401621057 1600451420618051551215793)
                    ·
                      refine ⟨1200338565463538663411845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1600451420618051551215793 1200338565463538663411845)
                      ·
                        rfl

theorem cell23_2337651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 2, 2].length) (baseStart_2337651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337651 prefixEnd_2337651 := by exact prefixLift 2337651
  have htrace : WordTrace (prefixWord ++ tailWord_2337651) baseStart_2337651 baseEnd_2337651 := by
    simpa [prefixWord, tailWord_2337651, baseEnd_2337651] using wordTrace_append hprefix tailTrace_2337651
  have hstable : (prefixWord ++ tailWord_2337651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337651).length < 2 ^ (prefixWord ++ tailWord_2337651).sum := by decide
  have hdescent : baseEnd_2337651 < baseStart_2337651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337657 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 7]
def baseStart_2337657 : Nat := 118140960795 + 2337657 * 2 ^ 59
def prefixEnd_2337657 : Nat := 4983230072969 + 3 ^ 40 * 2337657 * 2
def baseEnd_2337657 : Nat := 133371294038607293326313

theorem tailTrace_2337657 : CollatzResearch.WordTrace tailWord_2337657 prefixEnd_2337657 133371294038607293326313 := by
  unfold tailWord_2337657
  simp only [CollatzResearch.WordTrace]
  refine ⟨85261355292075403875587225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56840903528050269250391483 85261355292075403875587225)
  ·
    refine ⟨63946016469056552906690419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85261355292075403875587225 63946016469056552906690419)
    ·
      refine ⟨95919024703584829360035629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63946016469056552906690419 95919024703584829360035629)
      ·
        refine ⟨35969634263844311010013361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95919024703584829360035629 35969634263844311010013361)
        ·
          refine ⟨26977225697883233257510021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35969634263844311010013361 26977225697883233257510021)
          ·
            refine ⟨5058229818353106235783129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26977225697883233257510021 5058229818353106235783129)
            ·
              refine ⟨3793672363764829676837347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5058229818353106235783129 3793672363764829676837347)
              ·
                refine ⟨5690508545647244515256021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3793672363764829676837347 5690508545647244515256021)
                ·
                  refine ⟨133371294038607293326313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5690508545647244515256021 133371294038607293326313)
                  ·
                    rfl

theorem cell23_2337657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 7].length) (baseStart_2337657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337657 prefixEnd_2337657 := by exact prefixLift 2337657
  have htrace : WordTrace (prefixWord ++ tailWord_2337657) baseStart_2337657 baseEnd_2337657 := by
    simpa [prefixWord, tailWord_2337657, baseEnd_2337657] using wordTrace_append hprefix tailTrace_2337657
  have hstable : (prefixWord ++ tailWord_2337657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337657).length < 2 ^ (prefixWord ++ tailWord_2337657).sum := by decide
  have hdescent : baseEnd_2337657 < baseStart_2337657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337667 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 3]
def baseStart_2337667 : Nat := 118140960795 + 2337667 * 2 ^ 59
def prefixEnd_2337667 : Nat := 4983230072969 + 3 ^ 40 * 2337667 * 2
def baseEnd_2337667 : Nat := 1200346781154010600811771

theorem tailTrace_2337667 : CollatzResearch.WordTrace tailWord_2337667 prefixEnd_2337667 1200346781154010600811771 := by
  unfold tailWord_2337667
  simp only [CollatzResearch.WordTrace]
  refine ⟨85261720022039175583451255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56841146681359450388967503 85261720022039175583451255)
  ·
    refine ⟨127892580033058763375176883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85261720022039175583451255 127892580033058763375176883)
    ·
      refine ⟨191838870049588145062765325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127892580033058763375176883 191838870049588145062765325)
      ·
        refine ⟨71939576268595554398536997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191838870049588145062765325 71939576268595554398536997)
        ·
          refine ⟨13488670550361666449725687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71939576268595554398536997 13488670550361666449725687)
          ·
            refine ⟨20233005825542499674588531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13488670550361666449725687 20233005825542499674588531)
            ·
              refine ⟨30349508738313749511882797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20233005825542499674588531 30349508738313749511882797)
              ·
                refine ⟨11381065776867656066956049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30349508738313749511882797 11381065776867656066956049)
                ·
                  refine ⟨8535799332650742050217037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11381065776867656066956049 8535799332650742050217037)
                  ·
                    refine ⟨3200924749744028268831389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8535799332650742050217037 3200924749744028268831389)
                    ·
                      refine ⟨1200346781154010600811771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3200924749744028268831389 1200346781154010600811771)
                      ·
                        rfl

theorem cell23_2337667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_2337667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337667 prefixEnd_2337667 := by exact prefixLift 2337667
  have htrace : WordTrace (prefixWord ++ tailWord_2337667) baseStart_2337667 baseEnd_2337667 := by
    simpa [prefixWord, tailWord_2337667, baseEnd_2337667] using wordTrace_append hprefix tailTrace_2337667
  have hstable : (prefixWord ++ tailWord_2337667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337667).length < 2 ^ (prefixWord ++ tailWord_2337667).sum := by decide
  have hdescent : baseEnd_2337667 < baseStart_2337667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337687 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 2, 5]
def baseStart_2337687 : Nat := 118140960795 + 2337687 * 2 ^ 59
def prefixEnd_2337687 : Nat := 4983230072969 + 3 ^ 40 * 2337687 * 2
def baseEnd_2337687 : Nat := 400119016922366840853893

theorem tailTrace_2337687 : CollatzResearch.WordTrace tailWord_2337687 prefixEnd_2337687 400119016922366840853893 := by
  unfold tailWord_2337687
  simp only [CollatzResearch.WordTrace]
  refine ⟨85262449481966718999179315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56841632987977812666119543 85262449481966718999179315)
  ·
    refine ⟨127893674222950078498768973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85262449481966718999179315 127893674222950078498768973)
    ·
      refine ⟨47960127833606279437038365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127893674222950078498768973 47960127833606279437038365)
      ·
        refine ⟨17985047937602354788889387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47960127833606279437038365 17985047937602354788889387)
        ·
          refine ⟨26977571906403532183334081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17985047937602354788889387 26977571906403532183334081)
          ·
            refine ⟨20233178929802649137500561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26977571906403532183334081 20233178929802649137500561)
            ·
              refine ⟨15174884197351986853125421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20233178929802649137500561 15174884197351986853125421)
              ·
                refine ⟨5690581574006995069922033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15174884197351986853125421 5690581574006995069922033)
                ·
                  refine ⟨4267936180505246302441525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5690581574006995069922033 4267936180505246302441525)
                  ·
                    refine ⟨400119016922366840853893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4267936180505246302441525 400119016922366840853893)
                    ·
                      rfl

theorem cell23_2337687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_2337687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337687 prefixEnd_2337687 := by exact prefixLift 2337687
  have htrace : WordTrace (prefixWord ++ tailWord_2337687) baseStart_2337687 baseEnd_2337687 := by
    simpa [prefixWord, tailWord_2337687, baseEnd_2337687] using wordTrace_append hprefix tailTrace_2337687
  have hstable : (prefixWord ++ tailWord_2337687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337687).length < 2 ^ (prefixWord ++ tailWord_2337687).sum := by decide
  have hdescent : baseEnd_2337687 < baseStart_2337687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337707 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 4]
def baseStart_2337707 : Nat := 118140960795 + 2337707 * 2 ^ 59
def prefixEnd_2337707 : Nat := 4983230072969 + 3 ^ 40 * 2337707 * 2
def baseEnd_2337707 : Nat := 1200367320380190444311587

theorem tailTrace_2337707 : CollatzResearch.WordTrace tailWord_2337707 prefixEnd_2337707 1200367320380190444311587 := by
  unfold tailWord_2337707
  simp only [CollatzResearch.WordTrace]
  refine ⟨85263178941894262414907375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56842119294596174943271583 85263178941894262414907375)
  ·
    refine ⟨127894768412841393622361063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85263178941894262414907375 127894768412841393622361063)
    ·
      refine ⟨191842152619262090433541595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127894768412841393622361063 191842152619262090433541595)
      ·
        refine ⟨287763228928893135650312393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191842152619262090433541595 287763228928893135650312393)
        ·
          refine ⟨215822421696669851737734295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287763228928893135650312393 215822421696669851737734295)
          ·
            refine ⟨323733632545004777606601443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215822421696669851737734295 323733632545004777606601443)
            ·
              refine ⟨485600448817507166409902165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323733632545004777606601443 485600448817507166409902165)
              ·
                refine ⟨5690630259580162106366041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 485600448817507166409902165 5690630259580162106366041)
                ·
                  refine ⟨4267972694685121579774531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5690630259580162106366041 4267972694685121579774531)
                  ·
                    refine ⟨6401959042027682369661797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4267972694685121579774531 6401959042027682369661797)
                    ·
                      refine ⟨1200367320380190444311587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6401959042027682369661797 1200367320380190444311587)
                      ·
                        rfl

theorem cell23_2337707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 4].length) (baseStart_2337707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337707 prefixEnd_2337707 := by exact prefixLift 2337707
  have htrace : WordTrace (prefixWord ++ tailWord_2337707) baseStart_2337707 baseEnd_2337707 := by
    simpa [prefixWord, tailWord_2337707, baseEnd_2337707] using wordTrace_append hprefix tailTrace_2337707
  have hstable : (prefixWord ++ tailWord_2337707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337707).length < 2 ^ (prefixWord ++ tailWord_2337707).sum := by decide
  have hdescent : baseEnd_2337707 < baseStart_2337707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337727 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 3]
def baseStart_2337727 : Nat := 118140960795 + 2337727 * 2 ^ 59
def prefixEnd_2337727 : Nat := 4983230072969 + 3 ^ 40 * 2337727 * 2
def baseEnd_2337727 : Nat := 1200377589993280366061495

theorem tailTrace_2337727 : CollatzResearch.WordTrace tailWord_2337727 prefixEnd_2337727 1200377589993280366061495 := by
  unfold tailWord_2337727
  simp only [CollatzResearch.WordTrace]
  refine ⟨85263908401821805830635435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56842605601214537220423623 85263908401821805830635435)
  ·
    refine ⟨127895862602732708745953153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85263908401821805830635435 127895862602732708745953153)
    ·
      refine ⟨95921896952049531559464865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127895862602732708745953153 95921896952049531559464865)
      ·
        refine ⟨71941422714037148669598649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95921896952049531559464865 71941422714037148669598649)
        ·
          refine ⟨53956067035527861502198987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71941422714037148669598649 53956067035527861502198987)
          ·
            refine ⟨80934100553291792253298481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53956067035527861502198987 80934100553291792253298481)
            ·
              refine ⟨60700575414968844189973861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80934100553291792253298481 60700575414968844189973861)
              ·
                refine ⟨11381357890306658285620099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60700575414968844189973861 11381357890306658285620099)
                ·
                  refine ⟨17072036835459987428430149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11381357890306658285620099 17072036835459987428430149)
                  ·
                    refine ⟨3201006906648747642830653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17072036835459987428430149 3201006906648747642830653)
                    ·
                      refine ⟨1200377589993280366061495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3201006906648747642830653 1200377589993280366061495)
                      ·
                        rfl

theorem cell23_2337727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_2337727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337727 prefixEnd_2337727 := by exact prefixLift 2337727
  have htrace : WordTrace (prefixWord ++ tailWord_2337727) baseStart_2337727 baseEnd_2337727 := by
    simpa [prefixWord, tailWord_2337727, baseEnd_2337727] using wordTrace_append hprefix tailTrace_2337727
  have hstable : (prefixWord ++ tailWord_2337727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337727).length < 2 ^ (prefixWord ++ tailWord_2337727).sum := by decide
  have hdescent : baseEnd_2337727 < baseStart_2337727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337768 : List Nat := [2, 1, 4, 1, 1, 1, 6, 2, 1, 4]
def baseStart_2337768 : Nat := 118140960795 + 2337768 * 2 ^ 59
def prefixEnd_2337768 : Nat := 4983230072969 + 3 ^ 40 * 2337768 * 2
def baseEnd_2337768 : Nat := 400132880900038235216269

theorem tailTrace_2337768 : CollatzResearch.WordTrace tailWord_2337768 prefixEnd_2337768 400132880900038235216269 := by
  unfold tailWord_2337768
  simp only [CollatzResearch.WordTrace]
  refine ⟨42632701897336634916438979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56843602529782179888585305 42632701897336634916438979)
  ·
    refine ⟨63949052846004952374658469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42632701897336634916438979 63949052846004952374658469)
    ·
      refine ⟨11990447408625928570248463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63949052846004952374658469 11990447408625928570248463)
      ·
        refine ⟨17985671112938892855372695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11990447408625928570248463 17985671112938892855372695)
        ·
          refine ⟨26978506669408339283059043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17985671112938892855372695 26978506669408339283059043)
          ·
            refine ⟨40467760004112508924588565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26978506669408339283059043 40467760004112508924588565)
            ·
              refine ⟨1896926250192773855840089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40467760004112508924588565 1896926250192773855840089)
              ·
                refine ⟨1422694687644580391880067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1896926250192773855840089 1422694687644580391880067)
                ·
                  refine ⟨2134042031466870587820101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1422694687644580391880067 2134042031466870587820101)
                  ·
                    refine ⟨400132880900038235216269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2134042031466870587820101 400132880900038235216269)
                    ·
                      rfl

theorem cell23_2337768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_2337768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337768 prefixEnd_2337768 := by exact prefixLift 2337768
  have htrace : WordTrace (prefixWord ++ tailWord_2337768) baseStart_2337768 baseEnd_2337768 := by
    simpa [prefixWord, tailWord_2337768, baseEnd_2337768] using wordTrace_append hprefix tailTrace_2337768
  have hstable : (prefixWord ++ tailWord_2337768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337768).length < 2 ^ (prefixWord ++ tailWord_2337768).sum := by decide
  have hdescent : baseEnd_2337768 < baseStart_2337768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337784 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 1, 5, 2]
def baseStart_2337784 : Nat := 118140960795 + 2337784 * 2 ^ 59
def prefixEnd_2337784 : Nat := 4983230072969 + 3 ^ 40 * 2337784 * 2
def baseEnd_2337784 : Nat := 1200406858390586643048733

theorem tailTrace_2337784 : CollatzResearch.WordTrace tailWord_2337784 prefixEnd_2337784 1200406858390586643048733 := by
  unfold tailWord_2337784
  simp only [CollatzResearch.WordTrace]
  refine ⟨42632993681307652282730203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56843991575076869710306937 42632993681307652282730203)
  ·
    refine ⟨63949490521961478424095305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42632993681307652282730203 63949490521961478424095305)
    ·
      refine ⟨47962117891471108818071479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63949490521961478424095305 47962117891471108818071479)
      ·
        refine ⟨71943176837206663227107219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47962117891471108818071479 71943176837206663227107219)
        ·
          refine ⟨107914765255809994840660829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71943176837206663227107219 107914765255809994840660829)
          ·
            refine ⟨40468036970928748065247811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107914765255809994840660829 40468036970928748065247811)
            ·
              refine ⟨60702055456393122097871717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40468036970928748065247811 60702055456393122097871717)
              ·
                refine ⟨11381635398073710393350947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60702055456393122097871717 11381635398073710393350947)
                ·
                  refine ⟨17072453097110565590026421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11381635398073710393350947 17072453097110565590026421)
                  ·
                    refine ⟨1600542477854115524064977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17072453097110565590026421 1600542477854115524064977)
                    ·
                      refine ⟨1200406858390586643048733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1600542477854115524064977 1200406858390586643048733)
                      ·
                        rfl

theorem cell23_2337784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 1, 5, 2].length) (baseStart_2337784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337784 prefixEnd_2337784 := by exact prefixLift 2337784
  have htrace : WordTrace (prefixWord ++ tailWord_2337784) baseStart_2337784 baseEnd_2337784 := by
    simpa [prefixWord, tailWord_2337784, baseEnd_2337784] using wordTrace_append hprefix tailTrace_2337784
  have hstable : (prefixWord ++ tailWord_2337784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337784).length < 2 ^ (prefixWord ++ tailWord_2337784).sum := by decide
  have hdescent : baseEnd_2337784 < baseStart_2337784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337848 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 3, 2, 2]
def baseStart_2337848 : Nat := 118140960795 + 2337848 * 2 ^ 59
def prefixEnd_2337848 : Nat := 4983230072969 + 3 ^ 40 * 2337848 * 2
def baseEnd_2337848 : Nat := 1200439721152474392648439

theorem tailTrace_2337848 : CollatzResearch.WordTrace tailWord_2337848 prefixEnd_2337848 1200439721152474392648439 := by
  unfold tailWord_2337848
  simp only [CollatzResearch.WordTrace]
  refine ⟨42634160817191721747895099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56845547756255628997193465 42634160817191721747895099)
  ·
    refine ⟨63951241225787582621842649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42634160817191721747895099 63951241225787582621842649)
    ·
      refine ⟨47963430919340686966381987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63951241225787582621842649 47963430919340686966381987)
      ·
        refine ⟨71945146379011030449572981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47963430919340686966381987 71945146379011030449572981)
        ·
          refine ⟨6744857473032284104647467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71945146379011030449572981 6744857473032284104647467)
          ·
            refine ⟨10117286209548426156971201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6744857473032284104647467 10117286209548426156971201)
            ·
              refine ⟨7587964657161319617728401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10117286209548426156971201 7587964657161319617728401)
              ·
                refine ⟨5690973492870989713296301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7587964657161319617728401 5690973492870989713296301)
                ·
                  refine ⟨2134115059826621142486113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5690973492870989713296301 2134115059826621142486113)
                  ·
                    refine ⟨1600586294869965856864585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2134115059826621142486113 1600586294869965856864585)
                    ·
                      refine ⟨1200439721152474392648439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1600586294869965856864585 1200439721152474392648439)
                      ·
                        rfl

theorem cell23_2337848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 3, 2, 2].length) (baseStart_2337848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337848 prefixEnd_2337848 := by exact prefixLift 2337848
  have htrace : WordTrace (prefixWord ++ tailWord_2337848) baseStart_2337848 baseEnd_2337848 := by
    simpa [prefixWord, tailWord_2337848, baseEnd_2337848] using wordTrace_append hprefix tailTrace_2337848
  have hstable : (prefixWord ++ tailWord_2337848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337848).length < 2 ^ (prefixWord ++ tailWord_2337848).sum := by decide
  have hdescent : baseEnd_2337848 < baseStart_2337848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337864 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 3, 3, 3]
def baseStart_2337864 : Nat := 118140960795 + 2337864 * 2 ^ 59
def prefixEnd_2337864 : Nat := 4983230072969 + 3 ^ 40 * 2337864 * 2
def baseEnd_2337864 : Nat := 1200447936842946330048365

theorem tailTrace_2337864 : CollatzResearch.WordTrace tailWord_2337864 prefixEnd_2337864 1200447936842946330048365 := by
  unfold tailWord_2337864
  simp only [CollatzResearch.WordTrace]
  refine ⟨42634452601162739114186323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56845936801550318818915097 42634452601162739114186323)
  ·
    refine ⟨63951678901744108671279485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42634452601162739114186323 63951678901744108671279485)
    ·
      refine ⟨23981879588154040751729807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63951678901744108671279485 23981879588154040751729807)
      ·
        refine ⟨35972819382231061127594711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23981879588154040751729807 35972819382231061127594711)
        ·
          refine ⟨53959229073346591691392067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35972819382231061127594711 53959229073346591691392067)
          ·
            refine ⟨80938843610019887537088101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53959229073346591691392067 80938843610019887537088101)
            ·
              refine ⟨15176033176878728913204019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80938843610019887537088101 15176033176878728913204019)
              ·
                refine ⟨22764049765318093369806029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15176033176878728913204019 22764049765318093369806029)
                ·
                  refine ⟨8536518661994285013677261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22764049765318093369806029 8536518661994285013677261)
                  ·
                    refine ⟨3201194498247856880128973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8536518661994285013677261 3201194498247856880128973)
                    ·
                      refine ⟨1200447936842946330048365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3201194498247856880128973 1200447936842946330048365)
                      ·
                        rfl

theorem cell23_2337864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_2337864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337864 prefixEnd_2337864 := by exact prefixLift 2337864
  have htrace : WordTrace (prefixWord ++ tailWord_2337864) baseStart_2337864 baseEnd_2337864 := by
    simpa [prefixWord, tailWord_2337864, baseEnd_2337864] using wordTrace_append hprefix tailTrace_2337864
  have hstable : (prefixWord ++ tailWord_2337864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337864).length < 2 ^ (prefixWord ++ tailWord_2337864).sum := by decide
  have hdescent : baseEnd_2337864 < baseStart_2337864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337884 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 2, 7]
def baseStart_2337884 : Nat := 118140960795 + 2337884 * 2 ^ 59
def prefixEnd_2337884 : Nat := 4983230072969 + 3 ^ 40 * 2337884 * 2
def baseEnd_2337884 : Nat := 400152735485345417266091

theorem tailTrace_2337884 : CollatzResearch.WordTrace tailWord_2337884 prefixEnd_2337884 400152735485345417266091 := by
  unfold tailWord_2337884
  simp only [CollatzResearch.WordTrace]
  refine ⟨42634817331126510822050353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56846423108168681096067137 42634817331126510822050353)
  ·
    refine ⟨31976112998344883116537765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42634817331126510822050353 31976112998344883116537765)
    ·
      refine ⟨5995521187189665584350831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31976112998344883116537765 5995521187189665584350831)
      ·
        refine ⟨8993281780784498376526247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5995521187189665584350831 8993281780784498376526247)
        ·
          refine ⟨13489922671176747564789371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8993281780784498376526247 13489922671176747564789371)
          ·
            refine ⟨20234884006765121347184057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13489922671176747564789371 20234884006765121347184057)
            ·
              refine ⟨15176163005073841010388043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20234884006765121347184057 15176163005073841010388043)
              ·
                refine ⟨22764244507610761515582065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15176163005073841010388043 22764244507610761515582065)
                ·
                  refine ⟨17073183380708071136686549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22764244507610761515582065 17073183380708071136686549)
                  ·
                    refine ⟨400152735485345417266091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17073183380708071136686549 400152735485345417266091)
                    ·
                      rfl

theorem cell23_2337884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_2337884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337884 prefixEnd_2337884 := by exact prefixLift 2337884
  have htrace : WordTrace (prefixWord ++ tailWord_2337884) baseStart_2337884 baseEnd_2337884 := by
    simpa [prefixWord, tailWord_2337884, baseEnd_2337884] using wordTrace_append hprefix tailTrace_2337884
  have hstable : (prefixWord ++ tailWord_2337884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337884).length < 2 ^ (prefixWord ++ tailWord_2337884).sum := by decide
  have hdescent : baseEnd_2337884 < baseStart_2337884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337891 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 3, 3, 2]
def baseStart_2337891 : Nat := 118140960795 + 2337891 * 2 ^ 59
def prefixEnd_2337891 : Nat := 4983230072969 + 3 ^ 40 * 2337891 * 2
def baseEnd_2337891 : Nat := 1200461800820617724410741

theorem tailTrace_2337891 : CollatzResearch.WordTrace tailWord_2337891 prefixEnd_2337891 1200461800820617724410741 := by
  unfold tailWord_2337891
  simp only [CollatzResearch.WordTrace]
  refine ⟨85269889973227661839605527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56846593315485107893070351 85269889973227661839605527)
  ·
    refine ⟨127904834959841492759408291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85269889973227661839605527 127904834959841492759408291)
    ·
      refine ⟨191857252439762239139112437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127904834959841492759408291 191857252439762239139112437)
      ·
        refine ⟨17986617416227709919291791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 191857252439762239139112437 17986617416227709919291791)
        ·
          refine ⟨26979926124341564878937687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17986617416227709919291791 26979926124341564878937687)
          ·
            refine ⟨40469889186512347318406531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26979926124341564878937687 40469889186512347318406531)
            ·
              refine ⟨60704833779768520977609797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40469889186512347318406531 60704833779768520977609797)
              ·
                refine ⟨11382156333706597683301837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60704833779768520977609797 11382156333706597683301837)
                ·
                  refine ⟨4268308625139974131238189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11382156333706597683301837 4268308625139974131238189)
                  ·
                    refine ⟨1600615734427490299214321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4268308625139974131238189 1600615734427490299214321)
                    ·
                      refine ⟨1200461800820617724410741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1600615734427490299214321 1200461800820617724410741)
                      ·
                        rfl

theorem cell23_2337891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_2337891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337891 prefixEnd_2337891 := by exact prefixLift 2337891
  have htrace : WordTrace (prefixWord ++ tailWord_2337891) baseStart_2337891 baseEnd_2337891 := by
    simpa [prefixWord, tailWord_2337891, baseEnd_2337891] using wordTrace_append hprefix tailTrace_2337891
  have hstable : (prefixWord ++ tailWord_2337891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337891).length < 2 ^ (prefixWord ++ tailWord_2337891).sum := by decide
  have hdescent : baseEnd_2337891 < baseStart_2337891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337907 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 9]
def baseStart_2337907 : Nat := 118140960795 + 2337907 * 2 ^ 59
def prefixEnd_2337907 : Nat := 4983230072969 + 3 ^ 40 * 2337907 * 2
def baseEnd_2337907 : Nat := 1200470016511089661810667

theorem tailTrace_2337907 : CollatzResearch.WordTrace tailWord_2337907 prefixEnd_2337907 1200470016511089661810667 := by
  unfold tailWord_2337907
  simp only [CollatzResearch.WordTrace]
  refine ⟨85270473541169696572187975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56846982360779797714791983 85270473541169696572187975)
  ·
    refine ⟨127905710311754544858281963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85270473541169696572187975 127905710311754544858281963)
    ·
      refine ⟨191858565467631817287422945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127905710311754544858281963 191858565467631817287422945)
      ·
        refine ⟨143893924100723862965567209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191858565467631817287422945 143893924100723862965567209)
        ·
          refine ⟨107920443075542897224175407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143893924100723862965567209 107920443075542897224175407)
          ·
            refine ⟨161880664613314345836263111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107920443075542897224175407 161880664613314345836263111)
            ·
              refine ⟨242820996919971518754394667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161880664613314345836263111 242820996919971518754394667)
              ·
                refine ⟨364231495379957278131592001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242820996919971518754394667 364231495379957278131592001)
                ·
                  refine ⟨273173621534967958598694001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364231495379957278131592001 273173621534967958598694001)
                  ·
                    refine ⟨204880216151225968949020501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 273173621534967958598694001 204880216151225968949020501)
                    ·
                      refine ⟨1200470016511089661810667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 204880216151225968949020501 1200470016511089661810667)
                      ·
                        rfl

theorem cell23_2337907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_2337907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2337907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2337907 prefixEnd_2337907 := by exact prefixLift 2337907
  have htrace : WordTrace (prefixWord ++ tailWord_2337907) baseStart_2337907 baseEnd_2337907 := by
    simpa [prefixWord, tailWord_2337907, baseEnd_2337907] using wordTrace_append hprefix tailTrace_2337907
  have hstable : (prefixWord ++ tailWord_2337907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337907).length < 2 ^ (prefixWord ++ tailWord_2337907).sum := by decide
  have hdescent : baseEnd_2337907 < baseStart_2337907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338006 : List Nat := [5, 2, 1, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_2338006 : Nat := 118140960795 + 2338006 * 2 ^ 59
def prefixEnd_2338006 : Nat := 4983230072969 + 3 ^ 40 * 2338006 * 2
def baseEnd_2338006 : Nat := 1200520851095884774472713

theorem tailTrace_2338006 : CollatzResearch.WordTrace tailWord_2338006 prefixEnd_2338006 1200520851095884774472713 := by
  unfold tailWord_2338006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5329630272988189780002617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56849389578540690986694581 5329630272988189780002617)
  ·
    refine ⟨3997222704741142335001963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5329630272988189780002617 3997222704741142335001963)
    ·
      refine ⟨5995834057111713502502945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3997222704741142335001963 5995834057111713502502945)
      ·
        refine ⟨4496875542833785126877209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5995834057111713502502945 4496875542833785126877209)
        ·
          refine ⟨3372656657125338845157907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4496875542833785126877209 3372656657125338845157907)
          ·
            refine ⟨5058984985688008267736861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3372656657125338845157907 5058984985688008267736861)
            ·
              refine ⟨1897119369633003100401323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5058984985688008267736861 1897119369633003100401323)
              ·
                refine ⟨2845679054449504650601985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1897119369633003100401323 2845679054449504650601985)
                ·
                  refine ⟨2134259290837128487951489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2845679054449504650601985 2134259290837128487951489)
                  ·
                    refine ⟨1600694468127846365963617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2134259290837128487951489 1600694468127846365963617)
                    ·
                      refine ⟨1200520851095884774472713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1600694468127846365963617 1200520851095884774472713)
                      ·
                        rfl

theorem cell23_2338006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_2338006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338006 prefixEnd_2338006 := by exact prefixLift 2338006
  have htrace : WordTrace (prefixWord ++ tailWord_2338006) baseStart_2338006 baseEnd_2338006 := by
    simpa [prefixWord, tailWord_2338006, baseEnd_2338006] using wordTrace_append hprefix tailTrace_2338006
  have hstable : (prefixWord ++ tailWord_2338006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338006).length < 2 ^ (prefixWord ++ tailWord_2338006).sum := by decide
  have hdescent : baseEnd_2338006 < baseStart_2338006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338011 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 6, 4, 2]
def baseStart_2338011 : Nat := 118140960795 + 2338011 * 2 ^ 59
def prefixEnd_2338011 : Nat := 4983230072969 + 3 ^ 40 * 2338011 * 2
def baseEnd_2338011 : Nat := 1200523418499157254910189

theorem tailTrace_2338011 : CollatzResearch.WordTrace tailWord_2338011 prefixEnd_2338011 1200523418499157254910189 := by
  unfold tailWord_2338011
  simp only [CollatzResearch.WordTrace]
  refine ⟨85274266732792922333973887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56849511155195281555982591 85274266732792922333973887)
  ·
    refine ⟨127911400099189383500960831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85274266732792922333973887 127911400099189383500960831)
    ·
      refine ⟨191867100148784075251441247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127911400099189383500960831 191867100148784075251441247)
      ·
        refine ⟨287800650223176112877161871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191867100148784075251441247 287800650223176112877161871)
        ·
          refine ⟨431700975334764169315742807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287800650223176112877161871 431700975334764169315742807)
          ·
            refine ⟨647551463002146253973614211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431700975334764169315742807 647551463002146253973614211)
            ·
              refine ⟨971327194503219380960421317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647551463002146253973614211 971327194503219380960421317)
              ·
                refine ⟨182123848969353633930078997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 971327194503219380960421317 182123848969353633930078997)
                ·
                  refine ⟨8537055420438451590472453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 182123848969353633930078997 8537055420438451590472453)
                  ·
                    refine ⟨1600697891332209673213585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8537055420438451590472453 1600697891332209673213585)
                    ·
                      refine ⟨1200523418499157254910189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1600697891332209673213585 1200523418499157254910189)
                      ·
                        rfl

theorem cell23_2338011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 4, 2].length) (baseStart_2338011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338011 prefixEnd_2338011 := by exact prefixLift 2338011
  have htrace : WordTrace (prefixWord ++ tailWord_2338011) baseStart_2338011 baseEnd_2338011 := by
    simpa [prefixWord, tailWord_2338011, baseEnd_2338011] using wordTrace_append hprefix tailTrace_2338011
  have hstable : (prefixWord ++ tailWord_2338011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338011).length < 2 ^ (prefixWord ++ tailWord_2338011).sum := by decide
  have hdescent : baseEnd_2338011 < baseStart_2338011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338095 : List Nat := [1, 1, 2, 1, 2, 1, 3, 7, 1, 1, 3]
def baseStart_2338095 : Nat := 118140960795 + 2338095 * 2 ^ 59
def prefixEnd_2338095 : Nat := 4983230072969 + 3 ^ 40 * 2338095 * 2
def baseEnd_2338095 : Nat := 1200566550874134926259803

theorem tailTrace_2338095 : CollatzResearch.WordTrace tailWord_2338095 prefixEnd_2338095 1200566550874134926259803 := by
  unfold tailWord_2338095
  simp only [CollatzResearch.WordTrace]
  refine ⟨85277330464488604680031739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56851553642992403120021159 85277330464488604680031739)
  ·
    refine ⟨127915995696732907020047609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85277330464488604680031739 127915995696732907020047609)
    ·
      refine ⟨95936996772549680265035707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127915995696732907020047609 95936996772549680265035707)
      ·
        refine ⟨143905495158824520397553561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95936996772549680265035707 143905495158824520397553561)
        ·
          refine ⟨107929121369118390298165171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143905495158824520397553561 107929121369118390298165171)
          ·
            refine ⟨161893682053677585447247757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107929121369118390298165171 161893682053677585447247757)
            ·
              refine ⟨60710130770129094542717909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161893682053677585447247757 60710130770129094542717909)
              ·
                refine ⟨1422893689924900653344951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 60710130770129094542717909 1422893689924900653344951)
                ·
                  refine ⟨2134340534887350980017427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1422893689924900653344951 2134340534887350980017427)
                  ·
                    refine ⟨3201510802331026470026141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2134340534887350980017427 3201510802331026470026141)
                    ·
                      refine ⟨1200566550874134926259803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3201510802331026470026141 1200566550874134926259803)
                      ·
                        rfl

theorem cell23_2338095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 1, 1, 3].length) (baseStart_2338095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338095 prefixEnd_2338095 := by exact prefixLift 2338095
  have htrace : WordTrace (prefixWord ++ tailWord_2338095) baseStart_2338095 baseEnd_2338095 := by
    simpa [prefixWord, tailWord_2338095, baseEnd_2338095] using wordTrace_append hprefix tailTrace_2338095
  have hstable : (prefixWord ++ tailWord_2338095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338095).length < 2 ^ (prefixWord ++ tailWord_2338095).sum := by decide
  have hdescent : baseEnd_2338095 < baseStart_2338095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338102 : List Nat := [5, 1, 2, 3, 1, 1, 2, 2, 6]
def baseStart_2338102 : Nat := 118140960795 + 2338102 * 2 ^ 59
def prefixEnd_2338102 : Nat := 4983230072969 + 3 ^ 40 * 2338102 * 2
def baseEnd_2338102 : Nat := 133396682804301822096919

theorem tailTrace_2338102 : CollatzResearch.WordTrace tailWord_2338102 prefixEnd_2338102 133396682804301822096919 := by
  unfold tailWord_2338102
  simp only [CollatzResearch.WordTrace]
  refine ⟨5329849110966452804721035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56851723850308829917024373 5329849110966452804721035)
  ·
    refine ⟨7994773666449679207081553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5329849110966452804721035 7994773666449679207081553)
    ·
      refine ⟨5996080249837259405311165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7994773666449679207081553 5996080249837259405311165)
      ·
        refine ⟨2248530093688972276991687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5996080249837259405311165 2248530093688972276991687)
        ·
          refine ⟨3372795140533458415487531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2248530093688972276991687 3372795140533458415487531)
          ·
            refine ⟨5059192710800187623231297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3372795140533458415487531 5059192710800187623231297)
            ·
              refine ⟨3794394533100140717423473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5059192710800187623231297 3794394533100140717423473)
              ·
                refine ⟨2845795899825105538067605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3794394533100140717423473 2845795899825105538067605)
                ·
                  refine ⟨133396682804301822096919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2845795899825105538067605 133396682804301822096919)
                  ·
                    rfl

theorem cell23_2338102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_2338102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338102 prefixEnd_2338102 := by exact prefixLift 2338102
  have htrace : WordTrace (prefixWord ++ tailWord_2338102) baseStart_2338102 baseEnd_2338102 := by
    simpa [prefixWord, tailWord_2338102, baseEnd_2338102] using wordTrace_append hprefix tailTrace_2338102
  have hstable : (prefixWord ++ tailWord_2338102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338102).length < 2 ^ (prefixWord ++ tailWord_2338102).sum := by decide
  have hdescent : baseEnd_2338102 < baseStart_2338102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338121 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 1, 1, 5]
def baseStart_2338121 : Nat := 118140960795 + 2338121 * 2 ^ 59
def prefixEnd_2338121 : Nat := 4983230072969 + 3 ^ 40 * 2338121 * 2
def baseEnd_2338121 : Nat := 1200579901371151824534683

theorem tailTrace_2338121 : CollatzResearch.WordTrace tailWord_2338121 prefixEnd_2338121 1200579901371151824534683 := by
  unfold tailWord_2338121
  simp only [CollatzResearch.WordTrace]
  refine ⟨85278278762394411120478217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56852185841596274080318811 85278278762394411120478217)
  ·
    refine ⟨63958709071795808340358663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85278278762394411120478217 63958709071795808340358663)
    ·
      refine ⟨95938063607693712510537995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63958709071795808340358663 95938063607693712510537995)
      ·
        refine ⟨143907095411540568765806993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95938063607693712510537995 143907095411540568765806993)
        ·
          refine ⟨107930321558655426574355245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143907095411540568765806993 107930321558655426574355245)
          ·
            refine ⟨40473870584495784965383217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107930321558655426574355245 40473870584495784965383217)
            ·
              refine ⟨30355402938371838724037413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40473870584495784965383217 30355402938371838724037413)
              ·
                refine ⟨5691638050944719760757015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30355402938371838724037413 5691638050944719760757015)
                ·
                  refine ⟨8537457076417079641135523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5691638050944719760757015 8537457076417079641135523)
                  ·
                    refine ⟨12806185614625619461703285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8537457076417079641135523 12806185614625619461703285)
                    ·
                      refine ⟨1200579901371151824534683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12806185614625619461703285 1200579901371151824534683)
                      ·
                        rfl

theorem cell23_2338121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 1, 5].length) (baseStart_2338121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338121 prefixEnd_2338121 := by exact prefixLift 2338121
  have htrace : WordTrace (prefixWord ++ tailWord_2338121) baseStart_2338121 baseEnd_2338121 := by
    simpa [prefixWord, tailWord_2338121, baseEnd_2338121] using wordTrace_append hprefix tailTrace_2338121
  have hstable : (prefixWord ++ tailWord_2338121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338121).length < 2 ^ (prefixWord ++ tailWord_2338121).sum := by decide
  have hdescent : baseEnd_2338121 < baseStart_2338121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338128 : List Nat := [2, 1, 1, 1, 1, 5, 1, 5, 2, 4]
def baseStart_2338128 : Nat := 118140960795 + 2338128 * 2 ^ 59
def prefixEnd_2338128 : Nat := 4983230072969 + 3 ^ 40 * 2338128 * 2
def baseEnd_2338128 : Nat := 400194498578577765715717

theorem tailTrace_2338128 : CollatzResearch.WordTrace tailWord_2338128 prefixEnd_2338128 400194498578577765715717 := by
  unfold tailWord_2338128
  simp only [CollatzResearch.WordTrace]
  refine ⟨42639267036684525657991519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56852356048912700877322025 42639267036684525657991519)
  ·
    refine ⟨63958900555026788486987279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42639267036684525657991519 63958900555026788486987279)
    ·
      refine ⟨95938350832540182730480919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63958900555026788486987279 95938350832540182730480919)
      ·
        refine ⟨143907526248810274095721379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95938350832540182730480919 143907526248810274095721379)
        ·
          refine ⟨215861289373215411143582069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143907526248810274095721379 215861289373215411143582069)
          ·
            refine ⟨20236995878738944794710819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 215861289373215411143582069 20236995878738944794710819)
            ·
              refine ⟨30355493818108417192066229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20236995878738944794710819 30355493818108417192066229)
              ·
                refine ⟨2845827545447664111756209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30355493818108417192066229 2845827545447664111756209)
                ·
                  refine ⟨2134370659085748083817157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2845827545447664111756209 2134370659085748083817157)
                  ·
                    refine ⟨400194498578577765715717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2134370659085748083817157 400194498578577765715717)
                    ·
                      rfl

theorem cell23_2338128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 2, 4].length) (baseStart_2338128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338128 prefixEnd_2338128 := by exact prefixLift 2338128
  have htrace : WordTrace (prefixWord ++ tailWord_2338128) baseStart_2338128 baseEnd_2338128 := by
    simpa [prefixWord, tailWord_2338128, baseEnd_2338128] using wordTrace_append hprefix tailTrace_2338128
  have hstable : (prefixWord ++ tailWord_2338128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338128).length < 2 ^ (prefixWord ++ tailWord_2338128).sum := by decide
  have hdescent : baseEnd_2338128 < baseStart_2338128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338135 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 5, 2, 2]
def baseStart_2338135 : Nat := 118140960795 + 2338135 * 2 ^ 59
def prefixEnd_2338135 : Nat := 4983230072969 + 3 ^ 40 * 2338135 * 2
def baseEnd_2338135 : Nat := 1200587090100314769759619

theorem tailTrace_2338135 : CollatzResearch.WordTrace tailWord_2338135 prefixEnd_2338135 1200587090100314769759619 := by
  unfold tailWord_2338135
  simp only [CollatzResearch.WordTrace]
  refine ⟨85278789384343691511487859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56852526256229127674325239 85278789384343691511487859)
  ·
    refine ⟨127918184076515537267231789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85278789384343691511487859 127918184076515537267231789)
    ·
      refine ⟨47969319028693326475211921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127918184076515537267231789 47969319028693326475211921)
      ·
        refine ⟨35976989271519994856408941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47969319028693326475211921 35976989271519994856408941)
        ·
          refine ⟨13491370976819998071153353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35976989271519994856408941 13491370976819998071153353)
          ·
            refine ⟨10118528232614998553365015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13491370976819998071153353 10118528232614998553365015)
            ·
              refine ⟨15177792348922497830047523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10118528232614998553365015 15177792348922497830047523)
              ·
                refine ⟨22766688523383746745071285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15177792348922497830047523 22766688523383746745071285)
                ·
                  refine ⟨2134377049067226257350433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22766688523383746745071285 2134377049067226257350433)
                  ·
                    refine ⟨1600782786800419693012825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2134377049067226257350433 1600782786800419693012825)
                    ·
                      refine ⟨1200587090100314769759619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1600782786800419693012825 1200587090100314769759619)
                      ·
                        rfl

theorem cell23_2338135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_2338135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338135 prefixEnd_2338135 := by exact prefixLift 2338135
  have htrace : WordTrace (prefixWord ++ tailWord_2338135) baseStart_2338135 baseEnd_2338135 := by
    simpa [prefixWord, tailWord_2338135, baseEnd_2338135] using wordTrace_append hprefix tailTrace_2338135
  have hstable : (prefixWord ++ tailWord_2338135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338135).length < 2 ^ (prefixWord ++ tailWord_2338135).sum := by decide
  have hdescent : baseEnd_2338135 < baseStart_2338135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338138 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3]
def baseStart_2338138 : Nat := 118140960795 + 2338138 * 2 ^ 59
def prefixEnd_2338138 : Nat := 4983230072969 + 3 ^ 40 * 2338138 * 2
def baseEnd_2338138 : Nat := 1200588630542278258022105

theorem tailTrace_2338138 : CollatzResearch.WordTrace tailWord_2338138 prefixEnd_2338138 1200588630542278258022105 := by
  unfold tailWord_2338138
  simp only [CollatzResearch.WordTrace]
  refine ⟨21319724700833205755961767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56852599202221882015898045 21319724700833205755961767)
  ·
    refine ⟨31979587051249808633942651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21319724700833205755961767 31979587051249808633942651)
    ·
      refine ⟨47969380576874712950913977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31979587051249808633942651 47969380576874712950913977)
      ·
        refine ⟨35977035432656034713185483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47969380576874712950913977 35977035432656034713185483)
        ·
          refine ⟨53965553148984052069778225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35977035432656034713185483 53965553148984052069778225)
          ·
            refine ⟨40474164861738039052333669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53965553148984052069778225 40474164861738039052333669)
            ·
              refine ⟨7588905911575882322312563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40474164861738039052333669 7588905911575882322312563)
              ·
                refine ⟨11383358867363823483468845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7588905911575882322312563 11383358867363823483468845)
                ·
                  refine ⟨4268759575261433806300817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11383358867363823483468845 4268759575261433806300817)
                  ·
                    refine ⟨3201569681446075354725613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4268759575261433806300817 3201569681446075354725613)
                    ·
                      refine ⟨1200588630542278258022105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3201569681446075354725613 1200588630542278258022105)
                      ·
                        rfl

theorem cell23_2338138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_2338138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338138 prefixEnd_2338138 := by exact prefixLift 2338138
  have htrace : WordTrace (prefixWord ++ tailWord_2338138) baseStart_2338138 baseEnd_2338138 := by
    simpa [prefixWord, tailWord_2338138, baseEnd_2338138] using wordTrace_append hprefix tailTrace_2338138
  have hstable : (prefixWord ++ tailWord_2338138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338138).length < 2 ^ (prefixWord ++ tailWord_2338138).sum := by decide
  have hdescent : baseEnd_2338138 < baseStart_2338138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338148 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_2338148 : Nat := 118140960795 + 2338148 * 2 ^ 59
def prefixEnd_2338148 : Nat := 4983230072969 + 3 ^ 40 * 2338148 * 2
def baseEnd_2338148 : Nat := 1200593765348823218897059

theorem tailTrace_2338148 : CollatzResearch.WordTrace tailWord_2338148 prefixEnd_2338148 1200593765348823218897059 := by
  unfold tailWord_2338148
  simp only [CollatzResearch.WordTrace]
  refine ⟨42639631766648297365855549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56852842355531063154474065 42639631766648297365855549)
  ·
    refine ⟨15989861912493111512195831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42639631766648297365855549 15989861912493111512195831)
    ·
      refine ⟨23984792868739667268293747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15989861912493111512195831 23984792868739667268293747)
      ·
        refine ⟨35977189303109500902440621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23984792868739667268293747 35977189303109500902440621)
        ·
          refine ⟨13491445988666062838415233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35977189303109500902440621 13491445988666062838415233)
          ·
            refine ⟨10118584491499547128811425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13491445988666062838415233 10118584491499547128811425)
            ·
              refine ⟨7588938368624660346608569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10118584491499547128811425 7588938368624660346608569)
              ·
                refine ⟨5691703776468495259956427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7588938368624660346608569 5691703776468495259956427)
                ·
                  refine ⟨8537555664702742889934641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5691703776468495259956427 8537555664702742889934641)
                  ·
                    refine ⟨6403166748527057167450981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8537555664702742889934641 6403166748527057167450981)
                    ·
                      refine ⟨1200593765348823218897059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6403166748527057167450981 1200593765348823218897059)
                      ·
                        rfl

theorem cell23_2338148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_2338148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338148 prefixEnd_2338148 := by exact prefixLift 2338148
  have htrace : WordTrace (prefixWord ++ tailWord_2338148) baseStart_2338148 baseEnd_2338148 := by
    simpa [prefixWord, tailWord_2338148, baseEnd_2338148] using wordTrace_append hprefix tailTrace_2338148
  have hstable : (prefixWord ++ tailWord_2338148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338148).length < 2 ^ (prefixWord ++ tailWord_2338148).sum := by decide
  have hdescent : baseEnd_2338148 < baseStart_2338148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338236 : List Nat := [2, 2, 2, 4, 2, 2, 2, 1, 2, 1, 3]
def baseStart_2338236 : Nat := 118140960795 + 2338236 * 2 ^ 59
def prefixEnd_2338236 : Nat := 4983230072969 + 3 ^ 40 * 2338236 * 2
def baseEnd_2338236 : Nat := 1200638951646418874596655

theorem tailTrace_2338236 : CollatzResearch.WordTrace tailWord_2338236 prefixEnd_2338236 1200638951646418874596655 := by
  unfold tailWord_2338236
  simp only [CollatzResearch.WordTrace]
  refine ⟨42641236578488892880457281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56854982104651857173943041 42641236578488892880457281)
  ·
    refine ⟨31980927433866669660342961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42641236578488892880457281 31980927433866669660342961)
    ·
      refine ⟨23985695575400002245257221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31980927433866669660342961 23985695575400002245257221)
      ·
        refine ⟨4497317920387500420985729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23985695575400002245257221 4497317920387500420985729)
        ·
          refine ⟨3372988440290625315739297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4497317920387500420985729 3372988440290625315739297)
          ·
            refine ⟨2529741330217968986804473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3372988440290625315739297 2529741330217968986804473)
            ·
              refine ⟨1897305997663476740103355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2529741330217968986804473 1897305997663476740103355)
              ·
                refine ⟨2845958996495215110155033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1897305997663476740103355 2845958996495215110155033)
                ·
                  refine ⟨2134469247371411332616275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2845958996495215110155033 2134469247371411332616275)
                  ·
                    refine ⟨3201703871057116998924413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2134469247371411332616275 3201703871057116998924413)
                    ·
                      refine ⟨1200638951646418874596655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3201703871057116998924413 1200638951646418874596655)
                      ·
                        rfl

theorem cell23_2338236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_2338236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338236 prefixEnd_2338236 := by exact prefixLift 2338236
  have htrace : WordTrace (prefixWord ++ tailWord_2338236) baseStart_2338236 baseEnd_2338236 := by
    simpa [prefixWord, tailWord_2338236, baseEnd_2338236] using wordTrace_append hprefix tailTrace_2338236
  have hstable : (prefixWord ++ tailWord_2338236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338236).length < 2 ^ (prefixWord ++ tailWord_2338236).sum := by decide
  have hdescent : baseEnd_2338236 < baseStart_2338236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338238 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_2338238 : Nat := 118140960795 + 2338238 * 2 ^ 59
def prefixEnd_2338238 : Nat := 4983230072969 + 3 ^ 40 * 2338238 * 2
def baseEnd_2338238 : Nat := 1200639978607727866771645

theorem tailTrace_2338238 : CollatzResearch.WordTrace tailWord_2338238 prefixEnd_2338238 1200639978607727866771645 := by
  unfold tailWord_2338238
  simp only [CollatzResearch.WordTrace]
  refine ⟨10660318262871317512810921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56855030735313693401658245 10660318262871317512810921)
  ·
    refine ⟨7995238697153488134608191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10660318262871317512810921 7995238697153488134608191)
    ·
      refine ⟨11992858045730232201912287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7995238697153488134608191 11992858045730232201912287)
      ·
        refine ⟨17989287068595348302868431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11992858045730232201912287 17989287068595348302868431)
        ·
          refine ⟨26983930602893022454302647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17989287068595348302868431 26983930602893022454302647)
          ·
            refine ⟨40475895904339533681453971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26983930602893022454302647 40475895904339533681453971)
            ·
              refine ⟨60713843856509300522180957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40475895904339533681453971 60713843856509300522180957)
              ·
                refine ⟨22767691446190987695817859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60713843856509300522180957 22767691446190987695817859)
                ·
                  refine ⟨34151537169286481543726789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22767691446190987695817859 34151537169286481543726789)
                  ·
                    refine ⟨6403413219241215289448773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34151537169286481543726789 6403413219241215289448773)
                    ·
                      refine ⟨1200639978607727866771645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6403413219241215289448773 1200639978607727866771645)
                      ·
                        rfl

theorem cell23_2338238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_2338238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338238 prefixEnd_2338238 := by exact prefixLift 2338238
  have htrace : WordTrace (prefixWord ++ tailWord_2338238) baseStart_2338238 baseEnd_2338238 := by
    simpa [prefixWord, tailWord_2338238, baseEnd_2338238] using wordTrace_append hprefix tailTrace_2338238
  have hstable : (prefixWord ++ tailWord_2338238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338238).length < 2 ^ (prefixWord ++ tailWord_2338238).sum := by decide
  have hdescent : baseEnd_2338238 < baseStart_2338238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338282 : List Nat := [3, 1, 3, 1, 4, 1, 1, 4, 5]
def baseStart_2338282 : Nat := 118140960795 + 2338282 * 2 ^ 59
def prefixEnd_2338282 : Nat := 4983230072969 + 3 ^ 40 * 2338282 * 2
def baseEnd_2338282 : Nat := 133406952417391743846827

theorem tailTrace_2338282 : CollatzResearch.WordTrace tailWord_2338282 prefixEnd_2338282 133406952417391743846827 := by
  unfold tailWord_2338282
  simp only [CollatzResearch.WordTrace]
  refine ⟨21321037728702783904272275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56856100609874090411392733 21321037728702783904272275)
  ·
    refine ⟨31981556593054175856408413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21321037728702783904272275 31981556593054175856408413)
    ·
      refine ⟨11993083722395315946153155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31981556593054175856408413 11993083722395315946153155)
      ·
        refine ⟨17989625583592973919229733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11993083722395315946153155 17989625583592973919229733)
        ·
          refine ⟨3373054796923682609855575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17989625583592973919229733 3373054796923682609855575)
          ·
            refine ⟨5059582195385523914783363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3373054796923682609855575 5059582195385523914783363)
            ·
              refine ⟨7589373293078285872175045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5059582195385523914783363 7589373293078285872175045)
              ·
                refine ⟨1423007492452178601032821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7589373293078285872175045 1423007492452178601032821)
                ·
                  refine ⟨133406952417391743846827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1423007492452178601032821 133406952417391743846827)
                  ·
                    rfl

theorem cell23_2338282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 5].length) (baseStart_2338282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338282 prefixEnd_2338282 := by exact prefixLift 2338282
  have htrace : WordTrace (prefixWord ++ tailWord_2338282) baseStart_2338282 baseEnd_2338282 := by
    simpa [prefixWord, tailWord_2338282, baseEnd_2338282] using wordTrace_append hprefix tailTrace_2338282
  have hstable : (prefixWord ++ tailWord_2338282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338282).length < 2 ^ (prefixWord ++ tailWord_2338282).sum := by decide
  have hdescent : baseEnd_2338282 < baseStart_2338282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338288 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 5]
def baseStart_2338288 : Nat := 118140960795 + 2338288 * 2 ^ 59
def prefixEnd_2338288 : Nat := 4983230072969 + 3 ^ 40 * 2338288 * 2
def baseEnd_2338288 : Nat := 1200665652640452671146415

theorem tailTrace_2338288 : CollatzResearch.WordTrace tailWord_2338288 prefixEnd_2338288 1200665652640452671146415 := by
  unfold tailWord_2338288
  simp only [CollatzResearch.WordTrace]
  refine ⟨42642184876394699320903759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56856246501859599094538345 42642184876394699320903759)
  ·
    refine ⟨63963277314592048981355639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42642184876394699320903759 63963277314592048981355639)
    ·
      refine ⟨95944915971888073472033459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63963277314592048981355639 95944915971888073472033459)
      ·
        refine ⟨143917373957832110208050189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95944915971888073472033459 143917373957832110208050189)
        ·
          refine ⟨53969015234187041328018821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143917373957832110208050189 53969015234187041328018821)
          ·
            refine ⟨10119190356410070249003529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53969015234187041328018821 10119190356410070249003529)
            ·
              refine ⟨7589392767307552686752647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10119190356410070249003529 7589392767307552686752647)
              ·
                refine ⟨11384089150961329030128971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7589392767307552686752647 11384089150961329030128971)
                ·
                  refine ⟨17076133726441993545193457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11384089150961329030128971 17076133726441993545193457)
                  ·
                    refine ⟨12807100294831495158895093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17076133726441993545193457 12807100294831495158895093)
                    ·
                      refine ⟨1200665652640452671146415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12807100294831495158895093 1200665652640452671146415)
                      ·
                        rfl

theorem cell23_2338288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_2338288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338288 prefixEnd_2338288 := by exact prefixLift 2338288
  have htrace : WordTrace (prefixWord ++ tailWord_2338288) baseStart_2338288 baseEnd_2338288 := by
    simpa [prefixWord, tailWord_2338288, baseEnd_2338288] using wordTrace_append hprefix tailTrace_2338288
  have hstable : (prefixWord ++ tailWord_2338288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338288).length < 2 ^ (prefixWord ++ tailWord_2338288).sum := by decide
  have hdescent : baseEnd_2338288 < baseStart_2338288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338298 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4]
def baseStart_2338298 : Nat := 118140960795 + 2338298 * 2 ^ 59
def prefixEnd_2338298 : Nat := 4983230072969 + 3 ^ 40 * 2338298 * 2
def baseEnd_2338298 : Nat := 1200670787446997632021369

theorem tailTrace_2338298 : CollatzResearch.WordTrace tailWord_2338298 prefixEnd_2338298 1200670787446997632021369 := by
  unfold tailWord_2338298
  simp only [CollatzResearch.WordTrace]
  refine ⟨21321183620688292587417887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56856489655168780233114365 21321183620688292587417887)
  ·
    refine ⟨31981775431032438881126831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21321183620688292587417887 31981775431032438881126831)
    ·
      refine ⟨47972663146548658321690247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31981775431032438881126831 47972663146548658321690247)
      ·
        refine ⟨71958994719822987482535371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47972663146548658321690247 71958994719822987482535371)
        ·
          refine ⟨107938492079734481223803057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71958994719822987482535371 107938492079734481223803057)
          ·
            refine ⟨80953869059800860917852293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107938492079734481223803057 80953869059800860917852293)
            ·
              refine ⟨15178850448712661422097305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80953869059800860917852293 15178850448712661422097305)
              ·
                refine ⟨11384137836534496066572979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15178850448712661422097305 11384137836534496066572979)
                ·
                  refine ⟨17076206754801744099859469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11384137836534496066572979 17076206754801744099859469)
                  ·
                    refine ⟨6403577533050654037447301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17076206754801744099859469 6403577533050654037447301)
                    ·
                      refine ⟨1200670787446997632021369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6403577533050654037447301 1200670787446997632021369)
                      ·
                        rfl

theorem cell23_2338298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_2338298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338298 prefixEnd_2338298 := by exact prefixLift 2338298
  have htrace : WordTrace (prefixWord ++ tailWord_2338298) baseStart_2338298 baseEnd_2338298 := by
    simpa [prefixWord, tailWord_2338298, baseEnd_2338298] using wordTrace_append hprefix tailTrace_2338298
  have hstable : (prefixWord ++ tailWord_2338298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338298).length < 2 ^ (prefixWord ++ tailWord_2338298).sum := by decide
  have hdescent : baseEnd_2338298 < baseStart_2338298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338315 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 4]
def baseStart_2338315 : Nat := 118140960795 + 2338315 * 2 ^ 59
def prefixEnd_2338315 : Nat := 4983230072969 + 3 ^ 40 * 2338315 * 2
def baseEnd_2338315 : Nat := 1200679516618124065508791

theorem tailTrace_2338315 : CollatzResearch.WordTrace tailWord_2338315 prefixEnd_2338315 1200679516618124065508791 := by
  unfold tailWord_2338315
  simp only [CollatzResearch.WordTrace]
  refine ⟨85285354523691582253040399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56856903015794388168693599 85285354523691582253040399)
  ·
    refine ⟨127928031785537373379560599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85285354523691582253040399 127928031785537373379560599)
    ·
      refine ⟨191892047678306060069340899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127928031785537373379560599 191892047678306060069340899)
      ·
        refine ⟨287838071517459090104011349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191892047678306060069340899 287838071517459090104011349)
        ·
          refine ⟨3373102400595223712156383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 287838071517459090104011349 3373102400595223712156383)
          ·
            refine ⟨5059653600892835568234575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3373102400595223712156383 5059653600892835568234575)
            ·
              refine ⟨7589480401339253352351863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5059653600892835568234575 7589480401339253352351863)
              ·
                refine ⟨11384220602008880028527795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7589480401339253352351863 11384220602008880028527795)
                ·
                  refine ⟨17076330903013320042791693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11384220602008880028527795 17076330903013320042791693)
                  ·
                    refine ⟨6403624088629995016046885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17076330903013320042791693 6403624088629995016046885)
                    ·
                      refine ⟨1200679516618124065508791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6403624088629995016046885 1200679516618124065508791)
                      ·
                        rfl

theorem cell23_2338315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 4].length) (baseStart_2338315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338315 prefixEnd_2338315 := by exact prefixLift 2338315
  have htrace : WordTrace (prefixWord ++ tailWord_2338315) baseStart_2338315 baseEnd_2338315 := by
    simpa [prefixWord, tailWord_2338315, baseEnd_2338315] using wordTrace_append hprefix tailTrace_2338315
  have hstable : (prefixWord ++ tailWord_2338315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338315).length < 2 ^ (prefixWord ++ tailWord_2338315).sum := by decide
  have hdescent : baseEnd_2338315 < baseStart_2338315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338335 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 3]
def baseStart_2338335 : Nat := 118140960795 + 2338335 * 2 ^ 59
def prefixEnd_2338335 : Nat := 4983230072969 + 3 ^ 40 * 2338335 * 2
def baseEnd_2338335 : Nat := 1200689786231213987258699

theorem tailTrace_2338335 : CollatzResearch.WordTrace tailWord_2338335 prefixEnd_2338335 1200689786231213987258699 := by
  unfold tailWord_2338335
  simp only [CollatzResearch.WordTrace]
  refine ⟨85286083983619125668768459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56857389322412750445845639 85286083983619125668768459)
  ·
    refine ⟨127929125975428688503152689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85286083983619125668768459 127929125975428688503152689)
    ·
      refine ⟨95946844481571516377364517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127929125975428688503152689 95946844481571516377364517)
      ·
        refine ⟨17990033340294659320755847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95946844481571516377364517 17990033340294659320755847)
        ·
          refine ⟨26985050010441988981133771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17990033340294659320755847 26985050010441988981133771)
          ·
            refine ⟨40477575015662983471700657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26985050010441988981133771 40477575015662983471700657)
            ·
              refine ⟨30358181261747237603775493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40477575015662983471700657 30358181261747237603775493)
              ·
                refine ⟨5692158986577607050707905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30358181261747237603775493 5692158986577607050707905)
                ·
                  refine ⟨4269119239933205288030929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5692158986577607050707905 4269119239933205288030929)
                  ·
                    refine ⟨3201839429949903966023197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4269119239933205288030929 3201839429949903966023197)
                    ·
                      refine ⟨1200689786231213987258699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3201839429949903966023197 1200689786231213987258699)
                      ·
                        rfl

theorem cell23_2338335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_2338335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338335 prefixEnd_2338335 := by exact prefixLift 2338335
  have htrace : WordTrace (prefixWord ++ tailWord_2338335) baseStart_2338335 baseEnd_2338335 := by
    simpa [prefixWord, tailWord_2338335, baseEnd_2338335] using wordTrace_append hprefix tailTrace_2338335
  have hstable : (prefixWord ++ tailWord_2338335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338335).length < 2 ^ (prefixWord ++ tailWord_2338335).sum := by decide
  have hdescent : baseEnd_2338335 < baseStart_2338335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338385 : List Nat := [1, 2, 2, 1, 3, 2, 1, 5, 1, 5]
def baseStart_2338385 : Nat := 118140960795 + 2338385 * 2 ^ 59
def prefixEnd_2338385 : Nat := 4983230072969 + 3 ^ 40 * 2338385 * 2
def baseEnd_2338385 : Nat := 400238486754646263877823

theorem tailTrace_2338385 : CollatzResearch.WordTrace tailWord_2338385 prefixEnd_2338385 400238486754646263877823 := by
  unfold tailWord_2338385
  simp only [CollatzResearch.WordTrace]
  refine ⟨85287907633437984208088609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56858605088958656138725739 85287907633437984208088609)
  ·
    refine ⟨63965930725078488156066457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85287907633437984208088609 63965930725078488156066457)
    ·
      refine ⟨47974448043808866117049843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63965930725078488156066457 47974448043808866117049843)
      ·
        refine ⟨71961672065713299175574765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47974448043808866117049843 71961672065713299175574765)
        ·
          refine ⟨26985627024642487190840537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71961672065713299175574765 26985627024642487190840537)
          ·
            refine ⟨20239220268481865393130403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26985627024642487190840537 20239220268481865393130403)
            ·
              refine ⟨30358830402722798089695605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20239220268481865393130403 30358830402722798089695605)
              ·
                refine ⟨2846140350255262320908963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30358830402722798089695605 2846140350255262320908963)
                ·
                  refine ⟨4269210525382893481363445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2846140350255262320908963 4269210525382893481363445)
                  ·
                    refine ⟨400238486754646263877823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4269210525382893481363445 400238486754646263877823)
                    ·
                      rfl

theorem cell23_2338385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_2338385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338385 prefixEnd_2338385 := by exact prefixLift 2338385
  have htrace : WordTrace (prefixWord ++ tailWord_2338385) baseStart_2338385 baseEnd_2338385 := by
    simpa [prefixWord, tailWord_2338385, baseEnd_2338385] using wordTrace_append hprefix tailTrace_2338385
  have hstable : (prefixWord ++ tailWord_2338385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338385).length < 2 ^ (prefixWord ++ tailWord_2338385).sum := by decide
  have hdescent : baseEnd_2338385 < baseStart_2338385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338439 : List Nat := [1, 1, 4, 2, 1, 4, 3, 1, 1, 1, 4]
def baseStart_2338439 : Nat := 118140960795 + 2338439 * 2 ^ 59
def prefixEnd_2338439 : Nat := 4983230072969 + 3 ^ 40 * 2338439 * 2
def baseEnd_2338439 : Nat := 1200743188219281580358221

theorem tailTrace_2338439 : CollatzResearch.WordTrace tailWord_2338439 prefixEnd_2338439 1200743188219281580358221 := by
  unfold tailWord_2338439
  simp only [CollatzResearch.WordTrace]
  refine ⟨85289877175242351430554371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56859918116828234287036247 85289877175242351430554371)
  ·
    refine ⟨127934815762863527145831557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85289877175242351430554371 127934815762863527145831557)
    ·
      refine ⟨23987777955536911339843417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127934815762863527145831557 23987777955536911339843417)
      ·
        refine ⟨17990833466652683504882563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23987777955536911339843417 17990833466652683504882563)
        ·
          refine ⟨26986250199979025257323845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17990833466652683504882563 26986250199979025257323845)
          ·
            refine ⟨5059921912496067235748221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26986250199979025257323845 5059921912496067235748221)
            ·
              refine ⟨1897470717186025213405583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5059921912496067235748221 1897470717186025213405583)
              ·
                refine ⟨2846206075779037820108375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1897470717186025213405583 2846206075779037820108375)
                ·
                  refine ⟨4269309113668556730162563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2846206075779037820108375 4269309113668556730162563)
                  ·
                    refine ⟨6403963670502835095243845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4269309113668556730162563 6403963670502835095243845)
                    ·
                      refine ⟨1200743188219281580358221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6403963670502835095243845 1200743188219281580358221)
                      ·
                        rfl

theorem cell23_2338439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_2338439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338439 prefixEnd_2338439 := by exact prefixLift 2338439
  have htrace : WordTrace (prefixWord ++ tailWord_2338439) baseStart_2338439 baseEnd_2338439 := by
    simpa [prefixWord, tailWord_2338439, baseEnd_2338439] using wordTrace_append hprefix tailTrace_2338439
  have hstable : (prefixWord ++ tailWord_2338439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338439).length < 2 ^ (prefixWord ++ tailWord_2338439).sum := by decide
  have hdescent : baseEnd_2338439 < baseStart_2338439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338442 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 1, 1, 5]
def baseStart_2338442 : Nat := 118140960795 + 2338442 * 2 ^ 59
def prefixEnd_2338442 : Nat := 4983230072969 + 3 ^ 40 * 2338442 * 2
def baseEnd_2338442 : Nat := 1200744728661245068620707

theorem tailTrace_2338442 : CollatzResearch.WordTrace tailWord_2338442 prefixEnd_2338442 1200744728661245068620707 := by
  unfold tailWord_2338442
  simp only [CollatzResearch.WordTrace]
  refine ⟨21322496648557870735728395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56859991062820988628609053 21322496648557870735728395)
  ·
    refine ⟨31983744972836806103592593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21322496648557870735728395 31983744972836806103592593)
    ·
      refine ⟨23987808729627604577694445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31983744972836806103592593 23987808729627604577694445)
      ·
        refine ⟨8995428273610351716635417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23987808729627604577694445 8995428273610351716635417)
        ·
          refine ⟨6746571205207763787476563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8995428273610351716635417 6746571205207763787476563)
          ·
            refine ⟨10119856807811645681214845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6746571205207763787476563 10119856807811645681214845)
            ·
              refine ⟨3794946302929367130455567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10119856807811645681214845 3794946302929367130455567)
              ·
                refine ⟨5692419454394050695683351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3794946302929367130455567 5692419454394050695683351)
                ·
                  refine ⟨8538629181591076043525027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5692419454394050695683351 8538629181591076043525027)
                  ·
                    refine ⟨12807943772386614065287541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8538629181591076043525027 12807943772386614065287541)
                    ·
                      refine ⟨1200744728661245068620707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12807943772386614065287541 1200744728661245068620707)
                      ·
                        rfl

theorem cell23_2338442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_2338442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338442 prefixEnd_2338442 := by exact prefixLift 2338442
  have htrace : WordTrace (prefixWord ++ tailWord_2338442) baseStart_2338442 baseEnd_2338442 := by
    simpa [prefixWord, tailWord_2338442, baseEnd_2338442] using wordTrace_append hprefix tailTrace_2338442
  have hstable : (prefixWord ++ tailWord_2338442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338442).length < 2 ^ (prefixWord ++ tailWord_2338442).sum := by decide
  have hdescent : baseEnd_2338442 < baseStart_2338442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338450 : List Nat := [3, 2, 3, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_2338450 : Nat := 118140960795 + 2338450 * 2 ^ 59
def prefixEnd_2338450 : Nat := 4983230072969 + 3 ^ 40 * 2338450 * 2
def baseEnd_2338450 : Nat := 1200748836506481037320671

theorem tailTrace_2338450 : CollatzResearch.WordTrace tailWord_2338450 prefixEnd_2338450 1200748836506481037320671 := by
  unfold tailWord_2338450
  simp only [CollatzResearch.WordTrace]
  refine ⟨21322569594550625077301201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56860185585468333539469869 21322569594550625077301201)
  ·
    refine ⟨15991927195912968807975901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21322569594550625077301201 15991927195912968807975901)
    ·
      refine ⟨5996972698467363302990963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15991927195912968807975901 5996972698467363302990963)
      ·
        refine ⟨8995459047701044954486445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5996972698467363302990963 8995459047701044954486445)
        ·
          refine ⟨3373297142887891857932417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8995459047701044954486445 3373297142887891857932417)
          ·
            refine ⟨2529972857165918893449313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3373297142887891857932417 2529972857165918893449313)
            ·
              refine ⟨1897479642874439170086985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2529972857165918893449313 1897479642874439170086985)
              ·
                refine ⟨1423109732155829377565239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1897479642874439170086985 1423109732155829377565239)
                ·
                  refine ⟨2134664598233744066347859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1423109732155829377565239 2134664598233744066347859)
                  ·
                    refine ⟨3201996897350616099521789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2134664598233744066347859 3201996897350616099521789)
                    ·
                      refine ⟨1200748836506481037320671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3201996897350616099521789 1200748836506481037320671)
                      ·
                        rfl

theorem cell23_2338450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_2338450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338450 prefixEnd_2338450 := by exact prefixLift 2338450
  have htrace : WordTrace (prefixWord ++ tailWord_2338450) baseStart_2338450 baseEnd_2338450 := by
    simpa [prefixWord, tailWord_2338450, baseEnd_2338450] using wordTrace_append hprefix tailTrace_2338450
  have hstable : (prefixWord ++ tailWord_2338450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338450).length < 2 ^ (prefixWord ++ tailWord_2338450).sum := by decide
  have hdescent : baseEnd_2338450 < baseStart_2338450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338462 : List Nat := [4, 3, 1, 1, 1, 2, 3, 8]
def baseStart_2338462 : Nat := 118140960795 + 2338462 * 2 ^ 59
def prefixEnd_2338462 : Nat := 4983230072969 + 3 ^ 40 * 2338462 * 2
def baseEnd_2338462 : Nat := 44472407343493888532245

theorem tailTrace_2338462 : CollatzResearch.WordTrace tailWord_2338462 prefixEnd_2338462 44472407343493888532245 := by
  unfold tailWord_2338462
  simp only [CollatzResearch.WordTrace]
  refine ⟨10661339506769878294830205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56860477369439350905761093 10661339506769878294830205)
  ·
    refine ⟨3998002315038704360561327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10661339506769878294830205 3998002315038704360561327)
    ·
      refine ⟨5997003472558056540841991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3998002315038704360561327 5997003472558056540841991)
      ·
        refine ⟨8995505208837084811262987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5997003472558056540841991 8995505208837084811262987)
        ·
          refine ⟨13493257813255627216894481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8995505208837084811262987 13493257813255627216894481)
          ·
            refine ⟨10119943359941720412670861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13493257813255627216894481 10119943359941720412670861)
            ·
              refine ⟨3794978759978145154751573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10119943359941720412670861 3794978759978145154751573)
              ·
                refine ⟨44472407343493888532245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3794978759978145154751573 44472407343493888532245)
                ·
                  rfl

theorem cell23_2338462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 8].length) (baseStart_2338462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338462 prefixEnd_2338462 := by exact prefixLift 2338462
  have htrace : WordTrace (prefixWord ++ tailWord_2338462) baseStart_2338462 baseEnd_2338462 := by
    simpa [prefixWord, tailWord_2338462, baseEnd_2338462] using wordTrace_append hprefix tailTrace_2338462
  have hstable : (prefixWord ++ tailWord_2338462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338462).length < 2 ^ (prefixWord ++ tailWord_2338462).sum := by decide
  have hdescent : baseEnd_2338462 < baseStart_2338462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338515 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 3]
def baseStart_2338515 : Nat := 118140960795 + 2338515 * 2 ^ 59
def prefixEnd_2338515 : Nat := 4983230072969 + 3 ^ 40 * 2338515 * 2
def baseEnd_2338515 : Nat := 1200782212749023283007871

theorem tailTrace_2338515 : CollatzResearch.WordTrace tailWord_2338515 prefixEnd_2338515 1200782212749023283007871 := by
  unfold tailWord_2338515
  simp only [CollatzResearch.WordTrace]
  refine ⟨85292649122967016410320999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56861766081978010940213999 85292649122967016410320999)
  ·
    refine ⟨127938973684450524615481499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85292649122967016410320999 127938973684450524615481499)
    ·
      refine ⟨191908460526675786923222249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127938973684450524615481499 191908460526675786923222249)
      ·
        refine ⟨143931345395006840192416687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191908460526675786923222249 143931345395006840192416687)
        ·
          refine ⟨215897018092510260288625031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143931345395006840192416687 215897018092510260288625031)
          ·
            refine ⟨323845527138765390432937547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215897018092510260288625031 323845527138765390432937547)
            ·
              refine ⟨485768290708148085649406321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323845527138765390432937547 485768290708148085649406321)
              ·
                refine ⟨364326218031111064237054741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485768290708148085649406321 364326218031111064237054741)
                ·
                  refine ⟨17077791470208331136111941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 364326218031111064237054741 17077791470208331136111941)
                  ·
                    refine ⟨3202085900664062088020989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17077791470208331136111941 3202085900664062088020989)
                    ·
                      refine ⟨1200782212749023283007871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3202085900664062088020989 1200782212749023283007871)
                      ·
                        rfl

theorem cell23_2338515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 3].length) (baseStart_2338515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338515 prefixEnd_2338515 := by exact prefixLift 2338515
  have htrace : WordTrace (prefixWord ++ tailWord_2338515) baseStart_2338515 baseEnd_2338515 := by
    simpa [prefixWord, tailWord_2338515, baseEnd_2338515] using wordTrace_append hprefix tailTrace_2338515
  have hstable : (prefixWord ++ tailWord_2338515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338515).length < 2 ^ (prefixWord ++ tailWord_2338515).sum := by decide
  have hdescent : baseEnd_2338515 < baseStart_2338515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338552 : List Nat := [2, 1, 2, 1, 1, 2, 2, 7, 5]
def baseStart_2338552 : Nat := 118140960795 + 2338552 * 2 ^ 59
def prefixEnd_2338552 : Nat := 4983230072969 + 3 ^ 40 * 2338552 * 2
def baseEnd_2338552 : Nat := 133422356837026626471689

theorem tailTrace_2338552 : CollatzResearch.WordTrace tailWord_2338552 prefixEnd_2338552 133422356837026626471689 := by
  unfold tailWord_2338552
  simp only [CollatzResearch.WordTrace]
  refine ⟨42646999311916485864708955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56862665749221981152945273 42646999311916485864708955)
  ·
    refine ⟨63970498967874728797063433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42646999311916485864708955 63970498967874728797063433)
    ·
      refine ⟨47977874225906046597797575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63970498967874728797063433 47977874225906046597797575)
      ·
        refine ⟨71966811338859069896696363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47977874225906046597797575 71966811338859069896696363)
        ·
          refine ⟨107950217008288604845044545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71966811338859069896696363 107950217008288604845044545)
          ·
            refine ⟨80962662756216453633783409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107950217008288604845044545 80962662756216453633783409)
            ·
              refine ⟨60721997067162340225337557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80962662756216453633783409 60721997067162340225337557)
              ·
                refine ⟨1423171806261617349031349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 60721997067162340225337557 1423171806261617349031349)
                ·
                  refine ⟨133422356837026626471689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1423171806261617349031349 133422356837026626471689)
                  ·
                    rfl

theorem cell23_2338552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 5].length) (baseStart_2338552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338552 prefixEnd_2338552 := by exact prefixLift 2338552
  have htrace : WordTrace (prefixWord ++ tailWord_2338552) baseStart_2338552 baseEnd_2338552 := by
    simpa [prefixWord, tailWord_2338552, baseEnd_2338552] using wordTrace_append hprefix tailTrace_2338552
  have hstable : (prefixWord ++ tailWord_2338552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338552).length < 2 ^ (prefixWord ++ tailWord_2338552).sum := by decide
  have hdescent : baseEnd_2338552 < baseStart_2338552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338562 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_2338562 : Nat := 118140960795 + 2338562 * 2 ^ 59
def prefixEnd_2338562 : Nat := 4983230072969 + 3 ^ 40 * 2338562 * 2
def baseEnd_2338562 : Nat := 1200806346339784599120155

theorem tailTrace_2338562 : CollatzResearch.WordTrace tailWord_2338562 prefixEnd_2338562 1200806346339784599120155 := by
  unfold tailWord_2338562
  simp only [CollatzResearch.WordTrace]
  refine ⟨21323590838449185859320485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56862908902531162291521293 21323590838449185859320485)
  ·
    refine ⟨3998173282209222348622591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21323590838449185859320485 3998173282209222348622591)
    ·
      refine ⟨5997259923313833522933887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3998173282209222348622591 5997259923313833522933887)
      ·
        refine ⟨8995889884970750284400831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5997259923313833522933887 8995889884970750284400831)
        ·
          refine ⟨13493834827456125426601247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8995889884970750284400831 13493834827456125426601247)
          ·
            refine ⟨20240752241184188139901871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13493834827456125426601247 20240752241184188139901871)
            ·
              refine ⟨30361128361776282209852807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20240752241184188139901871 30361128361776282209852807)
              ·
                refine ⟨45541692542664423314779211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30361128361776282209852807 45541692542664423314779211)
                ·
                  refine ⟨68312538813996634972168817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45541692542664423314779211 68312538813996634972168817)
                  ·
                    refine ⟨51234404110497476229126613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68312538813996634972168817 51234404110497476229126613)
                    ·
                      refine ⟨1200806346339784599120155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51234404110497476229126613 1200806346339784599120155)
                      ·
                        rfl

theorem cell23_2338562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_2338562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338562 prefixEnd_2338562 := by exact prefixLift 2338562
  have htrace : WordTrace (prefixWord ++ tailWord_2338562) baseStart_2338562 baseEnd_2338562 := by
    simpa [prefixWord, tailWord_2338562, baseEnd_2338562] using wordTrace_append hprefix tailTrace_2338562
  have hstable : (prefixWord ++ tailWord_2338562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338562).length < 2 ^ (prefixWord ++ tailWord_2338562).sum := by decide
  have hdescent : baseEnd_2338562 < baseStart_2338562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338595 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 2, 8]
def baseStart_2338595 : Nat := 118140960795 + 2338595 * 2 ^ 59
def prefixEnd_2338595 : Nat := 4983230072969 + 3 ^ 40 * 2338595 * 2
def baseEnd_2338595 : Nat := 400274430400460990002501

theorem tailTrace_2338595 : CollatzResearch.WordTrace tailWord_2338595 prefixEnd_2338595 400274430400460990002501 := by
  unfold tailWord_2338595
  simp only [CollatzResearch.WordTrace]
  refine ⟨85295566962677190073233239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56863711308451460048822159 85295566962677190073233239)
  ·
    refine ⟨127943350444015785109849859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85295566962677190073233239 127943350444015785109849859)
    ·
      refine ⟨191915025666023677664774789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127943350444015785109849859 191915025666023677664774789)
      ·
        refine ⟨35984067312379439562145273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191915025666023677664774789 35984067312379439562145273)
        ·
          refine ⟨26988050484284579671608955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35984067312379439562145273 26988050484284579671608955)
          ·
            refine ⟨40482075726426869507413433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26988050484284579671608955 40482075726426869507413433)
            ·
              refine ⟨30361556794820152130560075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40482075726426869507413433 30361556794820152130560075)
              ·
                refine ⟨45542335192230228195840113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30361556794820152130560075 45542335192230228195840113)
                ·
                  refine ⟨34156751394172671146880085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45542335192230228195840113 34156751394172671146880085)
                  ·
                    refine ⟨400274430400460990002501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34156751394172671146880085 400274430400460990002501)
                    ·
                      rfl

theorem cell23_2338595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 8].length) (baseStart_2338595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338595 prefixEnd_2338595 := by exact prefixLift 2338595
  have htrace : WordTrace (prefixWord ++ tailWord_2338595) baseStart_2338595 baseEnd_2338595 := by
    simpa [prefixWord, tailWord_2338595, baseEnd_2338595] using wordTrace_append hprefix tailTrace_2338595
  have hstable : (prefixWord ++ tailWord_2338595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338595).length < 2 ^ (prefixWord ++ tailWord_2338595).sum := by decide
  have hdescent : baseEnd_2338595 < baseStart_2338595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338636 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 2, 4, 2]
def baseStart_2338636 : Nat := 118140960795 + 2338636 * 2 ^ 59
def prefixEnd_2338636 : Nat := 4983230072969 + 3 ^ 40 * 2338636 * 2
def baseEnd_2338636 : Nat := 1200844343908217309594815

theorem tailTrace_2338636 : CollatzResearch.WordTrace tailWord_2338636 prefixEnd_2338636 1200844343908217309594815 := by
  unfold tailWord_2338636
  simp only [CollatzResearch.WordTrace]
  refine ⟨42648531177764327037737881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56864708237019102716983841 42648531177764327037737881)
  ·
    refine ⟨31986398383323245278303411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42648531177764327037737881 31986398383323245278303411)
    ·
      refine ⟨47979597574984867917455117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31986398383323245278303411 47979597574984867917455117)
      ·
        refine ⟨17992349090619325469045669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47979597574984867917455117 17992349090619325469045669)
        ·
          refine ⟨3373565454491123525446063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17992349090619325469045669 3373565454491123525446063)
          ·
            refine ⟨5060348181736685288169095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3373565454491123525446063 5060348181736685288169095)
            ·
              refine ⟨7590522272605027932253643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5060348181736685288169095 7590522272605027932253643)
              ·
                refine ⟨11385783408907541898380465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7590522272605027932253643 11385783408907541898380465)
                ·
                  refine ⟨8539337556680656423785349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11385783408907541898380465 8539337556680656423785349)
                  ·
                    refine ⟨1601125791877623079459753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8539337556680656423785349 1601125791877623079459753)
                    ·
                      refine ⟨1200844343908217309594815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1601125791877623079459753 1200844343908217309594815)
                      ·
                        rfl

theorem cell23_2338636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_2338636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338636 prefixEnd_2338636 := by exact prefixLift 2338636
  have htrace : WordTrace (prefixWord ++ tailWord_2338636) baseStart_2338636 baseEnd_2338636 := by
    simpa [prefixWord, tailWord_2338636, baseEnd_2338636] using wordTrace_append hprefix tailTrace_2338636
  have hstable : (prefixWord ++ tailWord_2338636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338636).length < 2 ^ (prefixWord ++ tailWord_2338636).sum := by decide
  have hdescent : baseEnd_2338636 < baseStart_2338636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338656 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 3]
def baseStart_2338656 : Nat := 118140960795 + 2338656 * 2 ^ 59
def prefixEnd_2338656 : Nat := 4983230072969 + 3 ^ 40 * 2338656 * 2
def baseEnd_2338656 : Nat := 1200854613521307231344723

theorem tailTrace_2338656 : CollatzResearch.WordTrace tailWord_2338656 prefixEnd_2338656 1200854613521307231344723 := by
  unfold tailWord_2338656
  simp only [CollatzResearch.WordTrace]
  refine ⟨42648895907728098745601911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56865194543637464994135881 42648895907728098745601911)
  ·
    refine ⟨63973343861592148118402867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42648895907728098745601911 63973343861592148118402867)
    ·
      refine ⟨95960015792388222177604301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63973343861592148118402867 95960015792388222177604301)
      ·
        refine ⟨35985005922145583316601613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95960015792388222177604301 35985005922145583316601613)
        ·
          refine ⟨13494377220804593743725605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35985005922145583316601613 13494377220804593743725605)
          ·
            refine ⟨2530195728900861326948551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13494377220804593743725605 2530195728900861326948551)
            ·
              refine ⟨3795293593351291990422827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2530195728900861326948551 3795293593351291990422827)
              ·
                refine ⟨5692940390026937985634241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3795293593351291990422827 5692940390026937985634241)
                ·
                  refine ⟨4269705292520203489225681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5692940390026937985634241 4269705292520203489225681)
                  ·
                    refine ⟨3202278969390152616919261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4269705292520203489225681 3202278969390152616919261)
                    ·
                      refine ⟨1200854613521307231344723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3202278969390152616919261 1200854613521307231344723)
                      ·
                        rfl

theorem cell23_2338656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_2338656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338656 prefixEnd_2338656 := by exact prefixLift 2338656
  have htrace : WordTrace (prefixWord ++ tailWord_2338656) baseStart_2338656 baseEnd_2338656 := by
    simpa [prefixWord, tailWord_2338656, baseEnd_2338656] using wordTrace_append hprefix tailTrace_2338656
  have hstable : (prefixWord ++ tailWord_2338656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338656).length < 2 ^ (prefixWord ++ tailWord_2338656).sum := by decide
  have hdescent : baseEnd_2338656 < baseStart_2338656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338706 : List Nat := [3, 2, 3, 2, 1, 1, 1, 4, 1, 5]
def baseStart_2338706 : Nat := 118140960795 + 2338706 * 2 ^ 59
def prefixEnd_2338706 : Nat := 4983230072969 + 3 ^ 40 * 2338706 * 2
def baseEnd_2338706 : Nat := 400293429184677345239831

theorem tailTrace_2338706 : CollatzResearch.WordTrace tailWord_2338706 prefixEnd_2338706 400293429184677345239831 := by
  unfold tailWord_2338706
  simp only [CollatzResearch.WordTrace]
  refine ⟨21324903866318764007630993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56866410310183370687015981 21324903866318764007630993)
  ·
    refine ⟨15993677899739073005723245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21324903866318764007630993 15993677899739073005723245)
    ·
      refine ⟨5997629212402152377146217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15993677899739073005723245 5997629212402152377146217)
      ·
        refine ⟨4498221909301614282859663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5997629212402152377146217 4498221909301614282859663)
        ·
          refine ⟨6747332863952421424289495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4498221909301614282859663 6747332863952421424289495)
          ·
            refine ⟨10120999295928632136434243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6747332863952421424289495 10120999295928632136434243)
            ·
              refine ⟨15181498943892948204651365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10120999295928632136434243 15181498943892948204651365)
              ·
                refine ⟨2846531051979927788372131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15181498943892948204651365 2846531051979927788372131)
                ·
                  refine ⟨4269796577969891682558197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2846531051979927788372131 4269796577969891682558197)
                  ·
                    refine ⟨400293429184677345239831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4269796577969891682558197 400293429184677345239831)
                    ·
                      rfl

theorem cell23_2338706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_2338706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338706 prefixEnd_2338706 := by exact prefixLift 2338706
  have htrace : WordTrace (prefixWord ++ tailWord_2338706) baseStart_2338706 baseEnd_2338706 := by
    simpa [prefixWord, tailWord_2338706, baseEnd_2338706] using wordTrace_append hprefix tailTrace_2338706
  have hstable : (prefixWord ++ tailWord_2338706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338706).length < 2 ^ (prefixWord ++ tailWord_2338706).sum := by decide
  have hdescent : baseEnd_2338706 < baseStart_2338706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338709 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 2, 6, 2]
def baseStart_2338709 : Nat := 118140960795 + 2338709 * 2 ^ 59
def prefixEnd_2338709 : Nat := 4983230072969 + 3 ^ 40 * 2338709 * 2
def baseEnd_2338709 : Nat := 1200881827995995523981979

theorem tailTrace_2338709 : CollatzResearch.WordTrace tailWord_2338709 prefixEnd_2338709 1200881827995995523981979 := by
  unfold tailWord_2338709
  simp only [CollatzResearch.WordTrace]
  refine ⟨85299724884264187542883181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56866483256176125028588787 85299724884264187542883181)
  ·
    refine ⟨31987396831599070328581193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85299724884264187542883181 31987396831599070328581193)
    ·
      refine ⟨23990547623699302746435895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31987396831599070328581193 23990547623699302746435895)
      ·
        refine ⟨35985821435548954119653843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23990547623699302746435895 35985821435548954119653843)
        ·
          refine ⟨53978732153323431179480765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35985821435548954119653843 53978732153323431179480765)
          ·
            refine ⟨20242024557496286692305287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53978732153323431179480765 20242024557496286692305287)
            ·
              refine ⟨30363036836244430038457931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20242024557496286692305287 30363036836244430038457931)
              ·
                refine ⟨45544555254366645057686897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30363036836244430038457931 45544555254366645057686897)
                ·
                  refine ⟨34158416440774983793265173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45544555254366645057686897 34158416440774983793265173)
                  ·
                    refine ⟨1601175770661327365309305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34158416440774983793265173 1601175770661327365309305)
                    ·
                      refine ⟨1200881827995995523981979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1601175770661327365309305 1200881827995995523981979)
                      ·
                        rfl

theorem cell23_2338709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_2338709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338709 prefixEnd_2338709 := by exact prefixLift 2338709
  have htrace : WordTrace (prefixWord ++ tailWord_2338709) baseStart_2338709 baseEnd_2338709 := by
    simpa [prefixWord, tailWord_2338709, baseEnd_2338709] using wordTrace_append hprefix tailTrace_2338709
  have hstable : (prefixWord ++ tailWord_2338709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338709).length < 2 ^ (prefixWord ++ tailWord_2338709).sum := by decide
  have hdescent : baseEnd_2338709 < baseStart_2338709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338749 : List Nat := [1, 4, 1, 2, 3, 2, 2, 8]
def baseStart_2338749 : Nat := 118140960795 + 2338749 * 2 ^ 59
def prefixEnd_2338749 : Nat := 4983230072969 + 3 ^ 40 * 2338749 * 2
def baseEnd_2338749 : Nat := 44477865452673161758585

theorem tailTrace_2338749 : CollatzResearch.WordTrace tailWord_2338749 prefixEnd_2338749 44477865452673161758585 := by
  unfold tailWord_2338749
  simp only [CollatzResearch.WordTrace]
  refine ⟨85301183804119274374339301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56867455869412849582892867 85301183804119274374339301)
  ·
    refine ⟨15993971963272363945188619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85301183804119274374339301 15993971963272363945188619)
    ·
      refine ⟨23990957944908545917782929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15993971963272363945188619 23990957944908545917782929)
      ·
        refine ⟨17993218458681409438337197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23990957944908545917782929 17993218458681409438337197)
        ·
          refine ⟨6747456922005528539376449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17993218458681409438337197 6747456922005528539376449)
          ·
            refine ⟨5060592691504146404532337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6747456922005528539376449 5060592691504146404532337)
            ·
              refine ⟨3795444518628109803399253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5060592691504146404532337 3795444518628109803399253)
              ·
                refine ⟨44477865452673161758585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3795444518628109803399253 44477865452673161758585)
                ·
                  rfl

theorem cell23_2338749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 8].length) (baseStart_2338749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338749 prefixEnd_2338749 := by exact prefixLift 2338749
  have htrace : WordTrace (prefixWord ++ tailWord_2338749) baseStart_2338749 baseEnd_2338749 := by
    simpa [prefixWord, tailWord_2338749, baseEnd_2338749] using wordTrace_append hprefix tailTrace_2338749
  have hstable : (prefixWord ++ tailWord_2338749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338749).length < 2 ^ (prefixWord ++ tailWord_2338749).sum := by decide
  have hdescent : baseEnd_2338749 < baseStart_2338749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338752 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 6]
def baseStart_2338752 : Nat := 118140960795 + 2338752 * 2 ^ 59
def prefixEnd_2338752 : Nat := 4983230072969 + 3 ^ 40 * 2338752 * 2
def baseEnd_2338752 : Nat := 1200903907664138855744281

theorem tailTrace_2338752 : CollatzResearch.WordTrace tailWord_2338752 prefixEnd_2338752 1200903907664138855744281 := by
  unfold tailWord_2338752
  simp only [CollatzResearch.WordTrace]
  refine ⟨42650646611554202943349255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56867528815405603924465673 42650646611554202943349255)
  ·
    refine ⟨63975969917331304415023883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42650646611554202943349255 63975969917331304415023883)
    ·
      refine ⟨95963954875996956622535825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63975969917331304415023883 95963954875996956622535825)
      ·
        refine ⟨71972966156997717466901869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95963954875996956622535825 71972966156997717466901869)
        ·
          refine ⟨26989862308874144050088201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71972966156997717466901869 26989862308874144050088201)
          ·
            refine ⟨20242396731655608037566151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26989862308874144050088201 20242396731655608037566151)
            ·
              refine ⟨30363595097483412056349227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20242396731655608037566151 30363595097483412056349227)
              ·
                refine ⟨45545392646225118084523841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30363595097483412056349227 45545392646225118084523841)
                ·
                  refine ⟨34159044484668838563392881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45545392646225118084523841 34159044484668838563392881)
                  ·
                    refine ⟨25619283363501628922544661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34159044484668838563392881 25619283363501628922544661)
                    ·
                      refine ⟨1200903907664138855744281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25619283363501628922544661 1200903907664138855744281)
                      ·
                        rfl

theorem cell23_2338752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_2338752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338752 prefixEnd_2338752 := by exact prefixLift 2338752
  have htrace : WordTrace (prefixWord ++ tailWord_2338752) baseStart_2338752 baseEnd_2338752 := by
    simpa [prefixWord, tailWord_2338752, baseEnd_2338752] using wordTrace_append hprefix tailTrace_2338752
  have hstable : (prefixWord ++ tailWord_2338752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338752).length < 2 ^ (prefixWord ++ tailWord_2338752).sum := by decide
  have hdescent : baseEnd_2338752 < baseStart_2338752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338759 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 3]
def baseStart_2338759 : Nat := 118140960795 + 2338759 * 2 ^ 59
def prefixEnd_2338759 : Nat := 4983230072969 + 3 ^ 40 * 2338759 * 2
def baseEnd_2338759 : Nat := 1200907502028720328356749

theorem tailTrace_2338759 : CollatzResearch.WordTrace tailWord_2338759 prefixEnd_2338759 1200907502028720328356749 := by
  unfold tailWord_2338759
  simp only [CollatzResearch.WordTrace]
  refine ⟨85301548534083046082203331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56867699022722030721468887 85301548534083046082203331)
  ·
    refine ⟨127952322801124569123304997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85301548534083046082203331 127952322801124569123304997)
    ·
      refine ⟨23991060525210856710619687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127952322801124569123304997 23991060525210856710619687)
      ·
        refine ⟨35986590787816285065929531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23991060525210856710619687 35986590787816285065929531)
        ·
          refine ⟨53979886181724427598894297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35986590787816285065929531 53979886181724427598894297)
          ·
            refine ⟨40484914636293320699170723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53979886181724427598894297 40484914636293320699170723)
            ·
              refine ⟨60727371954439981048756085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40484914636293320699170723 60727371954439981048756085)
              ·
                refine ⟨5693191120728748223320883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60727371954439981048756085 5693191120728748223320883)
                ·
                  refine ⟨8539786681093122334981325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5693191120728748223320883 8539786681093122334981325)
                  ·
                    refine ⟨3202420005409920875617997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8539786681093122334981325 3202420005409920875617997)
                    ·
                      refine ⟨1200907502028720328356749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3202420005409920875617997 1200907502028720328356749)
                      ·
                        rfl

theorem cell23_2338759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_2338759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338759 prefixEnd_2338759 := by exact prefixLift 2338759
  have htrace : WordTrace (prefixWord ++ tailWord_2338759) baseStart_2338759 baseEnd_2338759 := by
    simpa [prefixWord, tailWord_2338759, baseEnd_2338759] using wordTrace_append hprefix tailTrace_2338759
  have hstable : (prefixWord ++ tailWord_2338759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338759).length < 2 ^ (prefixWord ++ tailWord_2338759).sum := by decide
  have hdescent : baseEnd_2338759 < baseStart_2338759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338809 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 2, 6]
def baseStart_2338809 : Nat := 118140960795 + 2338809 * 2 ^ 59
def prefixEnd_2338809 : Nat := 4983230072969 + 3 ^ 40 * 2338809 * 2
def baseEnd_2338809 : Nat := 400311058687148377577173

theorem tailTrace_2338809 : CollatzResearch.WordTrace tailWord_2338809 prefixEnd_2338809 400311058687148377577173 := by
  unfold tailWord_2338809
  simp only [CollatzResearch.WordTrace]
  refine ⟨85303372183901904621523481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56868914789267936414348987 85303372183901904621523481)
  ·
    refine ⟨63977529137926428466142611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85303372183901904621523481 63977529137926428466142611)
    ·
      refine ⟨95966293706889642699213917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63977529137926428466142611 95966293706889642699213917)
      ·
        refine ⟨35987360140083616012205219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95966293706889642699213917 35987360140083616012205219)
        ·
          refine ⟨53981040210125424018307829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35987360140083616012205219 53981040210125424018307829)
          ·
            refine ⟨5060722519699258501716359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53981040210125424018307829 5060722519699258501716359)
            ·
              refine ⟨7591083779548887752574539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5060722519699258501716359 7591083779548887752574539)
              ·
                refine ⟨11386625669323331628861809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7591083779548887752574539 11386625669323331628861809)
                ·
                  refine ⟨8539969251992498721646357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11386625669323331628861809 8539969251992498721646357)
                  ·
                    refine ⟨400311058687148377577173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8539969251992498721646357 400311058687148377577173)
                    ·
                      rfl

theorem cell23_2338809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 6].length) (baseStart_2338809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338809 prefixEnd_2338809 := by exact prefixLift 2338809
  have htrace : WordTrace (prefixWord ++ tailWord_2338809) baseStart_2338809 baseEnd_2338809 := by
    simpa [prefixWord, tailWord_2338809, baseEnd_2338809] using wordTrace_append hprefix tailTrace_2338809
  have hstable : (prefixWord ++ tailWord_2338809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338809).length < 2 ^ (prefixWord ++ tailWord_2338809).sum := by decide
  have hdescent : baseEnd_2338809 < baseStart_2338809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338837 : List Nat := [1, 3, 2, 1, 5, 2, 2, 1, 1, 3, 2]
def baseStart_2338837 : Nat := 118140960795 + 2338837 * 2 ^ 59
def prefixEnd_2338837 : Nat := 4983230072969 + 3 ^ 40 * 2338837 * 2
def baseEnd_2338837 : Nat := 1200947553519771023181391

theorem tailTrace_2338837 : CollatzResearch.WordTrace tailWord_2338837 prefixEnd_2338837 1200947553519771023181391 := by
  unfold tailWord_2338837
  simp only [CollatzResearch.WordTrace]
  refine ⟨85304393427800465403542765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56869595618533643602361843 85304393427800465403542765)
  ·
    refine ⟨31989147535425174526328537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85304393427800465403542765 31989147535425174526328537)
    ·
      refine ⟨23991860651568880894746403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31989147535425174526328537 23991860651568880894746403)
      ·
        refine ⟨35987790977353321342119605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23991860651568880894746403 35987790977353321342119605)
        ·
          refine ⟨3373855404126873875823713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35987790977353321342119605 3373855404126873875823713)
          ·
            refine ⟨2530391553095155406867785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3373855404126873875823713 2530391553095155406867785)
            ·
              refine ⟨1897793664821366555150839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2530391553095155406867785 1897793664821366555150839)
              ·
                refine ⟨2846690497232049832726259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1897793664821366555150839 2846690497232049832726259)
                ·
                  refine ⟨4270035745848074749089389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2846690497232049832726259 4270035745848074749089389)
                  ·
                    refine ⟨1601263404693028030908521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4270035745848074749089389 1601263404693028030908521)
                    ·
                      refine ⟨1200947553519771023181391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1601263404693028030908521 1200947553519771023181391)
                      ·
                        rfl

theorem cell23_2338837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_2338837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338837 prefixEnd_2338837 := by exact prefixLift 2338837
  have htrace : WordTrace (prefixWord ++ tailWord_2338837) baseStart_2338837 baseEnd_2338837 := by
    simpa [prefixWord, tailWord_2338837, baseEnd_2338837] using wordTrace_append hprefix tailTrace_2338837
  have hstable : (prefixWord ++ tailWord_2338837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338837).length < 2 ^ (prefixWord ++ tailWord_2338837).sum := by decide
  have hdescent : baseEnd_2338837 < baseStart_2338837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338866 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3]
def baseStart_2338866 : Nat := 118140960795 + 2338866 * 2 ^ 59
def prefixEnd_2338866 : Nat := 4983230072969 + 3 ^ 40 * 2338866 * 2
def baseEnd_2338866 : Nat := 1200962444458751409718757

theorem tailTrace_2338866 : CollatzResearch.WordTrace tailWord_2338866 prefixEnd_2338866 1200962444458751409718757 := by
  unfold tailWord_2338866
  simp only [CollatzResearch.WordTrace]
  refine ⟨21326362786173850839087113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56870300763130268904232301 21326362786173850839087113)
  ·
    refine ⟨15994772089630388129315335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21326362786173850839087113 15994772089630388129315335)
    ·
      refine ⟨23992158134445582193973003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15994772089630388129315335 23992158134445582193973003)
      ·
        refine ⟨35988237201668373290959505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23992158134445582193973003 35988237201668373290959505)
        ·
          refine ⟨26991177901251279968219629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35988237201668373290959505 26991177901251279968219629)
          ·
            refine ⟨10121691712969229988082361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26991177901251279968219629 10121691712969229988082361)
            ·
              refine ⟨7591268784726922491061771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10121691712969229988082361 7591268784726922491061771)
              ·
                refine ⟨11386903177090383736592657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7591268784726922491061771 11386903177090383736592657)
                ·
                  refine ⟨8540177382817787802444493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11386903177090383736592657 8540177382817787802444493)
                  ·
                    refine ⟨3202566518556670425916685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8540177382817787802444493 3202566518556670425916685)
                    ·
                      refine ⟨1200962444458751409718757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3202566518556670425916685 1200962444458751409718757)
                      ·
                        rfl

theorem cell23_2338866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_2338866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338866 prefixEnd_2338866 := by exact prefixLift 2338866
  have htrace : WordTrace (prefixWord ++ tailWord_2338866) baseStart_2338866 baseEnd_2338866 := by
    simpa [prefixWord, tailWord_2338866, baseEnd_2338866] using wordTrace_append hprefix tailTrace_2338866
  have hstable : (prefixWord ++ tailWord_2338866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338866).length < 2 ^ (prefixWord ++ tailWord_2338866).sum := by decide
  have hdescent : baseEnd_2338866 < baseStart_2338866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338869 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 1, 7]
def baseStart_2338869 : Nat := 118140960795 + 2338869 * 2 ^ 59
def prefixEnd_2338869 : Nat := 4983230072969 + 3 ^ 40 * 2338869 * 2
def baseEnd_2338869 : Nat := 400321328300238299327081

theorem tailTrace_2338869 : CollatzResearch.WordTrace tailWord_2338869 prefixEnd_2338869 400321328300238299327081 := by
  unfold tailWord_2338869
  simp only [CollatzResearch.WordTrace]
  refine ⟨85305560563684534868707661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56870373709123023245805107 85305560563684534868707661)
  ·
    refine ⟨31989585211381700575765373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85305560563684534868707661 31989585211381700575765373)
    ·
      refine ⟨11996094454268137715912015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31989585211381700575765373 11996094454268137715912015)
      ·
        refine ⟨17994141681402206573868023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11996094454268137715912015 17994141681402206573868023)
        ·
          refine ⟨26991212522103309860802035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17994141681402206573868023 26991212522103309860802035)
          ·
            refine ⟨40486818783154964791203053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26991212522103309860802035 40486818783154964791203053)
            ·
              refine ⟨15182557043683111796701145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40486818783154964791203053 15182557043683111796701145)
              ·
                refine ⟨11386917782762333847525859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15182557043683111796701145 11386917782762333847525859)
                ·
                  refine ⟨17080376674143500771288789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11386917782762333847525859 17080376674143500771288789)
                  ·
                    refine ⟨400321328300238299327081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17080376674143500771288789 400321328300238299327081)
                    ·
                      rfl

theorem cell23_2338869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_2338869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338869 prefixEnd_2338869 := by exact prefixLift 2338869
  have htrace : WordTrace (prefixWord ++ tailWord_2338869) baseStart_2338869 baseEnd_2338869 := by
    simpa [prefixWord, tailWord_2338869, baseEnd_2338869] using wordTrace_append hprefix tailTrace_2338869
  have hstable : (prefixWord ++ tailWord_2338869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338869).length < 2 ^ (prefixWord ++ tailWord_2338869).sum := by decide
  have hdescent : baseEnd_2338869 < baseStart_2338869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338889 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 1, 3, 4]
def baseStart_2338889 : Nat := 118140960795 + 2338889 * 2 ^ 59
def prefixEnd_2338889 : Nat := 4983230072969 + 3 ^ 40 * 2338889 * 2
def baseEnd_2338889 : Nat := 1200974254513804819731151

theorem tailTrace_2338889 : CollatzResearch.WordTrace tailWord_2338889 prefixEnd_2338889 1200974254513804819731151 := by
  unfold tailWord_2338889
  simp only [CollatzResearch.WordTrace]
  refine ⟨85306290023612078284435721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56870860015741385522957147 85306290023612078284435721)
  ·
    refine ⟨63979717517709058713326791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85306290023612078284435721 63979717517709058713326791)
    ·
      refine ⟨95969576276563588069990187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63979717517709058713326791 95969576276563588069990187)
      ·
        refine ⟨143954364414845382104985281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95969576276563588069990187 143954364414845382104985281)
        ·
          refine ⟨107965773311134036578738961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143954364414845382104985281 107965773311134036578738961)
          ·
            refine ⟨80974329983350527434054221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107965773311134036578738961 80974329983350527434054221)
            ·
              refine ⟨30365373743756447787770333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80974329983350527434054221 30365373743756447787770333)
              ·
                refine ⟨11387015153908667920413875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30365373743756447787770333 11387015153908667920413875)
                ·
                  refine ⟨17080522730863001880620813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11387015153908667920413875 17080522730863001880620813)
                  ·
                    refine ⟨6405196024073625705232805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17080522730863001880620813 6405196024073625705232805)
                    ·
                      refine ⟨1200974254513804819731151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6405196024073625705232805 1200974254513804819731151)
                      ·
                        rfl

theorem cell23_2338889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_2338889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338889 prefixEnd_2338889 := by exact prefixLift 2338889
  have htrace : WordTrace (prefixWord ++ tailWord_2338889) baseStart_2338889 baseEnd_2338889 := by
    simpa [prefixWord, tailWord_2338889, baseEnd_2338889] using wordTrace_append hprefix tailTrace_2338889
  have hstable : (prefixWord ++ tailWord_2338889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338889).length < 2 ^ (prefixWord ++ tailWord_2338889).sum := by decide
  have hdescent : baseEnd_2338889 < baseStart_2338889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338906 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4]
def baseStart_2338906 : Nat := 118140960795 + 2338906 * 2 ^ 59
def prefixEnd_2338906 : Nat := 4983230072969 + 3 ^ 40 * 2338906 * 2
def baseEnd_2338906 : Nat := 1200982983684931253218573

theorem tailTrace_2338906 : CollatzResearch.WordTrace tailWord_2338906 prefixEnd_2338906 1200982983684931253218573 := by
  unfold tailWord_2338906
  simp only [CollatzResearch.WordTrace]
  refine ⟨21326727516137622546951143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56871273376366993458536381 21326727516137622546951143)
  ·
    refine ⟨31990091274206433820426715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21326727516137622546951143 31990091274206433820426715)
    ·
      refine ⟨47985136911309650730640073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31990091274206433820426715 47985136911309650730640073)
      ·
        refine ⟨35988852683482238047980055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47985136911309650730640073 35988852683482238047980055)
        ·
          refine ⟨53983279025223357071970083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35988852683482238047980055 53983279025223357071970083)
          ·
            refine ⟨80974918537835035607955125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53983279025223357071970083 80974918537835035607955125)
            ·
              refine ⟨7591398612922034588245793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80974918537835035607955125 7591398612922034588245793)
              ·
                refine ⟨5693548959691525941184345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7591398612922034588245793 5693548959691525941184345)
                ·
                  refine ⟨4270161719768644455888259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5693548959691525941184345 4270161719768644455888259)
                  ·
                    refine ⟨6405242579652966683832389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4270161719768644455888259 6405242579652966683832389)
                    ·
                      refine ⟨1200982983684931253218573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6405242579652966683832389 1200982983684931253218573)
                      ·
                        rfl

theorem cell23_2338906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_2338906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338906 prefixEnd_2338906 := by exact prefixLift 2338906
  have htrace : WordTrace (prefixWord ++ tailWord_2338906) baseStart_2338906 baseEnd_2338906 := by
    simpa [prefixWord, tailWord_2338906, baseEnd_2338906] using wordTrace_append hprefix tailTrace_2338906
  have hstable : (prefixWord ++ tailWord_2338906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338906).length < 2 ^ (prefixWord ++ tailWord_2338906).sum := by decide
  have hdescent : baseEnd_2338906 < baseStart_2338906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338969 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 5]
def baseStart_2338969 : Nat := 118140960795 + 2338969 * 2 ^ 59
def prefixEnd_2338969 : Nat := 4983230072969 + 3 ^ 40 * 2338969 * 2
def baseEnd_2338969 : Nat := 1201015332966164506730783

theorem tailTrace_2338969 : CollatzResearch.WordTrace tailWord_2338969 prefixEnd_2338969 1201015332966164506730783 := by
  unfold tailWord_2338969
  simp only [CollatzResearch.WordTrace]
  refine ⟨85309207863322251947347961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56872805242214834631565307 85309207863322251947347961)
  ·
    refine ⟨63981905897491688960510971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85309207863322251947347961 63981905897491688960510971)
    ·
      refine ⟨95972858846237533440766457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63981905897491688960510971 95972858846237533440766457)
      ·
        refine ⟨71979644134678150080574843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95972858846237533440766457 71979644134678150080574843)
        ·
          refine ⟨107969466202017225120862265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71979644134678150080574843 107969466202017225120862265)
          ·
            refine ⟨80977099651512918840646699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107969466202017225120862265 80977099651512918840646699)
            ·
              refine ⟨121465649477269378260970049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80977099651512918840646699 121465649477269378260970049)
              ·
                refine ⟨91099237107952033695727537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121465649477269378260970049 91099237107952033695727537)
                ·
                  refine ⟨68324427830964025271795653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91099237107952033695727537 68324427830964025271795653)
                  ·
                    refine ⟨12810830218305754738461685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68324427830964025271795653 12810830218305754738461685)
                    ·
                      refine ⟨1201015332966164506730783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12810830218305754738461685 1201015332966164506730783)
                      ·
                        rfl

theorem cell23_2338969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_2338969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338969 prefixEnd_2338969 := by exact prefixLift 2338969
  have htrace : WordTrace (prefixWord ++ tailWord_2338969) baseStart_2338969 baseEnd_2338969 := by
    simpa [prefixWord, tailWord_2338969, baseEnd_2338969] using wordTrace_append hprefix tailTrace_2338969
  have hstable : (prefixWord ++ tailWord_2338969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338969).length < 2 ^ (prefixWord ++ tailWord_2338969).sum := by decide
  have hdescent : baseEnd_2338969 < baseStart_2338969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338976 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 3, 5]
def baseStart_2338976 : Nat := 118140960795 + 2338976 * 2 ^ 59
def prefixEnd_2338976 : Nat := 4983230072969 + 3 ^ 40 * 2338976 * 2
def baseEnd_2338976 : Nat := 400339642443581993114417

theorem tailTrace_2338976 : CollatzResearch.WordTrace tailWord_2338976 prefixEnd_2338976 400339642443581993114417 := by
  unfold tailWord_2338976
  simp only [CollatzResearch.WordTrace]
  refine ⟨42654731587148446071426391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56872975449531261428568521 42654731587148446071426391)
  ·
    refine ⟨63982097380722669107139587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42654731587148446071426391 63982097380722669107139587)
    ·
      refine ⟨95973146071084003660709381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63982097380722669107139587 95973146071084003660709381)
      ·
        refine ⟨17994964888328250686383009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95973146071084003660709381 17994964888328250686383009)
        ·
          refine ⟨13496223666246188014787257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17994964888328250686383009 13496223666246188014787257)
          ·
            refine ⟨10122167749684641011090443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13496223666246188014787257 10122167749684641011090443)
            ·
              refine ⟨15183251624526961516635665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10122167749684641011090443 15183251624526961516635665)
              ·
                refine ⟨11387438718395221137476749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15183251624526961516635665 11387438718395221137476749)
                ·
                  refine ⟨4270289519398207926553781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11387438718395221137476749 4270289519398207926553781)
                  ·
                    refine ⟨400339642443581993114417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4270289519398207926553781 400339642443581993114417)
                    ·
                      rfl

theorem cell23_2338976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 3, 5].length) (baseStart_2338976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2338976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2338976 prefixEnd_2338976 := by exact prefixLift 2338976
  have htrace : WordTrace (prefixWord ++ tailWord_2338976) baseStart_2338976 baseEnd_2338976 := by
    simpa [prefixWord, tailWord_2338976, baseEnd_2338976] using wordTrace_append hprefix tailTrace_2338976
  have hstable : (prefixWord ++ tailWord_2338976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338976).length < 2 ^ (prefixWord ++ tailWord_2338976).sum := by decide
  have hdescent : baseEnd_2338976 < baseStart_2338976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339016 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_2339016 : Nat := 118140960795 + 2339016 * 2 ^ 59
def prefixEnd_2339016 : Nat := 4983230072969 + 3 ^ 40 * 2339016 * 2
def baseEnd_2339016 : Nat := 1201039466556925822843067

theorem tailTrace_2339016 : CollatzResearch.WordTrace tailWord_2339016 prefixEnd_2339016 1201039466556925822843067 := by
  unfold tailWord_2339016
  simp only [CollatzResearch.WordTrace]
  refine ⟨42655461047075989487154451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56873948062767985982872601 42655461047075989487154451)
  ·
    refine ⟨63983191570613984230731677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42655461047075989487154451 63983191570613984230731677)
    ·
      refine ⟨23993696838980244086524379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63983191570613984230731677 23993696838980244086524379)
      ·
        refine ⟨35990545258470366129786569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23993696838980244086524379 35990545258470366129786569)
        ·
          refine ⟨26992908943852774597339927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35990545258470366129786569 26992908943852774597339927)
          ·
            refine ⟨40489363415779161896009891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26992908943852774597339927 40489363415779161896009891)
            ·
              refine ⟨60734045123668742844014837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40489363415779161896009891 60734045123668742844014837)
              ·
                refine ⟨5693816730343944641626391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60734045123668742844014837 5693816730343944641626391)
                ·
                  refine ⟨8540725095515916962439587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5693816730343944641626391 8540725095515916962439587)
                  ·
                    refine ⟨12811087643273875443659381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8540725095515916962439587 12811087643273875443659381)
                    ·
                      refine ⟨1201039466556925822843067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12811087643273875443659381 1201039466556925822843067)
                      ·
                        rfl

theorem cell23_2339016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_2339016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339016 prefixEnd_2339016 := by exact prefixLift 2339016
  have htrace : WordTrace (prefixWord ++ tailWord_2339016) baseStart_2339016 baseEnd_2339016 := by
    simpa [prefixWord, tailWord_2339016, baseEnd_2339016] using wordTrace_append hprefix tailTrace_2339016
  have hstable : (prefixWord ++ tailWord_2339016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339016).length < 2 ^ (prefixWord ++ tailWord_2339016).sum := by decide
  have hdescent : baseEnd_2339016 < baseStart_2339016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339019 : List Nat := [1, 1, 1, 1, 3, 2, 14]
def baseStart_2339019 : Nat := 118140960795 + 2339019 * 2 ^ 59
def prefixEnd_2339019 : Nat := 4983230072969 + 3 ^ 40 * 2339019 * 2
def baseEnd_2339019 : Nat := 14827666753072707544513

theorem tailTrace_2339019 : CollatzResearch.WordTrace tailWord_2339019 prefixEnd_2339019 14827666753072707544513 := by
  unfold tailWord_2339019
  simp only [CollatzResearch.WordTrace]
  refine ⟨85311031513141110486668111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56874021008760740324445407 85311031513141110486668111)
  ·
    refine ⟨127966547269711665730002167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85311031513141110486668111 127966547269711665730002167)
    ·
      refine ⟨191949820904567498595003251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127966547269711665730002167 191949820904567498595003251)
      ·
        refine ⟨287924731356851247892504877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191949820904567498595003251 287924731356851247892504877)
        ·
          refine ⟨107971774258819217959689329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 287924731356851247892504877 107971774258819217959689329)
          ·
            refine ⟨80978830694114413469766997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107971774258819217959689329 80978830694114413469766997)
            ·
              refine ⟨14827666753072707544513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 80978830694114413469766997 14827666753072707544513)
              ·
                rfl

theorem cell23_2339019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 14].length) (baseStart_2339019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339019 prefixEnd_2339019 := by exact prefixLift 2339019
  have htrace : WordTrace (prefixWord ++ tailWord_2339019) baseStart_2339019 baseEnd_2339019 := by
    simpa [prefixWord, tailWord_2339019, baseEnd_2339019] using wordTrace_append hprefix tailTrace_2339019
  have hstable : (prefixWord ++ tailWord_2339019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339019).length < 2 ^ (prefixWord ++ tailWord_2339019).sum := by decide
  have hdescent : baseEnd_2339019 < baseStart_2339019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339040 : List Nat := [2, 1, 1, 3, 1, 3, 5, 1, 2, 4]
def baseStart_2339040 : Nat := 118140960795 + 2339040 * 2 ^ 59
def prefixEnd_2339040 : Nat := 4983230072969 + 3 ^ 40 * 2339040 * 2
def baseEnd_2339040 : Nat := 400350596697544576314319

theorem tailTrace_2339040 : CollatzResearch.WordTrace tailWord_2339040 prefixEnd_2339040 400350596697544576314319 := by
  unfold tailWord_2339040
  simp only [CollatzResearch.WordTrace]
  refine ⟨42655898723032515536591287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56874531630710020715455049 42655898723032515536591287)
  ·
    refine ⟨63983848084548773304886931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42655898723032515536591287 63983848084548773304886931)
    ·
      refine ⟨95975772126823159957330397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63983848084548773304886931 95975772126823159957330397)
      ·
        refine ⟨35990914547558684983998899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95975772126823159957330397 35990914547558684983998899)
        ·
          refine ⟨53986371821338027475998349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35990914547558684983998899 53986371821338027475998349)
          ·
            refine ⟨20244889433001760303499381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53986371821338027475998349 20244889433001760303499381)
            ·
              refine ⟨1897958384343915028453067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20244889433001760303499381 1897958384343915028453067)
              ·
                refine ⟨2846937576515872542679601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1897958384343915028453067 2846937576515872542679601)
                ·
                  refine ⟨2135203182386904407009701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2846937576515872542679601 2135203182386904407009701)
                  ·
                    refine ⟨400350596697544576314319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2135203182386904407009701 400350596697544576314319)
                    ·
                      rfl

theorem cell23_2339040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 2, 4].length) (baseStart_2339040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339040 prefixEnd_2339040 := by exact prefixLift 2339040
  have htrace : WordTrace (prefixWord ++ tailWord_2339040) baseStart_2339040 baseEnd_2339040 := by
    simpa [prefixWord, tailWord_2339040, baseEnd_2339040] using wordTrace_append hprefix tailTrace_2339040
  have hstable : (prefixWord ++ tailWord_2339040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339040).length < 2 ^ (prefixWord ++ tailWord_2339040).sum := by decide
  have hdescent : baseEnd_2339040 < baseStart_2339040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339047 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 3, 2, 2]
def baseStart_2339047 : Nat := 118140960795 + 2339047 * 2 ^ 59
def prefixEnd_2339047 : Nat := 4983230072969 + 3 ^ 40 * 2339047 * 2
def baseEnd_2339047 : Nat := 1201055384457215201555425

theorem tailTrace_2339047 : CollatzResearch.WordTrace tailWord_2339047 prefixEnd_2339047 1201055384457215201555425 := by
  unfold tailWord_2339047
  simp only [CollatzResearch.WordTrace]
  refine ⟨85312052757039671268687395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56874701838026447512458263 85312052757039671268687395)
  ·
    refine ⟨127968079135559506903031093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85312052757039671268687395 127968079135559506903031093)
    ·
      refine ⟨11997007418958703772159165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127968079135559506903031093 11997007418958703772159165)
      ·
        refine ⟨4498877782109513914559687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11997007418958703772159165 4498877782109513914559687)
        ·
          refine ⟨6748316673164270871839531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4498877782109513914559687 6748316673164270871839531)
          ·
            refine ⟨10122475009746406307759297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6748316673164270871839531 10122475009746406307759297)
            ·
              refine ⟨7591856257309804730819473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10122475009746406307759297 7591856257309804730819473)
              ·
                refine ⟨5693892192982353548114605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7591856257309804730819473 5693892192982353548114605)
                ·
                  refine ⟨2135209572368382580542977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5693892192982353548114605 2135209572368382580542977)
                  ·
                    refine ⟨1601407179276286935407233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2135209572368382580542977 1601407179276286935407233)
                    ·
                      refine ⟨1201055384457215201555425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1601407179276286935407233 1201055384457215201555425)
                      ·
                        rfl

theorem cell23_2339047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_2339047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339047 prefixEnd_2339047 := by exact prefixLift 2339047
  have htrace : WordTrace (prefixWord ++ tailWord_2339047) baseStart_2339047 baseEnd_2339047 := by
    simpa [prefixWord, tailWord_2339047, baseEnd_2339047] using wordTrace_append hprefix tailTrace_2339047
  have hstable : (prefixWord ++ tailWord_2339047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339047).length < 2 ^ (prefixWord ++ tailWord_2339047).sum := by decide
  have hdescent : baseEnd_2339047 < baseStart_2339047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339050 : List Nat := [3, 1, 3, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_2339050 : Nat := 118140960795 + 2339050 * 2 ^ 59
def prefixEnd_2339050 : Nat := 4983230072969 + 3 ^ 40 * 2339050 * 2
def baseEnd_2339050 : Nat := 1201056924899178689817911

theorem tailTrace_2339050 : CollatzResearch.WordTrace tailWord_2339050 prefixEnd_2339050 1201056924899178689817911 := by
  unfold tailWord_2339050
  simp only [CollatzResearch.WordTrace]
  refine ⟨21328040544007200695261651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56874774784019201854031069 21328040544007200695261651)
  ·
    refine ⟨31992060816010801042892477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21328040544007200695261651 31992060816010801042892477)
    ·
      refine ⟨11997022806004050391084679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31992060816010801042892477 11997022806004050391084679)
      ·
        refine ⟨17995534209006075586627019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11997022806004050391084679 17995534209006075586627019)
        ·
          refine ⟨26993301313509113379940529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17995534209006075586627019 26993301313509113379940529)
          ·
            refine ⟨20244975985131835034955397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26993301313509113379940529 20244975985131835034955397)
            ·
              refine ⟨3795932997212219069054137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20244975985131835034955397 3795932997212219069054137)
              ·
                refine ⟨2846949747909164301790603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3795932997212219069054137 2846949747909164301790603)
                ·
                  refine ⟨4270424621863746452685905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2846949747909164301790603 4270424621863746452685905)
                  ·
                    refine ⟨3202818466397809839514429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4270424621863746452685905 3202818466397809839514429)
                    ·
                      refine ⟨1201056924899178689817911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3202818466397809839514429 1201056924899178689817911)
                      ·
                        rfl

theorem cell23_2339050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_2339050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339050 prefixEnd_2339050 := by exact prefixLift 2339050
  have htrace : WordTrace (prefixWord ++ tailWord_2339050) baseStart_2339050 baseEnd_2339050 := by
    simpa [prefixWord, tailWord_2339050, baseEnd_2339050] using wordTrace_append hprefix tailTrace_2339050
  have hstable : (prefixWord ++ tailWord_2339050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339050).length < 2 ^ (prefixWord ++ tailWord_2339050).sum := by decide
  have hdescent : baseEnd_2339050 < baseStart_2339050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339053 : List Nat := [1, 5, 1, 2, 3, 1, 1, 9]
def baseStart_2339053 : Nat := 118140960795 + 2339053 * 2 ^ 59
def prefixEnd_2339053 : Nat := 4983230072969 + 3 ^ 40 * 2339053 * 2
def baseEnd_2339053 : Nat := 44483646864486747336311

theorem tailTrace_2339053 : CollatzResearch.WordTrace tailWord_2339053 prefixEnd_2339053 44483646864486747336311 := by
  unfold tailWord_2339053
  simp only [CollatzResearch.WordTrace]
  refine ⟨85312271595017934293405813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56874847730011956195603875 85312271595017934293405813)
  ·
    refine ⟨7998025462032931340006795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85312271595017934293405813 7998025462032931340006795)
    ·
      refine ⟨11997038193049397010010193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7998025462032931340006795 11997038193049397010010193)
      ·
        refine ⟨8997778644787047757507645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11997038193049397010010193 8997778644787047757507645)
        ·
          refine ⟨3374166991795142909065367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8997778644787047757507645 3374166991795142909065367)
          ·
            refine ⟨5061250487692714363598051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3374166991795142909065367 5061250487692714363598051)
            ·
              refine ⟨7591875731539071545397077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5061250487692714363598051 7591875731539071545397077)
              ·
                refine ⟨44483646864486747336311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7591875731539071545397077 44483646864486747336311)
                ·
                  rfl

theorem cell23_2339053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 9].length) (baseStart_2339053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339053 prefixEnd_2339053 := by exact prefixLift 2339053
  have htrace : WordTrace (prefixWord ++ tailWord_2339053) baseStart_2339053 baseEnd_2339053 := by
    simpa [prefixWord, tailWord_2339053, baseEnd_2339053] using wordTrace_append hprefix tailTrace_2339053
  have hstable : (prefixWord ++ tailWord_2339053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339053).length < 2 ^ (prefixWord ++ tailWord_2339053).sum := by decide
  have hdescent : baseEnd_2339053 < baseStart_2339053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339080 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 4, 1, 3]
def baseStart_2339080 : Nat := 118140960795 + 2339080 * 2 ^ 59
def prefixEnd_2339080 : Nat := 4983230072969 + 3 ^ 40 * 2339080 * 2
def baseEnd_2339080 : Nat := 1201072329318813572442773

theorem tailTrace_2339080 : CollatzResearch.WordTrace tailWord_2339080 prefixEnd_2339080 1201072329318813572442773 := by
  unfold tailWord_2339080
  simp only [CollatzResearch.WordTrace]
  refine ⟨42656628182960058952319347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56875504243946745269759129 42656628182960058952319347)
  ·
    refine ⟨63984942274440088428479021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42656628182960058952319347 63984942274440088428479021)
    ·
      refine ⟨23994353352915033160679633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63984942274440088428479021 23994353352915033160679633)
      ·
        refine ⟨17995765014686274870509725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23994353352915033160679633 17995765014686274870509725)
        ·
          refine ⟨6748411880507353076441147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17995765014686274870509725 6748411880507353076441147)
          ·
            refine ⟨10122617820761029614661721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6748411880507353076441147 10122617820761029614661721)
            ·
              refine ⟨7591963365570772210996291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10122617820761029614661721 7591963365570772210996291)
              ·
                refine ⟨11387945048356158316494437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7591963365570772210996291 11387945048356158316494437)
                ·
                  refine ⟨2135239696566779684342707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11387945048356158316494437 2135239696566779684342707)
                  ·
                    refine ⟨3202859544850169526514061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2135239696566779684342707 3202859544850169526514061)
                    ·
                      refine ⟨1201072329318813572442773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3202859544850169526514061 1201072329318813572442773)
                      ·
                        rfl

theorem cell23_2339080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_2339080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339080 prefixEnd_2339080 := by exact prefixLift 2339080
  have htrace : WordTrace (prefixWord ++ tailWord_2339080) baseStart_2339080 baseEnd_2339080 := by
    simpa [prefixWord, tailWord_2339080, baseEnd_2339080] using wordTrace_append hprefix tailTrace_2339080
  have hstable : (prefixWord ++ tailWord_2339080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339080).length < 2 ^ (prefixWord ++ tailWord_2339080).sum := by decide
  have hdescent : baseEnd_2339080 < baseStart_2339080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339096 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 1, 8]
def baseStart_2339096 : Nat := 118140960795 + 2339096 * 2 ^ 59
def prefixEnd_2339096 : Nat := 4983230072969 + 3 ^ 40 * 2339096 * 2
def baseEnd_2339096 : Nat := 400360181669761836614233

theorem tailTrace_2339096 : CollatzResearch.WordTrace tailWord_2339096 prefixEnd_2339096 400360181669761836614233 := by
  unfold tailWord_2339096
  simp only [CollatzResearch.WordTrace]
  refine ⟨42656919966931076318610571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56875893289241435091480761 42656919966931076318610571)
  ·
    refine ⟨63985379950396614477915857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42656919966931076318610571 63985379950396614477915857)
    ·
      refine ⟨47989034962797460858436893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63985379950396614477915857 47989034962797460858436893)
      ·
        refine ⟨17995888111049047821913835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47989034962797460858436893 17995888111049047821913835)
        ·
          refine ⟨26993832166573571732870753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17995888111049047821913835 26993832166573571732870753)
          ·
            refine ⟨20245374124930178799653065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26993832166573571732870753 20245374124930178799653065)
            ·
              refine ⟨15184030593697634099739799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20245374124930178799653065 15184030593697634099739799)
              ·
                refine ⟨22776045890546451149609699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15184030593697634099739799 22776045890546451149609699)
                ·
                  refine ⟨34164068835819676724414549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22776045890546451149609699 34164068835819676724414549)
                  ·
                    refine ⟨400360181669761836614233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34164068835819676724414549 400360181669761836614233)
                    ·
                      rfl

theorem cell23_2339096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_2339096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339096 prefixEnd_2339096 := by exact prefixLift 2339096
  have htrace : WordTrace (prefixWord ++ tailWord_2339096) baseStart_2339096 baseEnd_2339096 := by
    simpa [prefixWord, tailWord_2339096, baseEnd_2339096] using wordTrace_append hprefix tailTrace_2339096
  have hstable : (prefixWord ++ tailWord_2339096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339096).length < 2 ^ (prefixWord ++ tailWord_2339096).sum := by decide
  have hdescent : baseEnd_2339096 < baseStart_2339096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339120 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 4, 2, 2]
def baseStart_2339120 : Nat := 118140960795 + 2339120 * 2 ^ 59
def prefixEnd_2339120 : Nat := 4983230072969 + 3 ^ 40 * 2339120 * 2
def baseEnd_2339120 : Nat := 1201092868544993415942589

theorem tailTrace_2339120 : CollatzResearch.WordTrace tailWord_2339120 prefixEnd_2339120 1201092868544993415942589 := by
  unfold tailWord_2339120
  simp only [CollatzResearch.WordTrace]
  refine ⟨42657357642887602368047407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56876476857183469824063209 42657357642887602368047407)
  ·
    refine ⟨63986036464331403552071111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42657357642887602368047407 63986036464331403552071111)
    ·
      refine ⟨95979054696497105328106667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63986036464331403552071111 95979054696497105328106667)
      ·
        refine ⟨143968582044745657992160001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95979054696497105328106667 143968582044745657992160001)
        ·
          refine ⟨107976436533559243494120001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143968582044745657992160001 107976436533559243494120001)
          ·
            refine ⟨80982327400169432620590001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107976436533559243494120001 80982327400169432620590001)
            ·
              refine ⟨60736745550127074465442501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80982327400169432620590001 60736745550127074465442501)
              ·
                refine ⟨11388139790648826462270469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60736745550127074465442501 11388139790648826462270469)
                ·
                  refine ⟨2135276210746654961675713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11388139790648826462270469 2135276210746654961675713)
                  ·
                    refine ⟨1601457158059991221256785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2135276210746654961675713 1601457158059991221256785)
                    ·
                      refine ⟨1201092868544993415942589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1601457158059991221256785 1201092868544993415942589)
                      ·
                        rfl

theorem cell23_2339120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 4, 2, 2].length) (baseStart_2339120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339120 prefixEnd_2339120 := by exact prefixLift 2339120
  have htrace : WordTrace (prefixWord ++ tailWord_2339120) baseStart_2339120 baseEnd_2339120 := by
    simpa [prefixWord, tailWord_2339120, baseEnd_2339120] using wordTrace_append hprefix tailTrace_2339120
  have hstable : (prefixWord ++ tailWord_2339120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339120).length < 2 ^ (prefixWord ++ tailWord_2339120).sum := by decide
  have hdescent : baseEnd_2339120 < baseStart_2339120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339146 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_2339146 : Nat := 118140960795 + 2339146 * 2 ^ 59
def prefixEnd_2339146 : Nat := 4983230072969 + 3 ^ 40 * 2339146 * 2
def baseEnd_2339146 : Nat := 1201106219042010314217469

theorem tailTrace_2339146 : CollatzResearch.WordTrace tailWord_2339146 prefixEnd_2339146 1201106219042010314217469 := by
  unfold tailWord_2339146
  simp only [CollatzResearch.WordTrace]
  refine ⟨21328915895920252794135323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56877109055787340784360861 21328915895920252794135323)
  ·
    refine ⟨31993373843880379191202985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21328915895920252794135323 31993373843880379191202985)
    ·
      refine ⟨23995030382910284393402239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31993373843880379191202985 23995030382910284393402239)
      ·
        refine ⟨35992545574365426590103359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23995030382910284393402239 35992545574365426590103359)
        ·
          refine ⟨53988818361548139885155039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35992545574365426590103359 53988818361548139885155039)
          ·
            refine ⟨80983227542322209827732559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53988818361548139885155039 80983227542322209827732559)
            ·
              refine ⟨121474841313483314741598839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80983227542322209827732559 121474841313483314741598839)
              ·
                refine ⟨182212261970224972112398259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121474841313483314741598839 182212261970224972112398259)
                ·
                  refine ⟨273318392955337458168597389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182212261970224972112398259 273318392955337458168597389)
                  ·
                    refine ⟨102494397358251546813224021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 273318392955337458168597389 102494397358251546813224021)
                    ·
                      refine ⟨1201106219042010314217469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 102494397358251546813224021 1201106219042010314217469)
                      ·
                        rfl

theorem cell23_2339146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_2339146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339146 prefixEnd_2339146 := by exact prefixLift 2339146
  have htrace : WordTrace (prefixWord ++ tailWord_2339146) baseStart_2339146 baseEnd_2339146 := by
    simpa [prefixWord, tailWord_2339146, baseEnd_2339146] using wordTrace_append hprefix tailTrace_2339146
  have hstable : (prefixWord ++ tailWord_2339146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339146).length < 2 ^ (prefixWord ++ tailWord_2339146).sum := by decide
  have hdescent : baseEnd_2339146 < baseStart_2339146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339153 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 1, 5, 3]
def baseStart_2339153 : Nat := 118140960795 + 2339153 * 2 ^ 59
def prefixEnd_2339153 : Nat := 4983230072969 + 3 ^ 40 * 2339153 * 2
def baseEnd_2339153 : Nat := 1201109813406591786829937

theorem tailTrace_2339153 : CollatzResearch.WordTrace tailWord_2339153 prefixEnd_2339153 1201109813406591786829937 := by
  unfold tailWord_2339153
  simp only [CollatzResearch.WordTrace]
  refine ⟨85315918894655651372046113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56877279263103767581364075 85315918894655651372046113)
  ·
    refine ⟨63986939170991738529034585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85315918894655651372046113 63986939170991738529034585)
    ·
      refine ⟨47990204378243803896775939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63986939170991738529034585 47990204378243803896775939)
      ·
        refine ⟨71985306567365705845163909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47990204378243803896775939 71985306567365705845163909)
        ·
          refine ⟨13497244981381069845968233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71985306567365705845163909 13497244981381069845968233)
          ·
            refine ⟨10122933736035802384476175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13497244981381069845968233 10122933736035802384476175)
            ·
              refine ⟨15184400604053703576714263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10122933736035802384476175 15184400604053703576714263)
              ·
                refine ⟨22776600906080555365071395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15184400604053703576714263 22776600906080555365071395)
                ·
                  refine ⟨34164901359120833047607093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22776600906080555365071395 34164901359120833047607093)
                  ·
                    refine ⟨3202959502417578098213165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34164901359120833047607093 3202959502417578098213165)
                    ·
                      refine ⟨1201109813406591786829937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3202959502417578098213165 1201109813406591786829937)
                      ·
                        rfl

theorem cell23_2339153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_2339153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339153 prefixEnd_2339153 := by exact prefixLift 2339153
  have htrace : WordTrace (prefixWord ++ tailWord_2339153) baseStart_2339153 baseEnd_2339153 := by
    simpa [prefixWord, tailWord_2339153, baseEnd_2339153] using wordTrace_append hprefix tailTrace_2339153
  have hstable : (prefixWord ++ tailWord_2339153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339153).length < 2 ^ (prefixWord ++ tailWord_2339153).sum := by decide
  have hdescent : baseEnd_2339153 < baseStart_2339153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339163 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 2, 11, 2]
def baseStart_2339163 : Nat := 118140960795 + 2339163 * 2 ^ 59
def prefixEnd_2339163 : Nat := 4983230072969 + 3 ^ 40 * 2339163 * 2
def baseEnd_2339163 : Nat := 1201114948213136747704891

theorem tailTrace_2339163 : CollatzResearch.WordTrace tailWord_2339163 prefixEnd_2339163 1201114948213136747704891 := by
  unfold tailWord_2339163
  simp only [CollatzResearch.WordTrace]
  refine ⟨85316283624619423079910143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56877522416412948719940095 85316283624619423079910143)
  ·
    refine ⟨127974425436929134619865215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85316283624619423079910143 127974425436929134619865215)
    ·
      refine ⟨191961638155393701929797823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127974425436929134619865215 191961638155393701929797823)
      ·
        refine ⟨287942457233090552894696735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191961638155393701929797823 287942457233090552894696735)
        ·
          refine ⟨431913685849635829342045103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287942457233090552894696735 431913685849635829342045103)
          ·
            refine ⟨647870528774453744013067655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431913685849635829342045103 647870528774453744013067655)
            ·
              refine ⟨971805793161680616019601483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647870528774453744013067655 971805793161680616019601483)
              ·
                refine ⟨1457708689742520924029402225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 971805793161680616019601483 1457708689742520924029402225)
                ·
                  refine ⟨1093281517306890693022051669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1457708689742520924029402225 1093281517306890693022051669)
                  ·
                    refine ⟨1601486597617515663606521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 1093281517306890693022051669 1601486597617515663606521)
                    ·
                      refine ⟨1201114948213136747704891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1601486597617515663606521 1201114948213136747704891)
                      ·
                        rfl

theorem cell23_2339163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 11, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 11, 2].length) (baseStart_2339163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339163 prefixEnd_2339163 := by exact prefixLift 2339163
  have htrace : WordTrace (prefixWord ++ tailWord_2339163) baseStart_2339163 baseEnd_2339163 := by
    simpa [prefixWord, tailWord_2339163, baseEnd_2339163] using wordTrace_append hprefix tailTrace_2339163
  have hstable : (prefixWord ++ tailWord_2339163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339163).length < 2 ^ (prefixWord ++ tailWord_2339163).sum := by decide
  have hdescent : baseEnd_2339163 < baseStart_2339163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339173 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 1, 7]
def baseStart_2339173 : Nat := 118140960795 + 2339173 * 2 ^ 59
def prefixEnd_2339173 : Nat := 4983230072969 + 3 ^ 40 * 2339173 * 2
def baseEnd_2339173 : Nat := 400373361006560569526615

theorem tailTrace_2339173 : CollatzResearch.WordTrace tailWord_2339173 prefixEnd_2339173 400373361006560569526615 := by
  unfold tailWord_2339173
  simp only [CollatzResearch.WordTrace]
  refine ⟨85316648354583194787774173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56877765569722129858516115 85316648354583194787774173)
  ·
    refine ⟨31993743132968698045415315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85316648354583194787774173 31993743132968698045415315)
    ·
      refine ⟨47990614699453047068122973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31993743132968698045415315 47990614699453047068122973)
      ·
        refine ⟨17996480512294892650546115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47990614699453047068122973 17996480512294892650546115)
        ·
          refine ⟨26994720768442338975819173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17996480512294892650546115 26994720768442338975819173)
          ·
            refine ⟨5061510144082938557966095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26994720768442338975819173 5061510144082938557966095)
            ·
              refine ⟨7592265216124407836949143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5061510144082938557966095 7592265216124407836949143)
              ·
                refine ⟨11388397824186611755423715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7592265216124407836949143 11388397824186611755423715)
                ·
                  refine ⟨17082596736279917633135573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11388397824186611755423715 17082596736279917633135573)
                  ·
                    refine ⟨400373361006560569526615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17082596736279917633135573 400373361006560569526615)
                    ·
                      rfl

theorem cell23_2339173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_2339173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339173 prefixEnd_2339173 := by exact prefixLift 2339173
  have htrace : WordTrace (prefixWord ++ tailWord_2339173) baseStart_2339173 baseEnd_2339173 := by
    simpa [prefixWord, tailWord_2339173, baseEnd_2339173] using wordTrace_append hprefix tailTrace_2339173
  have hstable : (prefixWord ++ tailWord_2339173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339173).length < 2 ^ (prefixWord ++ tailWord_2339173).sum := by decide
  have hdescent : baseEnd_2339173 < baseStart_2339173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339193 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 4, 1, 4]
def baseStart_2339193 : Nat := 118140960795 + 2339193 * 2 ^ 59
def prefixEnd_2339193 : Nat := 4983230072969 + 3 ^ 40 * 2339193 * 2
def baseEnd_2339193 : Nat := 1201130352632771630329753

theorem tailTrace_2339193 : CollatzResearch.WordTrace tailWord_2339193 prefixEnd_2339193 1201130352632771630329753 := by
  unfold tailWord_2339193
  simp only [CollatzResearch.WordTrace]
  refine ⟨85317377814510738203502233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56878251876340492135668155 85317377814510738203502233)
  ·
    refine ⟨63988033360883053652626675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85317377814510738203502233 63988033360883053652626675)
    ·
      refine ⟨95982050041324580478940013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63988033360883053652626675 95982050041324580478940013)
      ·
        refine ⟨35993268765496717679602505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95982050041324580478940013 35993268765496717679602505)
        ·
          refine ⟨26994951574122538259701879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35993268765496717679602505 26994951574122538259701879)
          ·
            refine ⟨40492427361183807389552819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26994951574122538259701879 40492427361183807389552819)
            ·
              refine ⟨60738641041775711084329229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40492427361183807389552819 60738641041775711084329229)
              ·
                refine ⟨22776990390665891656623461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60738641041775711084329229 22776990390665891656623461)
                ·
                  refine ⟨4270685698249854685616899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22776990390665891656623461 4270685698249854685616899)
                  ·
                    refine ⟨6406028547374782028425349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4270685698249854685616899 6406028547374782028425349)
                    ·
                      refine ⟨1201130352632771630329753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6406028547374782028425349 1201130352632771630329753)
                      ·
                        rfl

theorem cell23_2339193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_2339193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339193 prefixEnd_2339193 := by exact prefixLift 2339193
  have htrace : WordTrace (prefixWord ++ tailWord_2339193) baseStart_2339193 baseEnd_2339193 := by
    simpa [prefixWord, tailWord_2339193, baseEnd_2339193] using wordTrace_append hprefix tailTrace_2339193
  have hstable : (prefixWord ++ tailWord_2339193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339193).length < 2 ^ (prefixWord ++ tailWord_2339193).sum := by decide
  have hdescent : baseEnd_2339193 < baseStart_2339193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339297 : List Nat := [1, 2, 3, 1, 2, 2, 5, 1, 1, 5]
def baseStart_2339297 : Nat := 118140960795 + 2339297 * 2 ^ 59
def prefixEnd_2339297 : Nat := 4983230072969 + 3 ^ 40 * 2339297 * 2
def baseEnd_2339297 : Nat := 400394584873613074476425

theorem tailTrace_2339297 : CollatzResearch.WordTrace tailWord_2339297 prefixEnd_2339297 400394584873613074476425 := by
  unfold tailWord_2339297
  simp only [CollatzResearch.WordTrace]
  refine ⟨85321171006133963965288145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56880780670755975976858763 85321171006133963965288145)
  ·
    refine ⟨63990878254600472973966109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85321171006133963965288145 63990878254600472973966109)
    ·
      refine ⟨23996579345475177365237291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63990878254600472973966109 23996579345475177365237291)
      ·
        refine ⟨35994869018212766047855937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23996579345475177365237291 35994869018212766047855937)
        ·
          refine ⟨26996151763659574535891953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35994869018212766047855937 26996151763659574535891953)
          ·
            refine ⟨20247113822744680901918965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26996151763659574535891953 20247113822744680901918965)
            ·
              refine ⟨1898166920882313834554903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20247113822744680901918965 1898166920882313834554903)
              ·
                refine ⟨2847250381323470751832355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1898166920882313834554903 2847250381323470751832355)
                ·
                  refine ⟨4270875571985206127748533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2847250381323470751832355 4270875571985206127748533)
                  ·
                    refine ⟨400394584873613074476425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4270875571985206127748533 400394584873613074476425)
                    ·
                      rfl

theorem cell23_2339297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_2339297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339297 prefixEnd_2339297 := by exact prefixLift 2339297
  have htrace : WordTrace (prefixWord ++ tailWord_2339297) baseStart_2339297 baseEnd_2339297 := by
    simpa [prefixWord, tailWord_2339297, baseEnd_2339297] using wordTrace_append hprefix tailTrace_2339297
  have hstable : (prefixWord ++ tailWord_2339297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339297).length < 2 ^ (prefixWord ++ tailWord_2339297).sum := by decide
  have hdescent : baseEnd_2339297 < baseStart_2339297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339320 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 5, 2, 3]
def baseStart_2339320 : Nat := 118140960795 + 2339320 * 2 ^ 59
def prefixEnd_2339320 : Nat := 4983230072969 + 3 ^ 40 * 2339320 * 2
def baseEnd_2339320 : Nat := 1201195564675892633441669

theorem tailTrace_2339320 : CollatzResearch.WordTrace tailWord_2339320 prefixEnd_2339320 1201195564675892633441669 := by
  unfold tailWord_2339320
  simp only [CollatzResearch.WordTrace]
  refine ⟨42661004942525319446687707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56881339923367092595583609 42661004942525319446687707)
  ·
    refine ⟨63991507413787979170031561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42661004942525319446687707 63991507413787979170031561)
    ·
      refine ⟨47993630560340984377523671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63991507413787979170031561 47993630560340984377523671)
      ·
        refine ⟨71990445840511476566285507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47993630560340984377523671 71990445840511476566285507)
        ·
          refine ⟨107985668760767214849428261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71990445840511476566285507 107985668760767214849428261)
          ·
            refine ⟨20247312892643852784267799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107985668760767214849428261 20247312892643852784267799)
            ·
              refine ⟨30370969338965779176401699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20247312892643852784267799 30370969338965779176401699)
              ·
                refine ⟨45556454008448668764602549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30370969338965779176401699 45556454008448668764602549)
                ·
                  refine ⟨4270917563292062696681489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45556454008448668764602549 4270917563292062696681489)
                  ·
                    refine ⟨3203188172469047022511117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4270917563292062696681489 3203188172469047022511117)
                    ·
                      refine ⟨1201195564675892633441669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3203188172469047022511117 1201195564675892633441669)
                      ·
                        rfl

theorem cell23_2339320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_2339320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339320 prefixEnd_2339320 := by exact prefixLift 2339320
  have htrace : WordTrace (prefixWord ++ tailWord_2339320) baseStart_2339320 baseEnd_2339320 := by
    simpa [prefixWord, tailWord_2339320, baseEnd_2339320] using wordTrace_append hprefix tailTrace_2339320
  have hstable : (prefixWord ++ tailWord_2339320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339320).length < 2 ^ (prefixWord ++ tailWord_2339320).sum := by decide
  have hdescent : baseEnd_2339320 < baseStart_2339320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339353 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 4, 7]
def baseStart_2339353 : Nat := 118140960795 + 2339353 * 2 ^ 59
def prefixEnd_2339353 : Nat := 4983230072969 + 3 ^ 40 * 2339353 * 2
def baseEnd_2339353 : Nat := 400404169845830334776339

theorem tailTrace_2339353 : CollatzResearch.WordTrace tailWord_2339353 prefixEnd_2339353 400404169845830334776339 := by
  unfold tailWord_2339353
  simp only [CollatzResearch.WordTrace]
  refine ⟨85323213493931085529326713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56882142329287390352884475 85323213493931085529326713)
  ·
    refine ⟨63992410120448314146995035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85323213493931085529326713 63992410120448314146995035)
    ·
      refine ⟨95988615180672471220492553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63992410120448314146995035 95988615180672471220492553)
      ·
        refine ⟨71991461385504353415369415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95988615180672471220492553 71991461385504353415369415)
        ·
          refine ⟨107987192078256530123054123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71991461385504353415369415 107987192078256530123054123)
          ·
            refine ⟨161980788117384795184581185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107987192078256530123054123 161980788117384795184581185)
            ·
              refine ⟨121485591088038596388435889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161980788117384795184581185 121485591088038596388435889)
              ·
                refine ⟨91114193316028947291326917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121485591088038596388435889 91114193316028947291326917)
                ·
                  refine ⟨17083911246755427617123797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91114193316028947291326917 17083911246755427617123797)
                  ·
                    refine ⟨400404169845830334776339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17083911246755427617123797 400404169845830334776339)
                    ·
                      rfl

theorem cell23_2339353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 7].length) (baseStart_2339353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339353 prefixEnd_2339353 := by exact prefixLift 2339353
  have htrace : WordTrace (prefixWord ++ tailWord_2339353) baseStart_2339353 baseEnd_2339353 := by
    simpa [prefixWord, tailWord_2339353, baseEnd_2339353] using wordTrace_append hprefix tailTrace_2339353
  have hstable : (prefixWord ++ tailWord_2339353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339353).length < 2 ^ (prefixWord ++ tailWord_2339353).sum := by decide
  have hdescent : baseEnd_2339353 < baseStart_2339353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339354 : List Nat := [3, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3]
def baseStart_2339354 : Nat := 118140960795 + 2339354 * 2 ^ 59
def prefixEnd_2339354 : Nat := 4983230072969 + 3 ^ 40 * 2339354 * 2
def baseEnd_2339354 : Nat := 1201213023018145500416513

theorem tailTrace_2339354 : CollatzResearch.WordTrace tailWord_2339354 prefixEnd_2339354 1201213023018145500416513 := by
  unfold tailWord_2339354
  simp only [CollatzResearch.WordTrace]
  refine ⟨21330812491731865675028279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56882166644618308466742077 21330812491731865675028279)
  ·
    refine ⟨31996218737597798512542419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21330812491731865675028279 31996218737597798512542419)
    ·
      refine ⟨47994328106396697768813629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31996218737597798512542419 47994328106396697768813629)
      ·
        refine ⟨17997873039898761663305111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47994328106396697768813629 17997873039898761663305111)
        ·
          refine ⟨26996809559848142494957667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17997873039898761663305111 26996809559848142494957667)
          ·
            refine ⟨40495214339772213742436501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26996809559848142494957667 40495214339772213742436501)
            ·
              refine ⟨1898213172176822519176711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40495214339772213742436501 1898213172176822519176711)
              ·
                refine ⟨2847319758265233778765067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1898213172176822519176711 2847319758265233778765067)
                ·
                  refine ⟨4270979637397850668147601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2847319758265233778765067 4270979637397850668147601)
                  ·
                    refine ⟨3203234728048388001110701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4270979637397850668147601 3203234728048388001110701)
                    ·
                      refine ⟨1201213023018145500416513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3203234728048388001110701 1201213023018145500416513)
                      ·
                        rfl

theorem cell23_2339354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_2339354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339354 prefixEnd_2339354 := by exact prefixLift 2339354
  have htrace : WordTrace (prefixWord ++ tailWord_2339354) baseStart_2339354 baseEnd_2339354 := by
    simpa [prefixWord, tailWord_2339354, baseEnd_2339354] using wordTrace_append hprefix tailTrace_2339354
  have hstable : (prefixWord ++ tailWord_2339354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339354).length < 2 ^ (prefixWord ++ tailWord_2339354).sum := by decide
  have hdescent : baseEnd_2339354 < baseStart_2339354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339368 : List Nat := [2, 1, 5, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_2339368 : Nat := 118140960795 + 2339368 * 2 ^ 59
def prefixEnd_2339368 : Nat := 4983230072969 + 3 ^ 40 * 2339368 * 2
def baseEnd_2339368 : Nat := 1201220211747308445641449

theorem tailTrace_2339368 : CollatzResearch.WordTrace tailWord_2339368 prefixEnd_2339368 1201220211747308445641449 := by
  unfold tailWord_2339368
  simp only [CollatzResearch.WordTrace]
  refine ⟨42661880294438371545561379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56882507059251162060748505 42661880294438371545561379)
  ·
    refine ⟨63992820441657557318342069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42661880294438371545561379 63992820441657557318342069)
    ·
      refine ⟨5999326916405395998594569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63992820441657557318342069 5999326916405395998594569)
      ·
        refine ⟨4499495187304046998945927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5999326916405395998594569 4499495187304046998945927)
        ·
          refine ⟨6749242780956070498418891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4499495187304046998945927 6749242780956070498418891)
          ·
            refine ⟨10123864171434105747628337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6749242780956070498418891 10123864171434105747628337)
            ·
              refine ⟨7592898128575579310721253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10123864171434105747628337 7592898128575579310721253)
              ·
                refine ⟨1423668399107921120760235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7592898128575579310721253 1423668399107921120760235)
                ·
                  refine ⟨2135502598661881681140353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1423668399107921120760235 2135502598661881681140353)
                  ·
                    refine ⟨1601626948996411260855265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2135502598661881681140353 1601626948996411260855265)
                    ·
                      refine ⟨1201220211747308445641449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1601626948996411260855265 1201220211747308445641449)
                      ·
                        rfl

theorem cell23_2339368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_2339368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339368 prefixEnd_2339368 := by exact prefixLift 2339368
  have htrace : WordTrace (prefixWord ++ tailWord_2339368) baseStart_2339368 baseEnd_2339368 := by
    simpa [prefixWord, tailWord_2339368, baseEnd_2339368] using wordTrace_append hprefix tailTrace_2339368
  have hstable : (prefixWord ++ tailWord_2339368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339368).length < 2 ^ (prefixWord ++ tailWord_2339368).sum := by decide
  have hdescent : baseEnd_2339368 < baseStart_2339368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339377 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 5, 3, 2]
def baseStart_2339377 : Nat := 118140960795 + 2339377 * 2 ^ 59
def prefixEnd_2339377 : Nat := 4983230072969 + 3 ^ 40 * 2339377 * 2
def baseEnd_2339377 : Nat := 1201224833073198910428907

theorem tailTrace_2339377 : CollatzResearch.WordTrace tailWord_2339377 prefixEnd_2339377 1201224833073198910428907 := by
  unfold tailWord_2339377
  simp only [CollatzResearch.WordTrace]
  refine ⟨85324088845844137628200385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56882725897229425085466923 85324088845844137628200385)
  ·
    refine ⟨63993066634383103221150289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85324088845844137628200385 63993066634383103221150289)
    ·
      refine ⟨47994799975787327415862717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63993066634383103221150289 47994799975787327415862717)
      ·
        refine ⟨17998049990920247780948519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47994799975787327415862717 17998049990920247780948519)
        ·
          refine ⟨26997074986380371671422779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17998049990920247780948519 26997074986380371671422779)
          ·
            refine ⟨40495612479570557507134169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26997074986380371671422779 40495612479570557507134169)
            ·
              refine ⟨30371709359677918130350627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40495612479570557507134169 30371709359677918130350627)
              ·
                refine ⟨45557564039516877195525941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30371709359677918130350627 45557564039516877195525941)
                ·
                  refine ⟨4271021628704707237080557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45557564039516877195525941 4271021628704707237080557)
                  ·
                    refine ⟨1601633110764265213905209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4271021628704707237080557 1601633110764265213905209)
                    ·
                      refine ⟨1201224833073198910428907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1601633110764265213905209 1201224833073198910428907)
                      ·
                        rfl

theorem cell23_2339377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_2339377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339377 prefixEnd_2339377 := by exact prefixLift 2339377
  have htrace : WordTrace (prefixWord ++ tailWord_2339377) baseStart_2339377 baseEnd_2339377 := by
    simpa [prefixWord, tailWord_2339377, baseEnd_2339377] using wordTrace_append hprefix tailTrace_2339377
  have hstable : (prefixWord ++ tailWord_2339377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339377).length < 2 ^ (prefixWord ++ tailWord_2339377).sum := by decide
  have hdescent : baseEnd_2339377 < baseStart_2339377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339407 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 1, 4, 2]
def baseStart_2339407 : Nat := 118140960795 + 2339407 * 2 ^ 59
def prefixEnd_2339407 : Nat := 4983230072969 + 3 ^ 40 * 2339407 * 2
def baseEnd_2339407 : Nat := 1201240237492833793053769

theorem tailTrace_2339407 : CollatzResearch.WordTrace tailWord_2339407 prefixEnd_2339407 1201240237492833793053769 := by
  unfold tailWord_2339407
  simp only [CollatzResearch.WordTrace]
  refine ⟨85325183035735452751792475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56883455357156968501194983 85325183035735452751792475)
  ·
    refine ⟨127987774553603179127688713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85325183035735452751792475 127987774553603179127688713)
    ·
      refine ⟨95990830915202384345766535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127987774553603179127688713 95990830915202384345766535)
      ·
        refine ⟨143986246372803576518649803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95990830915202384345766535 143986246372803576518649803)
        ·
          refine ⟨215979369559205364777974705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143986246372803576518649803 215979369559205364777974705)
          ·
            refine ⟨161984527169404023583481029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215979369559205364777974705 161984527169404023583481029)
            ·
              refine ⟨30372098844263254421902693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161984527169404023583481029 30372098844263254421902693)
              ·
                refine ⟨5694768533299360204106755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30372098844263254421902693 5694768533299360204106755)
                ·
                  refine ⟨8542152799949040306160133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5694768533299360204106755 8542152799949040306160133)
                  ·
                    refine ⟨1601653649990445057405025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8542152799949040306160133 1601653649990445057405025)
                    ·
                      refine ⟨1201240237492833793053769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1601653649990445057405025 1201240237492833793053769)
                      ·
                        rfl

theorem cell23_2339407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 4, 2].length) (baseStart_2339407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339407 prefixEnd_2339407 := by exact prefixLift 2339407
  have htrace : WordTrace (prefixWord ++ tailWord_2339407) baseStart_2339407 baseEnd_2339407 := by
    simpa [prefixWord, tailWord_2339407, baseEnd_2339407] using wordTrace_append hprefix tailTrace_2339407
  have hstable : (prefixWord ++ tailWord_2339407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339407).length < 2 ^ (prefixWord ++ tailWord_2339407).sum := by decide
  have hdescent : baseEnd_2339407 < baseStart_2339407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339424 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 4, 2, 2]
def baseStart_2339424 : Nat := 118140960795 + 2339424 * 2 ^ 59
def prefixEnd_2339424 : Nat := 4983230072969 + 3 ^ 40 * 2339424 * 2
def baseEnd_2339424 : Nat := 1201248966663960226541191

theorem tailTrace_2339424 : CollatzResearch.WordTrace tailWord_2339424 prefixEnd_2339424 1201248966663960226541191 := by
  unfold tailWord_2339424
  simp only [CollatzResearch.WordTrace]
  refine ⟨42662901538336932327580663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56883868717782576436774217 42662901538336932327580663)
  ·
    refine ⟨63994352307505398491370995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42662901538336932327580663 63994352307505398491370995)
    ·
      refine ⟨95991528461258097737056493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63994352307505398491370995 95991528461258097737056493)
      ·
        refine ⟨35996823172971786651396185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95991528461258097737056493 35996823172971786651396185)
        ·
          refine ⟨26997617379728839988547139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35996823172971786651396185 26997617379728839988547139)
          ·
            refine ⟨40496426069593259982820709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26997617379728839988547139 40496426069593259982820709)
            ·
              refine ⟨7593079888048736246778883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40496426069593259982820709 7593079888048736246778883)
              ·
                refine ⟨11389619832073104370168325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7593079888048736246778883 11389619832073104370168325)
                ·
                  refine ⟨2135553718513707069406561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11389619832073104370168325 2135553718513707069406561)
                  ·
                    refine ⟨1601665288885280302054921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2135553718513707069406561 1601665288885280302054921)
                    ·
                      refine ⟨1201248966663960226541191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1601665288885280302054921 1201248966663960226541191)
                      ·
                        rfl

theorem cell23_2339424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_2339424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339424 prefixEnd_2339424 := by exact prefixLift 2339424
  have htrace : WordTrace (prefixWord ++ tailWord_2339424) baseStart_2339424 baseEnd_2339424 := by
    simpa [prefixWord, tailWord_2339424, baseEnd_2339424] using wordTrace_append hprefix tailTrace_2339424
  have hstable : (prefixWord ++ tailWord_2339424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339424).length < 2 ^ (prefixWord ++ tailWord_2339424).sum := by decide
  have hdescent : baseEnd_2339424 < baseStart_2339424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339445 : List Nat := [1, 3, 4, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_2339445 : Nat := 118140960795 + 2339445 * 2 ^ 59
def prefixEnd_2339445 : Nat := 4983230072969 + 3 ^ 40 * 2339445 * 2
def baseEnd_2339445 : Nat := 1201259749757704644378595

theorem tailTrace_2339445 : CollatzResearch.WordTrace tailWord_2339445 prefixEnd_2339445 1201259749757704644378595 := by
  unfold tailWord_2339445
  simp only [CollatzResearch.WordTrace]
  refine ⟨85326569009597785241675789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56884379339731856827783859 85326569009597785241675789)
  ·
    refine ⟨31997463378599169465628421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85326569009597785241675789 31997463378599169465628421)
    ·
      refine ⟨5999524383487344274805329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31997463378599169465628421 5999524383487344274805329)
      ·
        refine ⟨4499643287615508206103997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5999524383487344274805329 4499643287615508206103997)
        ·
          refine ⟨1687366232855815577288999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4499643287615508206103997 1687366232855815577288999)
          ·
            refine ⟨2531049349283723365933499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1687366232855815577288999 2531049349283723365933499)
            ·
              refine ⟨3796574023925585048900249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2531049349283723365933499 3796574023925585048900249)
              ·
                refine ⟨2847430517944188786675187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3796574023925585048900249 2847430517944188786675187)
                ·
                  refine ⟨4271145776916283180012781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2847430517944188786675187 4271145776916283180012781)
                  ·
                    refine ⟨1601679666343606192504793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4271145776916283180012781 1601679666343606192504793)
                    ·
                      refine ⟨1201259749757704644378595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1601679666343606192504793 1201259749757704644378595)
                      ·
                        rfl

theorem cell23_2339445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_2339445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339445 prefixEnd_2339445 := by exact prefixLift 2339445
  have htrace : WordTrace (prefixWord ++ tailWord_2339445) baseStart_2339445 baseEnd_2339445 := by
    simpa [prefixWord, tailWord_2339445, baseEnd_2339445] using wordTrace_append hprefix tailTrace_2339445
  have hstable : (prefixWord ++ tailWord_2339445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339445).length < 2 ^ (prefixWord ++ tailWord_2339445).sum := by decide
  have hdescent : baseEnd_2339445 < baseStart_2339445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339484 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 2, 5, 2]
def baseStart_2339484 : Nat := 118140960795 + 2339484 * 2 ^ 59
def prefixEnd_2339484 : Nat := 4983230072969 + 3 ^ 40 * 2339484 * 2
def baseEnd_2339484 : Nat := 1201279775503229991790915

theorem tailTrace_2339484 : CollatzResearch.WordTrace tailWord_2339484 prefixEnd_2339484 1201279775503229991790915 := by
  unfold tailWord_2339484
  simp only [CollatzResearch.WordTrace]
  refine ⟨42663995728228247451172753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56885327637637663268230337 42663995728228247451172753)
  ·
    refine ⟨31997996796171185588379565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42663995728228247451172753 31997996796171185588379565)
    ·
      refine ⟨11999248798564194595642337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31997996796171185588379565 11999248798564194595642337)
      ·
        refine ⟨8999436598923145946731753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11999248798564194595642337 8999436598923145946731753)
        ·
          refine ⟨6749577449192359460048815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8999436598923145946731753 6749577449192359460048815)
          ·
            refine ⟨10124366173788539190073223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6749577449192359460048815 10124366173788539190073223)
            ·
              refine ⟨15186549260682808785109835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10124366173788539190073223 15186549260682808785109835)
              ·
                refine ⟨22779823891024213177664753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15186549260682808785109835 22779823891024213177664753)
                ·
                  refine ⟨17084867918268159883248565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22779823891024213177664753 17084867918268159883248565)
                  ·
                    refine ⟨1601706367337639989054553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17084867918268159883248565 1601706367337639989054553)
                    ·
                      refine ⟨1201279775503229991790915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1601706367337639989054553 1201279775503229991790915)
                      ·
                        rfl

theorem cell23_2339484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_2339484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339484 prefixEnd_2339484 := by exact prefixLift 2339484
  have htrace : WordTrace (prefixWord ++ tailWord_2339484) baseStart_2339484 baseEnd_2339484 := by
    simpa [prefixWord, tailWord_2339484, baseEnd_2339484] using wordTrace_append hprefix tailTrace_2339484
  have hstable : (prefixWord ++ tailWord_2339484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339484).length < 2 ^ (prefixWord ++ tailWord_2339484).sum := by decide
  have hdescent : baseEnd_2339484 < baseStart_2339484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339497 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 1, 6, 2]
def baseStart_2339497 : Nat := 118140960795 + 2339497 * 2 ^ 59
def prefixEnd_2339497 : Nat := 4983230072969 + 3 ^ 40 * 2339497 * 2
def baseEnd_2339497 : Nat := 1201286450751738440928355

theorem tailTrace_2339497 : CollatzResearch.WordTrace tailWord_2339497 prefixEnd_2339497 1201286450751738440928355 := by
  unfold tailWord_2339497
  simp only [CollatzResearch.WordTrace]
  refine ⟨85328465605409398122568745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56885643736939598748379163 85328465605409398122568745)
  ·
    refine ⟨63996349204057048591926559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85328465605409398122568745 63996349204057048591926559)
    ·
      refine ⟨95994523806085572887889839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63996349204057048591926559 95994523806085572887889839)
      ·
        refine ⟨143991785709128359331834759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95994523806085572887889839 143991785709128359331834759)
        ·
          refine ⟨215987678563692538997752139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143991785709128359331834759 215987678563692538997752139)
          ·
            refine ⟨323981517845538808496628209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215987678563692538997752139 323981517845538808496628209)
            ·
              refine ⟨242986138384154106372471157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323981517845538808496628209 242986138384154106372471157)
              ·
                refine ⟨22779950473514447472419171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 242986138384154106372471157 22779950473514447472419171)
                ·
                  refine ⟨34169925710271671208628757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22779950473514447472419171 34169925710271671208628757)
                  ·
                    refine ⟨1601715267668984587904473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34169925710271671208628757 1601715267668984587904473)
                    ·
                      refine ⟨1201286450751738440928355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1601715267668984587904473 1201286450751738440928355)
                      ·
                        rfl

theorem cell23_2339497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 6, 2].length) (baseStart_2339497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339497 prefixEnd_2339497 := by exact prefixLift 2339497
  have htrace : WordTrace (prefixWord ++ tailWord_2339497) baseStart_2339497 baseEnd_2339497 := by
    simpa [prefixWord, tailWord_2339497, baseEnd_2339497] using wordTrace_append hprefix tailTrace_2339497
  have hstable : (prefixWord ++ tailWord_2339497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339497).length < 2 ^ (prefixWord ++ tailWord_2339497).sum := by decide
  have hdescent : baseEnd_2339497 < baseStart_2339497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339507 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 5, 4]
def baseStart_2339507 : Nat := 118140960795 + 2339507 * 2 ^ 59
def prefixEnd_2339507 : Nat := 4983230072969 + 3 ^ 40 * 2339507 * 2
def baseEnd_2339507 : Nat := 400430528519427800601103

theorem tailTrace_2339507 : CollatzResearch.WordTrace tailWord_2339507 prefixEnd_2339507 400430528519427800601103 := by
  unfold tailWord_2339507
  simp only [CollatzResearch.WordTrace]
  refine ⟨85328830335373169830432775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56885886890248779886955183 85328830335373169830432775)
  ·
    refine ⟨127993245503059754745649163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85328830335373169830432775 127993245503059754745649163)
    ·
      refine ⟨191989868254589632118473745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127993245503059754745649163 191989868254589632118473745)
      ·
        refine ⟨143992401190942224088855309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191989868254589632118473745 143992401190942224088855309)
        ·
          refine ⟨53997150446603334033320741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143992401190942224088855309 53997150446603334033320741)
          ·
            refine ⟨10124465708738125131247639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53997150446603334033320741 10124465708738125131247639)
            ·
              refine ⟨15186698563107187696871459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10124465708738125131247639 15186698563107187696871459)
              ·
                refine ⟨22780047844660781545307189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15186698563107187696871459 22780047844660781545307189)
                ·
                  refine ⟨2135629485436948269872549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22780047844660781545307189 2135629485436948269872549)
                  ·
                    refine ⟨400430528519427800601103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2135629485436948269872549 400430528519427800601103)
                    ·
                      rfl

theorem cell23_2339507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 4].length) (baseStart_2339507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339507 prefixEnd_2339507 := by exact prefixLift 2339507
  have htrace : WordTrace (prefixWord ++ tailWord_2339507) baseStart_2339507 baseEnd_2339507 := by
    simpa [prefixWord, tailWord_2339507, baseEnd_2339507] using wordTrace_append hprefix tailTrace_2339507
  have hstable : (prefixWord ++ tailWord_2339507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339507).length < 2 ^ (prefixWord ++ tailWord_2339507).sum := by decide
  have hdescent : baseEnd_2339507 < baseStart_2339507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339511 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 2, 5]
def baseStart_2339511 : Nat := 118140960795 + 2339511 * 2 ^ 59
def prefixEnd_2339511 : Nat := 4983230072969 + 3 ^ 40 * 2339511 * 2
def baseEnd_2339511 : Nat := 400431213160300462051097

theorem tailTrace_2339511 : CollatzResearch.WordTrace tailWord_2339511 prefixEnd_2339511 400431213160300462051097 := by
  unfold tailWord_2339511
  simp only [CollatzResearch.WordTrace]
  refine ⟨85328976227358678513578387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56885984151572452342385591 85328976227358678513578387)
  ·
    refine ⟨127993464341038017770367581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85328976227358678513578387 127993464341038017770367581)
    ·
      refine ⟨47997549127889256663887843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127993464341038017770367581 47997549127889256663887843)
      ·
        refine ⟨71996323691833884995831765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47997549127889256663887843 71996323691833884995831765)
        ·
          refine ⟨1687413836527356679589807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 71996323691833884995831765 1687413836527356679589807)
          ·
            refine ⟨2531120754791035019384711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1687413836527356679589807 2531120754791035019384711)
            ·
              refine ⟨3796681132186552529077067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2531120754791035019384711 3796681132186552529077067)
              ·
                refine ⟨5695021698279828793615601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3796681132186552529077067 5695021698279828793615601)
                ·
                  refine ⟨4271266273709871595211701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5695021698279828793615601 4271266273709871595211701)
                  ·
                    refine ⟨400431213160300462051097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4271266273709871595211701 400431213160300462051097)
                    ·
                      rfl

theorem cell23_2339511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 2, 5].length) (baseStart_2339511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339511 prefixEnd_2339511 := by exact prefixLift 2339511
  have htrace : WordTrace (prefixWord ++ tailWord_2339511) baseStart_2339511 baseEnd_2339511 := by
    simpa [prefixWord, tailWord_2339511, baseEnd_2339511] using wordTrace_append hprefix tailTrace_2339511
  have hstable : (prefixWord ++ tailWord_2339511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339511).length < 2 ^ (prefixWord ++ tailWord_2339511).sum := by decide
  have hdescent : baseEnd_2339511 < baseStart_2339511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339587 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 4]
def baseStart_2339587 : Nat := 118140960795 + 2339587 * 2 ^ 59
def prefixEnd_2339587 : Nat := 4983230072969 + 3 ^ 40 * 2339587 * 2
def baseEnd_2339587 : Nat := 1201332664010643088802941

theorem tailTrace_2339587 : CollatzResearch.WordTrace tailWord_2339587 prefixEnd_2339587 1201332664010643088802941 := by
  unfold tailWord_2339587
  simp only [CollatzResearch.WordTrace]
  refine ⟨85331748175083343493345015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56887832116722228995563343 85331748175083343493345015)
  ·
    refine ⟨127997622262625015240017523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85331748175083343493345015 127997622262625015240017523)
    ·
      refine ⟨191996433393937522860026285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127997622262625015240017523 191996433393937522860026285)
      ·
        refine ⟨71998662522726571072509857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191996433393937522860026285 71998662522726571072509857)
        ·
          refine ⟨53998996892044928304382393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71998662522726571072509857 53998996892044928304382393)
          ·
            refine ⟨40499247669033696228286795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53998996892044928304382393 40499247669033696228286795)
            ·
              refine ⟨60748871503550544342430193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40499247669033696228286795 60748871503550544342430193)
              ·
                refine ⟨45561653627662908256822645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60748871503550544342430193 45561653627662908256822645)
                ·
                  refine ⟨4271405027593397649077123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45561653627662908256822645 4271405027593397649077123)
                  ·
                    refine ⟨6407107541390096473615685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4271405027593397649077123 6407107541390096473615685)
                    ·
                      refine ⟨1201332664010643088802941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6407107541390096473615685 1201332664010643088802941)
                      ·
                        rfl

theorem cell23_2339587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_2339587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339587 prefixEnd_2339587 := by exact prefixLift 2339587
  have htrace : WordTrace (prefixWord ++ tailWord_2339587) baseStart_2339587 baseEnd_2339587 := by
    simpa [prefixWord, tailWord_2339587, baseEnd_2339587] using wordTrace_append hprefix tailTrace_2339587
  have hstable : (prefixWord ++ tailWord_2339587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339587).length < 2 ^ (prefixWord ++ tailWord_2339587).sum := by decide
  have hdescent : baseEnd_2339587 < baseStart_2339587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339591 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 4, 3, 2]
def baseStart_2339591 : Nat := 118140960795 + 2339591 * 2 ^ 59
def prefixEnd_2339591 : Nat := 4983230072969 + 3 ^ 40 * 2339591 * 2
def baseEnd_2339591 : Nat := 1201334717933261073152923

theorem tailTrace_2339591 : CollatzResearch.WordTrace tailWord_2339591 prefixEnd_2339591 1201334717933261073152923 := by
  unfold tailWord_2339591
  simp only [CollatzResearch.WordTrace]
  refine ⟨85331894067068852176490627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56887929378045901450993751 85331894067068852176490627)
  ·
    refine ⟨127997841100603278264735941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85331894067068852176490627 127997841100603278264735941)
    ·
      refine ⟨23999595206363114674637989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127997841100603278264735941 23999595206363114674637989)
      ·
        refine ⟨4499924101193084001494623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23999595206363114674637989 4499924101193084001494623)
        ·
          refine ⟨6749886151789626002241935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4499924101193084001494623 6749886151789626002241935)
          ·
            refine ⟨10124829227684439003362903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6749886151789626002241935 10124829227684439003362903)
            ·
              refine ⟨15187243841526658505044355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10124829227684439003362903 15187243841526658505044355)
              ·
                refine ⟨22780865762289987757566533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15187243841526658505044355 22780865762289987757566533)
                ·
                  refine ⟨4271412330429372704543725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22780865762289987757566533 4271412330429372704543725)
                  ·
                    refine ⟨1601779623911014764203897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4271412330429372704543725 1601779623911014764203897)
                    ·
                      refine ⟨1201334717933261073152923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1601779623911014764203897 1201334717933261073152923)
                      ·
                        rfl

theorem cell23_2339591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_2339591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339591 prefixEnd_2339591 := by exact prefixLift 2339591
  have htrace : WordTrace (prefixWord ++ tailWord_2339591) baseStart_2339591 baseEnd_2339591 := by
    simpa [prefixWord, tailWord_2339591, baseEnd_2339591] using wordTrace_append hprefix tailTrace_2339591
  have hstable : (prefixWord ++ tailWord_2339591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339591).length < 2 ^ (prefixWord ++ tailWord_2339591).sum := by decide
  have hdescent : baseEnd_2339591 < baseStart_2339591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339617 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_2339617 : Nat := 118140960795 + 2339617 * 2 ^ 59
def prefixEnd_2339617 : Nat := 4983230072969 + 3 ^ 40 * 2339617 * 2
def baseEnd_2339617 : Nat := 1201348068430277971427803

theorem tailTrace_2339617 : CollatzResearch.WordTrace tailWord_2339617 prefixEnd_2339617 1201348068430277971427803 := by
  unfold tailWord_2339617
  simp only [CollatzResearch.WordTrace]
  refine ⟨85332842364974658616937105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56888561576649772411291403 85332842364974658616937105)
  ·
    refine ⟨63999631773730993962702829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85332842364974658616937105 63999631773730993962702829)
    ·
      refine ⟨23999861915149122736013561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63999631773730993962702829 23999861915149122736013561)
      ·
        refine ⟨17999896436361842052010171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23999861915149122736013561 17999896436361842052010171)
        ·
          refine ⟨26999844654542763078015257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17999896436361842052010171 26999844654542763078015257)
          ·
            refine ⟨20249883490907072308511443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26999844654542763078015257 20249883490907072308511443)
            ·
              refine ⟨30374825236360608462767165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20249883490907072308511443 30374825236360608462767165)
              ·
                refine ⟨11390559463635228173537687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30374825236360608462767165 11390559463635228173537687)
                ·
                  refine ⟨17085839195452842260306531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11390559463635228173537687 17085839195452842260306531)
                  ·
                    refine ⟨25628758793179263390459797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17085839195452842260306531 25628758793179263390459797)
                    ·
                      refine ⟨1201348068430277971427803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25628758793179263390459797 1201348068430277971427803)
                      ·
                        rfl

theorem cell23_2339617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_2339617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339617 prefixEnd_2339617 := by exact prefixLift 2339617
  have htrace : WordTrace (prefixWord ++ tailWord_2339617) baseStart_2339617 baseEnd_2339617 := by
    simpa [prefixWord, tailWord_2339617, baseEnd_2339617] using wordTrace_append hprefix tailTrace_2339617
  have hstable : (prefixWord ++ tailWord_2339617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339617).length < 2 ^ (prefixWord ++ tailWord_2339617).sum := by decide
  have hdescent : baseEnd_2339617 < baseStart_2339617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339621 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 5, 2, 2]
def baseStart_2339621 : Nat := 118140960795 + 2339621 * 2 ^ 59
def prefixEnd_2339621 : Nat := 4983230072969 + 3 ^ 40 * 2339621 * 2
def baseEnd_2339621 : Nat := 1201350122352895955777785

theorem tailTrace_2339621 : CollatzResearch.WordTrace tailWord_2339621 prefixEnd_2339621 1201350122352895955777785 := by
  unfold tailWord_2339621
  simp only [CollatzResearch.WordTrace]
  refine ⟨85332988256960167300082717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56888658837973444866721811 85332988256960167300082717)
  ·
    refine ⟨31999870596360062737531019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85332988256960167300082717 31999870596360062737531019)
    ·
      refine ⟨47999805894540094106296529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31999870596360062737531019 47999805894540094106296529)
      ·
        refine ⟨35999854420905070579722397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47999805894540094106296529 35999854420905070579722397)
        ·
          refine ⟨13499945407839401467395899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35999854420905070579722397 13499945407839401467395899)
          ·
            refine ⟨20249918111759102201093849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13499945407839401467395899 20249918111759102201093849)
            ·
              refine ⟨15187438583819326650820387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20249918111759102201093849 15187438583819326650820387)
              ·
                refine ⟨22781157875728989976230581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15187438583819326650820387 22781157875728989976230581)
                ·
                  refine ⟨2135733550849592810271617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22781157875728989976230581 2135733550849592810271617)
                  ·
                    refine ⟨1601800163137194607703713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2135733550849592810271617 1601800163137194607703713)
                    ·
                      refine ⟨1201350122352895955777785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1601800163137194607703713 1201350122352895955777785)
                      ·
                        rfl

theorem cell23_2339621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_2339621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339621 prefixEnd_2339621 := by exact prefixLift 2339621
  have htrace : WordTrace (prefixWord ++ tailWord_2339621) baseStart_2339621 baseEnd_2339621 := by
    simpa [prefixWord, tailWord_2339621, baseEnd_2339621] using wordTrace_append hprefix tailTrace_2339621
  have hstable : (prefixWord ++ tailWord_2339621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339621).length < 2 ^ (prefixWord ++ tailWord_2339621).sum := by decide
  have hdescent : baseEnd_2339621 < baseStart_2339621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339634 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_2339634 : Nat := 118140960795 + 2339634 * 2 ^ 59
def prefixEnd_2339634 : Nat := 4983230072969 + 3 ^ 40 * 2339634 * 2
def baseEnd_2339634 : Nat := 1201356797601404404915225

theorem tailTrace_2339634 : CollatzResearch.WordTrace tailWord_2339634 prefixEnd_2339634 1201356797601404404915225 := by
  unfold tailWord_2339634
  simp only [CollatzResearch.WordTrace]
  refine ⟨21333365601478267630076489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56888974937275380346870637 21333365601478267630076489)
  ·
    refine ⟨16000024201108700722557367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21333365601478267630076489 16000024201108700722557367)
    ·
      refine ⟨24000036301663051083836051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16000024201108700722557367 24000036301663051083836051)
      ·
        refine ⟨36000054452494576625754077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24000036301663051083836051 36000054452494576625754077)
        ·
          refine ⟨13500020419685466234657779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36000054452494576625754077 13500020419685466234657779)
          ·
            refine ⟨20250030629528199351986669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13500020419685466234657779 20250030629528199351986669)
            ·
              refine ⟨7593761486073074756995001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20250030629528199351986669 7593761486073074756995001)
              ·
                refine ⟨5695321114554806067746251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7593761486073074756995001 5695321114554806067746251)
                ·
                  refine ⟨8542981671832209101619377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5695321114554806067746251 8542981671832209101619377)
                  ·
                    refine ⟨6407236253874156826214533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8542981671832209101619377 6407236253874156826214533)
                    ·
                      refine ⟨1201356797601404404915225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6407236253874156826214533 1201356797601404404915225)
                      ·
                        rfl

theorem cell23_2339634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_2339634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339634 prefixEnd_2339634 := by exact prefixLift 2339634
  have htrace : WordTrace (prefixWord ++ tailWord_2339634) baseStart_2339634 baseEnd_2339634 := by
    simpa [prefixWord, tailWord_2339634, baseEnd_2339634] using wordTrace_append hprefix tailTrace_2339634
  have hstable : (prefixWord ++ tailWord_2339634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339634).length < 2 ^ (prefixWord ++ tailWord_2339634).sum := by decide
  have hdescent : baseEnd_2339634 < baseStart_2339634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339649 : List Nat := [1, 2, 5, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_2339649 : Nat := 118140960795 + 2339649 * 2 ^ 59
def prefixEnd_2339649 : Nat := 4983230072969 + 3 ^ 40 * 2339649 * 2
def baseEnd_2339649 : Nat := 1201364499811221846227657

theorem tailTrace_2339649 : CollatzResearch.WordTrace tailWord_2339649 prefixEnd_2339649 1201364499811221846227657 := by
  unfold tailWord_2339649
  simp only [CollatzResearch.WordTrace]
  refine ⟨85334009500858728082102001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56889339667239152054734667 85334009500858728082102001)
  ·
    refine ⟨64000507125644046061576501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85334009500858728082102001 64000507125644046061576501)
    ·
      refine ⟨6000047543029129318272797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64000507125644046061576501 6000047543029129318272797)
      ·
        refine ⟨2250017828635923494352299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6000047543029129318272797 2250017828635923494352299)
        ·
          refine ⟨3375026742953885241528449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2250017828635923494352299 3375026742953885241528449)
          ·
            refine ⟨2531270057215413931146337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3375026742953885241528449 2531270057215413931146337)
            ·
              refine ⟨1898452542911560448359753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2531270057215413931146337 1898452542911560448359753)
              ·
                refine ⟨1423839407183670336269815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1898452542911560448359753 1423839407183670336269815)
                ·
                  refine ⟨2135759110775505504404723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1423839407183670336269815 2135759110775505504404723)
                  ·
                    refine ⟨3203638666163258256607085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2135759110775505504404723 3203638666163258256607085)
                    ·
                      refine ⟨1201364499811221846227657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3203638666163258256607085 1201364499811221846227657)
                      ·
                        rfl

theorem cell23_2339649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_2339649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339649 prefixEnd_2339649 := by exact prefixLift 2339649
  have htrace : WordTrace (prefixWord ++ tailWord_2339649) baseStart_2339649 baseEnd_2339649 := by
    simpa [prefixWord, tailWord_2339649, baseEnd_2339649] using wordTrace_append hprefix tailTrace_2339649
  have hstable : (prefixWord ++ tailWord_2339649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339649).length < 2 ^ (prefixWord ++ tailWord_2339649).sum := by decide
  have hdescent : baseEnd_2339649 < baseStart_2339649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339657 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 2, 7]
def baseStart_2339657 : Nat := 118140960795 + 2339657 * 2 ^ 59
def prefixEnd_2339657 : Nat := 4983230072969 + 3 ^ 40 * 2339657 * 2
def baseEnd_2339657 : Nat := 400456202552152604975873

theorem tailTrace_2339657 : CollatzResearch.WordTrace tailWord_2339657 prefixEnd_2339657 400456202552152604975873 := by
  unfold tailWord_2339657
  simp only [CollatzResearch.WordTrace]
  refine ⟨85334301284829745448393225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56889534189886496965595483 85334301284829745448393225)
  ·
    refine ⟨64000725963622309086294919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85334301284829745448393225 64000725963622309086294919)
    ·
      refine ⟨96001088945433463629442379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64000725963622309086294919 96001088945433463629442379)
      ·
        refine ⟨144001633418150195444163569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96001088945433463629442379 144001633418150195444163569)
        ·
          refine ⟨108001225063612646583122677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144001633418150195444163569 108001225063612646583122677)
          ·
            refine ⟨10125114849713685617167751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108001225063612646583122677 10125114849713685617167751)
            ·
              refine ⟨15187672274570528425751627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10125114849713685617167751 15187672274570528425751627)
              ·
                refine ⟨22781508411855792638627441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15187672274570528425751627 22781508411855792638627441)
                ·
                  refine ⟨17086131308891844478970581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22781508411855792638627441 17086131308891844478970581)
                  ·
                    refine ⟨400456202552152604975873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17086131308891844478970581 400456202552152604975873)
                    ·
                      rfl

theorem cell23_2339657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 7].length) (baseStart_2339657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339657 prefixEnd_2339657 := by exact prefixLift 2339657
  have htrace : WordTrace (prefixWord ++ tailWord_2339657) baseStart_2339657 baseEnd_2339657 := by
    simpa [prefixWord, tailWord_2339657, baseEnd_2339657] using wordTrace_append hprefix tailTrace_2339657
  have hstable : (prefixWord ++ tailWord_2339657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339657).length < 2 ^ (prefixWord ++ tailWord_2339657).sum := by decide
  have hdescent : baseEnd_2339657 < baseStart_2339657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339671 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 3]
def baseStart_2339671 : Nat := 118140960795 + 2339671 * 2 ^ 59
def prefixEnd_2339671 : Nat := 4983230072969 + 3 ^ 40 * 2339671 * 2
def baseEnd_2339671 : Nat := 1201375796385620760152555

theorem tailTrace_2339671 : CollatzResearch.WordTrace tailWord_2339671 prefixEnd_2339671 1201375796385620760152555 := by
  unfold tailWord_2339671
  simp only [CollatzResearch.WordTrace]
  refine ⟨85334811906779025839402867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56889874604519350559601911 85334811906779025839402867)
  ·
    refine ⟨128002217860168538759104301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85334811906779025839402867 128002217860168538759104301)
    ·
      refine ⟨48000831697563202034664113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128002217860168538759104301 48000831697563202034664113)
      ·
        refine ⟨36000623773172401525998085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48000831697563202034664113 36000623773172401525998085)
        ·
          refine ⟨6750116957469825286124641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36000623773172401525998085 6750116957469825286124641)
          ·
            refine ⟨5062587718102368964593481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6750116957469825286124641 5062587718102368964593481)
            ·
              refine ⟨3796940788576776723445111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5062587718102368964593481 3796940788576776723445111)
              ·
                refine ⟨5695411182865165085167667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3796940788576776723445111 5695411182865165085167667)
                ·
                  refine ⟨8543116774297747627751501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5695411182865165085167667 8543116774297747627751501)
                  ·
                    refine ⟨3203668790361655360406813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8543116774297747627751501 3203668790361655360406813)
                    ·
                      refine ⟨1201375796385620760152555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3203668790361655360406813 1201375796385620760152555)
                      ·
                        rfl

theorem cell23_2339671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_2339671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339671 prefixEnd_2339671 := by exact prefixLift 2339671
  have htrace : WordTrace (prefixWord ++ tailWord_2339671) baseStart_2339671 baseEnd_2339671 := by
    simpa [prefixWord, tailWord_2339671, baseEnd_2339671] using wordTrace_append hprefix tailTrace_2339671
  have hstable : (prefixWord ++ tailWord_2339671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339671).length < 2 ^ (prefixWord ++ tailWord_2339671).sum := by decide
  have hdescent : baseEnd_2339671 < baseStart_2339671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339724 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 2, 2, 4]
def baseStart_2339724 : Nat := 118140960795 + 2339724 * 2 ^ 59
def prefixEnd_2339724 : Nat := 4983230072969 + 3 ^ 40 * 2339724 * 2
def baseEnd_2339724 : Nat := 1201403010860309052789811

theorem tailTrace_2339724 : CollatzResearch.WordTrace tailWord_2339724 prefixEnd_2339724 1201403010860309052789811 := by
  unfold tailWord_2339724
  simp only [CollatzResearch.WordTrace]
  refine ⟨42668372487793507945541113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56891163317058010594054817 42668372487793507945541113)
  ·
    refine ⟨32001279365845130959155835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42668372487793507945541113 32001279365845130959155835)
    ·
      refine ⟨48001919048767696438733753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32001279365845130959155835 48001919048767696438733753)
      ·
        refine ⟨36001439286575772329050315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48001919048767696438733753 36001439286575772329050315)
        ·
          refine ⟨54002158929863658493575473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36001439286575772329050315 54002158929863658493575473)
          ·
            refine ⟨40501619197397743870181605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54002158929863658493575473 40501619197397743870181605)
            ·
              refine ⟨7594053599512076975659051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40501619197397743870181605 7594053599512076975659051)
              ·
                refine ⟨11391080399268115463488577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7594053599512076975659051 11391080399268115463488577)
                ·
                  refine ⟨8543310299451086597616433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11391080399268115463488577 8543310299451086597616433)
                  ·
                    refine ⟨6407482724588314948212325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8543310299451086597616433 6407482724588314948212325)
                    ·
                      refine ⟨1201403010860309052789811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6407482724588314948212325 1201403010860309052789811)
                      ·
                        rfl

theorem cell23_2339724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_2339724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339724 prefixEnd_2339724 := by exact prefixLift 2339724
  have htrace : WordTrace (prefixWord ++ tailWord_2339724) baseStart_2339724 baseEnd_2339724 := by
    simpa [prefixWord, tailWord_2339724, baseEnd_2339724] using wordTrace_append hprefix tailTrace_2339724
  have hstable : (prefixWord ++ tailWord_2339724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339724).length < 2 ^ (prefixWord ++ tailWord_2339724).sum := by decide
  have hdescent : baseEnd_2339724 < baseStart_2339724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339744 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 3]
def baseStart_2339744 : Nat := 118140960795 + 2339744 * 2 ^ 59
def prefixEnd_2339744 : Nat := 4983230072969 + 3 ^ 40 * 2339744 * 2
def baseEnd_2339744 : Nat := 1201413280473398974539719

theorem tailTrace_2339744 : CollatzResearch.WordTrace tailWord_2339744 prefixEnd_2339744 1201413280473398974539719 := by
  unfold tailWord_2339744
  simp only [CollatzResearch.WordTrace]
  refine ⟨42668737217757279653405143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56891649623676372871206857 42668737217757279653405143)
  ·
    refine ⟨64003105826635919480107715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42668737217757279653405143 64003105826635919480107715)
    ·
      refine ⟨96004658739953879220161573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64003105826635919480107715 96004658739953879220161573)
      ·
        refine ⟨18000873513741352353780295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96004658739953879220161573 18000873513741352353780295)
        ·
          refine ⟨27001310270612028530670443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18000873513741352353780295 27001310270612028530670443)
          ·
            refine ⟨40501965405918042796005665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27001310270612028530670443 40501965405918042796005665)
            ·
              refine ⟨30376474054438532097004249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40501965405918042796005665 30376474054438532097004249)
              ·
                refine ⟨22782355540828899072753187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30376474054438532097004249 22782355540828899072753187)
                ·
                  refine ⟨34173533311243348609129781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22782355540828899072753187 34173533311243348609129781)
                  ·
                    refine ⟨3203768747929063932105917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34173533311243348609129781 3203768747929063932105917)
                    ·
                      refine ⟨1201413280473398974539719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3203768747929063932105917 1201413280473398974539719)
                      ·
                        rfl

theorem cell23_2339744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_2339744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339744 prefixEnd_2339744 := by exact prefixLift 2339744
  have htrace : WordTrace (prefixWord ++ tailWord_2339744) baseStart_2339744 baseEnd_2339744 := by
    simpa [prefixWord, tailWord_2339744, baseEnd_2339744] using wordTrace_append hprefix tailTrace_2339744
  have hstable : (prefixWord ++ tailWord_2339744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339744).length < 2 ^ (prefixWord ++ tailWord_2339744).sum := by decide
  have hdescent : baseEnd_2339744 < baseStart_2339744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339768 : List Nat := [2, 1, 2, 1, 2, 5, 3, 2, 5]
def baseStart_2339768 : Nat := 118140960795 + 2339768 * 2 ^ 59
def prefixEnd_2339768 : Nat := 4983230072969 + 3 ^ 40 * 2339768 * 2
def baseEnd_2339768 : Nat := 133491733778789653404401

theorem tailTrace_2339768 : CollatzResearch.WordTrace tailWord_2339768 prefixEnd_2339768 133491733778789653404401 := by
  unfold tailWord_2339768
  simp only [CollatzResearch.WordTrace]
  refine ⟨42669174893713805702841979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56892233191618407603789305 42669174893713805702841979)
  ·
    refine ⟨64003762340570708554262969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42669174893713805702841979 64003762340570708554262969)
    ·
      refine ⟨48002821755428031415697227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64003762340570708554262969 48002821755428031415697227)
      ·
        refine ⟨72004232633142047123545841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48002821755428031415697227 72004232633142047123545841)
        ·
          refine ⟨54003174474856535342659381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72004232633142047123545841 54003174474856535342659381)
          ·
            refine ⟨5062797607017800188374317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54003174474856535342659381 5062797607017800188374317)
            ·
              refine ⟨1898549102631675070640369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5062797607017800188374317 1898549102631675070640369)
              ·
                refine ⟨1423911826973756302980277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1898549102631675070640369 1423911826973756302980277)
                ·
                  refine ⟨133491733778789653404401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1423911826973756302980277 133491733778789653404401)
                  ·
                    rfl

theorem cell23_2339768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 5].length) (baseStart_2339768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339768 prefixEnd_2339768 := by exact prefixLift 2339768
  have htrace : WordTrace (prefixWord ++ tailWord_2339768) baseStart_2339768 baseEnd_2339768 := by
    simpa [prefixWord, tailWord_2339768, baseEnd_2339768] using wordTrace_append hprefix tailTrace_2339768
  have hstable : (prefixWord ++ tailWord_2339768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339768).length < 2 ^ (prefixWord ++ tailWord_2339768).sum := by decide
  have hdescent : baseEnd_2339768 < baseStart_2339768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339798 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_2339798 : Nat := 118140960795 + 2339798 * 2 ^ 59
def prefixEnd_2339798 : Nat := 4983230072969 + 3 ^ 40 * 2339798 * 2
def baseEnd_2339798 : Nat := 400480336142913921088157

theorem tailTrace_2339798 : CollatzResearch.WordTrace tailWord_2339798 prefixEnd_2339798 400480336142913921088157 := by
  unfold tailWord_2339798
  simp only [CollatzResearch.WordTrace]
  refine ⟨5333715248582432908079753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56892962651545951019517365 5333715248582432908079753)
  ·
    refine ⟨4000286436436824681059815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5333715248582432908079753 4000286436436824681059815)
    ·
      refine ⟨6000429654655237021589723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4000286436436824681059815 6000429654655237021589723)
      ·
        refine ⟨9000644481982855532384585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6000429654655237021589723 9000644481982855532384585)
        ·
          refine ⟨6750483361487141649288439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9000644481982855532384585 6750483361487141649288439)
          ·
            refine ⟨10125725042230712473932659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6750483361487141649288439 10125725042230712473932659)
            ·
              refine ⟨15188587563346068710898989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10125725042230712473932659 15188587563346068710898989)
              ·
                refine ⟨5695720336254775766587121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15188587563346068710898989 5695720336254775766587121)
                ·
                  refine ⟨4271790252191081824940341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5695720336254775766587121 4271790252191081824940341)
                  ·
                    refine ⟨400480336142913921088157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4271790252191081824940341 400480336142913921088157)
                    ·
                      rfl

theorem cell23_2339798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_2339798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339798 prefixEnd_2339798 := by exact prefixLift 2339798
  have htrace : WordTrace (prefixWord ++ tailWord_2339798) baseStart_2339798 baseEnd_2339798 := by
    simpa [prefixWord, tailWord_2339798, baseEnd_2339798] using wordTrace_append hprefix tailTrace_2339798
  have hstable : (prefixWord ++ tailWord_2339798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339798).length < 2 ^ (prefixWord ++ tailWord_2339798).sum := by decide
  have hdescent : baseEnd_2339798 < baseStart_2339798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339801 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 2, 1, 4]
def baseStart_2339801 : Nat := 118140960795 + 2339801 * 2 ^ 59
def prefixEnd_2339801 : Nat := 4983230072969 + 3 ^ 40 * 2339801 * 2
def baseEnd_2339801 : Nat := 1201442548870705251526957

theorem tailTrace_2339801 : CollatzResearch.WordTrace tailWord_2339801 prefixEnd_2339801 1201442548870705251526957 := by
  unfold tailWord_2339801
  simp only [CollatzResearch.WordTrace]
  refine ⟨85339553396308058041635257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56893035597538705361090171 85339553396308058041635257)
  ·
    refine ⟨64004665047231043531226443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85339553396308058041635257 64004665047231043531226443)
    ·
      refine ⟨96006997570846565296839665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64004665047231043531226443 96006997570846565296839665)
      ·
        refine ⟨72005248178134923972629749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96006997570846565296839665 72005248178134923972629749)
        ·
          refine ⟨6750492016700149122434039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72005248178134923972629749 6750492016700149122434039)
          ·
            refine ⟨10125738025050223683651059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6750492016700149122434039 10125738025050223683651059)
            ·
              refine ⟨15188607037575335525476589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10125738025050223683651059 15188607037575335525476589)
              ·
                refine ⟨5695727639090750822053721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15188607037575335525476589 5695727639090750822053721)
                ·
                  refine ⟨4271795729318063116540291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5695727639090750822053721 4271795729318063116540291)
                  ·
                    refine ⟨6407693593977094674810437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4271795729318063116540291 6407693593977094674810437)
                    ·
                      refine ⟨1201442548870705251526957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6407693593977094674810437 1201442548870705251526957)
                      ·
                        rfl

theorem cell23_2339801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_2339801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339801 prefixEnd_2339801 := by exact prefixLift 2339801
  have htrace : WordTrace (prefixWord ++ tailWord_2339801) baseStart_2339801 baseEnd_2339801 := by
    simpa [prefixWord, tailWord_2339801, baseEnd_2339801] using wordTrace_append hprefix tailTrace_2339801
  have hstable : (prefixWord ++ tailWord_2339801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339801).length < 2 ^ (prefixWord ++ tailWord_2339801).sum := by decide
  have hdescent : baseEnd_2339801 < baseStart_2339801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339841 : List Nat := [1, 2, 4, 1, 2, 2, 2, 3, 6]
def baseStart_2339841 : Nat := 118140960795 + 2339841 * 2 ^ 59
def prefixEnd_2339841 : Nat := 4983230072969 + 3 ^ 40 * 2339841 * 2
def baseEnd_2339841 : Nat := 133495898677431677225197

theorem tailTrace_2339841 : CollatzResearch.WordTrace tailWord_2339841 prefixEnd_2339841 133495898677431677225197 := by
  unfold tailWord_2339841
  simp only [CollatzResearch.WordTrace]
  refine ⟨85341012316163144873091377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56894008210775429915394251 85341012316163144873091377)
  ·
    refine ⟨64005759237122358654818533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85341012316163144873091377 64005759237122358654818533)
    ·
      refine ⟨12001079856960442247778475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64005759237122358654818533 12001079856960442247778475)
      ·
        refine ⟨18001619785440663371667713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12001079856960442247778475 18001619785440663371667713)
        ·
          refine ⟨13501214839080497528750785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18001619785440663371667713 13501214839080497528750785)
          ·
            refine ⟨10125911129310373146563089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13501214839080497528750785 10125911129310373146563089)
            ·
              refine ⟨7594433346982779859922317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10125911129310373146563089 7594433346982779859922317)
              ·
                refine ⟨2847912505118542447470869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7594433346982779859922317 2847912505118542447470869)
                ·
                  refine ⟨133495898677431677225197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2847912505118542447470869 133495898677431677225197)
                  ·
                    rfl

theorem cell23_2339841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 6].length) (baseStart_2339841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339841 prefixEnd_2339841 := by exact prefixLift 2339841
  have htrace : WordTrace (prefixWord ++ tailWord_2339841) baseStart_2339841 baseEnd_2339841 := by
    simpa [prefixWord, tailWord_2339841, baseEnd_2339841] using wordTrace_append hprefix tailTrace_2339841
  have hstable : (prefixWord ++ tailWord_2339841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339841).length < 2 ^ (prefixWord ++ tailWord_2339841).sum := by decide
  have hdescent : baseEnd_2339841 < baseStart_2339841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339905 : List Nat := [1, 2, 5, 1, 3, 1, 2, 2, 1, 5]
def baseStart_2339905 : Nat := 118140960795 + 2339905 * 2 ^ 59
def prefixEnd_2339905 : Nat := 4983230072969 + 3 ^ 40 * 2339905 * 2
def baseEnd_2339905 : Nat := 400498650286257614875493

theorem tailTrace_2339905 : CollatzResearch.WordTrace tailWord_2339905 prefixEnd_2339905 400498650286257614875493 := by
  unfold tailWord_2339905
  simp only [CollatzResearch.WordTrace]
  refine ⟨85343346587931283803421169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56895564391954189202280779 85343346587931283803421169)
  ·
    refine ⟨64007509940948462852565877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85343346587931283803421169 64007509940948462852565877)
    ·
      refine ⟨6000704056963918392428051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64007509940948462852565877 6000704056963918392428051)
      ·
        refine ⟨9001056085445877588642077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6000704056963918392428051 9001056085445877588642077)
        ·
          refine ⟨3375396032042204095740779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9001056085445877588642077 3375396032042204095740779)
          ·
            refine ⟨5063094048063306143611169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3375396032042204095740779 5063094048063306143611169)
            ·
              refine ⟨3797320536047479607708377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5063094048063306143611169 3797320536047479607708377)
              ·
                refine ⟨2847990402035609705781283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3797320536047479607708377 2847990402035609705781283)
                ·
                  refine ⟨4271985603053414558671925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2847990402035609705781283 4271985603053414558671925)
                  ·
                    refine ⟨400498650286257614875493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4271985603053414558671925 400498650286257614875493)
                    ·
                      rfl

theorem cell23_2339905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_2339905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339905 prefixEnd_2339905 := by exact prefixLift 2339905
  have htrace : WordTrace (prefixWord ++ tailWord_2339905) baseStart_2339905 baseEnd_2339905 := by
    simpa [prefixWord, tailWord_2339905, baseEnd_2339905] using wordTrace_append hprefix tailTrace_2339905
  have hstable : (prefixWord ++ tailWord_2339905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339905).length < 2 ^ (prefixWord ++ tailWord_2339905).sum := by decide
  have hdescent : baseEnd_2339905 < baseStart_2339905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339921 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 1, 2, 4]
def baseStart_2339921 : Nat := 118140960795 + 2339921 * 2 ^ 59
def prefixEnd_2339921 : Nat := 4983230072969 + 3 ^ 40 * 2339921 * 2
def baseEnd_2339921 : Nat := 1201504166549244782026405

theorem tailTrace_2339921 : CollatzResearch.WordTrace tailWord_2339921 prefixEnd_2339921 1201504166549244782026405 := by
  unfold tailWord_2339921
  simp only [CollatzResearch.WordTrace]
  refine ⟨85343930155873318536003617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56895953437248879024002411 85343930155873318536003617)
  ·
    refine ⟨64007947616904988902002713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85343930155873318536003617 64007947616904988902002713)
    ·
      refine ⟨48005960712678741676502035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64007947616904988902002713 48005960712678741676502035)
      ·
        refine ⟨72008941069018112514753053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48005960712678741676502035 72008941069018112514753053)
        ·
          refine ⟨27003352900881792193032395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72008941069018112514753053 27003352900881792193032395)
          ·
            refine ⟨40505029351322688289548593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27003352900881792193032395 40505029351322688289548593)
            ·
              refine ⟨30378772013492016217161445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40505029351322688289548593 30378772013492016217161445)
              ·
                refine ⟨5696019752529753040717771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30378772013492016217161445 5696019752529753040717771)
                ·
                  refine ⟨8544029628794629561076657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5696019752529753040717771 8544029628794629561076657)
                  ·
                    refine ⟨6408022221595972170807493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8544029628794629561076657 6408022221595972170807493)
                    ·
                      refine ⟨1201504166549244782026405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6408022221595972170807493 1201504166549244782026405)
                      ·
                        rfl

theorem cell23_2339921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_2339921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339921 prefixEnd_2339921 := by exact prefixLift 2339921
  have htrace : WordTrace (prefixWord ++ tailWord_2339921) baseStart_2339921 baseEnd_2339921 := by
    simpa [prefixWord, tailWord_2339921, baseEnd_2339921] using wordTrace_append hprefix tailTrace_2339921
  have hstable : (prefixWord ++ tailWord_2339921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339921).length < 2 ^ (prefixWord ++ tailWord_2339921).sum := by decide
  have hdescent : baseEnd_2339921 < baseStart_2339921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339928 : List Nat := [2, 1, 2, 2, 1, 3, 1, 5, 1, 2, 3]
def baseStart_2339928 : Nat := 118140960795 + 2339928 * 2 ^ 59
def prefixEnd_2339928 : Nat := 4983230072969 + 3 ^ 40 * 2339928 * 2
def baseEnd_2339928 : Nat := 1201507760913826254638873

theorem tailTrace_2339928 : CollatzResearch.WordTrace tailWord_2339928 prefixEnd_2339928 1201507760913826254638873 := by
  unfold tailWord_2339928
  simp only [CollatzResearch.WordTrace]
  refine ⟨42672092733423979365754219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56896123644565305821005625 42672092733423979365754219)
  ·
    refine ⟨64008139100135969048631329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42672092733423979365754219 64008139100135969048631329)
    ·
      refine ⟨48006104325101976786473497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64008139100135969048631329 48006104325101976786473497)
      ·
        refine ⟨36004578243826482589855123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48006104325101976786473497 36004578243826482589855123)
        ·
          refine ⟨54006867365739723884782685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36004578243826482589855123 54006867365739723884782685)
          ·
            refine ⟨20252575262152396456793507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54006867365739723884782685 20252575262152396456793507)
            ·
              refine ⟨30378862893228594685190261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20252575262152396456793507 30378862893228594685190261)
              ·
                refine ⟨2848018396240180751736587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30378862893228594685190261 2848018396240180751736587)
                ·
                  refine ⟨4272027594360271127604881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2848018396240180751736587 4272027594360271127604881)
                  ·
                    refine ⟨3204020695770203345703661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4272027594360271127604881 3204020695770203345703661)
                    ·
                      refine ⟨1201507760913826254638873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3204020695770203345703661 1201507760913826254638873)
                      ·
                        rfl

theorem cell23_2339928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_2339928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339928 prefixEnd_2339928 := by exact prefixLift 2339928
  have htrace : WordTrace (prefixWord ++ tailWord_2339928) baseStart_2339928 baseEnd_2339928 := by
    simpa [prefixWord, tailWord_2339928, baseEnd_2339928] using wordTrace_append hprefix tailTrace_2339928
  have hstable : (prefixWord ++ tailWord_2339928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339928).length < 2 ^ (prefixWord ++ tailWord_2339928).sum := by decide
  have hdescent : baseEnd_2339928 < baseStart_2339928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339938 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2339938 : Nat := 118140960795 + 2339938 * 2 ^ 59
def prefixEnd_2339938 : Nat := 4983230072969 + 3 ^ 40 * 2339938 * 2
def baseEnd_2339938 : Nat := 1201512895720371215513827

theorem tailTrace_2339938 : CollatzResearch.WordTrace tailWord_2339938 prefixEnd_2339938 1201512895720371215513827 := by
  unfold tailWord_2339938
  simp only [CollatzResearch.WordTrace]
  refine ⟨21336137549202932609843117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56896366797874486959581645 21336137549202932609843117)
  ·
    refine ⟨8001051580951099728691169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21336137549202932609843117 8001051580951099728691169)
    ·
      refine ⟨6000788685713324796518377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8001051580951099728691169 6000788685713324796518377)
      ·
        refine ⟨4500591514284993597388783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6000788685713324796518377 4500591514284993597388783)
        ·
          refine ⟨6750887271427490396083175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4500591514284993597388783 6750887271427490396083175)
          ·
            refine ⟨10126330907141235594124763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6750887271427490396083175 10126330907141235594124763)
            ·
              refine ⟨15189496360711853391187145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10126330907141235594124763 15189496360711853391187145)
              ·
                refine ⟨11392122270533890043390359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15189496360711853391187145 11392122270533890043390359)
                ·
                  refine ⟨17088183405800835065085539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11392122270533890043390359 17088183405800835065085539)
                  ·
                    refine ⟨25632275108701252597628309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17088183405800835065085539 25632275108701252597628309)
                    ·
                      refine ⟨1201512895720371215513827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25632275108701252597628309 1201512895720371215513827)
                      ·
                        rfl

theorem cell23_2339938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2339938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339938 prefixEnd_2339938 := by exact prefixLift 2339938
  have htrace : WordTrace (prefixWord ++ tailWord_2339938) baseStart_2339938 baseEnd_2339938 := by
    simpa [prefixWord, tailWord_2339938, baseEnd_2339938] using wordTrace_append hprefix tailTrace_2339938
  have hstable : (prefixWord ++ tailWord_2339938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339938).length < 2 ^ (prefixWord ++ tailWord_2339938).sum := by decide
  have hdescent : baseEnd_2339938 < baseStart_2339938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339992 : List Nat := [2, 1, 2, 4, 2, 2, 2, 2, 2, 1, 3]
def baseStart_2339992 : Nat := 118140960795 + 2339992 * 2 ^ 59
def prefixEnd_2339992 : Nat := 4983230072969 + 3 ^ 40 * 2339992 * 2
def baseEnd_2339992 : Nat := 1201540623675714004238579

theorem tailTrace_2339992 : CollatzResearch.WordTrace tailWord_2339992 prefixEnd_2339992 1201540623675714004238579 := by
  unfold tailWord_2339992
  simp only [CollatzResearch.WordTrace]
  refine ⟨42673259869308048830919115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56897679825744065107892153 42673259869308048830919115)
  ·
    refine ⟨64009889803962073246378673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42673259869308048830919115 64009889803962073246378673)
    ·
      refine ⟨48007417352971554934784005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64009889803962073246378673 48007417352971554934784005)
      ·
        refine ⟨9001390753682166550272001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48007417352971554934784005 9001390753682166550272001)
        ·
          refine ⟨6751043065261624912704001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9001390753682166550272001 6751043065261624912704001)
          ·
            refine ⟨5063282298946218684528001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6751043065261624912704001 5063282298946218684528001)
            ·
              refine ⟨3797461724209664013396001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5063282298946218684528001 3797461724209664013396001)
              ·
                refine ⟨2848096293157248010047001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3797461724209664013396001 2848096293157248010047001)
                ·
                  refine ⟨2136072219867936007535251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2848096293157248010047001 2136072219867936007535251)
                  ·
                    refine ⟨3204108329801904011302877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2136072219867936007535251 3204108329801904011302877)
                    ·
                      refine ⟨1201540623675714004238579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3204108329801904011302877 1201540623675714004238579)
                      ·
                        rfl

theorem cell23_2339992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_2339992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2339992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2339992 prefixEnd_2339992 := by exact prefixLift 2339992
  have htrace : WordTrace (prefixWord ++ tailWord_2339992) baseStart_2339992 baseEnd_2339992 := by
    simpa [prefixWord, tailWord_2339992, baseEnd_2339992] using wordTrace_append hprefix tailTrace_2339992
  have hstable : (prefixWord ++ tailWord_2339992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339992).length < 2 ^ (prefixWord ++ tailWord_2339992).sum := by decide
  have hdescent : baseEnd_2339992 < baseStart_2339992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340036 : List Nat := [2, 3, 3, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_2340036 : Nat := 118140960795 + 2340036 * 2 ^ 59
def prefixEnd_2340036 : Nat := 4983230072969 + 3 ^ 40 * 2340036 * 2
def baseEnd_2340036 : Nat := 1201563216824511832088377

theorem tailTrace_2340036 : CollatzResearch.WordTrace tailWord_2340036 prefixEnd_2340036 1201563216824511832088377 := by
  unfold tailWord_2340036
  simp only [CollatzResearch.WordTrace]
  refine ⟨42674062275228346588219981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56898749700304462117626641 42674062275228346588219981)
  ·
    refine ⟨16002773353210629970582493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42674062275228346588219981 16002773353210629970582493)
    ·
      refine ⟨6001040007453986238968435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16002773353210629970582493 6001040007453986238968435)
      ·
        refine ⟨9001560011180979358452653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6001040007453986238968435 9001560011180979358452653)
        ·
          refine ⟨3375585004192867259419745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9001560011180979358452653 3375585004192867259419745)
          ·
            refine ⟨2531688753144650444564809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3375585004192867259419745 2531688753144650444564809)
            ·
              refine ⟨1898766564858487833423607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2531688753144650444564809 1898766564858487833423607)
              ·
                refine ⟨2848149847287731750135411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1898766564858487833423607 2848149847287731750135411)
                ·
                  refine ⟨4272224770931597625203117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2848149847287731750135411 4272224770931597625203117)
                  ·
                    refine ⟨1602084289099349109451169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4272224770931597625203117 1602084289099349109451169)
                    ·
                      refine ⟨1201563216824511832088377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1602084289099349109451169 1201563216824511832088377)
                      ·
                        rfl

theorem cell23_2340036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_2340036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340036 prefixEnd_2340036 := by exact prefixLift 2340036
  have htrace : WordTrace (prefixWord ++ tailWord_2340036) baseStart_2340036 baseEnd_2340036 := by
    simpa [prefixWord, tailWord_2340036, baseEnd_2340036] using wordTrace_append hprefix tailTrace_2340036
  have hstable : (prefixWord ++ tailWord_2340036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340036).length < 2 ^ (prefixWord ++ tailWord_2340036).sum := by decide
  have hdescent : baseEnd_2340036 < baseStart_2340036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340081 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 1, 10]
def baseStart_2340081 : Nat := 118140960795 + 2340081 * 2 ^ 59
def prefixEnd_2340081 : Nat := 4983230072969 + 3 ^ 40 * 2340081 * 2
def baseEnd_2340081 : Nat := 400528774484654718675223

theorem tailTrace_2340081 : CollatzResearch.WordTrace tailWord_2340081 prefixEnd_2340081 400528774484654718675223 := by
  unfold tailWord_2340081
  simp only [CollatzResearch.WordTrace]
  refine ⟨85349765835293665861828097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56899843890195777241218731 85349765835293665861828097)
  ·
    refine ⟨64012324376470249396371073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85349765835293665861828097 64012324376470249396371073)
    ·
      refine ⟨48009243282352687047278305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64012324376470249396371073 48009243282352687047278305)
      ·
        refine ⟨36006932461764515285458729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48009243282352687047278305 36006932461764515285458729)
        ·
          refine ⟨27005199346323386464094047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36006932461764515285458729 27005199346323386464094047)
          ·
            refine ⟨40507799019485079696141071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27005199346323386464094047 40507799019485079696141071)
            ·
              refine ⟨60761698529227619544211607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40507799019485079696141071 60761698529227619544211607)
              ·
                refine ⟨91142547793841429316317411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60761698529227619544211607 91142547793841429316317411)
                ·
                  refine ⟨136713821690762143974476117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91142547793841429316317411 136713821690762143974476117)
                  ·
                    refine ⟨400528774484654718675223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 136713821690762143974476117 400528774484654718675223)
                    ·
                      rfl

theorem cell23_2340081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_2340081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340081 prefixEnd_2340081 := by exact prefixLift 2340081
  have htrace : WordTrace (prefixWord ++ tailWord_2340081) baseStart_2340081 baseEnd_2340081 := by
    simpa [prefixWord, tailWord_2340081, baseEnd_2340081] using wordTrace_append hprefix tailTrace_2340081
  have hstable : (prefixWord ++ tailWord_2340081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340081).length < 2 ^ (prefixWord ++ tailWord_2340081).sum := by decide
  have hdescent : baseEnd_2340081 < baseStart_2340081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340195 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 4]
def baseStart_2340195 : Nat := 118140960795 + 2340195 * 2 ^ 59
def prefixEnd_2340195 : Nat := 4983230072969 + 3 ^ 40 * 2340195 * 2
def baseEnd_2340195 : Nat := 1201644860248576710000145

theorem tailTrace_2340195 : CollatzResearch.WordTrace tailWord_2340195 prefixEnd_2340195 1201644860248576710000145 := by
  unfold tailWord_2340195
  simp only [CollatzResearch.WordTrace]
  refine ⟨85353923756880663331478039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56902615837920442220985359 85353923756880663331478039)
  ·
    refine ⟨128030885635320994997217059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85353923756880663331478039 128030885635320994997217059)
    ·
      refine ⟨192046328452981492495825589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128030885635320994997217059 192046328452981492495825589)
      ·
        refine ⟨18004343292467014921483649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 192046328452981492495825589 18004343292467014921483649)
        ·
          refine ⟨13503257469350261191112737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18004343292467014921483649 13503257469350261191112737)
          ·
            refine ⟨10127443102012695893334553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13503257469350261191112737 10127443102012695893334553)
            ·
              refine ⟨7595582326509521920000915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10127443102012695893334553 7595582326509521920000915)
              ·
                refine ⟨11393373489764282880001373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7595582326509521920000915 11393373489764282880001373)
                ·
                  refine ⟨4272515058661606080000515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11393373489764282880001373 4272515058661606080000515)
                  ·
                    refine ⟨6408772587992409120000773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4272515058661606080000515 6408772587992409120000773)
                    ·
                      refine ⟨1201644860248576710000145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6408772587992409120000773 1201644860248576710000145)
                      ·
                        rfl

theorem cell23_2340195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_2340195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340195 prefixEnd_2340195 := by exact prefixLift 2340195
  have htrace : WordTrace (prefixWord ++ tailWord_2340195) baseStart_2340195 baseEnd_2340195 := by
    simpa [prefixWord, tailWord_2340195, baseEnd_2340195] using wordTrace_append hprefix tailTrace_2340195
  have hstable : (prefixWord ++ tailWord_2340195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340195).length < 2 ^ (prefixWord ++ tailWord_2340195).sum := by decide
  have hdescent : baseEnd_2340195 < baseStart_2340195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340205 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_2340205 : Nat := 118140960795 + 2340205 * 2 ^ 59
def prefixEnd_2340205 : Nat := 4983230072969 + 3 ^ 40 * 2340205 * 2
def baseEnd_2340205 : Nat := 400549998351707223625033

theorem tailTrace_2340205 : CollatzResearch.WordTrace tailWord_2340205 prefixEnd_2340205 400549998351707223625033 := by
  unfold tailWord_2340205
  simp only [CollatzResearch.WordTrace]
  refine ⟨85354288486844435039342069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56902858991229623359561379 85354288486844435039342069)
  ·
    refine ⟨8001964545641665784938319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85354288486844435039342069 8001964545641665784938319)
    ·
      refine ⟨12002946818462498677407479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8001964545641665784938319 12002946818462498677407479)
      ·
        refine ⟨18004420227693748016111219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12002946818462498677407479 18004420227693748016111219)
        ·
          refine ⟨27006630341540622024166829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18004420227693748016111219 27006630341540622024166829)
          ·
            refine ⟨10127486378077733259062561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27006630341540622024166829 10127486378077733259062561)
            ·
              refine ⟨7595614783558299944296921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10127486378077733259062561 7595614783558299944296921)
              ·
                refine ⟨5696711087668724958222691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7595614783558299944296921 5696711087668724958222691)
                ·
                  refine ⟨8545066631503087437334037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5696711087668724958222691 8545066631503087437334037)
                  ·
                    refine ⟨400549998351707223625033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8545066631503087437334037 400549998351707223625033)
                    ·
                      rfl

theorem cell23_2340205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_2340205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340205 prefixEnd_2340205 := by exact prefixLift 2340205
  have htrace : WordTrace (prefixWord ++ tailWord_2340205) baseStart_2340205 baseEnd_2340205 := by
    simpa [prefixWord, tailWord_2340205, baseEnd_2340205] using wordTrace_append hprefix tailTrace_2340205
  have hstable : (prefixWord ++ tailWord_2340205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340205).length < 2 ^ (prefixWord ++ tailWord_2340205).sum := by decide
  have hdescent : baseEnd_2340205 < baseStart_2340205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340252 : List Nat := [2, 2, 3, 4, 1, 1, 1, 9]
def baseStart_2340252 : Nat := 118140960795 + 2340252 * 2 ^ 59
def prefixEnd_2340252 : Nat := 4983230072969 + 3 ^ 40 * 2340252 * 2
def baseEnd_2340252 : Nat := 44506449209106777295829

theorem tailTrace_2340252 : CollatzResearch.WordTrace tailWord_2340252 prefixEnd_2340252 44506449209106777295829 := by
  unfold tailWord_2340252
  simp only [CollatzResearch.WordTrace]
  refine ⟨42678001358837081033151505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56904001811782774710868673 42678001358837081033151505)
  ·
    refine ⟨32008501019127810774863629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42678001358837081033151505 32008501019127810774863629)
    ·
      refine ⟨12003187882172929040573861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32008501019127810774863629 12003187882172929040573861)
      ·
        refine ⟨2250597727907424195107599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12003187882172929040573861 2250597727907424195107599)
        ·
          refine ⟨3375896591861136292661399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2250597727907424195107599 3375896591861136292661399)
          ·
            refine ⟨5063844887791704438992099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3375896591861136292661399 5063844887791704438992099)
            ·
              refine ⟨7595767331687556658488149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5063844887791704438992099 7595767331687556658488149)
              ·
                refine ⟨44506449209106777295829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7595767331687556658488149 44506449209106777295829)
                ·
                  rfl

theorem cell23_2340252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 9].length) (baseStart_2340252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340252 prefixEnd_2340252 := by exact prefixLift 2340252
  have htrace : WordTrace (prefixWord ++ tailWord_2340252) baseStart_2340252 baseEnd_2340252 := by
    simpa [prefixWord, tailWord_2340252, baseEnd_2340252] using wordTrace_append hprefix tailTrace_2340252
  have hstable : (prefixWord ++ tailWord_2340252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340252).length < 2 ^ (prefixWord ++ tailWord_2340252).sum := by decide
  have hdescent : baseEnd_2340252 < baseStart_2340252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340285 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_2340285 : Nat := 118140960795 + 2340285 * 2 ^ 59
def prefixEnd_2340285 : Nat := 4983230072969 + 3 ^ 40 * 2340285 * 2
def baseEnd_2340285 : Nat := 1201691073507481357874731

theorem tailTrace_2340285 : CollatzResearch.WordTrace tailWord_2340285 prefixEnd_2340285 1201691073507481357874731 := by
  unfold tailWord_2340285
  simp only [CollatzResearch.WordTrace]
  refine ⟨85357206326554608702254309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56904804217703072468169539 85357206326554608702254309)
  ·
    refine ⟨16004476186228989131672683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85357206326554608702254309 16004476186228989131672683)
    ·
      refine ⟨24006714279343483697509025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16004476186228989131672683 24006714279343483697509025)
      ·
        refine ⟨18005035709507612773131769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24006714279343483697509025 18005035709507612773131769)
        ·
          refine ⟨13503776782130709579848827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18005035709507612773131769 13503776782130709579848827)
          ·
            refine ⟨20255665173196064369773241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13503776782130709579848827 20255665173196064369773241)
            ·
              refine ⟨15191748879897048277329931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20255665173196064369773241 15191748879897048277329931)
              ·
                refine ⟨22787623319845572415994897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15191748879897048277329931 22787623319845572415994897)
                ·
                  refine ⟨17090717489884179311996173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22787623319845572415994897 17090717489884179311996173)
                  ·
                    refine ⟨6409019058706567241998565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17090717489884179311996173 6409019058706567241998565)
                    ·
                      refine ⟨1201691073507481357874731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6409019058706567241998565 1201691073507481357874731)
                      ·
                        rfl

theorem cell23_2340285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_2340285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340285 prefixEnd_2340285 := by exact prefixLift 2340285
  have htrace : WordTrace (prefixWord ++ tailWord_2340285) baseStart_2340285 baseEnd_2340285 := by
    simpa [prefixWord, tailWord_2340285, baseEnd_2340285] using wordTrace_append hprefix tailTrace_2340285
  have hstable : (prefixWord ++ tailWord_2340285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340285).length < 2 ^ (prefixWord ++ tailWord_2340285).sum := by decide
  have hdescent : baseEnd_2340285 < baseStart_2340285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340290 : List Nat := [3, 5, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2340290 : Nat := 118140960795 + 2340290 * 2 ^ 59
def prefixEnd_2340290 : Nat := 4983230072969 + 3 ^ 40 * 2340290 * 2
def baseEnd_2340290 : Nat := 400564546970251279437403

theorem tailTrace_2340290 : CollatzResearch.WordTrace tailWord_2340290 prefixEnd_2340290 400564546970251279437403 := by
  unfold tailWord_2340290
  simp only [CollatzResearch.WordTrace]
  refine ⟨21339347172884123639046581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56904925794357663037457549 21339347172884123639046581)
  ·
    refine ⟨2000563797457886591160617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21339347172884123639046581 2000563797457886591160617)
    ·
      refine ⟨1500422848093414943370463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2000563797457886591160617 1500422848093414943370463)
      ·
        refine ⟨2250634272140122415055695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1500422848093414943370463 2250634272140122415055695)
        ·
          refine ⟨3375951408210183622583543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2250634272140122415055695 3375951408210183622583543)
          ·
            refine ⟨5063927112315275433875315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3375951408210183622583543 5063927112315275433875315)
            ·
              refine ⟨7595890668472913150812973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5063927112315275433875315 7595890668472913150812973)
              ·
                refine ⟨2848459000677342431554865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7595890668472913150812973 2848459000677342431554865)
                ·
                  refine ⟨2136344250508006823666149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2848459000677342431554865 2136344250508006823666149)
                  ·
                    refine ⟨400564546970251279437403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2136344250508006823666149 400564546970251279437403)
                    ·
                      rfl

theorem cell23_2340290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2340290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340290 prefixEnd_2340290 := by exact prefixLift 2340290
  have htrace : WordTrace (prefixWord ++ tailWord_2340290) baseStart_2340290 baseEnd_2340290 := by
    simpa [prefixWord, tailWord_2340290, baseEnd_2340290] using wordTrace_append hprefix tailTrace_2340290
  have hstable : (prefixWord ++ tailWord_2340290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340290).length < 2 ^ (prefixWord ++ tailWord_2340290).sum := by decide
  have hdescent : baseEnd_2340290 < baseStart_2340290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340336 : List Nat := [2, 1, 1, 1, 3, 5, 2, 2, 2, 2, 2]
def baseStart_2340336 : Nat := 118140960795 + 2340336 * 2 ^ 59
def prefixEnd_2340336 : Nat := 4983230072969 + 3 ^ 40 * 2340336 * 2
def baseEnd_2340336 : Nat := 1201717261020860658336997

theorem tailTrace_2340336 : CollatzResearch.WordTrace tailWord_2340336 prefixEnd_2340336 1201717261020860658336997 := by
  unfold tailWord_2340336
  simp only [CollatzResearch.WordTrace]
  refine ⟨42679533224684922206180431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56906044299579896274907241 42679533224684922206180431)
  ·
    refine ⟨64019299837027383309270647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42679533224684922206180431 64019299837027383309270647)
    ·
      refine ⟨96028949755541074963905971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64019299837027383309270647 96028949755541074963905971)
      ·
        refine ⟨144043424633311612445858957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96028949755541074963905971 144043424633311612445858957)
        ·
          refine ⟨54016284237491854667197109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144043424633311612445858957 54016284237491854667197109)
          ·
            refine ⟨5064026647264861375049729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54016284237491854667197109 5064026647264861375049729)
            ·
              refine ⟨3798019985448646031287297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5064026647264861375049729 3798019985448646031287297)
              ·
                refine ⟨2848514989086484523465473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3798019985448646031287297 2848514989086484523465473)
                ·
                  refine ⟨2136386241814863392599105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2848514989086484523465473 2136386241814863392599105)
                  ·
                    refine ⟨1602289681361147544449329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2136386241814863392599105 1602289681361147544449329)
                    ·
                      refine ⟨1201717261020860658336997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1602289681361147544449329 1201717261020860658336997)
                      ·
                        rfl

theorem cell23_2340336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 2, 2, 2].length) (baseStart_2340336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340336 prefixEnd_2340336 := by exact prefixLift 2340336
  have htrace : WordTrace (prefixWord ++ tailWord_2340336) baseStart_2340336 baseEnd_2340336 := by
    simpa [prefixWord, tailWord_2340336, baseEnd_2340336] using wordTrace_append hprefix tailTrace_2340336
  have hstable : (prefixWord ++ tailWord_2340336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340336).length < 2 ^ (prefixWord ++ tailWord_2340336).sum := by decide
  have hdescent : baseEnd_2340336 < baseStart_2340336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340409 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 2, 4, 2]
def baseStart_2340409 : Nat := 118140960795 + 2340409 * 2 ^ 59
def prefixEnd_2340409 : Nat := 4983230072969 + 3 ^ 40 * 2340409 * 2
def baseEnd_2340409 : Nat := 1201754745108638872724161

theorem tailTrace_2340409 : CollatzResearch.WordTrace tailWord_2340409 prefixEnd_2340409 1201754745108638872724161 := by
  unfold tailWord_2340409
  simp only [CollatzResearch.WordTrace]
  refine ⟨85361728978105377879768281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56907819318736918586512187 85361728978105377879768281)
  ·
    refine ⟨64021296733579033409826211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85361728978105377879768281 64021296733579033409826211)
    ·
      refine ⟨96031945100368550114739317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64021296733579033409826211 96031945100368550114739317)
      ·
        refine ⟨9002994853159551573256811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96031945100368550114739317 9002994853159551573256811)
        ·
          refine ⟨13504492279739327359885217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9002994853159551573256811 13504492279739327359885217)
          ·
            refine ⟨10128369209804495519913913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13504492279739327359885217 10128369209804495519913913)
            ·
              refine ⟨7596276907353371639935435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10128369209804495519913913 7596276907353371639935435)
              ·
                refine ⟨11394415361030057459903153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7596276907353371639935435 11394415361030057459903153)
                ·
                  refine ⟨8545811520772543094927365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11394415361030057459903153 8545811520772543094927365)
                  ·
                    refine ⟨1602339660144851830298881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8545811520772543094927365 1602339660144851830298881)
                    ·
                      refine ⟨1201754745108638872724161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1602339660144851830298881 1201754745108638872724161)
                      ·
                        rfl

theorem cell23_2340409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_2340409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340409 prefixEnd_2340409 := by exact prefixLift 2340409
  have htrace : WordTrace (prefixWord ++ tailWord_2340409) baseStart_2340409 baseEnd_2340409 := by
    simpa [prefixWord, tailWord_2340409, baseEnd_2340409] using wordTrace_append hprefix tailTrace_2340409
  have hstable : (prefixWord ++ tailWord_2340409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340409).length < 2 ^ (prefixWord ++ tailWord_2340409).sum := by decide
  have hdescent : baseEnd_2340409 < baseStart_2340409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340453 : List Nat := [1, 3, 1, 3, 3, 2, 3, 2, 1, 4]
def baseStart_2340453 : Nat := 118140960795 + 2340453 * 2 ^ 59
def prefixEnd_2340453 : Nat := 4983230072969 + 3 ^ 40 * 2340453 * 2
def baseEnd_2340453 : Nat := 400592446085812233524653

theorem tailTrace_2340453 : CollatzResearch.WordTrace tailWord_2340453 prefixEnd_2340453 400592446085812233524653 := by
  unfold tailWord_2340453
  simp only [CollatzResearch.WordTrace]
  refine ⟨85363333789945973394370013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56908889193297315596246675 85363333789945973394370013)
  ·
    refine ⟨32011250171229740022888755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85363333789945973394370013 32011250171229740022888755)
    ·
      refine ⟨48016875256844610034333133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32011250171229740022888755 48016875256844610034333133)
      ·
        refine ⟨18006328221316728762874925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48016875256844610034333133 18006328221316728762874925)
        ·
          refine ⟨6752373082993773286078097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18006328221316728762874925 6752373082993773286078097)
          ·
            refine ⟨5064279812245329964558573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6752373082993773286078097 5064279812245329964558573)
            ·
              refine ⟨1899104929591998736709465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5064279812245329964558573 1899104929591998736709465)
              ·
                refine ⟨1424328697193999052532099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1899104929591998736709465 1424328697193999052532099)
                ·
                  refine ⟨2136493045790998578798149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1424328697193999052532099 2136493045790998578798149)
                  ·
                    refine ⟨400592446085812233524653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2136493045790998578798149 400592446085812233524653)
                    ·
                      rfl

theorem cell23_2340453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 1, 4].length) (baseStart_2340453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340453 prefixEnd_2340453 := by exact prefixLift 2340453
  have htrace : WordTrace (prefixWord ++ tailWord_2340453) baseStart_2340453 baseEnd_2340453 := by
    simpa [prefixWord, tailWord_2340453, baseEnd_2340453] using wordTrace_append hprefix tailTrace_2340453
  have hstable : (prefixWord ++ tailWord_2340453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340453).length < 2 ^ (prefixWord ++ tailWord_2340453).sum := by decide
  have hdescent : baseEnd_2340453 < baseStart_2340453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340466 : List Nat := [3, 2, 1, 2, 3, 3, 2, 1, 6]
def baseStart_2340466 : Nat := 118140960795 + 2340466 * 2 ^ 59
def prefixEnd_2340466 : Nat := 4983230072969 + 3 ^ 40 * 2340466 * 2
def baseEnd_2340466 : Nat := 133531557056216127745711

theorem tailTrace_2340466 : CollatzResearch.WordTrace tailWord_2340466 prefixEnd_2340466 133531557056216127745711 := by
  unfold tailWord_2340466
  simp only [CollatzResearch.WordTrace]
  refine ⟨21340951984724719153648313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56909205292599251076395501 21340951984724719153648313)
  ·
    refine ⟨16005713988543539365236235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21340951984724719153648313 16005713988543539365236235)
    ·
      refine ⟨24008570982815309047854353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16005713988543539365236235 24008570982815309047854353)
      ·
        refine ⟨18006428237111481785890765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24008570982815309047854353 18006428237111481785890765)
        ·
          refine ⟨6752410588916805669709037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18006428237111481785890765 6752410588916805669709037)
          ·
            refine ⟨2532153970843802126140889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6752410588916805669709037 2532153970843802126140889)
            ·
              refine ⟨1899115478132851594605667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2532153970843802126140889 1899115478132851594605667)
              ·
                refine ⟨2848673217199277391908501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1899115478132851594605667 2848673217199277391908501)
                ·
                  refine ⟨133531557056216127745711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2848673217199277391908501 133531557056216127745711)
                  ·
                    rfl

theorem cell23_2340466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_2340466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340466 prefixEnd_2340466 := by exact prefixLift 2340466
  have htrace : WordTrace (prefixWord ++ tailWord_2340466) baseStart_2340466 baseEnd_2340466 := by
    simpa [prefixWord, tailWord_2340466, baseEnd_2340466] using wordTrace_append hprefix tailTrace_2340466
  have hstable : (prefixWord ++ tailWord_2340466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340466).length < 2 ^ (prefixWord ++ tailWord_2340466).sum := by decide
  have hdescent : baseEnd_2340466 < baseStart_2340466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340492 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 1, 6]
def baseStart_2340492 : Nat := 118140960795 + 2340492 * 2 ^ 59
def prefixEnd_2340492 : Nat := 4983230072969 + 3 ^ 40 * 2340492 * 2
def baseEnd_2340492 : Nat := 400599121334320682662093

theorem tailTrace_2340492 : CollatzResearch.WordTrace tailWord_2340492 prefixEnd_2340492 400599121334320682662093 := by
  unfold tailWord_2340492
  simp only [CollatzResearch.WordTrace]
  refine ⟨42682378118402341527519865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56909837491203122036693153 42682378118402341527519865)
  ·
    refine ⟨32011783588801756145639899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42682378118402341527519865 32011783588801756145639899)
    ·
      refine ⟨48017675383202634218459849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32011783588801756145639899 48017675383202634218459849)
      ·
        refine ⟨36013256537401975663844887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48017675383202634218459849 36013256537401975663844887)
        ·
          refine ⟨54019884806102963495767331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36013256537401975663844887 54019884806102963495767331)
          ·
            refine ⟨81029827209154445243650997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54019884806102963495767331 81029827209154445243650997)
            ·
              refine ⟨7596546300858229241592281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81029827209154445243650997 7596546300858229241592281)
              ·
                refine ⟨5697409725643671931194211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7596546300858229241592281 5697409725643671931194211)
                ·
                  refine ⟨8546114588465507896791317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5697409725643671931194211 8546114588465507896791317)
                  ·
                    refine ⟨400599121334320682662093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8546114588465507896791317 400599121334320682662093)
                    ·
                      rfl

theorem cell23_2340492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_2340492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340492 prefixEnd_2340492 := by exact prefixLift 2340492
  have htrace : WordTrace (prefixWord ++ tailWord_2340492) baseStart_2340492 baseEnd_2340492 := by
    simpa [prefixWord, tailWord_2340492, baseEnd_2340492] using wordTrace_append hprefix tailTrace_2340492
  have hstable : (prefixWord ++ tailWord_2340492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340492).length < 2 ^ (prefixWord ++ tailWord_2340492).sum := by decide
  have hdescent : baseEnd_2340492 < baseStart_2340492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340510 : List Nat := [4, 3, 1, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_2340510 : Nat := 118140960795 + 2340510 * 2 ^ 59
def prefixEnd_2340510 : Nat := 4983230072969 + 3 ^ 40 * 2340510 * 2
def baseEnd_2340510 : Nat := 1201806606654742977561197

theorem tailTrace_2340510 : CollatzResearch.WordTrace tailWord_2340510 prefixEnd_2340510 1201806606654742977561197 := by
  unfold tailWord_2340510
  simp only [CollatzResearch.WordTrace]
  refine ⟨10670676593842434016149373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56910275167159648086129989 10670676593842434016149373)
  ·
    refine ⟨4001503722690912756056015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10670676593842434016149373 4001503722690912756056015)
    ·
      refine ⟨6002255584036369134084023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4001503722690912756056015 6002255584036369134084023)
      ·
        refine ⟨9003383376054553701126035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6002255584036369134084023 9003383376054553701126035)
        ·
          refine ⟨13505075064081830551689053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9003383376054553701126035 13505075064081830551689053)
          ·
            refine ⟨5064403149030686456883395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13505075064081830551689053 5064403149030686456883395)
            ·
              refine ⟨7596604723546029685325093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5064403149030686456883395 7596604723546029685325093)
              ·
                refine ⟨1424363385664880565998455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7596604723546029685325093 1424363385664880565998455)
                ·
                  refine ⟨2136545078497320848997683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1424363385664880565998455 2136545078497320848997683)
                  ·
                    refine ⟨3204817617745981273496525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2136545078497320848997683 3204817617745981273496525)
                    ·
                      refine ⟨1201806606654742977561197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3204817617745981273496525 1201806606654742977561197)
                      ·
                        rfl

theorem cell23_2340510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_2340510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340510 prefixEnd_2340510 := by exact prefixLift 2340510
  have htrace : WordTrace (prefixWord ++ tailWord_2340510) baseStart_2340510 baseEnd_2340510 := by
    simpa [prefixWord, tailWord_2340510, baseEnd_2340510] using wordTrace_append hprefix tailTrace_2340510
  have hstable : (prefixWord ++ tailWord_2340510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340510).length < 2 ^ (prefixWord ++ tailWord_2340510).sum := by decide
  have hdescent : baseEnd_2340510 < baseStart_2340510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340549 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 6, 1, 3]
def baseStart_2340549 : Nat := 118140960795 + 2340549 * 2 ^ 59
def prefixEnd_2340549 : Nat := 4983230072969 + 3 ^ 40 * 2340549 * 2
def baseEnd_2340549 : Nat := 1201826632400268324973517

theorem tailTrace_2340549 : CollatzResearch.WordTrace tailWord_2340549 prefixEnd_2340549 1201826632400268324973517 := by
  unfold tailWord_2340549
  simp only [CollatzResearch.WordTrace]
  refine ⟨85366835197598181789864701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56911223465065454526576467 85366835197598181789864701)
  ·
    refine ⟨32012563199099318171199263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85366835197598181789864701 32012563199099318171199263)
    ·
      refine ⟨48018844798648977256798895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32012563199099318171199263 48018844798648977256798895)
      ·
        refine ⟨72028267197973465885198343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48018844798648977256798895 72028267197973465885198343)
        ·
          refine ⟨108042400796960198827797515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72028267197973465885198343 108042400796960198827797515)
          ·
            refine ⟨162063601195440298241696273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108042400796960198827797515 162063601195440298241696273)
            ·
              refine ⟨121547700896580223681272205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162063601195440298241696273 121547700896580223681272205)
              ·
                refine ⟨45580387836217583880477077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121547700896580223681272205 45580387836217583880477077)
                ·
                  refine ⟨2136580679822699244397363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45580387836217583880477077 2136580679822699244397363)
                  ·
                    refine ⟨3204871019734048866596045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2136580679822699244397363 3204871019734048866596045)
                    ·
                      refine ⟨1201826632400268324973517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3204871019734048866596045 1201826632400268324973517)
                      ·
                        rfl

theorem cell23_2340549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 1, 3].length) (baseStart_2340549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340549 prefixEnd_2340549 := by exact prefixLift 2340549
  have htrace : WordTrace (prefixWord ++ tailWord_2340549) baseStart_2340549 baseEnd_2340549 := by
    simpa [prefixWord, tailWord_2340549, baseEnd_2340549] using wordTrace_append hprefix tailTrace_2340549
  have hstable : (prefixWord ++ tailWord_2340549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340549).length < 2 ^ (prefixWord ++ tailWord_2340549).sum := by decide
  have hdescent : baseEnd_2340549 < baseStart_2340549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340550 : List Nat := [6, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_2340550 : Nat := 118140960795 + 2340550 * 2 ^ 59
def prefixEnd_2340550 : Nat := 4983230072969 + 3 ^ 40 * 2340550 * 2
def baseEnd_2340550 : Nat := 1201827145880922821061013

theorem tailTrace_2340550 : CollatzResearch.WordTrace tailWord_2340550 prefixEnd_2340550 1201827145880922821061013 := by
  unfold tailWord_2340550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2667714739706079967520347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56911247780396372640434069 2667714739706079967520347)
  ·
    refine ⟨4001572109559119951280521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2667714739706079967520347 4001572109559119951280521)
    ·
      refine ⟨3001179082169339963460391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4001572109559119951280521 3001179082169339963460391)
      ·
        refine ⟨4501768623254009945190587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3001179082169339963460391 4501768623254009945190587)
        ·
          refine ⟨6752652934881014917785881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4501768623254009945190587 6752652934881014917785881)
          ·
            refine ⟨5064489701160761188339411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6752652934881014917785881 5064489701160761188339411)
            ·
              refine ⟨7596734551741141782509117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5064489701160761188339411 7596734551741141782509117)
              ·
                refine ⟨2848775456902928168440919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7596734551741141782509117 2848775456902928168440919)
                ·
                  refine ⟨4273163185354392252661379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2848775456902928168440919 4273163185354392252661379)
                  ·
                    refine ⟨6409744778031588378992069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4273163185354392252661379 6409744778031588378992069)
                    ·
                      refine ⟨1201827145880922821061013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6409744778031588378992069 1201827145880922821061013)
                      ·
                        rfl

theorem cell23_2340550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_2340550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340550 prefixEnd_2340550 := by exact prefixLift 2340550
  have htrace : WordTrace (prefixWord ++ tailWord_2340550) baseStart_2340550 baseEnd_2340550 := by
    simpa [prefixWord, tailWord_2340550, baseEnd_2340550] using wordTrace_append hprefix tailTrace_2340550
  have hstable : (prefixWord ++ tailWord_2340550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340550).length < 2 ^ (prefixWord ++ tailWord_2340550).sum := by decide
  have hdescent : baseEnd_2340550 < baseStart_2340550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340593 : List Nat := [1, 2, 2, 2, 2, 4, 2, 2, 1, 3, 2]
def baseStart_2340593 : Nat := 118140960795 + 2340593 * 2 ^ 59
def prefixEnd_2340593 : Nat := 4983230072969 + 3 ^ 40 * 2340593 * 2
def baseEnd_2340593 : Nat := 1201849225549066152823315

theorem tailTrace_2340593 : CollatzResearch.WordTrace tailWord_2340593 prefixEnd_2340593 1201849225549066152823315 := by
  unfold tailWord_2340593
  simp only [CollatzResearch.WordTrace]
  refine ⟨85368440009438777304466433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56912293339625851536310955 85368440009438777304466433)
  ·
    refine ⟨64026330007079082978349825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85368440009438777304466433 64026330007079082978349825)
    ·
      refine ⟨48019747505309312233762369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64026330007079082978349825 48019747505309312233762369)
      ·
        refine ⟨36014810628981984175321777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48019747505309312233762369 36014810628981984175321777)
        ·
          refine ⟨27011107971736488131491333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36014810628981984175321777 27011107971736488131491333)
          ·
            refine ⟨5064582744700591524654625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27011107971736488131491333 5064582744700591524654625)
            ·
              refine ⟨3798437058525443643490969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5064582744700591524654625 3798437058525443643490969)
              ·
                refine ⟨2848827793894082732618227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3798437058525443643490969 2848827793894082732618227)
                ·
                  refine ⟨4273241690841124098927341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2848827793894082732618227 4273241690841124098927341)
                  ·
                    refine ⟨1602465634065421537097753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4273241690841124098927341 1602465634065421537097753)
                    ·
                      refine ⟨1201849225549066152823315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1602465634065421537097753 1201849225549066152823315)
                      ·
                        rfl

theorem cell23_2340593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_2340593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340593 prefixEnd_2340593 := by exact prefixLift 2340593
  have htrace : WordTrace (prefixWord ++ tailWord_2340593) baseStart_2340593 baseEnd_2340593 := by
    simpa [prefixWord, tailWord_2340593, baseEnd_2340593] using wordTrace_append hprefix tailTrace_2340593
  have hstable : (prefixWord ++ tailWord_2340593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340593).length < 2 ^ (prefixWord ++ tailWord_2340593).sum := by decide
  have hdescent : baseEnd_2340593 < baseStart_2340593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340629 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 7]
def baseStart_2340629 : Nat := 118140960795 + 2340629 * 2 ^ 59
def prefixEnd_2340629 : Nat := 4983230072969 + 3 ^ 40 * 2340629 * 2
def baseEnd_2340629 : Nat := 133540856761403112441461

theorem tailTrace_2340629 : CollatzResearch.WordTrace tailWord_2340629 prefixEnd_2340629 133540856761403112441461 := by
  unfold tailWord_2340629
  simp only [CollatzResearch.WordTrace]
  refine ⟨85369753037308355452776941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56913168691538903635184627 85369753037308355452776941)
  ·
    refine ⟨32013657388990633294791353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85369753037308355452776941 32013657388990633294791353)
    ·
      refine ⟨24010243041742974971093515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32013657388990633294791353 24010243041742974971093515)
      ·
        refine ⟨36015364562614462456640273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24010243041742974971093515 36015364562614462456640273)
        ·
          refine ⟨27011523421960846842480205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36015364562614462456640273 27011523421960846842480205)
          ·
            refine ⟨10129321283235317565930077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27011523421960846842480205 10129321283235317565930077)
            ·
              refine ⟨3798495481213244087223779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10129321283235317565930077 3798495481213244087223779)
              ·
                refine ⟨5697743221819866130835669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3798495481213244087223779 5697743221819866130835669)
                ·
                  refine ⟨133540856761403112441461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5697743221819866130835669 133540856761403112441461)
                  ·
                    rfl

theorem cell23_2340629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 7].length) (baseStart_2340629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340629 prefixEnd_2340629 := by exact prefixLift 2340629
  have htrace : WordTrace (prefixWord ++ tailWord_2340629) baseStart_2340629 baseEnd_2340629 := by
    simpa [prefixWord, tailWord_2340629, baseEnd_2340629] using wordTrace_append hprefix tailTrace_2340629
  have hstable : (prefixWord ++ tailWord_2340629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340629).length < 2 ^ (prefixWord ++ tailWord_2340629).sum := by decide
  have hdescent : baseEnd_2340629 < baseStart_2340629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340639 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 3]
def baseStart_2340639 : Nat := 118140960795 + 2340639 * 2 ^ 59
def prefixEnd_2340639 : Nat := 4983230072969 + 3 ^ 40 * 2340639 * 2
def baseEnd_2340639 : Nat := 1201872845659172972848103

theorem tailTrace_2340639 : CollatzResearch.WordTrace tailWord_2340639 prefixEnd_2340639 1201872845659172972848103 := by
  unfold tailWord_2340639
  simp only [CollatzResearch.WordTrace]
  refine ⟨85370117767272127160640971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56913411844848084773760647 85370117767272127160640971)
  ·
    refine ⟨128055176650908190740961457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85370117767272127160640971 128055176650908190740961457)
    ·
      refine ⟨96041382488181143055721093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128055176650908190740961457 96041382488181143055721093)
      ·
        refine ⟨18007759216533964322947705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96041382488181143055721093 18007759216533964322947705)
        ·
          refine ⟨13505819412400473242210779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18007759216533964322947705 13505819412400473242210779)
          ·
            refine ⟨20258729118600709863316169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13505819412400473242210779 20258729118600709863316169)
            ·
              refine ⟨15194046838950532397487127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20258729118600709863316169 15194046838950532397487127)
              ·
                refine ⟨22791070258425798596230691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15194046838950532397487127 22791070258425798596230691)
                ·
                  refine ⟨34186605387638697894346037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22791070258425798596230691 34186605387638697894346037)
                  ·
                    refine ⟨3204994255091127927594941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34186605387638697894346037 3204994255091127927594941)
                    ·
                      refine ⟨1201872845659172972848103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3204994255091127927594941 1201872845659172972848103)
                      ·
                        rfl

theorem cell23_2340639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_2340639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340639 prefixEnd_2340639 := by exact prefixLift 2340639
  have htrace : WordTrace (prefixWord ++ tailWord_2340639) baseStart_2340639 baseEnd_2340639 := by
    simpa [prefixWord, tailWord_2340639, baseEnd_2340639] using wordTrace_append hprefix tailTrace_2340639
  have hstable : (prefixWord ++ tailWord_2340639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340639).length < 2 ^ (prefixWord ++ tailWord_2340639).sum := by decide
  have hdescent : baseEnd_2340639 < baseStart_2340639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340716 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 3]
def baseStart_2340716 : Nat := 118140960795 + 2340716 * 2 ^ 59
def prefixEnd_2340716 : Nat := 4983230072969 + 3 ^ 40 * 2340716 * 2
def baseEnd_2340716 : Nat := 1201912383669569171585249

theorem tailTrace_2340716 : CollatzResearch.WordTrace tailWord_2340716 prefixEnd_2340716 1201912383669569171585249 := by
  unfold tailWord_2340716
  simp only [CollatzResearch.WordTrace]
  refine ⟨42686463093996584655597001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56915284125328779540796001 42686463093996584655597001)
  ·
    refine ⟨32014847320497438491697751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42686463093996584655597001 32014847320497438491697751)
    ·
      refine ⟨48022270980746157737546627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32014847320497438491697751 48022270980746157737546627)
      ·
        refine ⟨72033406471119236606319941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48022270980746157737546627 72033406471119236606319941)
        ·
          refine ⟨13506263713334856863684989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72033406471119236606319941 13506263713334856863684989)
          ·
            refine ⟨5064848892500571323881871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13506263713334856863684989 5064848892500571323881871)
            ·
              refine ⟨7597273338750856985822807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5064848892500571323881871 7597273338750856985822807)
              ·
                refine ⟨11395910008126285478734211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7597273338750856985822807 11395910008126285478734211)
                ·
                  refine ⟨17093865012189428218101317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11395910008126285478734211 17093865012189428218101317)
                  ·
                    refine ⟨3205099689785517790893997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17093865012189428218101317 3205099689785517790893997)
                    ·
                      refine ⟨1201912383669569171585249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3205099689785517790893997 1201912383669569171585249)
                      ·
                        rfl

theorem cell23_2340716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_2340716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340716 prefixEnd_2340716 := by exact prefixLift 2340716
  have htrace : WordTrace (prefixWord ++ tailWord_2340716) baseStart_2340716 baseEnd_2340716 := by
    simpa [prefixWord, tailWord_2340716, baseEnd_2340716] using wordTrace_append hprefix tailTrace_2340716
  have hstable : (prefixWord ++ tailWord_2340716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340716).length < 2 ^ (prefixWord ++ tailWord_2340716).sum := by decide
  have hdescent : baseEnd_2340716 < baseStart_2340716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340739 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 6]
def baseStart_2340739 : Nat := 118140960795 + 2340739 * 2 ^ 59
def prefixEnd_2340739 : Nat := 4983230072969 + 3 ^ 40 * 2340739 * 2
def baseEnd_2340739 : Nat := 1201924193724622581597643

theorem tailTrace_2340739 : CollatzResearch.WordTrace tailWord_2340739 prefixEnd_2340739 1201924193724622581597643 := by
  unfold tailWord_2340739
  simp only [CollatzResearch.WordTrace]
  refine ⟨85373765066909844239281271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56915843377939896159520847 85373765066909844239281271)
  ·
    refine ⟨128060647600364766358921907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85373765066909844239281271 128060647600364766358921907)
    ·
      refine ⟨192090971400547149538382861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128060647600364766358921907 192090971400547149538382861)
      ·
        refine ⟨72034114275205181076893573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192090971400547149538382861 72034114275205181076893573)
        ·
          refine ⟨13506396426600971451917545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72034114275205181076893573 13506396426600971451917545)
          ·
            refine ⟨10129797319950728588938159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13506396426600971451917545 10129797319950728588938159)
            ·
              refine ⟨15194695979926092883407239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10129797319950728588938159 15194695979926092883407239)
              ·
                refine ⟨22792043969889139325110859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15194695979926092883407239 22792043969889139325110859)
                ·
                  refine ⟨34188065954833708987666289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22792043969889139325110859 34188065954833708987666289)
                  ·
                    refine ⟨25641049466125281740749717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34188065954833708987666289 25641049466125281740749717)
                    ·
                      refine ⟨1201924193724622581597643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25641049466125281740749717 1201924193724622581597643)
                      ·
                        rfl

theorem cell23_2340739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_2340739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340739 prefixEnd_2340739 := by exact prefixLift 2340739
  have htrace : WordTrace (prefixWord ++ tailWord_2340739) baseStart_2340739 baseEnd_2340739 := by
    simpa [prefixWord, tailWord_2340739, baseEnd_2340739] using wordTrace_append hprefix tailTrace_2340739
  have hstable : (prefixWord ++ tailWord_2340739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340739).length < 2 ^ (prefixWord ++ tailWord_2340739).sum := by decide
  have hdescent : baseEnd_2340739 < baseStart_2340739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340799 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 6]
def baseStart_2340799 : Nat := 118140960795 + 2340799 * 2 ^ 59
def prefixEnd_2340799 : Nat := 4983230072969 + 3 ^ 40 * 2340799 * 2
def baseEnd_2340799 : Nat := 1201955002563892346847367

theorem tailTrace_2340799 : CollatzResearch.WordTrace tailWord_2340799 prefixEnd_2340799 1201955002563892346847367 := by
  unfold tailWord_2340799
  simp only [CollatzResearch.WordTrace]
  refine ⟨85375953446692474486465451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56917302297794982990976967 85375953446692474486465451)
  ·
    refine ⟨128063930170038711729698177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85375953446692474486465451 128063930170038711729698177)
    ·
      refine ⟨96047947627529033797273633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128063930170038711729698177 96047947627529033797273633)
      ·
        refine ⟨72035960720646775347955225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96047947627529033797273633 72035960720646775347955225)
        ·
          refine ⟨54026970540485081510966419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72035960720646775347955225 54026970540485081510966419)
          ·
            refine ⟨81040455810727622266449629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54026970540485081510966419 81040455810727622266449629)
            ·
              refine ⟨30390170929022858349918611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81040455810727622266449629 30390170929022858349918611)
              ·
                refine ⟨45585256393534287524877917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30390170929022858349918611 45585256393534287524877917)
                ·
                  refine ⟨17094471147575357821829219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45585256393534287524877917 17094471147575357821829219)
                  ·
                    refine ⟨25641706721363036732743829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17094471147575357821829219 25641706721363036732743829)
                    ·
                      refine ⟨1201955002563892346847367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25641706721363036732743829 1201955002563892346847367)
                      ·
                        rfl

theorem cell23_2340799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_2340799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340799 prefixEnd_2340799 := by exact prefixLift 2340799
  have htrace : WordTrace (prefixWord ++ tailWord_2340799) baseStart_2340799 baseEnd_2340799 := by
    simpa [prefixWord, tailWord_2340799, baseEnd_2340799] using wordTrace_append hprefix tailTrace_2340799
  have hstable : (prefixWord ++ tailWord_2340799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340799).length < 2 ^ (prefixWord ++ tailWord_2340799).sum := by decide
  have hdescent : baseEnd_2340799 < baseStart_2340799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340820 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 5, 2, 2]
def baseStart_2340820 : Nat := 118140960795 + 2340820 * 2 ^ 59
def prefixEnd_2340820 : Nat := 4983230072969 + 3 ^ 40 * 2340820 * 2
def baseEnd_2340820 : Nat := 1201965785657636764684771

theorem tailTrace_2340820 : CollatzResearch.WordTrace tailWord_2340820 prefixEnd_2340820 1201965785657636764684771 := by
  unfold tailWord_2340820
  simp only [CollatzResearch.WordTrace]
  refine ⟨42688359689808197536489957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56917812919744263381986609 42688359689808197536489957)
  ·
    refine ⟨8004067441839037038091867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42688359689808197536489957 8004067441839037038091867)
    ·
      refine ⟨12006101162758555557137801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8004067441839037038091867 12006101162758555557137801)
      ·
        refine ⟨9004575872068916667853351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12006101162758555557137801 9004575872068916667853351)
        ·
          refine ⟨13506863808103375001780027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9004575872068916667853351 13506863808103375001780027)
          ·
            refine ⟨20260295712155062502670041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13506863808103375001780027 20260295712155062502670041)
            ·
              refine ⟨15195221784116296877002531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20260295712155062502670041 15195221784116296877002531)
              ·
                refine ⟨22792832676174445315503797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15195221784116296877002531 22792832676174445315503797)
                ·
                  refine ⟨2136828063391354248328481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22792832676174445315503797 2136828063391354248328481)
                  ·
                    refine ⟨1602621047543515686246361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2136828063391354248328481 1602621047543515686246361)
                    ·
                      refine ⟨1201965785657636764684771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1602621047543515686246361 1201965785657636764684771)
                      ·
                        rfl

theorem cell23_2340820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_2340820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340820 prefixEnd_2340820 := by exact prefixLift 2340820
  have htrace : WordTrace (prefixWord ++ tailWord_2340820) baseStart_2340820 baseEnd_2340820 := by
    simpa [prefixWord, tailWord_2340820, baseEnd_2340820] using wordTrace_append hprefix tailTrace_2340820
  have hstable : (prefixWord ++ tailWord_2340820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340820).length < 2 ^ (prefixWord ++ tailWord_2340820).sum := by decide
  have hdescent : baseEnd_2340820 < baseStart_2340820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340876 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 2, 3, 4]
def baseStart_2340876 : Nat := 118140960795 + 2340876 * 2 ^ 59
def prefixEnd_2340876 : Nat := 4983230072969 + 3 ^ 40 * 2340876 * 2
def baseEnd_2340876 : Nat := 1201994540574288545584513

theorem tailTrace_2340876 : CollatzResearch.WordTrace tailWord_2340876 prefixEnd_2340876 1201994540574288545584513 := by
  unfold tailWord_2340876
  simp only [CollatzResearch.WordTrace]
  refine ⟨42689380933706758318509241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56919174578275677758012321 42689380933706758318509241)
  ·
    refine ⟨32017035700280068738881931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42689380933706758318509241 32017035700280068738881931)
    ·
      refine ⟨48025553550420103108322897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32017035700280068738881931 48025553550420103108322897)
      ·
        refine ⟨36019165162815077331242173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48025553550420103108322897 36019165162815077331242173)
        ·
          refine ⟨13507186936055653999215815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36019165162815077331242173 13507186936055653999215815)
          ·
            refine ⟨20260780404083480998823723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13507186936055653999215815 20260780404083480998823723)
            ·
              refine ⟨30391170606125221498235585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20260780404083480998823723 30391170606125221498235585)
              ·
                refine ⟨22793377954593916123676689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30391170606125221498235585 22793377954593916123676689)
                ·
                  refine ⟨17095033465945437092757517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22793377954593916123676689 17095033465945437092757517)
                  ·
                    refine ⟨6410637549729538909784069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17095033465945437092757517 6410637549729538909784069)
                    ·
                      refine ⟨1201994540574288545584513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6410637549729538909784069 1201994540574288545584513)
                      ·
                        rfl

theorem cell23_2340876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_2340876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340876 prefixEnd_2340876 := by exact prefixLift 2340876
  have htrace : WordTrace (prefixWord ++ tailWord_2340876) baseStart_2340876 baseEnd_2340876 := by
    simpa [prefixWord, tailWord_2340876, baseEnd_2340876] using wordTrace_append hprefix tailTrace_2340876
  have hstable : (prefixWord ++ tailWord_2340876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340876).length < 2 ^ (prefixWord ++ tailWord_2340876).sum := by decide
  have hdescent : baseEnd_2340876 < baseStart_2340876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340897 : List Nat := [1, 2, 3, 2, 4, 1, 1, 3, 1, 3, 2]
def baseStart_2340897 : Nat := 118140960795 + 2340897 * 2 ^ 59
def prefixEnd_2340897 : Nat := 4983230072969 + 3 ^ 40 * 2340897 * 2
def baseEnd_2340897 : Nat := 1202005323668032963421917

theorem tailTrace_2340897 : CollatzResearch.WordTrace tailWord_2340897 prefixEnd_2340897 1202005323668032963421917 := by
  unfold tailWord_2340897
  simp only [CollatzResearch.WordTrace]
  refine ⟨85379527800337437223532945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56919685200224958149021963 85379527800337437223532945)
  ·
    refine ⟨64034645850253077917649709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85379527800337437223532945 64034645850253077917649709)
    ·
      refine ⟨24012992193844904219118641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64034645850253077917649709 24012992193844904219118641)
      ·
        refine ⟨18009744145383678164338981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24012992193844904219118641 18009744145383678164338981)
        ·
          refine ⟨3376827027259439655813559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18009744145383678164338981 3376827027259439655813559)
          ·
            refine ⟨5065240540889159483720339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3376827027259439655813559 5065240540889159483720339)
            ·
              refine ⟨7597860811333739225580509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5065240540889159483720339 7597860811333739225580509)
              ·
                refine ⟨2849197804250152209592691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7597860811333739225580509 2849197804250152209592691)
                ·
                  refine ⟨4273796706375228314389037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2849197804250152209592691 4273796706375228314389037)
                  ·
                    refine ⟨1602673764890710617895889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4273796706375228314389037 1602673764890710617895889)
                    ·
                      refine ⟨1202005323668032963421917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1602673764890710617895889 1202005323668032963421917)
                      ·
                        rfl

theorem cell23_2340897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_2340897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340897 prefixEnd_2340897 := by exact prefixLift 2340897
  have htrace : WordTrace (prefixWord ++ tailWord_2340897) baseStart_2340897 baseEnd_2340897 := by
    simpa [prefixWord, tailWord_2340897, baseEnd_2340897] using wordTrace_append hprefix tailTrace_2340897
  have hstable : (prefixWord ++ tailWord_2340897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340897).length < 2 ^ (prefixWord ++ tailWord_2340897).sum := by decide
  have hdescent : baseEnd_2340897 < baseStart_2340897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340973 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_2340973 : Nat := 118140960795 + 2340973 * 2 ^ 59
def prefixEnd_2340973 : Nat := 4983230072969 + 3 ^ 40 * 2340973 * 2
def baseEnd_2340973 : Nat := 1202044348197774666071567

theorem tailTrace_2340973 : CollatzResearch.WordTrace tailWord_2340973 prefixEnd_2340973 1202044348197774666071567 := by
  unfold tailWord_2340973
  simp only [CollatzResearch.WordTrace]
  refine ⟨85382299748062102203299573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56921533165374734802199715 85382299748062102203299573)
  ·
    refine ⟨8004590601380822081559335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85382299748062102203299573 8004590601380822081559335)
    ·
      refine ⟨12006885902071233122339003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8004590601380822081559335 12006885902071233122339003)
      ·
        refine ⟨18010328853106849683508505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12006885902071233122339003 18010328853106849683508505)
        ·
          refine ⟨13507746639830137262631379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18010328853106849683508505 13507746639830137262631379)
          ·
            refine ⟨20261619959745205893947069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13507746639830137262631379 20261619959745205893947069)
            ·
              refine ⟨7598107484904452210230151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20261619959745205893947069 7598107484904452210230151)
              ·
                refine ⟨11397161227356678315345227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7598107484904452210230151 11397161227356678315345227)
                ·
                  refine ⟨17095741841035017473017841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11397161227356678315345227 17095741841035017473017841)
                  ·
                    refine ⟨12821806380776263104763381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17095741841035017473017841 12821806380776263104763381)
                    ·
                      refine ⟨1202044348197774666071567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12821806380776263104763381 1202044348197774666071567)
                      ·
                        rfl

theorem cell23_2340973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_2340973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340973 prefixEnd_2340973 := by exact prefixLift 2340973
  have htrace : WordTrace (prefixWord ++ tailWord_2340973) baseStart_2340973 baseEnd_2340973 := by
    simpa [prefixWord, tailWord_2340973, baseEnd_2340973] using wordTrace_append hprefix tailTrace_2340973
  have hstable : (prefixWord ++ tailWord_2340973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340973).length < 2 ^ (prefixWord ++ tailWord_2340973).sum := by decide
  have hdescent : baseEnd_2340973 < baseStart_2340973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340986 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5]
def baseStart_2340986 : Nat := 118140960795 + 2340986 * 2 ^ 59
def prefixEnd_2340986 : Nat := 4983230072969 + 3 ^ 40 * 2340986 * 2
def baseEnd_2340986 : Nat := 1202051023446283115209007

theorem tailTrace_2340986 : CollatzResearch.WordTrace tailWord_2340986 prefixEnd_2340986 1202051023446283115209007 := by
  unfold tailWord_2340986
  simp only [CollatzResearch.WordTrace]
  refine ⟨21345693474253751355880703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56921849264676670282348541 21345693474253751355880703)
  ·
    refine ⟨32018540211380627033821055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21345693474253751355880703 32018540211380627033821055)
    ·
      refine ⟨48027810317070940550731583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32018540211380627033821055 48027810317070940550731583)
      ·
        refine ⟨72041715475606410826097375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48027810317070940550731583 72041715475606410826097375)
        ·
          refine ⟨108062573213409616239146063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72041715475606410826097375 108062573213409616239146063)
          ·
            refine ⟨162093859820114424358719095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108062573213409616239146063 162093859820114424358719095)
            ·
              refine ⟨243140789730171636538078643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162093859820114424358719095 243140789730171636538078643)
              ·
                refine ⟨364711184595257454807117965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243140789730171636538078643 364711184595257454807117965)
                ·
                  refine ⟨136766694223221545552669237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 364711184595257454807117965 136766694223221545552669237)
                  ·
                    refine ⟨12821877583427019895562741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 136766694223221545552669237 12821877583427019895562741)
                    ·
                      refine ⟨1202051023446283115209007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12821877583427019895562741 1202051023446283115209007)
                      ·
                        rfl

theorem cell23_2340986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_2340986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2340986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2340986 prefixEnd_2340986 := by exact prefixLift 2340986
  have htrace : WordTrace (prefixWord ++ tailWord_2340986) baseStart_2340986 baseEnd_2340986 := by
    simpa [prefixWord, tailWord_2340986, baseEnd_2340986] using wordTrace_append hprefix tailTrace_2340986
  have hstable : (prefixWord ++ tailWord_2340986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340986).length < 2 ^ (prefixWord ++ tailWord_2340986).sum := by decide
  have hdescent : baseEnd_2340986 < baseStart_2340986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341000 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_2341000 : Nat := 118140960795 + 2341000 * 2 ^ 59
def prefixEnd_2341000 : Nat := 4983230072969 + 3 ^ 40 * 2341000 * 2
def baseEnd_2341000 : Nat := 1202058212175446060433943

theorem tailTrace_2341000 : CollatzResearch.WordTrace tailWord_2341000 prefixEnd_2341000 1202058212175446060433943 := by
  unfold tailWord_2341000
  simp only [CollatzResearch.WordTrace]
  refine ⟨42691642259482142907266227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56922189679309523876354969 42691642259482142907266227)
  ·
    refine ⟨64037463389223214360899341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42691642259482142907266227 64037463389223214360899341)
    ·
      refine ⟨24014048770958705385337253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64037463389223214360899341 24014048770958705385337253)
      ·
        refine ⟨4502634144554757259750735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24014048770958705385337253 4502634144554757259750735)
        ·
          refine ⟨6753951216832135889626103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4502634144554757259750735 6753951216832135889626103)
          ·
            refine ⟨10130926825248203834439155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6753951216832135889626103 10130926825248203834439155)
            ·
              refine ⟨15196390237872305751658733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10130926825248203834439155 15196390237872305751658733)
              ·
                refine ⟨5698646339202114656872025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15196390237872305751658733 5698646339202114656872025)
                ·
                  refine ⟨4273984754401585992654019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5698646339202114656872025 4273984754401585992654019)
                  ·
                    refine ⟨6410977131602378988981029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4273984754401585992654019 6410977131602378988981029)
                    ·
                      refine ⟨1202058212175446060433943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6410977131602378988981029 1202058212175446060433943)
                      ·
                        rfl

theorem cell23_2341000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_2341000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341000 prefixEnd_2341000 := by exact prefixLift 2341000
  have htrace : WordTrace (prefixWord ++ tailWord_2341000) baseStart_2341000 baseEnd_2341000 := by
    simpa [prefixWord, tailWord_2341000, baseEnd_2341000] using wordTrace_append hprefix tailTrace_2341000
  have hstable : (prefixWord ++ tailWord_2341000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341000).length < 2 ^ (prefixWord ++ tailWord_2341000).sum := by decide
  have hdescent : baseEnd_2341000 < baseStart_2341000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341020 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_2341020 : Nat := 118140960795 + 2341020 * 2 ^ 59
def prefixEnd_2341020 : Nat := 4983230072969 + 3 ^ 40 * 2341020 * 2
def baseEnd_2341020 : Nat := 1202068481788535982183851

theorem tailTrace_2341020 : CollatzResearch.WordTrace tailWord_2341020 prefixEnd_2341020 1202068481788535982183851 := by
  unfold tailWord_2341020
  simp only [CollatzResearch.WordTrace]
  refine ⟨42692006989445914615130257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56922675985927886153507009 42692006989445914615130257)
  ·
    refine ⟨32019005242084435961347693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42692006989445914615130257 32019005242084435961347693)
    ·
      refine ⟨12007126965781663485505385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32019005242084435961347693 12007126965781663485505385)
      ·
        refine ⟨9005345224336247614129039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12007126965781663485505385 9005345224336247614129039)
        ·
          refine ⟨13508017836504371421193559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9005345224336247614129039 13508017836504371421193559)
          ·
            refine ⟨20262026754756557131790339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13508017836504371421193559 20262026754756557131790339)
            ·
              refine ⟨30393040132134835697685509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20262026754756557131790339 30393040132134835697685509)
              ·
                refine ⟨5698695024775281693316033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30393040132134835697685509 5698695024775281693316033)
                ·
                  refine ⟨4274021268581461269987025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5698695024775281693316033 4274021268581461269987025)
                  ·
                    refine ⟨3205515951436095952490269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4274021268581461269987025 3205515951436095952490269)
                    ·
                      refine ⟨1202068481788535982183851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3205515951436095952490269 1202068481788535982183851)
                      ·
                        rfl

theorem cell23_2341020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_2341020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341020 prefixEnd_2341020 := by exact prefixLift 2341020
  have htrace : WordTrace (prefixWord ++ tailWord_2341020) baseStart_2341020 baseEnd_2341020 := by
    simpa [prefixWord, tailWord_2341020, baseEnd_2341020] using wordTrace_append hprefix tailTrace_2341020
  have hstable : (prefixWord ++ tailWord_2341020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341020).length < 2 ^ (prefixWord ++ tailWord_2341020).sum := by decide
  have hdescent : baseEnd_2341020 < baseStart_2341020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341034 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_2341034 : Nat := 118140960795 + 2341034 * 2 ^ 59
def prefixEnd_2341034 : Nat := 4983230072969 + 3 ^ 40 * 2341034 * 2
def baseEnd_2341034 : Nat := 1202075670517698927408787

theorem tailTrace_2341034 : CollatzResearch.WordTrace tailWord_2341034 prefixEnd_2341034 1202075670517698927408787 := by
  unfold tailWord_2341034
  simp only [CollatzResearch.WordTrace]
  refine ⟨21346131150210277405317539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56923016400560739747513437 21346131150210277405317539)
  ·
    refine ⟨32019196725315416107976309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21346131150210277405317539 32019196725315416107976309)
    ·
      refine ⟨3001799692998320260122779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32019196725315416107976309 3001799692998320260122779)
      ·
        refine ⟨4502699539497480390184169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3001799692998320260122779 4502699539497480390184169)
        ·
          refine ⟨3377024654623110292638127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4502699539497480390184169 3377024654623110292638127)
          ·
            refine ⟨5065536981934665438957191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3377024654623110292638127 5065536981934665438957191)
            ·
              refine ⟨7598305472901998158435787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5065536981934665438957191 7598305472901998158435787)
              ·
                refine ⟨11397458209352997237653681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7598305472901998158435787 11397458209352997237653681)
                ·
                  refine ⟨8548093657014747928240261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11397458209352997237653681 8548093657014747928240261)
                  ·
                    refine ⟨1602767560690265236545049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8548093657014747928240261 1602767560690265236545049)
                    ·
                      refine ⟨1202075670517698927408787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1602767560690265236545049 1202075670517698927408787)
                      ·
                        rfl

theorem cell23_2341034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_2341034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341034 prefixEnd_2341034 := by exact prefixLift 2341034
  have htrace : WordTrace (prefixWord ++ tailWord_2341034) baseStart_2341034 baseEnd_2341034 := by
    simpa [prefixWord, tailWord_2341034, baseEnd_2341034] using wordTrace_append hprefix tailTrace_2341034
  have hstable : (prefixWord ++ tailWord_2341034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341034).length < 2 ^ (prefixWord ++ tailWord_2341034).sum := by decide
  have hdescent : baseEnd_2341034 < baseStart_2341034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341050 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3]
def baseStart_2341050 : Nat := 118140960795 + 2341050 * 2 ^ 59
def prefixEnd_2341050 : Nat := 4983230072969 + 3 ^ 40 * 2341050 * 2
def baseEnd_2341050 : Nat := 1202083886208170864808713

theorem tailTrace_2341050 : CollatzResearch.WordTrace tailWord_2341050 prefixEnd_2341050 1202083886208170864808713 := by
  unfold tailWord_2341050
  simp only [CollatzResearch.WordTrace]
  refine ⟨21346277042195786088463151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56923405445855429569235069 21346277042195786088463151)
  ·
    refine ⟨32019415563293679132694727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21346277042195786088463151 32019415563293679132694727)
    ·
      refine ⟨48029123344940518699042091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32019415563293679132694727 48029123344940518699042091)
      ·
        refine ⟨72043685017410778048563137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48029123344940518699042091 72043685017410778048563137)
        ·
          refine ⟨54032763763058083536422353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72043685017410778048563137 54032763763058083536422353)
          ·
            refine ⟨40524572822293562652316765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54032763763058083536422353 40524572822293562652316765)
            ·
              refine ⟨15196714808360085994618787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40524572822293562652316765 15196714808360085994618787)
              ·
                refine ⟨22795072212540128991928181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15196714808360085994618787 22795072212540128991928181)
                ·
                  refine ⟨2137038019925637092993267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22795072212540128991928181 2137038019925637092993267)
                  ·
                    refine ⟨3205557029888455639489901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2137038019925637092993267 3205557029888455639489901)
                    ·
                      refine ⟨1202083886208170864808713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3205557029888455639489901 1202083886208170864808713)
                      ·
                        rfl

theorem cell23_2341050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3].length) (baseStart_2341050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341050 prefixEnd_2341050 := by exact prefixLift 2341050
  have htrace : WordTrace (prefixWord ++ tailWord_2341050) baseStart_2341050 baseEnd_2341050 := by
    simpa [prefixWord, tailWord_2341050, baseEnd_2341050] using wordTrace_append hprefix tailTrace_2341050
  have hstable : (prefixWord ++ tailWord_2341050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341050).length < 2 ^ (prefixWord ++ tailWord_2341050).sum := by decide
  have hdescent : baseEnd_2341050 < baseStart_2341050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341054 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_2341054 : Nat := 118140960795 + 2341054 * 2 ^ 59
def prefixEnd_2341054 : Nat := 4983230072969 + 3 ^ 40 * 2341054 * 2
def baseEnd_2341054 : Nat := 1202085940130788849158695

theorem tailTrace_2341054 : CollatzResearch.WordTrace tailWord_2341054 prefixEnd_2341054 1202085940130788849158695 := by
  unfold tailWord_2341054
  simp only [CollatzResearch.WordTrace]
  refine ⟨10673156757596081629624777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56923502707179102024665477 10673156757596081629624777)
  ·
    refine ⟨8004867568197061222218583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10673156757596081629624777 8004867568197061222218583)
    ·
      refine ⟨12007301352295591833327875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8004867568197061222218583 12007301352295591833327875)
      ·
        refine ⟨18010952028443387749991813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12007301352295591833327875 18010952028443387749991813)
        ·
          refine ⟨3377053505333135203123465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18010952028443387749991813 3377053505333135203123465)
          ·
            refine ⟨2532790128999851402342599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3377053505333135203123465 2532790128999851402342599)
            ·
              refine ⟨3799185193499777103513899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2532790128999851402342599 3799185193499777103513899)
              ·
                refine ⟨5698777790249665655270849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3799185193499777103513899 5698777790249665655270849)
                ·
                  refine ⟨4274083342687249241453137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5698777790249665655270849 4274083342687249241453137)
                  ·
                    refine ⟨3205562507015436931089853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4274083342687249241453137 3205562507015436931089853)
                    ·
                      refine ⟨1202085940130788849158695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3205562507015436931089853 1202085940130788849158695)
                      ·
                        rfl

theorem cell23_2341054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_2341054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341054 prefixEnd_2341054 := by exact prefixLift 2341054
  have htrace : WordTrace (prefixWord ++ tailWord_2341054) baseStart_2341054 baseEnd_2341054 := by
    simpa [prefixWord, tailWord_2341054, baseEnd_2341054] using wordTrace_append hprefix tailTrace_2341054
  have hstable : (prefixWord ++ tailWord_2341054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341054).length < 2 ^ (prefixWord ++ tailWord_2341054).sum := by decide
  have hdescent : baseEnd_2341054 < baseStart_2341054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341107 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 3, 2, 2]
def baseStart_2341107 : Nat := 118140960795 + 2341107 * 2 ^ 59
def prefixEnd_2341107 : Nat := 4983230072969 + 3 ^ 40 * 2341107 * 2
def baseEnd_2341107 : Nat := 1202113154605477141795951

theorem tailTrace_2341107 : CollatzResearch.WordTrace tailWord_2341107 prefixEnd_2341107 1202113154605477141795951 := by
  unfold tailWord_2341107
  simp only [CollatzResearch.WordTrace]
  refine ⟨85387187129576643088677575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56924791419717762059118383 85387187129576643088677575)
  ·
    refine ⟨128080780694364964633016363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85387187129576643088677575 128080780694364964633016363)
    ·
      refine ⟨192121171041547446949524545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128080780694364964633016363 192121171041547446949524545)
      ·
        refine ⟨144090878281160585212143409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192121171041547446949524545 144090878281160585212143409)
        ·
          refine ⟨108068158710870438909107557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144090878281160585212143409 108068158710870438909107557)
          ·
            refine ⟨20262779758288207295457667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108068158710870438909107557 20262779758288207295457667)
            ·
              refine ⟨30394169637432310943186501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20262779758288207295457667 30394169637432310943186501)
              ·
                refine ⟨5698906807018558301847469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30394169637432310943186501 5698906807018558301847469)
                ·
                  refine ⟨2137090052631959363192801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5698906807018558301847469 2137090052631959363192801)
                  ·
                    refine ⟨1602817539473969522394601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2137090052631959363192801 1602817539473969522394601)
                    ·
                      refine ⟨1202113154605477141795951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1602817539473969522394601 1202113154605477141795951)
                      ·
                        rfl

theorem cell23_2341107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 2, 2].length) (baseStart_2341107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341107 prefixEnd_2341107 := by exact prefixLift 2341107
  have htrace : WordTrace (prefixWord ++ tailWord_2341107) baseStart_2341107 baseEnd_2341107 := by
    simpa [prefixWord, tailWord_2341107, baseEnd_2341107] using wordTrace_append hprefix tailTrace_2341107
  have hstable : (prefixWord ++ tailWord_2341107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341107).length < 2 ^ (prefixWord ++ tailWord_2341107).sum := by decide
  have hdescent : baseEnd_2341107 < baseStart_2341107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341193 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 2, 3, 6]
def baseStart_2341193 : Nat := 118140960795 + 2341193 * 2 ^ 59
def prefixEnd_2341193 : Nat := 4983230072969 + 3 ^ 40 * 2341193 * 2
def baseEnd_2341193 : Nat := 1202157313941763805320555

theorem tailTrace_2341193 : CollatzResearch.WordTrace tailWord_2341193 prefixEnd_2341193 1202157313941763805320555 := by
  unfold tailWord_2341193
  simp only [CollatzResearch.WordTrace]
  refine ⟨85390323807265079776308233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56926882538176719850872155 85390323807265079776308233)
  ·
    refine ⟨64042742855448809832231175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85390323807265079776308233 64042742855448809832231175)
    ·
      refine ⟨96064114283173214748346763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64042742855448809832231175 96064114283173214748346763)
      ·
        refine ⟨144096171424759822122520145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96064114283173214748346763 144096171424759822122520145)
        ·
          refine ⟨108072128568569866591890109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144096171424759822122520145 108072128568569866591890109)
          ·
            refine ⟨40527048213213699971958791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108072128568569866591890109 40527048213213699971958791)
            ·
              refine ⟨60790572319820549957938187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40527048213213699971958791 60790572319820549957938187)
              ·
                refine ⟨91185858479730824936907281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60790572319820549957938187 91185858479730824936907281)
                ·
                  refine ⟨68389393859798118702680461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91185858479730824936907281 68389393859798118702680461)
                  ·
                    refine ⟨25646022697424294513505173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68389393859798118702680461 25646022697424294513505173)
                    ·
                      refine ⟨1202157313941763805320555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25646022697424294513505173 1202157313941763805320555)
                      ·
                        rfl

theorem cell23_2341193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_2341193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341193 prefixEnd_2341193 := by exact prefixLift 2341193
  have htrace : WordTrace (prefixWord ++ tailWord_2341193) baseStart_2341193 baseEnd_2341193 := by
    simpa [prefixWord, tailWord_2341193, baseEnd_2341193] using wordTrace_append hprefix tailTrace_2341193
  have hstable : (prefixWord ++ tailWord_2341193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341193).length < 2 ^ (prefixWord ++ tailWord_2341193).sum := by decide
  have hdescent : baseEnd_2341193 < baseStart_2341193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341200 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 3]
def baseStart_2341200 : Nat := 118140960795 + 2341200 * 2 ^ 59
def prefixEnd_2341200 : Nat := 4983230072969 + 3 ^ 40 * 2341200 * 2
def baseEnd_2341200 : Nat := 1202160908306345277933023

theorem tailTrace_2341200 : CollatzResearch.WordTrace tailWord_2341200 prefixEnd_2341200 1202160908306345277933023 := by
  unfold tailWord_2341200
  simp only [CollatzResearch.WordTrace]
  refine ⟨42695289559119859985906527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56927052745493146647875369 42695289559119859985906527)
  ·
    refine ⟨64042934338679789978859791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42695289559119859985906527 64042934338679789978859791)
    ·
      refine ⟨96064401508019684968289687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64042934338679789978859791 96064401508019684968289687)
      ·
        refine ⟨144096602262029527452434531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96064401508019684968289687 144096602262029527452434531)
        ·
          refine ⟨216144903393044291178651797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144096602262029527452434531 216144903393044291178651797)
          ·
            refine ⟨10131792346548951148999303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 216144903393044291178651797 10131792346548951148999303)
            ·
              refine ⟨15197688519823426723498955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10131792346548951148999303 15197688519823426723498955)
              ·
                refine ⟨22796532779735140085248433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15197688519823426723498955 22796532779735140085248433)
                ·
                  refine ⟨17097399584801355063936325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22796532779735140085248433 17097399584801355063936325)
                  ·
                    refine ⟨3205762422150254074488061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17097399584801355063936325 3205762422150254074488061)
                    ·
                      refine ⟨1202160908306345277933023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3205762422150254074488061 1202160908306345277933023)
                      ·
                        rfl

theorem cell23_2341200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 3].length) (baseStart_2341200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341200 prefixEnd_2341200 := by exact prefixLift 2341200
  have htrace : WordTrace (prefixWord ++ tailWord_2341200) baseStart_2341200 baseEnd_2341200 := by
    simpa [prefixWord, tailWord_2341200, baseEnd_2341200] using wordTrace_append hprefix tailTrace_2341200
  have hstable : (prefixWord ++ tailWord_2341200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341200).length < 2 ^ (prefixWord ++ tailWord_2341200).sum := by decide
  have hdescent : baseEnd_2341200 < baseStart_2341200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341220 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 7]
def baseStart_2341220 : Nat := 118140960795 + 2341220 * 2 ^ 59
def prefixEnd_2341220 : Nat := 4983230072969 + 3 ^ 40 * 2341220 * 2
def baseEnd_2341220 : Nat := 133574575324381688853659

theorem tailTrace_2341220 : CollatzResearch.WordTrace tailWord_2341220 prefixEnd_2341220 133574575324381688853659 := by
  unfold tailWord_2341220
  simp only [CollatzResearch.WordTrace]
  refine ⟨42695654289083631693770557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56927539052111508925027409 42695654289083631693770557)
  ·
    refine ⟨16010870358406361885163959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42695654289083631693770557 16010870358406361885163959)
    ·
      refine ⟨24016305537609542827745939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16010870358406361885163959 24016305537609542827745939)
      ·
        refine ⟨36024458306414314241618909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24016305537609542827745939 36024458306414314241618909)
        ·
          refine ⟨13509171864905367840607091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36024458306414314241618909 13509171864905367840607091)
          ·
            refine ⟨20263757797358051760910637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13509171864905367840607091 20263757797358051760910637)
            ·
              refine ⟨7598909174009269410341489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20263757797358051760910637 7598909174009269410341489)
              ·
                refine ⟨5699181880506952057756117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7598909174009269410341489 5699181880506952057756117)
                ·
                  refine ⟨133574575324381688853659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5699181880506952057756117 133574575324381688853659)
                  ·
                    rfl

theorem cell23_2341220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_2341220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341220 prefixEnd_2341220 := by exact prefixLift 2341220
  have htrace : WordTrace (prefixWord ++ tailWord_2341220) baseStart_2341220 baseEnd_2341220 := by
    simpa [prefixWord, tailWord_2341220, baseEnd_2341220] using wordTrace_append hprefix tailTrace_2341220
  have hstable : (prefixWord ++ tailWord_2341220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341220).length < 2 ^ (prefixWord ++ tailWord_2341220).sum := by decide
  have hdescent : baseEnd_2341220 < baseStart_2341220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341287 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_2341287 : Nat := 118140960795 + 2341287 * 2 ^ 59
def prefixEnd_2341287 : Nat := 4983230072969 + 3 ^ 40 * 2341287 * 2
def baseEnd_2341287 : Nat := 1202205581123286437545123

theorem tailTrace_2341287 : CollatzResearch.WordTrace tailWord_2341287 prefixEnd_2341287 1202205581123286437545123 := by
  unfold tailWord_2341287
  simp only [CollatzResearch.WordTrace]
  refine ⟨85393752268924533830230115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56929168179283022553486743 85393752268924533830230115)
  ·
    refine ⟨128090628403386800745345173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85393752268924533830230115 128090628403386800745345173)
    ·
      refine ⟨6004248206408756284938055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 128090628403386800745345173 6004248206408756284938055)
      ·
        refine ⟨9006372309613134427407083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6004248206408756284938055 9006372309613134427407083)
        ·
          refine ⟨13509558464419701641110625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9006372309613134427407083 13509558464419701641110625)
          ·
            refine ⟨10132168848314776230832969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13509558464419701641110625 10132168848314776230832969)
            ·
              refine ⟨7599126636236082173124727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10132168848314776230832969 7599126636236082173124727)
              ·
                refine ⟨11398689954354123259687091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7599126636236082173124727 11398689954354123259687091)
                ·
                  refine ⟨17098034931531184889530637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11398689954354123259687091 17098034931531184889530637)
                  ·
                    refine ⟨6411763099324194333573989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17098034931531184889530637 6411763099324194333573989)
                    ·
                      refine ⟨1202205581123286437545123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6411763099324194333573989 1202205581123286437545123)
                      ·
                        rfl

theorem cell23_2341287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_2341287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341287 prefixEnd_2341287 := by exact prefixLift 2341287
  have htrace : WordTrace (prefixWord ++ tailWord_2341287) baseStart_2341287 baseEnd_2341287 := by
    simpa [prefixWord, tailWord_2341287, baseEnd_2341287] using wordTrace_append hprefix tailTrace_2341287
  have hstable : (prefixWord ++ tailWord_2341287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341287).length < 2 ^ (prefixWord ++ tailWord_2341287).sum := by decide
  have hdescent : baseEnd_2341287 < baseStart_2341287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341387 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 1, 6]
def baseStart_2341387 : Nat := 118140960795 + 2341387 * 2 ^ 59
def prefixEnd_2341387 : Nat := 4983230072969 + 3 ^ 40 * 2341387 * 2
def baseEnd_2341387 : Nat := 400752309729578682098221

theorem tailTrace_2341387 : CollatzResearch.WordTrace tailWord_2341387 prefixEnd_2341387 400752309729578682098221 := by
  unfold tailWord_2341387
  simp only [CollatzResearch.WordTrace]
  refine ⟨85397399568562250908870415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56931599712374833939246943 85397399568562250908870415)
  ·
    refine ⟨128096099352843376363305623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85397399568562250908870415 128096099352843376363305623)
    ·
      refine ⟨192144149029265064544958435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128096099352843376363305623 192144149029265064544958435)
      ·
        refine ⟨288216223543897596817437653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192144149029265064544958435 288216223543897596817437653)
        ·
          refine ⟨6755067739310099925408695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 288216223543897596817437653 6755067739310099925408695)
          ·
            refine ⟨10132601608965149888113043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6755067739310099925408695 10132601608965149888113043)
            ·
              refine ⟨15198902413447724832169565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10132601608965149888113043 15198902413447724832169565)
              ·
                refine ⟨5699588405042896812063587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15198902413447724832169565 5699588405042896812063587)
                ·
                  refine ⟨8549382607564345218095381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5699588405042896812063587 8549382607564345218095381)
                  ·
                    refine ⟨400752309729578682098221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8549382607564345218095381 400752309729578682098221)
                    ·
                      rfl

theorem cell23_2341387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 6].length) (baseStart_2341387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341387 prefixEnd_2341387 := by exact prefixLift 2341387
  have htrace : WordTrace (prefixWord ++ tailWord_2341387) baseStart_2341387 baseEnd_2341387 := by
    simpa [prefixWord, tailWord_2341387, baseEnd_2341387] using wordTrace_append hprefix tailTrace_2341387
  have hstable : (prefixWord ++ tailWord_2341387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341387).length < 2 ^ (prefixWord ++ tailWord_2341387).sum := by decide
  have hdescent : baseEnd_2341387 < baseStart_2341387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341408 : List Nat := [2, 1, 1, 6, 2, 2, 2, 1, 1, 5]
def baseStart_2341408 : Nat := 118140960795 + 2341408 * 2 ^ 59
def prefixEnd_2341408 : Nat := 4983230072969 + 3 ^ 40 * 2341408 * 2
def baseEnd_2341408 : Nat := 400755904094160154710689

theorem tailTrace_2341408 : CollatzResearch.WordTrace tailWord_2341408 prefixEnd_2341408 400755904094160154710689 := by
  unfold tailWord_2341408
  simp only [CollatzResearch.WordTrace]
  refine ⟨42699082750743085747692439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56932110334324114330256585 42699082750743085747692439)
  ·
    refine ⟨64048624126114628621538659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42699082750743085747692439 64048624126114628621538659)
    ·
      refine ⟨96072936189171942932307989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64048624126114628621538659 96072936189171942932307989)
      ·
        refine ⟨4503418883867434824951937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 96072936189171942932307989 4503418883867434824951937)
        ·
          refine ⟨3377564162900576118713953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4503418883867434824951937 3377564162900576118713953)
          ·
            refine ⟨2533173122175432089035465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3377564162900576118713953 2533173122175432089035465)
            ·
              refine ⟨1899879841631574066776599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2533173122175432089035465 1899879841631574066776599)
              ·
                refine ⟨2849819762447361100164899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1899879841631574066776599 2849819762447361100164899)
                ·
                  refine ⟨4274729643671041650247349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2849819762447361100164899 4274729643671041650247349)
                  ·
                    refine ⟨400755904094160154710689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4274729643671041650247349 400755904094160154710689)
                    ·
                      rfl

theorem cell23_2341408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 1, 5].length) (baseStart_2341408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341408 prefixEnd_2341408 := by exact prefixLift 2341408
  have htrace : WordTrace (prefixWord ++ tailWord_2341408) baseStart_2341408 baseEnd_2341408 := by
    simpa [prefixWord, tailWord_2341408, baseEnd_2341408] using wordTrace_append hprefix tailTrace_2341408
  have hstable : (prefixWord ++ tailWord_2341408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341408).length < 2 ^ (prefixWord ++ tailWord_2341408).sum := by decide
  have hdescent : baseEnd_2341408 < baseStart_2341408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341411 : List Nat := [1, 1, 1, 4, 4, 1, 4, 1, 1, 1, 4]
def baseStart_2341411 : Nat := 118140960795 + 2341411 * 2 ^ 59
def prefixEnd_2341411 : Nat := 4983230072969 + 3 ^ 40 * 2341411 * 2
def baseEnd_2341411 : Nat := 1202269252724443952394553

theorem tailTrace_2341411 : CollatzResearch.WordTrace tailWord_2341411 prefixEnd_2341411 1202269252724443952394553 := by
  unfold tailWord_2341411
  simp only [CollatzResearch.WordTrace]
  refine ⟨85398274920475303007744087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56932183280316868671829391 85398274920475303007744087)
  ·
    refine ⟨128097412380712954511616131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85398274920475303007744087 128097412380712954511616131)
    ·
      refine ⟨192146118571069431767424197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128097412380712954511616131 192146118571069431767424197)
      ·
        refine ⟨36027397232075518456392037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192146118571069431767424197 36027397232075518456392037)
        ·
          refine ⟨6755136981014159710573507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36027397232075518456392037 6755136981014159710573507)
          ·
            refine ⟨10132705471521239565860261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6755136981014159710573507 10132705471521239565860261)
            ·
              refine ⟨1899882275910232418598799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10132705471521239565860261 1899882275910232418598799)
              ·
                refine ⟨2849823413865348627898199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1899882275910232418598799 2849823413865348627898199)
                ·
                  refine ⟨4274735120798022941847299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2849823413865348627898199 4274735120798022941847299)
                  ·
                    refine ⟨6412102681197034412770949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4274735120798022941847299 6412102681197034412770949)
                    ·
                      refine ⟨1202269252724443952394553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6412102681197034412770949 1202269252724443952394553)
                      ·
                        rfl

theorem cell23_2341411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_2341411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341411 prefixEnd_2341411 := by exact prefixLift 2341411
  have htrace : WordTrace (prefixWord ++ tailWord_2341411) baseStart_2341411 baseEnd_2341411 := by
    simpa [prefixWord, tailWord_2341411, baseEnd_2341411] using wordTrace_append hprefix tailTrace_2341411
  have hstable : (prefixWord ++ tailWord_2341411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341411).length < 2 ^ (prefixWord ++ tailWord_2341411).sum := by decide
  have hdescent : baseEnd_2341411 < baseStart_2341411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341438 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_2341438 : Nat := 118140960795 + 2341438 * 2 ^ 59
def prefixEnd_2341438 : Nat := 4983230072969 + 3 ^ 40 * 2341438 * 2
def baseEnd_2341438 : Nat := 400761038900705115585643

theorem tailTrace_2341438 : CollatzResearch.WordTrace tailWord_2341438 prefixEnd_2341438 400761038900705115585643 := by
  unfold tailWord_2341438
  simp only [CollatzResearch.WordTrace]
  refine ⟨10674907461422185827372121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56932839794251657745984645 10674907461422185827372121)
  ·
    refine ⟨8006180596066639370529091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10674907461422185827372121 8006180596066639370529091)
    ·
      refine ⟨12009270894099959055793637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8006180596066639370529091 12009270894099959055793637)
      ·
        refine ⟨2251738292643742322961307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12009270894099959055793637 2251738292643742322961307)
        ·
          refine ⟨3377607438965613484441961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2251738292643742322961307 3377607438965613484441961)
          ·
            refine ⟨2533205579224210113331471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3377607438965613484441961 2533205579224210113331471)
            ·
              refine ⟨3799808368836315169997207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2533205579224210113331471 3799808368836315169997207)
              ·
                refine ⟨5699712553254472754995811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3799808368836315169997207 5699712553254472754995811)
                ·
                  refine ⟨8549568829881709132493717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5699712553254472754995811 8549568829881709132493717)
                  ·
                    refine ⟨400761038900705115585643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8549568829881709132493717 400761038900705115585643)
                    ·
                      rfl

theorem cell23_2341438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_2341438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341438 prefixEnd_2341438 := by exact prefixLift 2341438
  have htrace : WordTrace (prefixWord ++ tailWord_2341438) baseStart_2341438 baseEnd_2341438 := by
    simpa [prefixWord, tailWord_2341438, baseEnd_2341438] using wordTrace_append hprefix tailTrace_2341438
  have hstable : (prefixWord ++ tailWord_2341438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341438).length < 2 ^ (prefixWord ++ tailWord_2341438).sum := by decide
  have hdescent : baseEnd_2341438 < baseStart_2341438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341441 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_2341441 : Nat := 118140960795 + 2341441 * 2 ^ 59
def prefixEnd_2341441 : Nat := 4983230072969 + 3 ^ 40 * 2341441 * 2
def baseEnd_2341441 : Nat := 1202284657144078835019415

theorem tailTrace_2341441 : CollatzResearch.WordTrace tailWord_2341441 prefixEnd_2341441 1202284657144078835019415 := by
  unfold tailWord_2341441
  simp only [CollatzResearch.WordTrace]
  refine ⟨85399369110366618131336177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56932912740244412087557451 85399369110366618131336177)
  ·
    refine ⟨64049526832774963598502133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85399369110366618131336177 64049526832774963598502133)
    ·
      refine ⟨6004643140572652837359575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64049526832774963598502133 6004643140572652837359575)
      ·
        refine ⟨9006964710858979256039363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6004643140572652837359575 9006964710858979256039363)
        ·
          refine ⟨13510447066288468884059045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9006964710858979256039363 13510447066288468884059045)
          ·
            refine ⟨2533208824929087915761071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13510447066288468884059045 2533208824929087915761071)
            ·
              refine ⟨3799813237393631873641607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2533208824929087915761071 3799813237393631873641607)
              ·
                refine ⟨5699719856090447810462411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3799813237393631873641607 5699719856090447810462411)
                ·
                  refine ⟨8549579784135671715693617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5699719856090447810462411 8549579784135671715693617)
                  ·
                    refine ⟨6412184838101753786770213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8549579784135671715693617 6412184838101753786770213)
                    ·
                      refine ⟨1202284657144078835019415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6412184838101753786770213 1202284657144078835019415)
                      ·
                        rfl

theorem cell23_2341441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_2341441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341441 prefixEnd_2341441 := by exact prefixLift 2341441
  have htrace : WordTrace (prefixWord ++ tailWord_2341441) baseStart_2341441 baseEnd_2341441 := by
    simpa [prefixWord, tailWord_2341441, baseEnd_2341441] using wordTrace_append hprefix tailTrace_2341441
  have hstable : (prefixWord ++ tailWord_2341441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341441).length < 2 ^ (prefixWord ++ tailWord_2341441).sum := by decide
  have hdescent : baseEnd_2341441 < baseStart_2341441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341457 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 2, 2, 5]
def baseStart_2341457 : Nat := 118140960795 + 2341457 * 2 ^ 59
def prefixEnd_2341457 : Nat := 4983230072969 + 3 ^ 40 * 2341457 * 2
def baseEnd_2341457 : Nat := 1202292872834550772419341

theorem tailTrace_2341457 : CollatzResearch.WordTrace tailWord_2341457 prefixEnd_2341457 1202292872834550772419341 := by
  unfold tailWord_2341457
  simp only [CollatzResearch.WordTrace]
  refine ⟨85399952678308652863918625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56933301785539101909279083 85399952678308652863918625)
  ·
    refine ⟨64049964508731489647938969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85399952678308652863918625 64049964508731489647938969)
    ·
      refine ⟨48037473381548617235954227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64049964508731489647938969 48037473381548617235954227)
      ·
        refine ⟨72056210072322925853931341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48037473381548617235954227 72056210072322925853931341)
        ·
          refine ⟨27021078777121097195224253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72056210072322925853931341 27021078777121097195224253)
          ·
            refine ⟨10132904541420411448209095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27021078777121097195224253 10132904541420411448209095)
            ·
              refine ⟨15199356812130617172313643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10132904541420411448209095 15199356812130617172313643)
              ·
                refine ⟨22799035218195925758470465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15199356812130617172313643 22799035218195925758470465)
                ·
                  refine ⟨17099276413646944318852849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22799035218195925758470465 17099276413646944318852849)
                  ·
                    refine ⟨12824457310235208239139637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17099276413646944318852849 12824457310235208239139637)
                    ·
                      refine ⟨1202292872834550772419341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12824457310235208239139637 1202292872834550772419341)
                      ·
                        rfl

theorem cell23_2341457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_2341457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341457 prefixEnd_2341457 := by exact prefixLift 2341457
  have htrace : WordTrace (prefixWord ++ tailWord_2341457) baseStart_2341457 baseEnd_2341457 := by
    simpa [prefixWord, tailWord_2341457, baseEnd_2341457] using wordTrace_append hprefix tailTrace_2341457
  have hstable : (prefixWord ++ tailWord_2341457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341457).length < 2 ^ (prefixWord ++ tailWord_2341457).sum := by decide
  have hdescent : baseEnd_2341457 < baseStart_2341457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341507 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 7]
def baseStart_2341507 : Nat := 118140960795 + 2341507 * 2 ^ 59
def prefixEnd_2341507 : Nat := 4983230072969 + 3 ^ 40 * 2341507 * 2
def baseEnd_2341507 : Nat := 133590949651919508532679

theorem tailTrace_2341507 : CollatzResearch.WordTrace tailWord_2341507 prefixEnd_2341507 133590949651919508532679 := by
  unfold tailWord_2341507
  simp only [CollatzResearch.WordTrace]
  refine ⟨85401776328127511403238775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56934517552085007602159183 85401776328127511403238775)
  ·
    refine ⟨128102664492191267104858163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85401776328127511403238775 128102664492191267104858163)
    ·
      refine ⟨192153996738286900657287245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128102664492191267104858163 192153996738286900657287245)
      ·
        refine ⟨72057748776857587746482717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192153996738286900657287245 72057748776857587746482717)
        ·
          refine ⟨27021655791321595404931019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72057748776857587746482717 27021655791321595404931019)
          ·
            refine ⟨40532483686982393107396529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27021655791321595404931019 40532483686982393107396529)
            ·
              refine ⟨30399362765236794830547397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40532483686982393107396529 30399362765236794830547397)
              ·
                refine ⟨5699880518481899030727637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30399362765236794830547397 5699880518481899030727637)
                ·
                  refine ⟨133590949651919508532679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5699880518481899030727637 133590949651919508532679)
                  ·
                    rfl

theorem cell23_2341507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 7].length) (baseStart_2341507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341507 prefixEnd_2341507 := by exact prefixLift 2341507
  have htrace : WordTrace (prefixWord ++ tailWord_2341507) baseStart_2341507 baseEnd_2341507 := by
    simpa [prefixWord, tailWord_2341507, baseEnd_2341507] using wordTrace_append hprefix tailTrace_2341507
  have hstable : (prefixWord ++ tailWord_2341507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341507).length < 2 ^ (prefixWord ++ tailWord_2341507).sum := by decide
  have hdescent : baseEnd_2341507 < baseStart_2341507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341558 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 7]
def baseStart_2341558 : Nat := 118140960795 + 2341558 * 2 ^ 59
def prefixEnd_2341558 : Nat := 4983230072969 + 3 ^ 40 * 2341558 * 2
def baseEnd_2341558 : Nat := 133593859375628319695153

theorem tailTrace_2341558 : CollatzResearch.WordTrace tailWord_2341558 prefixEnd_2341558 133593859375628319695153 := by
  unfold tailWord_2341558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5337727278183921694584083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56935757633961831408896885 5337727278183921694584083)
  ·
    refine ⟨8006590917275882541876125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5337727278183921694584083 8006590917275882541876125)
    ·
      refine ⟨3002471593978455953203547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8006590917275882541876125 3002471593978455953203547)
      ·
        refine ⟨4503707390967683929805321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3002471593978455953203547 4503707390967683929805321)
        ·
          refine ⟨3377780543225762947353991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4503707390967683929805321 3377780543225762947353991)
          ·
            refine ⟨5066670814838644421030987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3377780543225762947353991 5066670814838644421030987)
            ·
              refine ⟨7600006222257966631546481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5066670814838644421030987 7600006222257966631546481)
              ·
                refine ⟨5700004666693474973659861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7600006222257966631546481 5700004666693474973659861)
                ·
                  refine ⟨133593859375628319695153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5700004666693474973659861 133593859375628319695153)
                  ·
                    rfl

theorem cell23_2341558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_2341558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341558 prefixEnd_2341558 := by exact prefixLift 2341558
  have htrace : WordTrace (prefixWord ++ tailWord_2341558) baseStart_2341558 baseEnd_2341558 := by
    simpa [prefixWord, tailWord_2341558, baseEnd_2341558] using wordTrace_append hprefix tailTrace_2341558
  have hstable : (prefixWord ++ tailWord_2341558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341558).length < 2 ^ (prefixWord ++ tailWord_2341558).sum := by decide
  have hdescent : baseEnd_2341558 < baseStart_2341558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341591 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 2, 4, 2]
def baseStart_2341591 : Nat := 118140960795 + 2341591 * 2 ^ 59
def prefixEnd_2341591 : Nat := 4983230072969 + 3 ^ 40 * 2341591 * 2
def baseEnd_2341591 : Nat := 1202361679242253248143725

theorem tailTrace_2341591 : CollatzResearch.WordTrace tailWord_2341591 prefixEnd_2341591 1202361679242253248143725 := by
  unfold tailWord_2341591
  simp only [CollatzResearch.WordTrace]
  refine ⟨85404840059823193749296627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56936560039882129166197751 85404840059823193749296627)
  ·
    refine ⟨128107260089734790623944941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85404840059823193749296627 128107260089734790623944941)
    ·
      refine ⟨48040222533650546483979353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128107260089734790623944941 48040222533650546483979353)
      ·
        refine ⟨36030166900237909862984515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48040222533650546483979353 36030166900237909862984515)
        ·
          refine ⟨54045250350356864794476773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36030166900237909862984515 54045250350356864794476773)
          ·
            refine ⟨10133484440691912148964395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54045250350356864794476773 10133484440691912148964395)
            ·
              refine ⟨15200226661037868223446593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10133484440691912148964395 15200226661037868223446593)
              ·
                refine ⟨11400169995778401167584945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15200226661037868223446593 11400169995778401167584945)
                ·
                  refine ⟨8550127496833800875688709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11400169995778401167584945 8550127496833800875688709)
                  ·
                    refine ⟨1603148905656337664191633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8550127496833800875688709 1603148905656337664191633)
                    ·
                      refine ⟨1202361679242253248143725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1603148905656337664191633 1202361679242253248143725)
                      ·
                        rfl

theorem cell23_2341591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_2341591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341591 prefixEnd_2341591 := by exact prefixLift 2341591
  have htrace : WordTrace (prefixWord ++ tailWord_2341591) baseStart_2341591 baseEnd_2341591 := by
    simpa [prefixWord, tailWord_2341591, baseEnd_2341591] using wordTrace_append hprefix tailTrace_2341591
  have hstable : (prefixWord ++ tailWord_2341591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341591).length < 2 ^ (prefixWord ++ tailWord_2341591).sum := by decide
  have hdescent : baseEnd_2341591 < baseStart_2341591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341601 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 3, 4]
def baseStart_2341601 : Nat := 118140960795 + 2341601 * 2 ^ 59
def prefixEnd_2341601 : Nat := 4983230072969 + 3 ^ 40 * 2341601 * 2
def baseEnd_2341601 : Nat := 400788938016266069672893

theorem tailTrace_2341601 : CollatzResearch.WordTrace tailWord_2341601 prefixEnd_2341601 400788938016266069672893 := by
  unfold tailWord_2341601
  simp only [CollatzResearch.WordTrace]
  refine ⟨85405204789786965457160657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56936803193191310304773771 85405204789786965457160657)
  ·
    refine ⟨64053903592340224092870493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85405204789786965457160657 64053903592340224092870493)
    ·
      refine ⟨24020213847127584034826435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64053903592340224092870493 24020213847127584034826435)
      ·
        refine ⟨36030320770691376052239653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24020213847127584034826435 36030320770691376052239653)
        ·
          refine ⟨6755685144504633009794935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36030320770691376052239653 6755685144504633009794935)
          ·
            refine ⟨10133527716756949514692403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6755685144504633009794935 10133527716756949514692403)
            ·
              refine ⟨15200291575135424272038605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10133527716756949514692403 15200291575135424272038605)
              ·
                refine ⟨5700109340675784102014477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15200291575135424272038605 5700109340675784102014477)
                ·
                  refine ⟨2137541002753419038255429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5700109340675784102014477 2137541002753419038255429)
                  ·
                    refine ⟨400788938016266069672893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2137541002753419038255429 400788938016266069672893)
                    ·
                      rfl

theorem cell23_2341601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_2341601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341601 prefixEnd_2341601 := by exact prefixLift 2341601
  have htrace : WordTrace (prefixWord ++ tailWord_2341601) baseStart_2341601 baseEnd_2341601 := by
    simpa [prefixWord, tailWord_2341601, baseEnd_2341601] using wordTrace_append hprefix tailTrace_2341601
  have hstable : (prefixWord ++ tailWord_2341601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341601).length < 2 ^ (prefixWord ++ tailWord_2341601).sum := by decide
  have hdescent : baseEnd_2341601 < baseStart_2341601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341624 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 2, 5, 3]
def baseStart_2341624 : Nat := 118140960795 + 2341624 * 2 ^ 59
def prefixEnd_2341624 : Nat := 4983230072969 + 3 ^ 40 * 2341624 * 2
def baseEnd_2341624 : Nat := 1202378624103851619031073

theorem tailTrace_2341624 : CollatzResearch.WordTrace tailWord_2341624 prefixEnd_2341624 1202378624103851619031073 := by
  unfold tailWord_2341624
  simp only [CollatzResearch.WordTrace]
  refine ⟨42703021834351820192623963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56937362445802426923498617 42703021834351820192623963)
  ·
    refine ⟨64054532751527730288935945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42703021834351820192623963 64054532751527730288935945)
    ·
      refine ⟨48040899563645797716701959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64054532751527730288935945 48040899563645797716701959)
      ·
        refine ⟨72061349345468696575052939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48040899563645797716701959 72061349345468696575052939)
        ·
          refine ⟨108092024018203044862579409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72061349345468696575052939 108092024018203044862579409)
          ·
            refine ⟨81069018013652283646934557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108092024018203044862579409 81069018013652283646934557)
            ·
              refine ⟨30400881755119606367600459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81069018013652283646934557 30400881755119606367600459)
              ·
                refine ⟨45601322632679409551400689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30400881755119606367600459 45601322632679409551400689)
                ·
                  refine ⟨34200991974509557163550517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45601322632679409551400689 34200991974509557163550517)
                  ·
                    refine ⟨3206342997610270984082861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34200991974509557163550517 3206342997610270984082861)
                    ·
                      refine ⟨1202378624103851619031073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3206342997610270984082861 1202378624103851619031073)
                      ·
                        rfl

theorem cell23_2341624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_2341624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341624 prefixEnd_2341624 := by exact prefixLift 2341624
  have htrace : WordTrace (prefixWord ++ tailWord_2341624) baseStart_2341624 baseEnd_2341624 := by
    simpa [prefixWord, tailWord_2341624, baseEnd_2341624] using wordTrace_append hprefix tailTrace_2341624
  have hstable : (prefixWord ++ tailWord_2341624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341624).length < 2 ^ (prefixWord ++ tailWord_2341624).sum := by decide
  have hdescent : baseEnd_2341624 < baseStart_2341624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341641 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 5, 1, 3]
def baseStart_2341641 : Nat := 118140960795 + 2341641 * 2 ^ 59
def prefixEnd_2341641 : Nat := 4983230072969 + 3 ^ 40 * 2341641 * 2
def baseEnd_2341641 : Nat := 1202387353274978052518495

theorem tailTrace_2341641 : CollatzResearch.WordTrace tailWord_2341641 prefixEnd_2341641 1202387353274978052518495 := by
  unfold tailWord_2341641
  simp only [CollatzResearch.WordTrace]
  refine ⟨85406663709642052288616777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56937775806428034859077851 85406663709642052288616777)
  ·
    refine ⟨64054997782231539216462583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85406663709642052288616777 64054997782231539216462583)
    ·
      refine ⟨96082496673347308824693875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64054997782231539216462583 96082496673347308824693875)
      ·
        refine ⟨144123745010020963237040813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96082496673347308824693875 144123745010020963237040813)
        ·
          refine ⟨54046404378757861213890305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144123745010020963237040813 54046404378757861213890305)
          ·
            refine ⟨40534803284068395910417729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54046404378757861213890305 40534803284068395910417729)
            ·
              refine ⟨30401102463051296932813297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40534803284068395910417729 30401102463051296932813297)
              ·
                refine ⟨22800826847288472699609973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30401102463051296932813297 22800826847288472699609973)
                ·
                  refine ⟨2137577516933294315588435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22800826847288472699609973 2137577516933294315588435)
                  ·
                    refine ⟨3206366275399941473382653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2137577516933294315588435 3206366275399941473382653)
                    ·
                      refine ⟨1202387353274978052518495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3206366275399941473382653 1202387353274978052518495)
                      ·
                        rfl

theorem cell23_2341641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 1, 3].length) (baseStart_2341641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341641 prefixEnd_2341641 := by exact prefixLift 2341641
  have htrace : WordTrace (prefixWord ++ tailWord_2341641) baseStart_2341641 baseEnd_2341641 := by
    simpa [prefixWord, tailWord_2341641, baseEnd_2341641] using wordTrace_append hprefix tailTrace_2341641
  have hstable : (prefixWord ++ tailWord_2341641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341641).length < 2 ^ (prefixWord ++ tailWord_2341641).sum := by decide
  have hdescent : baseEnd_2341641 < baseStart_2341641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341644 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 5, 5]
def baseStart_2341644 : Nat := 118140960795 + 2341644 * 2 ^ 59
def prefixEnd_2341644 : Nat := 4983230072969 + 3 ^ 40 * 2341644 * 2
def baseEnd_2341644 : Nat := 400796297905647180260327

theorem tailTrace_2341644 : CollatzResearch.WordTrace tailWord_2341644 prefixEnd_2341644 400796297905647180260327 := by
  unfold tailWord_2341644
  simp only [CollatzResearch.WordTrace]
  refine ⟨42703386564315591900487993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56937848752420789200650657 42703386564315591900487993)
  ·
    refine ⟨32027539923236693925365995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42703386564315591900487993 32027539923236693925365995)
    ·
      refine ⟨48041309884855040888048993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32027539923236693925365995 48041309884855040888048993)
      ·
        refine ⟨36030982413641280666036745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48041309884855040888048993 36030982413641280666036745)
        ·
          refine ⟨27023236810230960499527559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36030982413641280666036745 27023236810230960499527559)
          ·
            refine ⟨40534855215346440749291339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27023236810230960499527559 40534855215346440749291339)
            ·
              refine ⟨60802282823019661123937009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40534855215346440749291339 60802282823019661123937009)
              ·
                refine ⟨45601712117264745842952757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60802282823019661123937009 45601712117264745842952757)
                ·
                  refine ⟨4275160510993569922776821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45601712117264745842952757 4275160510993569922776821)
                  ·
                    refine ⟨400796297905647180260327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4275160510993569922776821 400796297905647180260327)
                    ·
                      rfl

theorem cell23_2341644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_2341644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341644 prefixEnd_2341644 := by exact prefixLift 2341644
  have htrace : WordTrace (prefixWord ++ tailWord_2341644) baseStart_2341644 baseEnd_2341644 := by
    simpa [prefixWord, tailWord_2341644, baseEnd_2341644] using wordTrace_append hprefix tailTrace_2341644
  have hstable : (prefixWord ++ tailWord_2341644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341644).length < 2 ^ (prefixWord ++ tailWord_2341644).sum := by decide
  have hdescent : baseEnd_2341644 < baseStart_2341644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341678 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 3, 5]
def baseStart_2341678 : Nat := 118140960795 + 2341678 * 2 ^ 59
def prefixEnd_2341678 : Nat := 4983230072969 + 3 ^ 40 * 2341678 * 2
def baseEnd_2341678 : Nat := 400802117353064802585275

theorem tailTrace_2341678 : CollatzResearch.WordTrace tailWord_2341678 prefixEnd_2341678 400802117353064802585275 := by
  unfold tailWord_2341678
  simp only [CollatzResearch.WordTrace]
  refine ⟨10676001651313500950964211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56938675473672005071809125 10676001651313500950964211)
  ·
    refine ⟨16014002476970251426446317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10676001651313500950964211 16014002476970251426446317)
    ·
      refine ⟨6005250928863844284917369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16014002476970251426446317 6005250928863844284917369)
      ·
        refine ⟨4503938196647883213688027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6005250928863844284917369 4503938196647883213688027)
        ·
          refine ⟨6755907294971824820532041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4503938196647883213688027 6755907294971824820532041)
          ·
            refine ⟨5066930471228868615399031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6755907294971824820532041 5066930471228868615399031)
            ·
              refine ⟨7600395706843302923098547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5066930471228868615399031 7600395706843302923098547)
              ·
                refine ⟨11400593560264954384647821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7600395706843302923098547 11400593560264954384647821)
                ·
                  refine ⟨4275222585099357894242933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11400593560264954384647821 4275222585099357894242933)
                  ·
                    refine ⟨400802117353064802585275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4275222585099357894242933 400802117353064802585275)
                    ·
                      rfl

theorem cell23_2341678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_2341678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341678 prefixEnd_2341678 := by exact prefixLift 2341678
  have htrace : WordTrace (prefixWord ++ tailWord_2341678) baseStart_2341678 baseEnd_2341678 := by
    simpa [prefixWord, tailWord_2341678, baseEnd_2341678] using wordTrace_append hprefix tailTrace_2341678
  have hstable : (prefixWord ++ tailWord_2341678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341678).length < 2 ^ (prefixWord ++ tailWord_2341678).sum := by decide
  have hdescent : baseEnd_2341678 < baseStart_2341678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341681 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 3, 1, 4]
def baseStart_2341681 : Nat := 118140960795 + 2341681 * 2 ^ 59
def prefixEnd_2341681 : Nat := 4983230072969 + 3 ^ 40 * 2341681 * 2
def baseEnd_2341681 : Nat := 1202407892501157896018311

theorem tailTrace_2341681 : CollatzResearch.WordTrace tailWord_2341681 prefixEnd_2341681 1202407892501157896018311 := by
  unfold tailWord_2341681
  simp only [CollatzResearch.WordTrace]
  refine ⟨85408122629497139120072897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56938748419664759413381931 85408122629497139120072897)
  ·
    refine ⟨64056091972122854340054673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85408122629497139120072897 64056091972122854340054673)
    ·
      refine ⟨48042068979092140755041005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64056091972122854340054673 48042068979092140755041005)
      ·
        refine ⟨18015775867159552783140377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48042068979092140755041005 18015775867159552783140377)
        ·
          refine ⟨13511831900369664587355283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18015775867159552783140377 13511831900369664587355283)
          ·
            refine ⟨20267747850554496881032925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13511831900369664587355283 20267747850554496881032925)
            ·
              refine ⟨7600405443957936330387347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20267747850554496881032925 7600405443957936330387347)
              ·
                refine ⟨11400608165936904495581021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7600405443957936330387347 11400608165936904495581021)
                ·
                  refine ⟨4275228062226339185842883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11400608165936904495581021 4275228062226339185842883)
                  ·
                    refine ⟨6412842093339508778764325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4275228062226339185842883 6412842093339508778764325)
                    ·
                      refine ⟨1202407892501157896018311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6412842093339508778764325 1202407892501157896018311)
                      ·
                        rfl

theorem cell23_2341681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_2341681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341681 prefixEnd_2341681 := by exact prefixLift 2341681
  have htrace : WordTrace (prefixWord ++ tailWord_2341681) baseStart_2341681 baseEnd_2341681 := by
    simpa [prefixWord, tailWord_2341681, baseEnd_2341681] using wordTrace_append hprefix tailTrace_2341681
  have hstable : (prefixWord ++ tailWord_2341681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341681).length < 2 ^ (prefixWord ++ tailWord_2341681).sum := by decide
  have hdescent : baseEnd_2341681 < baseStart_2341681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341685 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 2, 3, 2]
def baseStart_2341685 : Nat := 118140960795 + 2341685 * 2 ^ 59
def prefixEnd_2341685 : Nat := 4983230072969 + 3 ^ 40 * 2341685 * 2
def baseEnd_2341685 : Nat := 1202409946423775880368293

theorem tailTrace_2341685 : CollatzResearch.WordTrace tailWord_2341685 prefixEnd_2341685 1202409946423775880368293 := by
  unfold tailWord_2341685
  simp only [CollatzResearch.WordTrace]
  refine ⟨85408268521482647803218509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56938845680988431868812339 85408268521482647803218509)
  ·
    refine ⟨32028100695555992926206941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85408268521482647803218509 32028100695555992926206941)
    ·
      refine ⟨12010537760833497347327603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32028100695555992926206941 12010537760833497347327603)
      ·
        refine ⟨18015806641250246020991405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12010537760833497347327603 18015806641250246020991405)
        ·
          refine ⟨6755927490468842257871777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18015806641250246020991405 6755927490468842257871777)
          ·
            refine ⟨5066945617851631693403833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6755927490468842257871777 5066945617851631693403833)
            ·
              refine ⟨3800209213388723770052875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5066945617851631693403833 3800209213388723770052875)
              ·
                refine ⟨5700313820083085655079313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3800209213388723770052875 5700313820083085655079313)
                ·
                  refine ⟨4275235365062314241309485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5700313820083085655079313 4275235365062314241309485)
                  ·
                    refine ⟨1603213261898367840491057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4275235365062314241309485 1603213261898367840491057)
                    ·
                      refine ⟨1202409946423775880368293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1603213261898367840491057 1202409946423775880368293)
                      ·
                        rfl

theorem cell23_2341685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_2341685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341685 prefixEnd_2341685 := by exact prefixLift 2341685
  have htrace : WordTrace (prefixWord ++ tailWord_2341685) baseStart_2341685 baseEnd_2341685 := by
    simpa [prefixWord, tailWord_2341685, baseEnd_2341685] using wordTrace_append hprefix tailTrace_2341685
  have hstable : (prefixWord ++ tailWord_2341685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341685).length < 2 ^ (prefixWord ++ tailWord_2341685).sum := by decide
  have hdescent : baseEnd_2341685 < baseStart_2341685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341708 : List Nat := [2, 2, 1, 3, 3, 1, 1, 4, 2, 4]
def baseStart_2341708 : Nat := 118140960795 + 2341708 * 2 ^ 59
def prefixEnd_2341708 : Nat := 4983230072969 + 3 ^ 40 * 2341708 * 2
def baseEnd_2341708 : Nat := 400807252159609763460229

theorem tailTrace_2341708 : CollatzResearch.WordTrace tailWord_2341708 prefixEnd_2341708 400807252159609763460229 := by
  unfold tailWord_2341708
  simp only [CollatzResearch.WordTrace]
  refine ⟨42704553700199661365652889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56939404933599548487537185 42704553700199661365652889)
  ·
    refine ⟨32028415275149746024239667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42704553700199661365652889 32028415275149746024239667)
    ·
      refine ⟨48042622912724619036359501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32028415275149746024239667 48042622912724619036359501)
      ·
        refine ⟨18015983592271732138634813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48042622912724619036359501 18015983592271732138634813)
        ·
          refine ⟨6755993847101899551988055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18015983592271732138634813 6755993847101899551988055)
          ·
            refine ⟨10133990770652849327982083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6755993847101899551988055 10133990770652849327982083)
            ·
              refine ⟨15200986155979273991973125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10133990770652849327982083 15200986155979273991973125)
              ·
                refine ⟨2850184904246113873494961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15200986155979273991973125 2850184904246113873494961)
                ·
                  refine ⟨2137638678184585405121221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2850184904246113873494961 2137638678184585405121221)
                  ·
                    refine ⟨400807252159609763460229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2137638678184585405121221 400807252159609763460229)
                    ·
                      rfl

theorem cell23_2341708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_2341708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341708 prefixEnd_2341708 := by exact prefixLift 2341708
  have htrace : WordTrace (prefixWord ++ tailWord_2341708) baseStart_2341708 baseEnd_2341708 := by
    simpa [prefixWord, tailWord_2341708, baseEnd_2341708] using wordTrace_append hprefix tailTrace_2341708
  have hstable : (prefixWord ++ tailWord_2341708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341708).length < 2 ^ (prefixWord ++ tailWord_2341708).sum := by decide
  have hdescent : baseEnd_2341708 < baseStart_2341708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341709 : List Nat := [1, 6, 1, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_2341709 : Nat := 118140960795 + 2341709 * 2 ^ 59
def prefixEnd_2341709 : Nat := 4983230072969 + 3 ^ 40 * 2341709 * 2
def baseEnd_2341709 : Nat := 1202422269959483786468183

theorem tailTrace_2341709 : CollatzResearch.WordTrace tailWord_2341709 prefixEnd_2341709 1202422269959483786468183 := by
  unfold tailWord_2341709
  simp only [CollatzResearch.WordTrace]
  refine ⟨85409143873395699902092181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56939429248930466601394787 85409143873395699902092181)
  ·
    refine ⟨4003553619065423432910571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85409143873395699902092181 4003553619065423432910571)
    ·
      refine ⟨6005330428598135149365857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4003553619065423432910571 6005330428598135149365857)
      ·
        refine ⟨4503997821448601362024393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6005330428598135149365857 4503997821448601362024393)
        ·
          refine ⟨3377998366086451021518295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4503997821448601362024393 3377998366086451021518295)
          ·
            refine ⟨5066997549129676532277443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3377998366086451021518295 5066997549129676532277443)
            ·
              refine ⟨7600496323694514798416165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5066997549129676532277443 7600496323694514798416165)
              ·
                refine ⟨1425093060692721524703031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7600496323694514798416165 1425093060692721524703031)
                ·
                  refine ⟨2137639591039082287054547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1425093060692721524703031 2137639591039082287054547)
                  ·
                    refine ⟨3206459386558623430581821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2137639591039082287054547 3206459386558623430581821)
                    ·
                      refine ⟨1202422269959483786468183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3206459386558623430581821 1202422269959483786468183)
                      ·
                        rfl

theorem cell23_2341709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_2341709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341709 prefixEnd_2341709 := by exact prefixLift 2341709
  have htrace : WordTrace (prefixWord ++ tailWord_2341709) baseStart_2341709 baseEnd_2341709 := by
    simpa [prefixWord, tailWord_2341709, baseEnd_2341709] using wordTrace_append hprefix tailTrace_2341709
  have hstable : (prefixWord ++ tailWord_2341709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341709).length < 2 ^ (prefixWord ++ tailWord_2341709).sum := by decide
  have hdescent : baseEnd_2341709 < baseStart_2341709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341721 : List Nat := [1, 2, 1, 2, 2, 6, 1, 8]
def baseStart_2341721 : Nat := 118140960795 + 2341721 * 2 ^ 59
def prefixEnd_2341721 : Nat := 4983230072969 + 3 ^ 40 * 2341721 * 2
def baseEnd_2341721 : Nat := 44534386360271768130301

theorem tailTrace_2341721 : CollatzResearch.WordTrace tailWord_2341721 prefixEnd_2341721 44534386360271768130301 := by
  unfold tailWord_2341721
  simp only [CollatzResearch.WordTrace]
  refine ⟨85409581549352225951529017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56939721032901483967686011 85409581549352225951529017)
  ·
    refine ⟨64057186162014169463646763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85409581549352225951529017 64057186162014169463646763)
    ·
      refine ⟨96085779243021254195470145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64057186162014169463646763 96085779243021254195470145)
      ·
        refine ⟨72064334432265940646602609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96085779243021254195470145 72064334432265940646602609)
        ·
          refine ⟨54048250824199455484951957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72064334432265940646602609 54048250824199455484951957)
          ·
            refine ⟨2533511757384349475857123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54048250824199455484951957 2533511757384349475857123)
            ·
              refine ⟨3800267636076524213785685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2533511757384349475857123 3800267636076524213785685)
              ·
                refine ⟨44534386360271768130301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3800267636076524213785685 44534386360271768130301)
                ·
                  rfl

theorem cell23_2341721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 8].length) (baseStart_2341721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341721 prefixEnd_2341721 := by exact prefixLift 2341721
  have htrace : WordTrace (prefixWord ++ tailWord_2341721) baseStart_2341721 baseEnd_2341721 := by
    simpa [prefixWord, tailWord_2341721, baseEnd_2341721] using wordTrace_append hprefix tailTrace_2341721
  have hstable : (prefixWord ++ tailWord_2341721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341721).length < 2 ^ (prefixWord ++ tailWord_2341721).sum := by decide
  have hdescent : baseEnd_2341721 < baseStart_2341721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341749 : List Nat := [1, 3, 4, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_2341749 : Nat := 118140960795 + 2341749 * 2 ^ 59
def prefixEnd_2341749 : Nat := 4983230072969 + 3 ^ 40 * 2341749 * 2
def baseEnd_2341749 : Nat := 1202442809185663629967999

theorem tailTrace_2341749 : CollatzResearch.WordTrace tailWord_2341749 prefixEnd_2341749 1202442809185663629967999 := by
  unfold tailWord_2341749
  simp only [CollatzResearch.WordTrace]
  refine ⟨85410602793250786733548301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56940401862167191155698867 85410602793250786733548301)
  ·
    refine ⟨32028976047469045025080613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85410602793250786733548301 32028976047469045025080613)
    ·
      refine ⟨6005433008900445942202615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32028976047469045025080613 6005433008900445942202615)
      ·
        refine ⟨9008149513350668913303923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6005433008900445942202615 9008149513350668913303923)
        ·
          refine ⟨13512224270026003369955885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9008149513350668913303923 13512224270026003369955885)
          ·
            refine ⟨5067084101259751263733457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13512224270026003369955885 5067084101259751263733457)
            ·
              refine ⟨3800313075944813447800093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5067084101259751263733457 3800313075944813447800093)
              ·
                refine ⟨1425117403479305042925035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3800313075944813447800093 1425117403479305042925035)
                ·
                  refine ⟨2137676105218957564387553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1425117403479305042925035 2137676105218957564387553)
                  ·
                    refine ⟨1603257078914218173290665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2137676105218957564387553 1603257078914218173290665)
                    ·
                      refine ⟨1202442809185663629967999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1603257078914218173290665 1202442809185663629967999)
                      ·
                        rfl

theorem cell23_2341749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_2341749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341749 prefixEnd_2341749 := by exact prefixLift 2341749
  have htrace : WordTrace (prefixWord ++ tailWord_2341749) baseStart_2341749 baseEnd_2341749 := by
    simpa [prefixWord, tailWord_2341749, baseEnd_2341749] using wordTrace_append hprefix tailTrace_2341749
  have hstable : (prefixWord ++ tailWord_2341749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341749).length < 2 ^ (prefixWord ++ tailWord_2341749).sum := by decide
  have hdescent : baseEnd_2341749 < baseStart_2341749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341765 : List Nat := [1, 3, 1, 1, 3, 3, 3, 2, 2, 1, 3]
def baseStart_2341765 : Nat := 118140960795 + 2341765 * 2 ^ 59
def prefixEnd_2341765 : Nat := 4983230072969 + 3 ^ 40 * 2341765 * 2
def baseEnd_2341765 : Nat := 1202451024876135567367925

theorem tailTrace_2341765 : CollatzResearch.WordTrace tailWord_2341765 prefixEnd_2341765 1202451024876135567367925 := by
  unfold tailWord_2341765
  simp only [CollatzResearch.WordTrace]
  refine ⟨85411186361192821466130749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56940790907461880977420499 85411186361192821466130749)
  ·
    refine ⟨32029194885447308049799031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85411186361192821466130749 32029194885447308049799031)
    ·
      refine ⟨48043792328170962074698547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32029194885447308049799031 48043792328170962074698547)
      ·
        refine ⟨72065688492256443112047821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48043792328170962074698547 72065688492256443112047821)
        ·
          refine ⟨27024633184596166167017933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72065688492256443112047821 27024633184596166167017933)
          ·
            refine ⟨10134237444223562312631725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27024633184596166167017933 10134237444223562312631725)
            ·
              refine ⟨3800339041583835867236897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10134237444223562312631725 3800339041583835867236897)
              ·
                refine ⟨2850254281187876900427673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3800339041583835867236897 2850254281187876900427673)
                ·
                  refine ⟨2137690710890907675320755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2850254281187876900427673 2137690710890907675320755)
                  ·
                    refine ⟨3206536066336361512981133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2137690710890907675320755 3206536066336361512981133)
                    ·
                      refine ⟨1202451024876135567367925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3206536066336361512981133 1202451024876135567367925)
                      ·
                        rfl

theorem cell23_2341765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 1, 3].length) (baseStart_2341765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341765 prefixEnd_2341765 := by exact prefixLift 2341765
  have htrace : WordTrace (prefixWord ++ tailWord_2341765) baseStart_2341765 baseEnd_2341765 := by
    simpa [prefixWord, tailWord_2341765, baseEnd_2341765] using wordTrace_append hprefix tailTrace_2341765
  have hstable : (prefixWord ++ tailWord_2341765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341765).length < 2 ^ (prefixWord ++ tailWord_2341765).sum := by decide
  have hdescent : baseEnd_2341765 < baseStart_2341765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341781 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 2, 6]
def baseStart_2341781 : Nat := 118140960795 + 2341781 * 2 ^ 59
def prefixEnd_2341781 : Nat := 4983230072969 + 3 ^ 40 * 2341781 * 2
def baseEnd_2341781 : Nat := 400819746855535834922617

theorem tailTrace_2341781 : CollatzResearch.WordTrace tailWord_2341781 prefixEnd_2341781 400819746855535834922617 := by
  unfold tailWord_2341781
  simp only [CollatzResearch.WordTrace]
  refine ⟨85411769929134856198713197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56941179952756570799142131 85411769929134856198713197)
  ·
    refine ⟨32029413723425571074517449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85411769929134856198713197 32029413723425571074517449)
    ·
      refine ⟨24022060292569178305888087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32029413723425571074517449 24022060292569178305888087)
      ·
        refine ⟨36033090438853767458832131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24022060292569178305888087 36033090438853767458832131)
        ·
          refine ⟨54049635658280651188248197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36033090438853767458832131 54049635658280651188248197)
          ·
            refine ⟨10134306685927622097796537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54049635658280651188248197 10134306685927622097796537)
            ·
              refine ⟨7600730014445716573347403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10134306685927622097796537 7600730014445716573347403)
              ·
                refine ⟨11401095021668574860021105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7600730014445716573347403 11401095021668574860021105)
                ·
                  refine ⟨8550821266251431145015829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11401095021668574860021105 8550821266251431145015829)
                  ·
                    refine ⟨400819746855535834922617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8550821266251431145015829 400819746855535834922617)
                    ·
                      rfl

theorem cell23_2341781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_2341781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341781 prefixEnd_2341781 := by exact prefixLift 2341781
  have htrace : WordTrace (prefixWord ++ tailWord_2341781) baseStart_2341781 baseEnd_2341781 := by
    simpa [prefixWord, tailWord_2341781, baseEnd_2341781] using wordTrace_append hprefix tailTrace_2341781
  have hstable : (prefixWord ++ tailWord_2341781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341781).length < 2 ^ (prefixWord ++ tailWord_2341781).sum := by decide
  have hdescent : baseEnd_2341781 < baseStart_2341781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341822 : List Nat := [4, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2]
def baseStart_2341822 : Nat := 118140960795 + 2341822 * 2 ^ 59
def prefixEnd_2341822 : Nat := 4983230072969 + 3 ^ 40 * 2341822 * 2
def baseEnd_2341822 : Nat := 1202480293273441844355163

theorem tailTrace_2341822 : CollatzResearch.WordTrace tailWord_2341822 prefixEnd_2341822 1202480293273441844355163 := by
  unfold tailWord_2341822
  simp only [CollatzResearch.WordTrace]
  refine ⟨10676658165248290025119465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56942176881324213467303813 10676658165248290025119465)
  ·
    refine ⟨8007493623936217518839599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10676658165248290025119465 8007493623936217518839599)
    ·
      refine ⟨12011240435904326278259399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8007493623936217518839599 12011240435904326278259399)
      ·
        refine ⟨18016860653856489417389099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12011240435904326278259399 18016860653856489417389099)
        ·
          refine ⟨27025290980784734126083649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18016860653856489417389099 27025290980784734126083649)
          ·
            refine ⟨20268968235588550594562737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27025290980784734126083649 20268968235588550594562737)
            ·
              refine ⟨15201726176691412945922053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20268968235588550594562737 15201726176691412945922053)
              ·
                refine ⟨2850323658129639927360385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15201726176691412945922053 2850323658129639927360385)
                ·
                  refine ⟨2137742743597229945520289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2850323658129639927360385 2137742743597229945520289)
                  ·
                    refine ⟨1603307057697922459140217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2137742743597229945520289 1603307057697922459140217)
                    ·
                      refine ⟨1202480293273441844355163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1603307057697922459140217 1202480293273441844355163)
                      ·
                        rfl

theorem cell23_2341822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_2341822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341822 prefixEnd_2341822 := by exact prefixLift 2341822
  have htrace : WordTrace (prefixWord ++ tailWord_2341822) baseStart_2341822 baseEnd_2341822 := by
    simpa [prefixWord, tailWord_2341822, baseEnd_2341822] using wordTrace_append hprefix tailTrace_2341822
  have hstable : (prefixWord ++ tailWord_2341822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341822).length < 2 ^ (prefixWord ++ tailWord_2341822).sum := by decide
  have hdescent : baseEnd_2341822 < baseStart_2341822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341839 : List Nat := [1, 1, 2, 1, 1, 8, 2, 1, 2, 2, 2]
def baseStart_2341839 : Nat := 118140960795 + 2341839 * 2 ^ 59
def prefixEnd_2341839 : Nat := 4983230072969 + 3 ^ 40 * 2341839 * 2
def baseEnd_2341839 : Nat := 1202489022444568277842585

theorem tailTrace_2341839 : CollatzResearch.WordTrace tailWord_2341839 prefixEnd_2341839 1202489022444568277842585 := by
  unfold tailWord_2341839
  simp only [CollatzResearch.WordTrace]
  refine ⟨85413885362924732104324571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56942590241949821402883047 85413885362924732104324571)
  ·
    refine ⟨128120828044387098156486857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85413885362924732104324571 128120828044387098156486857)
    ·
      refine ⟨96090621033290323617365143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128120828044387098156486857 96090621033290323617365143)
      ·
        refine ⟨144135931549935485426047715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96090621033290323617365143 144135931549935485426047715)
        ·
          refine ⟨216203897324903228139071573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144135931549935485426047715 216203897324903228139071573)
          ·
            refine ⟨2533639421776209704754745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 216203897324903228139071573 2533639421776209704754745)
            ·
              refine ⟨1900229566332157278566059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2533639421776209704754745 1900229566332157278566059)
              ·
                refine ⟨2850344349498235917849089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1900229566332157278566059 2850344349498235917849089)
                ·
                  refine ⟨2137758262123676938386817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2850344349498235917849089 2137758262123676938386817)
                  ·
                    refine ⟨1603318696592757703790113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2137758262123676938386817 1603318696592757703790113)
                    ·
                      refine ⟨1202489022444568277842585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1603318696592757703790113 1202489022444568277842585)
                      ·
                        rfl

theorem cell23_2341839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 2, 2, 2].length) (baseStart_2341839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341839 prefixEnd_2341839 := by exact prefixLift 2341839
  have htrace : WordTrace (prefixWord ++ tailWord_2341839) baseStart_2341839 baseEnd_2341839 := by
    simpa [prefixWord, tailWord_2341839, baseEnd_2341839] using wordTrace_append hprefix tailTrace_2341839
  have hstable : (prefixWord ++ tailWord_2341839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341839).length < 2 ^ (prefixWord ++ tailWord_2341839).sum := by decide
  have hdescent : baseEnd_2341839 < baseStart_2341839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341841 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 4, 5]
def baseStart_2341841 : Nat := 118140960795 + 2341841 * 2 ^ 59
def prefixEnd_2341841 : Nat := 4983230072969 + 3 ^ 40 * 2341841 * 2
def baseEnd_2341841 : Nat := 400830016468625756672525

theorem tailTrace_2341841 : CollatzResearch.WordTrace tailWord_2341841 prefixEnd_2341841 400830016468625756672525 := by
  unfold tailWord_2341841
  simp only [CollatzResearch.WordTrace]
  refine ⟨85413958308917486445897377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56942638872611657630598251 85413958308917486445897377)
  ·
    refine ⟨64060468731688114834423033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85413958308917486445897377 64060468731688114834423033)
    ·
      refine ⟨48045351548766086125817275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64060468731688114834423033 48045351548766086125817275)
      ·
        refine ⟨72068027323149129188725913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48045351548766086125817275 72068027323149129188725913)
        ·
          refine ⟨54051020492361846891544435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72068027323149129188725913 54051020492361846891544435)
          ·
            refine ⟨81076530738542770337316653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54051020492361846891544435 81076530738542770337316653)
            ·
              refine ⟨30403699026953538876493745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81076530738542770337316653 30403699026953538876493745)
              ·
                refine ⟨22802774270215154157370309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30403699026953538876493745 22802774270215154157370309)
                ·
                  refine ⟨4275520175665341404506933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22802774270215154157370309 4275520175665341404506933)
                  ·
                    refine ⟨400830016468625756672525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4275520175665341404506933 400830016468625756672525)
                    ·
                      rfl

theorem cell23_2341841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_2341841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2341841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2341841 prefixEnd_2341841 := by exact prefixLift 2341841
  have htrace : WordTrace (prefixWord ++ tailWord_2341841) baseStart_2341841 baseEnd_2341841 := by
    simpa [prefixWord, tailWord_2341841, baseEnd_2341841] using wordTrace_append hprefix tailTrace_2341841
  have hstable : (prefixWord ++ tailWord_2341841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341841).length < 2 ^ (prefixWord ++ tailWord_2341841).sum := by decide
  have hdescent : baseEnd_2341841 < baseStart_2341841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
