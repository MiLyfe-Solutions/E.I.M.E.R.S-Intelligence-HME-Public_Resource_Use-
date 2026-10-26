import V185TrunkScan21Chunk159

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1951353 : List Nat := [1, 2, 1, 3, 3, 1, 5, 5]
def baseStart_1951353 : Nat := 118140960795 + 1951353 * 2 ^ 59
def prefixEnd_1951353 : Nat := 4983230072969 + 3 ^ 40 * 1951353 * 2
def baseEnd_1951353 : Nat := 148441780087853193498281

theorem tailTrace_1951353 : CollatzResearch.WordTrace tailWord_1951353 prefixEnd_1951353 148441780087853193498281 := by
  unfold tailWord_1951353
  simp only [CollatzResearch.WordTrace]
  refine ⟨71171690899588820404962713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47447793933059213603308475 71171690899588820404962713)
  ·
    refine ⟨53378768174691615303722035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71171690899588820404962713 53378768174691615303722035)
    ·
      refine ⟨80068152262037422955583053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53378768174691615303722035 80068152262037422955583053)
      ·
        refine ⟨30025557098264033608343645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80068152262037422955583053 30025557098264033608343645)
        ·
          refine ⟨11259583911849012603128867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30025557098264033608343645 11259583911849012603128867)
          ·
            refine ⟨16889375867773518904693301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11259583911849012603128867 16889375867773518904693301)
            ·
              refine ⟨1583378987603767397314997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16889375867773518904693301 1583378987603767397314997)
              ·
                refine ⟨148441780087853193498281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1583378987603767397314997 148441780087853193498281)
                ·
                  rfl

theorem cell21_1951353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 5].length) (baseStart_1951353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1951353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1951353 prefixEnd_1951353 := by exact prefixLift 1951353
  have htrace : WordTrace (prefixWord ++ tailWord_1951353) baseStart_1951353 baseEnd_1951353 := by
    simpa [prefixWord, tailWord_1951353, baseEnd_1951353] using wordTrace_append hprefix tailTrace_1951353
  have hstable : (prefixWord ++ tailWord_1951353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951353).length < 2 ^ (prefixWord ++ tailWord_1951353).sum := by decide
  have hdescent : baseEnd_1951353 < baseStart_1951353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951384 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 5]
def baseStart_1951384 : Nat := 118140960795 + 1951384 * 2 ^ 59
def prefixEnd_1951384 : Nat := 4983230072969 + 3 ^ 40 * 1951384 * 2
def baseEnd_1951384 : Nat := 445332414885910415478113

theorem tailTrace_1951384 : CollatzResearch.WordTrace tailWord_1951384 prefixEnd_1951384 445332414885910415478113 := by
  unfold tailWord_1951384
  simp only [CollatzResearch.WordTrace]
  refine ⟨35586410781238256349670603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47448547708317675132894137 35586410781238256349670603)
  ·
    refine ⟨53379616171857384524505905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35586410781238256349670603 53379616171857384524505905)
    ·
      refine ⟨40034712128893038393379429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53379616171857384524505905 40034712128893038393379429)
      ·
        refine ⟨7506508524167444698758643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40034712128893038393379429 7506508524167444698758643)
        ·
          refine ⟨11259762786251167048137965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7506508524167444698758643 11259762786251167048137965)
          ·
            refine ⟨4222411044844187643051737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11259762786251167048137965 4222411044844187643051737)
            ·
              refine ⟨3166808283633140732288803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4222411044844187643051737 3166808283633140732288803)
              ·
                refine ⟨4750212425449711098433205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3166808283633140732288803 4750212425449711098433205)
                ·
                  refine ⟨445332414885910415478113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4750212425449711098433205 445332414885910415478113)
                  ·
                    rfl

theorem cell21_1951384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_1951384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1951384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1951384 prefixEnd_1951384 := by exact prefixLift 1951384
  have htrace : WordTrace (prefixWord ++ tailWord_1951384) baseStart_1951384 baseEnd_1951384 := by
    simpa [prefixWord, tailWord_1951384, baseEnd_1951384] using wordTrace_append hprefix tailTrace_1951384
  have hstable : (prefixWord ++ tailWord_1951384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951384).length < 2 ^ (prefixWord ++ tailWord_1951384).sum := by decide
  have hdescent : baseEnd_1951384 < baseStart_1951384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951519 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 5]
def baseStart_1951519 : Nat := 118140960795 + 1951519 * 2 ^ 59
def prefixEnd_1951519 : Nat := 4983230072969 + 3 ^ 40 * 1951519 * 2
def baseEnd_1951519 : Nat := 445363223725180180727837

theorem tailTrace_1951519 : CollatzResearch.WordTrace tailWord_1951519 prefixEnd_1951519 445363223725180180727837 := by
  unfold tailWord_1951519
  simp only [CollatzResearch.WordTrace]
  refine ⟨71177745416987430755505611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47451830277991620503670407 71177745416987430755505611)
  ·
    refine ⟨106766618125481146133258417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71177745416987430755505611 106766618125481146133258417)
    ·
      refine ⟨80074963594110859599943813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106766618125481146133258417 80074963594110859599943813)
      ·
        refine ⟨15014055673895786174989465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80074963594110859599943813 15014055673895786174989465)
        ·
          refine ⟨11260541755421839631242099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15014055673895786174989465 11260541755421839631242099)
          ·
            refine ⟨16890812633132759446863149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11260541755421839631242099 16890812633132759446863149)
            ·
              refine ⟨6334054737424784792573681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16890812633132759446863149 6334054737424784792573681)
              ·
                refine ⟨4750541053068588594430261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6334054737424784792573681 4750541053068588594430261)
                ·
                  refine ⟨445363223725180180727837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4750541053068588594430261 445363223725180180727837)
                  ·
                    rfl

theorem cell21_1951519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 5].length) (baseStart_1951519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1951519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1951519 prefixEnd_1951519 := by exact prefixLift 1951519
  have htrace : WordTrace (prefixWord ++ tailWord_1951519) baseStart_1951519 baseEnd_1951519 := by
    simpa [prefixWord, tailWord_1951519, baseEnd_1951519] using wordTrace_append hprefix tailTrace_1951519
  have hstable : (prefixWord ++ tailWord_1951519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951519).length < 2 ^ (prefixWord ++ tailWord_1951519).sum := by decide
  have hdescent : baseEnd_1951519 < baseStart_1951519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951609 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 6]
def baseStart_1951609 : Nat := 118140960795 + 1951609 * 2 ^ 59
def prefixEnd_1951609 : Nat := 4983230072969 + 3 ^ 40 * 1951609 * 2
def baseEnd_1951609 : Nat := 445383762951360024227653

theorem tailTrace_1951609 : CollatzResearch.WordTrace tailWord_1951609 prefixEnd_1951609 445383762951360024227653 := by
  unfold tailWord_1951609
  simp only [CollatzResearch.WordTrace]
  refine ⟨71181027986661376126281881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47454018657774250750854587 71181027986661376126281881)
  ·
    refine ⟨53385770989996032094711411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71181027986661376126281881 53385770989996032094711411)
    ·
      refine ⟨80078656484994048142067117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53385770989996032094711411 80078656484994048142067117)
      ·
        refine ⟨30029496181872768053275169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80078656484994048142067117 30029496181872768053275169)
        ·
          refine ⟨22522122136404576039956377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30029496181872768053275169 22522122136404576039956377)
          ·
            refine ⟨16891591602303432029967283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22522122136404576039956377 16891591602303432029967283)
            ·
              refine ⟨25337387403455148044950925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16891591602303432029967283 25337387403455148044950925)
              ·
                refine ⟨9501520276295680516856597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25337387403455148044950925 9501520276295680516856597)
                ·
                  refine ⟨445383762951360024227653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9501520276295680516856597 445383762951360024227653)
                  ·
                    rfl

theorem cell21_1951609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_1951609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1951609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1951609 prefixEnd_1951609 := by exact prefixLift 1951609
  have htrace : WordTrace (prefixWord ++ tailWord_1951609) baseStart_1951609 baseEnd_1951609 := by
    simpa [prefixWord, tailWord_1951609, baseEnd_1951609] using wordTrace_append hprefix tailTrace_1951609
  have hstable : (prefixWord ++ tailWord_1951609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951609).length < 2 ^ (prefixWord ++ tailWord_1951609).sum := by decide
  have hdescent : baseEnd_1951609 < baseStart_1951609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951705 : List Nat := [1, 2, 1, 2, 6, 1, 2, 3, 3]
def baseStart_1951705 : Nat := 118140960795 + 1951705 * 2 ^ 59
def prefixEnd_1951705 : Nat := 4983230072969 + 3 ^ 40 * 1951705 * 2
def baseEnd_1951705 : Nat := 445405671459285190627457

theorem tailTrace_1951705 : CollatzResearch.WordTrace tailWord_1951705 prefixEnd_1951705 445405671459285190627457 := by
  unfold tailWord_1951705
  simp only [CollatzResearch.WordTrace]
  refine ⟨71184529394313584521776569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47456352929542389681184379 71184529394313584521776569)
  ·
    refine ⟨53388397045735188391332427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71184529394313584521776569 53388397045735188391332427)
    ·
      refine ⟨80082595568602782586998641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53388397045735188391332427 80082595568602782586998641)
      ·
        refine ⟨60061946676452086940248981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80082595568602782586998641 60061946676452086940248981)
        ·
          refine ⟨2815403750458691575324171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60061946676452086940248981 2815403750458691575324171)
          ·
            refine ⟨4223105625688037362986257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815403750458691575324171 4223105625688037362986257)
            ·
              refine ⟨3167329219266028022239693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4223105625688037362986257 3167329219266028022239693)
              ·
                refine ⟨1187748457224760508339885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3167329219266028022239693 1187748457224760508339885)
                ·
                  refine ⟨445405671459285190627457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1187748457224760508339885 445405671459285190627457)
                  ·
                    rfl

theorem cell21_1951705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 3].length) (baseStart_1951705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1951705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1951705 prefixEnd_1951705 := by exact prefixLift 1951705
  have htrace : WordTrace (prefixWord ++ tailWord_1951705) baseStart_1951705 baseEnd_1951705 := by
    simpa [prefixWord, tailWord_1951705, baseEnd_1951705] using wordTrace_append hprefix tailTrace_1951705
  have hstable : (prefixWord ++ tailWord_1951705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951705).length < 2 ^ (prefixWord ++ tailWord_1951705).sum := by decide
  have hdescent : baseEnd_1951705 < baseStart_1951705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951778 : List Nat := [3, 3, 1, 1, 1, 2, 2, 4, 4]
def baseStart_1951778 : Nat := 118140960795 + 1951778 * 2 ^ 59
def prefixEnd_1951778 : Nat := 4983230072969 + 3 ^ 40 * 1951778 * 2
def baseEnd_1951778 : Nat := 445422331053853285910641

theorem tailTrace_1951778 : CollatzResearch.WordTrace tailWord_1951778 prefixEnd_1951778 445422331053853285910641 := by
  unfold tailWord_1951778
  simp only [CollatzResearch.WordTrace]
  refine ⟨17796797980762279497295997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47458127948699411992789325 17796797980762279497295997)
  ·
    refine ⟨6673799242785854811485999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17796797980762279497295997 6673799242785854811485999)
    ·
      refine ⟨10010698864178782217228999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6673799242785854811485999 10010698864178782217228999)
      ·
        refine ⟨15016048296268173325843499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10010698864178782217228999 15016048296268173325843499)
        ·
          refine ⟨22524072444402259988765249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15016048296268173325843499 22524072444402259988765249)
          ·
            refine ⟨16893054333301694991573937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22524072444402259988765249 16893054333301694991573937)
            ·
              refine ⟨12669790749976271243680453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16893054333301694991573937 12669790749976271243680453)
              ·
                refine ⟨2375585765620550858190085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12669790749976271243680453 2375585765620550858190085)
                ·
                  refine ⟨445422331053853285910641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2375585765620550858190085 445422331053853285910641)
                  ·
                    rfl

theorem cell21_1951778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_1951778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1951778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1951778 prefixEnd_1951778 := by exact prefixLift 1951778
  have htrace : WordTrace (prefixWord ++ tailWord_1951778) baseStart_1951778 baseEnd_1951778 := by
    simpa [prefixWord, tailWord_1951778, baseEnd_1951778] using wordTrace_append hprefix tailTrace_1951778
  have hstable : (prefixWord ++ tailWord_1951778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951778).length < 2 ^ (prefixWord ++ tailWord_1951778).sum := by decide
  have hdescent : baseEnd_1951778 < baseStart_1951778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951781 : List Nat := [1, 3, 1, 2, 2, 4, 3, 2, 3]
def baseStart_1951781 : Nat := 118140960795 + 1951781 * 2 ^ 59
def prefixEnd_1951781 : Nat := 4983230072969 + 3 ^ 40 * 1951781 * 2
def baseEnd_1951781 : Nat := 445423015694725947360635

theorem tailTrace_1951781 : CollatzResearch.WordTrace tailWord_1951781 prefixEnd_1951781 445423015694725947360635 := by
  unfold tailWord_1951781
  simp only [CollatzResearch.WordTrace]
  refine ⟨71187301342038249501543197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47458200894692166334362131 71187301342038249501543197)
  ·
    refine ⟨26695238003264343563078699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71187301342038249501543197 26695238003264343563078699)
    ·
      refine ⟨40042857004896515344618049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26695238003264343563078699 40042857004896515344618049)
      ·
        refine ⟨30032142753672386508463537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40042857004896515344618049 30032142753672386508463537)
        ·
          refine ⟨22524107065254289881347653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30032142753672386508463537 22524107065254289881347653)
          ·
            refine ⟨4223270074735179352752685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22524107065254289881347653 4223270074735179352752685)
            ·
              refine ⟨1583726278025692257282257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4223270074735179352752685 1583726278025692257282257)
              ·
                refine ⟨1187794708519269192961693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1583726278025692257282257 1187794708519269192961693)
                ·
                  refine ⟨445423015694725947360635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1187794708519269192961693 445423015694725947360635)
                  ·
                    rfl

theorem cell21_1951781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_1951781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1951781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1951781 prefixEnd_1951781 := by exact prefixLift 1951781
  have htrace : WordTrace (prefixWord ++ tailWord_1951781) baseStart_1951781 baseEnd_1951781 := by
    simpa [prefixWord, tailWord_1951781, baseEnd_1951781] using wordTrace_append hprefix tailTrace_1951781
  have hstable : (prefixWord ++ tailWord_1951781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951781).length < 2 ^ (prefixWord ++ tailWord_1951781).sum := by decide
  have hdescent : baseEnd_1951781 < baseStart_1951781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951792 : List Nat := [2, 1, 1, 1, 2, 6, 2, 6]
def baseStart_1951792 : Nat := 118140960795 + 1951792 * 2 ^ 59
def prefixEnd_1951792 : Nat := 4983230072969 + 3 ^ 40 * 1951792 * 2
def baseEnd_1951792 : Nat := 148475175348197457559093

theorem tailTrace_1951792 : CollatzResearch.WordTrace tailWord_1951792 prefixEnd_1951792 148475175348197457559093 := by
  unfold tailWord_1951792
  simp only [CollatzResearch.WordTrace]
  refine ⟨35593851272499199190096815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47458468363332265586795753 35593851272499199190096815)
  ·
    refine ⟨53390776908748798785145223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35593851272499199190096815 53390776908748798785145223)
    ·
      refine ⟨80086165363123198177717835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53390776908748798785145223 80086165363123198177717835)
      ·
        refine ⟨120129248044684797266576753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80086165363123198177717835 120129248044684797266576753)
        ·
          refine ⟨90096936033513597949932565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120129248044684797266576753 90096936033513597949932565)
          ·
            refine ⟨4223293876570949903903089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90096936033513597949932565 4223293876570949903903089)
            ·
              refine ⟨3167470407428212427927317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4223293876570949903903089 3167470407428212427927317)
              ·
                refine ⟨148475175348197457559093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3167470407428212427927317 148475175348197457559093)
                ·
                  rfl

theorem cell21_1951792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 6].length) (baseStart_1951792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1951792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1951792 prefixEnd_1951792 := by exact prefixLift 1951792
  have htrace : WordTrace (prefixWord ++ tailWord_1951792) baseStart_1951792 baseEnd_1951792 := by
    simpa [prefixWord, tailWord_1951792, baseEnd_1951792] using wordTrace_append hprefix tailTrace_1951792
  have hstable : (prefixWord ++ tailWord_1951792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951792).length < 2 ^ (prefixWord ++ tailWord_1951792).sum := by decide
  have hdescent : baseEnd_1951792 < baseStart_1951792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951840 : List Nat := [2, 1, 1, 3, 2, 4, 1, 4, 3]
def baseStart_1951840 : Nat := 118140960795 + 1951840 * 2 ^ 59
def prefixEnd_1951840 : Nat := 4983230072969 + 3 ^ 40 * 1951840 * 2
def baseEnd_1951840 : Nat := 445436480298554955877181

theorem tailTrace_1951840 : CollatzResearch.WordTrace tailWord_1951840 prefixEnd_1951840 445436480298554955877181 := by
  unfold tailWord_1951840
  simp only [CollatzResearch.WordTrace]
  refine ⟨35594726624412251288970487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47459635499216335051960649 35594726624412251288970487)
  ·
    refine ⟨53392089936618376933455731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35594726624412251288970487 53392089936618376933455731)
    ·
      refine ⟨80088134904927565400183597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53392089936618376933455731 80088134904927565400183597)
      ·
        refine ⟨30033050589347837025068849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80088134904927565400183597 30033050589347837025068849)
        ·
          refine ⟨22524787942010877768801637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30033050589347837025068849 22524787942010877768801637)
          ·
            refine ⟨4223397739127039581650307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22524787942010877768801637 4223397739127039581650307)
            ·
              refine ⟨6335096608690559372475461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223397739127039581650307 6335096608690559372475461)
              ·
                refine ⟨1187830614129479882339149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6335096608690559372475461 1187830614129479882339149)
                ·
                  refine ⟨445436480298554955877181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1187830614129479882339149 445436480298554955877181)
                  ·
                    rfl

theorem cell21_1951840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 3].length) (baseStart_1951840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1951840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1951840 prefixEnd_1951840 := by exact prefixLift 1951840
  have htrace : WordTrace (prefixWord ++ tailWord_1951840) baseStart_1951840 baseEnd_1951840 := by
    simpa [prefixWord, tailWord_1951840, baseEnd_1951840] using wordTrace_append hprefix tailTrace_1951840
  have hstable : (prefixWord ++ tailWord_1951840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951840).length < 2 ^ (prefixWord ++ tailWord_1951840).sum := by decide
  have hdescent : baseEnd_1951840 < baseStart_1951840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951854 : List Nat := [4, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_1951854 : Nat := 118140960795 + 1951854 * 2 ^ 59
def prefixEnd_1951854 : Nat := 4983230072969 + 3 ^ 40 * 1951854 * 2
def baseEnd_1951854 : Nat := 445439675289294042643819

theorem tailTrace_1951854 : CollatzResearch.WordTrace tailWord_1951854 prefixEnd_1951854 445439675289294042643819 := by
  unfold tailWord_1951854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8898745483846722871118827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47459975913849188645967077 8898745483846722871118827)
  ·
    refine ⟨13348118225770084306678241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8898745483846722871118827 13348118225770084306678241)
    ·
      refine ⟨10011088669327563230008681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13348118225770084306678241 10011088669327563230008681)
      ·
        refine ⟨7508316501995672422506511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10011088669327563230008681 7508316501995672422506511)
        ·
          refine ⟨11262474752993508633759767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7508316501995672422506511 11262474752993508633759767)
          ·
            refine ⟨16893712129490262950639651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11262474752993508633759767 16893712129490262950639651)
            ·
              refine ⟨25340568194235394425959477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16893712129490262950639651 25340568194235394425959477)
              ·
                refine ⟨2375678268209568227433701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25340568194235394425959477 2375678268209568227433701)
                ·
                  refine ⟨445439675289294042643819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2375678268209568227433701 445439675289294042643819)
                  ·
                    rfl

theorem cell21_1951854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_1951854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1951854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1951854 prefixEnd_1951854 := by exact prefixLift 1951854
  have htrace : WordTrace (prefixWord ++ tailWord_1951854) baseStart_1951854 baseEnd_1951854 := by
    simpa [prefixWord, tailWord_1951854, baseEnd_1951854] using wordTrace_append hprefix tailTrace_1951854
  have hstable : (prefixWord ++ tailWord_1951854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951854).length < 2 ^ (prefixWord ++ tailWord_1951854).sum := by decide
  have hdescent : baseEnd_1951854 < baseStart_1951854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951899 : List Nat := [1, 1, 1, 1, 1, 1, 2, 10, 3]
def baseStart_1951899 : Nat := 118140960795 + 1951899 * 2 ^ 59
def prefixEnd_1951899 : Nat := 4983230072969 + 3 ^ 40 * 1951899 * 2
def baseEnd_1951899 : Nat := 445449944902383964393727

theorem tailTrace_1951899 : CollatzResearch.WordTrace tailWord_1951899 prefixEnd_1951899 445449944902383964393727 := by
  unfold tailWord_1951899
  simp only [CollatzResearch.WordTrace]
  refine ⟨71191605155610755654338751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47461070103740503769559167 71191605155610755654338751)
  ·
    refine ⟨106787407733416133481508127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71191605155610755654338751 106787407733416133481508127)
    ·
      refine ⟨160181111600124200222262191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106787407733416133481508127 160181111600124200222262191)
      ·
        refine ⟨240271667400186300333393287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160181111600124200222262191 240271667400186300333393287)
        ·
          refine ⟨360407501100279450500089931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240271667400186300333393287 360407501100279450500089931)
          ·
            refine ⟨540611251650419175750134897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360407501100279450500089931 540611251650419175750134897)
            ·
              refine ⟨405458438737814381812601173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540611251650419175750134897 405458438737814381812601173)
              ·
                refine ⟨1187866519739690571716605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 405458438737814381812601173 1187866519739690571716605)
                ·
                  refine ⟨445449944902383964393727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1187866519739690571716605 445449944902383964393727)
                  ·
                    rfl

theorem cell21_1951899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 3].length) (baseStart_1951899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1951899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1951899 prefixEnd_1951899 := by exact prefixLift 1951899
  have htrace : WordTrace (prefixWord ++ tailWord_1951899) baseStart_1951899 baseEnd_1951899 := by
    simpa [prefixWord, tailWord_1951899, baseEnd_1951899] using wordTrace_append hprefix tailTrace_1951899
  have hstable : (prefixWord ++ tailWord_1951899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951899).length < 2 ^ (prefixWord ++ tailWord_1951899).sum := by decide
  have hdescent : baseEnd_1951899 < baseStart_1951899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951964 : List Nat := [2, 2, 5, 2, 1, 1, 1, 3, 4]
def baseStart_1951964 : Nat := 118140960795 + 1951964 * 2 ^ 59
def prefixEnd_1951964 : Nat := 4983230072969 + 3 ^ 40 * 1951964 * 2
def baseEnd_1951964 : Nat := 445464778787958295810261

theorem tailTrace_1951964 : CollatzResearch.WordTrace tailWord_1951964 prefixEnd_1951964 445464778787958295810261 := by
  unfold tailWord_1951964
  simp only [CollatzResearch.WordTrace]
  refine ⟨35596987950187635877727473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47462650600250181170303297 35596987950187635877727473)
  ·
    refine ⟨26697740962640726908295605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35596987950187635877727473 26697740962640726908295605)
    ·
      refine ⟨2502913215247568147652713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26697740962640726908295605 2502913215247568147652713)
      ·
        refine ⟨1877184911435676110739535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2502913215247568147652713 1877184911435676110739535)
        ·
          refine ⟨2815777367153514166109303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877184911435676110739535 2815777367153514166109303)
          ·
            refine ⟨4223666050730271249163955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815777367153514166109303 4223666050730271249163955)
            ·
              refine ⟨6335499076095406873745933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223666050730271249163955 6335499076095406873745933)
              ·
                refine ⟨2375812153535777577654725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6335499076095406873745933 2375812153535777577654725)
                ·
                  refine ⟨445464778787958295810261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2375812153535777577654725 445464778787958295810261)
                  ·
                    rfl

theorem cell21_1951964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_1951964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1951964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1951964 prefixEnd_1951964 := by exact prefixLift 1951964
  have htrace : WordTrace (prefixWord ++ tailWord_1951964) baseStart_1951964 baseEnd_1951964 := by
    simpa [prefixWord, tailWord_1951964, baseEnd_1951964] using wordTrace_append hprefix tailTrace_1951964
  have hstable : (prefixWord ++ tailWord_1951964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951964).length < 2 ^ (prefixWord ++ tailWord_1951964).sum := by decide
  have hdescent : baseEnd_1951964 < baseStart_1951964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952009 : List Nat := [1, 2, 1, 1, 3, 6, 2, 2, 3]
def baseStart_1952009 : Nat := 118140960795 + 1952009 * 2 ^ 59
def prefixEnd_1952009 : Nat := 4983230072969 + 3 ^ 40 * 1952009 * 2
def baseEnd_1952009 : Nat := 445475048401048217560169

theorem tailTrace_1952009 : CollatzResearch.WordTrace tailWord_1952009 prefixEnd_1952009 445475048401048217560169 := by
  unfold tailWord_1952009
  simp only [CollatzResearch.WordTrace]
  refine ⟨71195617185212244440843081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47463744790141496293895387 71195617185212244440843081)
  ·
    refine ⟨53396712888909183330632311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71195617185212244440843081 53396712888909183330632311)
    ·
      refine ⟨80095069333363774995948467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53396712888909183330632311 80095069333363774995948467)
      ·
        refine ⟨120142604000045662493922701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80095069333363774995948467 120142604000045662493922701)
        ·
          refine ⟨45053476500017123435221013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120142604000045662493922701 45053476500017123435221013)
          ·
            refine ⟨2111881710938302661025985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45053476500017123435221013 2111881710938302661025985)
            ·
              refine ⟨1583911283203726995769489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2111881710938302661025985 1583911283203726995769489)
              ·
                refine ⟨1187933462402795246827117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1583911283203726995769489 1187933462402795246827117)
                ·
                  refine ⟨445475048401048217560169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1187933462402795246827117 445475048401048217560169)
                  ·
                    rfl

theorem cell21_1952009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 3].length) (baseStart_1952009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952009 prefixEnd_1952009 := by exact prefixLift 1952009
  have htrace : WordTrace (prefixWord ++ tailWord_1952009) baseStart_1952009 baseEnd_1952009 := by
    simpa [prefixWord, tailWord_1952009, baseEnd_1952009] using wordTrace_append hprefix tailTrace_1952009
  have hstable : (prefixWord ++ tailWord_1952009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952009).length < 2 ^ (prefixWord ++ tailWord_1952009).sum := by decide
  have hdescent : baseEnd_1952009 < baseStart_1952009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952037 : List Nat := [1, 3, 1, 2, 5, 1, 3, 5]
def baseStart_1952037 : Nat := 118140960795 + 1952037 * 2 ^ 59
def prefixEnd_1952037 : Nat := 4983230072969 + 3 ^ 40 * 1952037 * 2
def baseEnd_1952037 : Nat := 148493812794175463697815

theorem tailTrace_1952037 : CollatzResearch.WordTrace tailWord_1952037 prefixEnd_1952037 148493812794175463697815 := by
  unfold tailWord_1952037
  simp only [CollatzResearch.WordTrace]
  refine ⟨71196638429110805222862365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47464425619407203481908243 71196638429110805222862365)
  ·
    refine ⟨26698739410916551958573387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71196638429110805222862365 26698739410916551958573387)
    ·
      refine ⟨40048109116374827937860081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26698739410916551958573387 40048109116374827937860081)
      ·
        refine ⟨30036081837281120953395061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40048109116374827937860081 30036081837281120953395061)
        ·
          refine ⟨2815882672245105089380787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30036081837281120953395061 2815882672245105089380787)
          ·
            refine ⟨4223824008367657634071181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815882672245105089380787 4223824008367657634071181)
            ·
              refine ⟨1583934003137871612776693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4223824008367657634071181 1583934003137871612776693)
              ·
                refine ⟨148493812794175463697815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1583934003137871612776693 148493812794175463697815)
                ·
                  rfl

theorem cell21_1952037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 5].length) (baseStart_1952037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952037 prefixEnd_1952037 := by exact prefixLift 1952037
  have htrace : WordTrace (prefixWord ++ tailWord_1952037) baseStart_1952037 baseEnd_1952037 := by
    simpa [prefixWord, tailWord_1952037, baseEnd_1952037] using wordTrace_append hprefix tailTrace_1952037
  have hstable : (prefixWord ++ tailWord_1952037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952037).length < 2 ^ (prefixWord ++ tailWord_1952037).sum := by decide
  have hdescent : baseEnd_1952037 < baseStart_1952037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952096 : List Nat := [2, 1, 1, 3, 5, 1, 1, 7]
def baseStart_1952096 : Nat := 118140960795 + 1952096 * 2 ^ 59
def prefixEnd_1952096 : Nat := 4983230072969 + 3 ^ 40 * 1952096 * 2
def baseEnd_1952096 : Nat := 148498300995451799869997

theorem tailTrace_1952096 : CollatzResearch.WordTrace tailWord_1952096 prefixEnd_1952096 148498300995451799869997 := by
  unfold tailWord_1952096
  simp only [CollatzResearch.WordTrace]
  refine ⟨35599395167948529149630071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47465860223931372199506761 35599395167948529149630071)
  ·
    refine ⟨53399092751922793724445107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35599395167948529149630071 53399092751922793724445107)
    ·
      refine ⟨80098639127884190586667661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53399092751922793724445107 80098639127884190586667661)
      ·
        refine ⟨30036989672956571470000373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80098639127884190586667661 30036989672956571470000373)
        ·
          refine ⟨2815967781839678575312535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30036989672956571470000373 2815967781839678575312535)
          ·
            refine ⟨4223951672759517862968803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815967781839678575312535 4223951672759517862968803)
            ·
              refine ⟨6335927509139276794453205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223951672759517862968803 6335927509139276794453205)
              ·
                refine ⟨148498300995451799869997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6335927509139276794453205 148498300995451799869997)
                ·
                  rfl

theorem cell21_1952096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 7].length) (baseStart_1952096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952096 prefixEnd_1952096 := by exact prefixLift 1952096
  have htrace : WordTrace (prefixWord ++ tailWord_1952096) baseStart_1952096 baseEnd_1952096 := by
    simpa [prefixWord, tailWord_1952096, baseEnd_1952096] using wordTrace_append hprefix tailTrace_1952096
  have hstable : (prefixWord ++ tailWord_1952096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952096).length < 2 ^ (prefixWord ++ tailWord_1952096).sum := by decide
  have hdescent : baseEnd_1952096 < baseStart_1952096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952130 : List Nat := [3, 4, 2, 1, 2, 1, 2, 6]
def baseStart_1952130 : Nat := 118140960795 + 1952130 * 2 ^ 59
def prefixEnd_1952130 : Nat := 4983230072969 + 3 ^ 40 * 1952130 * 2
def baseEnd_1952130 : Nat := 148500887416526298681085

theorem tailTrace_1952130 : CollatzResearch.WordTrace tailWord_1952130 prefixEnd_1952130 148500887416526298681085 := by
  unfold tailWord_1952130
  simp only [CollatzResearch.WordTrace]
  refine ⟨17800007604443470526499461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47466686945182588070665229 17800007604443470526499461)
  ·
    refine ⟨3337501425833150723718649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17800007604443470526499461 3337501425833150723718649)
    ·
      refine ⟨2503126069374863042788987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3337501425833150723718649 2503126069374863042788987)
      ·
        refine ⟨3754689104062294564183481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2503126069374863042788987 3754689104062294564183481)
        ·
          refine ⟨2816016828046720923137611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3754689104062294564183481 2816016828046720923137611)
          ·
            refine ⟨4224025242070081384706417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816016828046720923137611 4224025242070081384706417)
            ·
              refine ⟨3168018931552561038529813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4224025242070081384706417 3168018931552561038529813)
              ·
                refine ⟨148500887416526298681085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3168018931552561038529813 148500887416526298681085)
                ·
                  rfl

theorem cell21_1952130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_1952130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952130 prefixEnd_1952130 := by exact prefixLift 1952130
  have htrace : WordTrace (prefixWord ++ tailWord_1952130) baseStart_1952130 baseEnd_1952130 := by
    simpa [prefixWord, tailWord_1952130, baseEnd_1952130] using wordTrace_append hprefix tailTrace_1952130
  have hstable : (prefixWord ++ tailWord_1952130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952130).length < 2 ^ (prefixWord ++ tailWord_1952130).sum := by decide
  have hdescent : baseEnd_1952130 < baseStart_1952130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952231 : List Nat := [1, 1, 5, 2, 1, 1, 10]
def baseStart_1952231 : Nat := 118140960795 + 1952231 * 2 ^ 59
def prefixEnd_1952231 : Nat := 4983230072969 + 3 ^ 40 * 1952231 * 2
def baseEnd_1952231 : Nat := 49502856869513907206635

theorem tailTrace_1952231 : CollatzResearch.WordTrace tailWord_1952231 prefixEnd_1952231 49502856869513907206635 := by
  unfold tailWord_1952231
  simp only [CollatzResearch.WordTrace]
  refine ⟨71203714190407976355424547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47469142793605317570283031 71203714190407976355424547)
  ·
    refine ⟨106805571285611964533136821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71203714190407976355424547 106805571285611964533136821)
    ·
      refine ⟨10013022308026121674981577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106805571285611964533136821 10013022308026121674981577)
      ·
        refine ⟨7509766731019591256236183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10013022308026121674981577 7509766731019591256236183)
        ·
          refine ⟨11264650096529386884354275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7509766731019591256236183 11264650096529386884354275)
          ·
            refine ⟨16896975144794080326531413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11264650096529386884354275 16896975144794080326531413)
            ·
              refine ⟨49502856869513907206635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16896975144794080326531413 49502856869513907206635)
              ·
                rfl

theorem cell21_1952231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 10].length) (baseStart_1952231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952231 prefixEnd_1952231 := by exact prefixLift 1952231
  have htrace : WordTrace (prefixWord ++ tailWord_1952231) baseStart_1952231 baseEnd_1952231 := by
    simpa [prefixWord, tailWord_1952231, baseEnd_1952231] using wordTrace_append hprefix tailTrace_1952231
  have hstable : (prefixWord ++ tailWord_1952231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952231).length < 2 ^ (prefixWord ++ tailWord_1952231).sum := by decide
  have hdescent : baseEnd_1952231 < baseStart_1952231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952234 : List Nat := [3, 1, 3, 1, 3, 1, 3, 2, 4]
def baseStart_1952234 : Nat := 118140960795 + 1952234 * 2 ^ 59
def prefixEnd_1952234 : Nat := 4983230072969 + 3 ^ 40 * 1952234 * 2
def baseEnd_1952234 : Nat := 445526396466497826309709

theorem tailTrace_1952234 : CollatzResearch.WordTrace tailWord_1952234 prefixEnd_1952234 445526396466497826309709 := by
  unfold tailWord_1952234
  simp only [CollatzResearch.WordTrace]
  refine ⟨17800955902349276966945939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47469215739598071911855837 17800955902349276966945939)
  ·
    refine ⟨26701433853523915450418909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17800955902349276966945939 26701433853523915450418909)
    ·
      refine ⟨10013037695071468293907091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26701433853523915450418909 10013037695071468293907091)
      ·
        refine ⟨15019556542607202440860637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10013037695071468293907091 15019556542607202440860637)
        ·
          refine ⟨5632333703477700915322739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15019556542607202440860637 5632333703477700915322739)
          ·
            refine ⟨8448500555216551372984109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5632333703477700915322739 8448500555216551372984109)
            ·
              refine ⟨3168187708206206764869041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8448500555216551372984109 3168187708206206764869041)
              ·
                refine ⟨2376140781154655073651781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3168187708206206764869041 2376140781154655073651781)
                ·
                  refine ⟨445526396466497826309709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2376140781154655073651781 445526396466497826309709)
                  ·
                    rfl

theorem cell21_1952234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_1952234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952234 prefixEnd_1952234 := by exact prefixLift 1952234
  have htrace : WordTrace (prefixWord ++ tailWord_1952234) baseStart_1952234 baseEnd_1952234 := by
    simpa [prefixWord, tailWord_1952234, baseEnd_1952234] using wordTrace_append hprefix tailTrace_1952234
  have hstable : (prefixWord ++ tailWord_1952234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952234).length < 2 ^ (prefixWord ++ tailWord_1952234).sum := by decide
  have hdescent : baseEnd_1952234 < baseStart_1952234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952296 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 5]
def baseStart_1952296 : Nat := 118140960795 + 1952296 * 2 ^ 59
def prefixEnd_1952296 : Nat := 4983230072969 + 3 ^ 40 * 1952296 * 2
def baseEnd_1952296 : Nat := 445540545711199496276249

theorem tailTrace_1952296 : CollatzResearch.WordTrace tailWord_1952296 prefixEnd_1952296 445540545711199496276249 := by
  unfold tailWord_1952296
  simp only [CollatzResearch.WordTrace]
  refine ⟨35603042467586246228270371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47470723290114994971027161 35603042467586246228270371)
  ·
    refine ⟨53404563701379369342405557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35603042467586246228270371 53404563701379369342405557)
    ·
      refine ⟨5006677847004315875850521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53404563701379369342405557 5006677847004315875850521)
      ·
        refine ⟨3755008385253236906887891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5006677847004315875850521 3755008385253236906887891)
        ·
          refine ⟨5632512577879855360331837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3755008385253236906887891 5632512577879855360331837)
          ·
            refine ⟨2112192216704945760124439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5632512577879855360331837 2112192216704945760124439)
            ·
              refine ⟨3168288325057418640186659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112192216704945760124439 3168288325057418640186659)
              ·
                refine ⟨4752432487586127960279989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168288325057418640186659 4752432487586127960279989)
                ·
                  refine ⟨445540545711199496276249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4752432487586127960279989 445540545711199496276249)
                  ·
                    rfl

theorem cell21_1952296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 5].length) (baseStart_1952296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952296 prefixEnd_1952296 := by exact prefixLift 1952296
  have htrace : WordTrace (prefixWord ++ tailWord_1952296) baseStart_1952296 baseEnd_1952296 := by
    simpa [prefixWord, tailWord_1952296, baseEnd_1952296] using wordTrace_append hprefix tailTrace_1952296
  have hstable : (prefixWord ++ tailWord_1952296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952296).length < 2 ^ (prefixWord ++ tailWord_1952296).sum := by decide
  have hdescent : baseEnd_1952296 < baseStart_1952296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952307 : List Nat := [1, 1, 1, 2, 4, 2, 4, 6]
def baseStart_1952307 : Nat := 118140960795 + 1952307 * 2 ^ 59
def prefixEnd_1952307 : Nat := 4983230072969 + 3 ^ 40 * 1952307 * 2
def baseEnd_1952307 : Nat := 148514352020355307197631

theorem tailTrace_1952307 : CollatzResearch.WordTrace tailWord_1952307 prefixEnd_1952307 148514352020355307197631 := by
  unfold tailWord_1952307
  simp only [CollatzResearch.WordTrace]
  refine ⟨71206486138132641335191175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47470990758755094223460783 71206486138132641335191175)
  ·
    refine ⟨106809729207198962002786763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71206486138132641335191175 106809729207198962002786763)
    ·
      refine ⟨160214593810798443004180145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106809729207198962002786763 160214593810798443004180145)
      ·
        refine ⟨120160945358098832253135109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160214593810798443004180145 120160945358098832253135109)
        ·
          refine ⟨22530177254643531047462833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120160945358098832253135109 22530177254643531047462833)
          ·
            refine ⟨16897632940982648285597125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22530177254643531047462833 16897632940982648285597125)
            ·
              refine ⟨3168306176434246553549461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16897632940982648285597125 3168306176434246553549461)
              ·
                refine ⟨148514352020355307197631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3168306176434246553549461 148514352020355307197631)
                ·
                  rfl

theorem cell21_1952307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 6].length) (baseStart_1952307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952307 prefixEnd_1952307 := by exact prefixLift 1952307
  have htrace : WordTrace (prefixWord ++ tailWord_1952307) baseStart_1952307 baseEnd_1952307 := by
    simpa [prefixWord, tailWord_1952307, baseEnd_1952307] using wordTrace_append hprefix tailTrace_1952307
  have hstable : (prefixWord ++ tailWord_1952307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952307).length < 2 ^ (prefixWord ++ tailWord_1952307).sum := by decide
  have hdescent : baseEnd_1952307 < baseStart_1952307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952352 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 6]
def baseStart_1952352 : Nat := 118140960795 + 1952352 * 2 ^ 59
def prefixEnd_1952352 : Nat := 4983230072969 + 3 ^ 40 * 1952352 * 2
def baseEnd_1952352 : Nat := 445553325674155843342801

theorem tailTrace_1952352 : CollatzResearch.WordTrace tailWord_1952352 prefixEnd_1952352 445553325674155843342801 := by
  unfold tailWord_1952352
  simp only [CollatzResearch.WordTrace]
  refine ⟨35604063711484807010289655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47472084948646409347052873 35604063711484807010289655)
  ·
    refine ⟨53406095567227210515434483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35604063711484807010289655 53406095567227210515434483)
    ·
      refine ⟨80109143350840815773151725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53406095567227210515434483 80109143350840815773151725)
      ·
        refine ⟨30040928756565305914931897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80109143350840815773151725 30040928756565305914931897)
        ·
          refine ⟨22530696567423979436198923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30040928756565305914931897 22530696567423979436198923)
          ·
            refine ⟨33796044851135969154298385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22530696567423979436198923 33796044851135969154298385)
            ·
              refine ⟨25347033638351976865723789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33796044851135969154298385 25347033638351976865723789)
              ·
                refine ⟨9505137614381991324646421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25347033638351976865723789 9505137614381991324646421)
                ·
                  refine ⟨445553325674155843342801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9505137614381991324646421 445553325674155843342801)
                  ·
                    rfl

theorem cell21_1952352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_1952352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952352 prefixEnd_1952352 := by exact prefixLift 1952352
  have htrace : WordTrace (prefixWord ++ tailWord_1952352) baseStart_1952352 baseEnd_1952352 := by
    simpa [prefixWord, tailWord_1952352, baseEnd_1952352] using wordTrace_append hprefix tailTrace_1952352
  have hstable : (prefixWord ++ tailWord_1952352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952352).length < 2 ^ (prefixWord ++ tailWord_1952352).sum := by decide
  have hdescent : baseEnd_1952352 < baseStart_1952352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952355 : List Nat := [1, 1, 1, 5, 1, 2, 3, 4, 3]
def baseStart_1952355 : Nat := 118140960795 + 1952355 * 2 ^ 59
def prefixEnd_1952355 : Nat := 4983230072969 + 3 ^ 40 * 1952355 * 2
def baseEnd_1952355 : Nat := 445554010315028504792795

theorem tailTrace_1952355 : CollatzResearch.WordTrace tailWord_1952355 prefixEnd_1952355 445554010315028504792795 := by
  unfold tailWord_1952355
  simp only [CollatzResearch.WordTrace]
  refine ⟨71208236841958745532938519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47472157894639163688625679 71208236841958745532938519)
  ·
    refine ⟨106812355262938118299407779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71208236841958745532938519 106812355262938118299407779)
    ·
      refine ⟨160218532894407177449111669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106812355262938118299407779 160218532894407177449111669)
      ·
        refine ⟨15020487458850672885854219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160218532894407177449111669 15020487458850672885854219)
        ·
          refine ⟨22530731188276009328781329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15020487458850672885854219 22530731188276009328781329)
          ·
            refine ⟨16898048391207006996585997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22530731188276009328781329 16898048391207006996585997)
            ·
              refine ⟨6336768146702627623719749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16898048391207006996585997 6336768146702627623719749)
              ·
                refine ⟨1188144027506742679447453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6336768146702627623719749 1188144027506742679447453)
                ·
                  refine ⟨445554010315028504792795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188144027506742679447453 445554010315028504792795)
                  ·
                    rfl

theorem cell21_1952355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 3].length) (baseStart_1952355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952355 prefixEnd_1952355 := by exact prefixLift 1952355
  have htrace : WordTrace (prefixWord ++ tailWord_1952355) baseStart_1952355 baseEnd_1952355 := by
    simpa [prefixWord, tailWord_1952355, baseEnd_1952355] using wordTrace_append hprefix tailTrace_1952355
  have hstable : (prefixWord ++ tailWord_1952355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952355).length < 2 ^ (prefixWord ++ tailWord_1952355).sum := by decide
  have hdescent : baseEnd_1952355 < baseStart_1952355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952448 : List Nat := [2, 1, 1, 2, 4, 4, 1, 3, 3]
def baseStart_1952448 : Nat := 118140960795 + 1952448 * 2 ^ 59
def prefixEnd_1952448 : Nat := 4983230072969 + 3 ^ 40 * 1952448 * 2
def baseEnd_1952448 : Nat := 445575234182081009742605

theorem tailTrace_1952448 : CollatzResearch.WordTrace tailWord_1952448 prefixEnd_1952448 445575234182081009742605 := by
  unfold tailWord_1952448
  simp only [CollatzResearch.WordTrace]
  refine ⟨35605814415310911208036999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47474419220414548277382665 35605814415310911208036999)
  ·
    refine ⟨53408721622966366812055499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35605814415310911208036999 53408721622966366812055499)
    ·
      refine ⟨80113082434449550218083249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53408721622966366812055499 80113082434449550218083249)
      ·
        refine ⟨60084811825837162663562437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80113082434449550218083249 60084811825837162663562437)
        ·
          refine ⟨11265902217344467999417957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60084811825837162663562437 11265902217344467999417957)
          ·
            refine ⟨2112356665752087749890867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11265902217344467999417957 2112356665752087749890867)
            ·
              refine ⟨3168534998628131624836301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112356665752087749890867 3168534998628131624836301)
              ·
                refine ⟨1188200624485549359313613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3168534998628131624836301 1188200624485549359313613)
                ·
                  refine ⟨445575234182081009742605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188200624485549359313613 445575234182081009742605)
                  ·
                    rfl

theorem cell21_1952448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 3].length) (baseStart_1952448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952448 prefixEnd_1952448 := by exact prefixLift 1952448
  have htrace : WordTrace (prefixWord ++ tailWord_1952448) baseStart_1952448 baseEnd_1952448 := by
    simpa [prefixWord, tailWord_1952448, baseEnd_1952448] using wordTrace_append hprefix tailTrace_1952448
  have hstable : (prefixWord ++ tailWord_1952448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952448).length < 2 ^ (prefixWord ++ tailWord_1952448).sum := by decide
  have hdescent : baseEnd_1952448 < baseStart_1952448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952476 : List Nat := [2, 2, 5, 1, 1, 1, 1, 8]
def baseStart_1952476 : Nat := 118140960795 + 1952476 * 2 ^ 59
def prefixEnd_1952476 : Nat := 4983230072969 + 3 ^ 40 * 1952476 * 2
def baseEnd_1952476 : Nat := 148527208054519727758627

theorem tailTrace_1952476 : CollatzResearch.WordTrace tailWord_1952476 prefixEnd_1952476 148527208054519727758627 := by
  unfold tailWord_1952476
  simp only [CollatzResearch.WordTrace]
  refine ⟨35606325037260191599046641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47475100049680255465395521 35606325037260191599046641)
  ·
    refine ⟨26704743777945143699284981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35606325037260191599046641 26704743777945143699284981)
    ·
      refine ⟨2503569729182357221807967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26704743777945143699284981 2503569729182357221807967)
      ·
        refine ⟨3755354593773535832711951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2503569729182357221807967 3755354593773535832711951)
        ·
          refine ⟨5633031890660303749067927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3755354593773535832711951 5633031890660303749067927)
          ·
            refine ⟨8449547835990455623601891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5633031890660303749067927 8449547835990455623601891)
            ·
              refine ⟨12674321753985683435402837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8449547835990455623601891 12674321753985683435402837)
              ·
                refine ⟨148527208054519727758627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12674321753985683435402837 148527208054519727758627)
                ·
                  rfl

theorem cell21_1952476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 8].length) (baseStart_1952476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952476 prefixEnd_1952476 := by exact prefixLift 1952476
  have htrace : WordTrace (prefixWord ++ tailWord_1952476) baseStart_1952476 baseEnd_1952476 := by
    simpa [prefixWord, tailWord_1952476, baseEnd_1952476] using wordTrace_append hprefix tailTrace_1952476
  have hstable : (prefixWord ++ tailWord_1952476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952476).length < 2 ^ (prefixWord ++ tailWord_1952476).sum := by decide
  have hdescent : baseEnd_1952476 < baseStart_1952476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952552 : List Nat := [2, 1, 5, 1, 1, 1, 5, 5]
def baseStart_1952552 : Nat := 118140960795 + 1952552 * 2 ^ 59
def prefixEnd_1952552 : Nat := 4983230072969 + 3 ^ 40 * 1952552 * 2
def baseEnd_1952552 : Nat := 148532989466333313336353

theorem tailTrace_1952552 : CollatzResearch.WordTrace tailWord_1952552 prefixEnd_1952552 148532989466333313336353 := by
  unfold tailWord_1952552
  simp only [CollatzResearch.WordTrace]
  refine ⟨35607711011122524088929955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47476948014830032118573273 35607711011122524088929955)
  ·
    refine ⟨53411566516683786133394933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35607711011122524088929955 53411566516683786133394933)
    ·
      refine ⟨5007334360939104950005775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53411566516683786133394933 5007334360939104950005775)
      ·
        refine ⟨7511001541408657425008663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5007334360939104950005775 7511001541408657425008663)
        ·
          refine ⟨11266502312112986137512995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7511001541408657425008663 11266502312112986137512995)
          ·
            refine ⟨16899753468169479206269493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11266502312112986137512995 16899753468169479206269493)
            ·
              refine ⟨1584351887640888675587765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16899753468169479206269493 1584351887640888675587765)
              ·
                refine ⟨148532989466333313336353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1584351887640888675587765 148532989466333313336353)
                ·
                  rfl

theorem cell21_1952552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 5].length) (baseStart_1952552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952552 prefixEnd_1952552 := by exact prefixLift 1952552
  have htrace : WordTrace (prefixWord ++ tailWord_1952552) baseStart_1952552 baseEnd_1952552 := by
    simpa [prefixWord, tailWord_1952552, baseEnd_1952552] using wordTrace_append hprefix tailTrace_1952552
  have hstable : (prefixWord ++ tailWord_1952552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952552).length < 2 ^ (prefixWord ++ tailWord_1952552).sum := by decide
  have hdescent : baseEnd_1952552 < baseStart_1952552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952611 : List Nat := [1, 1, 1, 5, 3, 2, 1, 7]
def baseStart_1952611 : Nat := 118140960795 + 1952611 * 2 ^ 59
def prefixEnd_1952611 : Nat := 4983230072969 + 3 ^ 40 * 1952611 * 2
def baseEnd_1952611 : Nat := 148537477667609649508535

theorem tailTrace_1952611 : CollatzResearch.WordTrace tailWord_1952611 prefixEnd_1952611 148537477667609649508535 := by
  unfold tailWord_1952611
  simp only [CollatzResearch.WordTrace]
  refine ⟨71217573929031301254257687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47478382619354200836171791 71217573929031301254257687)
  ·
    refine ⟨106826360893546951881386531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71217573929031301254257687 106826360893546951881386531)
    ·
      refine ⟨160239541340320427822079797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106826360893546951881386531 160239541340320427822079797)
      ·
        refine ⟨15022457000655040108319981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160239541340320427822079797 15022457000655040108319981)
        ·
          refine ⟨5633421375245640040619993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15022457000655040108319981 5633421375245640040619993)
          ·
            refine ⟨4225066031434230030464995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5633421375245640040619993 4225066031434230030464995)
            ·
              refine ⟨6337599047151345045697493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4225066031434230030464995 6337599047151345045697493)
              ·
                refine ⟨148537477667609649508535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6337599047151345045697493 148537477667609649508535)
                ·
                  rfl

theorem cell21_1952611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 7].length) (baseStart_1952611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952611 prefixEnd_1952611 := by exact prefixLift 1952611
  have htrace : WordTrace (prefixWord ++ tailWord_1952611) baseStart_1952611 baseEnd_1952611 := by
    simpa [prefixWord, tailWord_1952611, baseEnd_1952611] using wordTrace_append hprefix tailTrace_1952611
  have hstable : (prefixWord ++ tailWord_1952611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952611).length < 2 ^ (prefixWord ++ tailWord_1952611).sum := by decide
  have hdescent : baseEnd_1952611 < baseStart_1952611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952710 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_1952710 : Nat := 118140960795 + 1952710 * 2 ^ 59
def prefixEnd_1952710 : Nat := 4983230072969 + 3 ^ 40 * 1952710 * 2
def baseEnd_1952710 : Nat := 445635026151626776375403

theorem tailTrace_1952710 : CollatzResearch.WordTrace tailWord_1952710 prefixEnd_1952710 445635026151626776375403 := by
  unfold tailWord_1952710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2225662023614770036315987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47480789837115094108074389 2225662023614770036315987)
  ·
    refine ⟨3338493035422155054473981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2225662023614770036315987 3338493035422155054473981)
    ·
      refine ⟨1251934888283308145427743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3338493035422155054473981 1251934888283308145427743)
      ·
        refine ⟨1877902332424962218141615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1251934888283308145427743 1877902332424962218141615)
        ·
          refine ⟨2816853498637443327212423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877902332424962218141615 2816853498637443327212423)
          ·
            refine ⟨4225280247956164990818635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816853498637443327212423 4225280247956164990818635)
            ·
              refine ⟨6337920371934247486227953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4225280247956164990818635 6337920371934247486227953)
              ·
                refine ⟨4753440278950685614670965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6337920371934247486227953 4753440278950685614670965)
                ·
                  refine ⟨445635026151626776375403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4753440278950685614670965 445635026151626776375403)
                  ·
                    rfl

theorem cell21_1952710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_1952710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952710 prefixEnd_1952710 := by exact prefixLift 1952710
  have htrace : WordTrace (prefixWord ++ tailWord_1952710) baseStart_1952710 baseEnd_1952710 := by
    simpa [prefixWord, tailWord_1952710, baseEnd_1952710] using wordTrace_append hprefix tailTrace_1952710
  have hstable : (prefixWord ++ tailWord_1952710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952710).length < 2 ^ (prefixWord ++ tailWord_1952710).sum := by decide
  have hdescent : baseEnd_1952710 < baseStart_1952710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952718 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_1952718 : Nat := 118140960795 + 1952718 * 2 ^ 59
def prefixEnd_1952718 : Nat := 4983230072969 + 3 ^ 40 * 1952718 * 2
def baseEnd_1952718 : Nat := 445636851860620540242053

theorem tailTrace_1952718 : CollatzResearch.WordTrace tailWord_1952718 prefixEnd_1952718 445636851860620540242053 := by
  unfold tailWord_1952718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8902684567455457316050351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47480984359762439018935205 8902684567455457316050351)
  ·
    refine ⟨13354026851183185974075527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8902684567455457316050351 13354026851183185974075527)
    ·
      refine ⟨20031040276774778961113291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13354026851183185974075527 20031040276774778961113291)
      ·
        refine ⟨30046560415162168441669937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20031040276774778961113291 30046560415162168441669937)
        ·
          refine ⟨22534920311371626331252453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30046560415162168441669937 22534920311371626331252453)
          ·
            refine ⟨4225297558382179937109835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22534920311371626331252453 4225297558382179937109835)
            ·
              refine ⟨6337946337573269905664753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4225297558382179937109835 6337946337573269905664753)
              ·
                refine ⟨4753459753179952429248565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6337946337573269905664753 4753459753179952429248565)
                ·
                  refine ⟨445636851860620540242053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4753459753179952429248565 445636851860620540242053)
                  ·
                    rfl

theorem cell21_1952718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_1952718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952718 prefixEnd_1952718 := by exact prefixLift 1952718
  have htrace : WordTrace (prefixWord ++ tailWord_1952718) baseStart_1952718 baseEnd_1952718 := by
    simpa [prefixWord, tailWord_1952718, baseEnd_1952718] using wordTrace_append hprefix tailTrace_1952718
  have hstable : (prefixWord ++ tailWord_1952718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952718).length < 2 ^ (prefixWord ++ tailWord_1952718).sum := by decide
  have hdescent : baseEnd_1952718 < baseStart_1952718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952780 : List Nat := [2, 2, 1, 2, 3, 4, 2, 5]
def baseStart_1952780 : Nat := 118140960795 + 1952780 * 2 ^ 59
def prefixEnd_1952780 : Nat := 4983230072969 + 3 ^ 40 * 1952780 * 2
def baseEnd_1952780 : Nat := 148550333701774070069531

theorem tailTrace_1952780 : CollatzResearch.WordTrace tailWord_1952780 prefixEnd_1952780 148550333701774070069531 := by
  unfold tailWord_1952780
  simp only [CollatzResearch.WordTrace]
  refine ⟨35611868932709521558579897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47482491910279362078106529 35611868932709521558579897)
  ·
    refine ⟨26708901699532141168934923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35611868932709521558579897 26708901699532141168934923)
    ·
      refine ⟨40063352549298211753402385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26708901699532141168934923 40063352549298211753402385)
      ·
        refine ⟨30047514411973658815051789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40063352549298211753402385 30047514411973658815051789)
        ·
          refine ⟨11267817904490122055644421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30047514411973658815051789 11267817904490122055644421)
          ·
            refine ⟨2112715857091897885433329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11267817904490122055644421 2112715857091897885433329)
            ·
              refine ⟨1584536892818923414074997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2112715857091897885433329 1584536892818923414074997)
              ·
                refine ⟨148550333701774070069531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1584536892818923414074997 148550333701774070069531)
                ·
                  rfl

theorem cell21_1952780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 5].length) (baseStart_1952780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952780 prefixEnd_1952780 := by exact prefixLift 1952780
  have htrace : WordTrace (prefixWord ++ tailWord_1952780) baseStart_1952780 baseEnd_1952780 := by
    simpa [prefixWord, tailWord_1952780, baseEnd_1952780] using wordTrace_append hprefix tailTrace_1952780
  have hstable : (prefixWord ++ tailWord_1952780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952780).length < 2 ^ (prefixWord ++ tailWord_1952780).sum := by decide
  have hdescent : baseEnd_1952780 < baseStart_1952780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952811 : List Nat := [1, 1, 1, 1, 2, 1, 9, 2, 3]
def baseStart_1952811 : Nat := 118140960795 + 1952811 * 2 ^ 59
def prefixEnd_1952811 : Nat := 4983230072969 + 3 ^ 40 * 1952811 * 2
def baseEnd_1952811 : Nat := 445658075727673045191863

theorem tailTrace_1952811 : CollatzResearch.WordTrace tailWord_1952811 prefixEnd_1952811 445658075727673045191863 := by
  unfold tailWord_1952811
  simp only [CollatzResearch.WordTrace]
  refine ⟨71224868528306735411538287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47483245685537823607692191 71224868528306735411538287)
  ·
    refine ⟨106837302792460103117307431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71224868528306735411538287 106837302792460103117307431)
    ·
      refine ⟨160255954188690154675961147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106837302792460103117307431 160255954188690154675961147)
      ·
        refine ⟨240383931283035232013941721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160255954188690154675961147 240383931283035232013941721)
        ·
          refine ⟨180287948462276424010456291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240383931283035232013941721 180287948462276424010456291)
          ·
            refine ⟨270431922693414636015684437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180287948462276424010456291 270431922693414636015684437)
            ·
              refine ⟨1584562047031726382904401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 270431922693414636015684437 1584562047031726382904401)
              ·
                refine ⟨1188421535273794787178301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1584562047031726382904401 1188421535273794787178301)
                ·
                  refine ⟨445658075727673045191863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188421535273794787178301 445658075727673045191863)
                  ·
                    rfl

theorem cell21_1952811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 3].length) (baseStart_1952811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952811 prefixEnd_1952811 := by exact prefixLift 1952811
  have htrace : WordTrace (prefixWord ++ tailWord_1952811) baseStart_1952811 baseEnd_1952811 := by
    simpa [prefixWord, tailWord_1952811, baseEnd_1952811] using wordTrace_append hprefix tailTrace_1952811
  have hstable : (prefixWord ++ tailWord_1952811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952811).length < 2 ^ (prefixWord ++ tailWord_1952811).sum := by decide
  have hdescent : baseEnd_1952811 < baseStart_1952811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952825 : List Nat := [1, 2, 1, 5, 2, 2, 1, 3, 4]
def baseStart_1952825 : Nat := 118140960795 + 1952825 * 2 ^ 59
def prefixEnd_1952825 : Nat := 4983230072969 + 3 ^ 40 * 1952825 * 2
def baseEnd_1952825 : Nat := 445661270718412131958501

theorem tailTrace_1952825 : CollatzResearch.WordTrace tailWord_1952825 prefixEnd_1952825 445661270718412131958501 := by
  unfold tailWord_1952825
  simp only [CollatzResearch.WordTrace]
  refine ⟨71225379150256015802547929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47483586100170677201698619 71225379150256015802547929)
  ·
    refine ⟨53419034362692011851910947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71225379150256015802547929 53419034362692011851910947)
    ·
      refine ⟨80128551544038017777866421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53419034362692011851910947 80128551544038017777866421)
      ·
        refine ⟨7512051707253564166674977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80128551544038017777866421 7512051707253564166674977)
        ·
          refine ⟨5634038780440173125006233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7512051707253564166674977 5634038780440173125006233)
          ·
            refine ⟨4225529085330129843754675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5634038780440173125006233 4225529085330129843754675)
            ·
              refine ⟨6338293627995194765632013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4225529085330129843754675 6338293627995194765632013)
              ·
                refine ⟨2376860110498198037112005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6338293627995194765632013 2376860110498198037112005)
                ·
                  refine ⟨445661270718412131958501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2376860110498198037112005 445661270718412131958501)
                  ·
                    rfl

theorem cell21_1952825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_1952825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952825 prefixEnd_1952825 := by exact prefixLift 1952825
  have htrace : WordTrace (prefixWord ++ tailWord_1952825) baseStart_1952825 baseEnd_1952825 := by
    simpa [prefixWord, tailWord_1952825, baseEnd_1952825] using wordTrace_append hprefix tailTrace_1952825
  have hstable : (prefixWord ++ tailWord_1952825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952825).length < 2 ^ (prefixWord ++ tailWord_1952825).sum := by decide
  have hdescent : baseEnd_1952825 < baseStart_1952825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952862 : List Nat := [4, 4, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1952862 : Nat := 118140960795 + 1952862 * 2 ^ 59
def prefixEnd_1952862 : Nat := 4983230072969 + 3 ^ 40 * 1952862 * 2
def baseEnd_1952862 : Nat := 445669714622508289841759

theorem tailTrace_1952862 : CollatzResearch.WordTrace tailWord_1952862 prefixEnd_1952862 445669714622508289841759 := by
  unfold tailWord_1952862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8903341081390246390205605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47484485767414647414429893 8903341081390246390205605)
  ·
    refine ⟨1669376452760671198163551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8903341081390246390205605 1669376452760671198163551)
    ·
      refine ⟨2504064679141006797245327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1669376452760671198163551 2504064679141006797245327)
      ·
        refine ⟨3756097018711510195867991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2504064679141006797245327 3756097018711510195867991)
        ·
          refine ⟨5634145528067265293801987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3756097018711510195867991 5634145528067265293801987)
          ·
            refine ⟨8451218292100897940702981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5634145528067265293801987 8451218292100897940702981)
            ·
              refine ⟨1584603429768918363881809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8451218292100897940702981 1584603429768918363881809)
              ·
                refine ⟨1188452572326688772911357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1584603429768918363881809 1188452572326688772911357)
                ·
                  refine ⟨445669714622508289841759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188452572326688772911357 445669714622508289841759)
                  ·
                    rfl

theorem cell21_1952862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1952862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952862 prefixEnd_1952862 := by exact prefixLift 1952862
  have htrace : WordTrace (prefixWord ++ tailWord_1952862) baseStart_1952862 baseEnd_1952862 := by
    simpa [prefixWord, tailWord_1952862, baseEnd_1952862] using wordTrace_append hprefix tailTrace_1952862
  have hstable : (prefixWord ++ tailWord_1952862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952862).length < 2 ^ (prefixWord ++ tailWord_1952862).sum := by decide
  have hdescent : baseEnd_1952862 < baseStart_1952862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952904 : List Nat := [2, 1, 3, 4, 2, 1, 2, 3, 3]
def baseStart_1952904 : Nat := 118140960795 + 1952904 * 2 ^ 59
def prefixEnd_1952904 : Nat := 4983230072969 + 3 ^ 40 * 1952904 * 2
def baseEnd_1952904 : Nat := 445679299594725550141673

theorem tailTrace_1952904 : CollatzResearch.WordTrace tailWord_1952904 prefixEnd_1952904 445679299594725550141673 := by
  unfold tailWord_1952904
  simp only [CollatzResearch.WordTrace]
  refine ⟨35614130258484906147336883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47485507011313208196449177 35614130258484906147336883)
  ·
    refine ⟨53421195387727359221005325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35614130258484906147336883 53421195387727359221005325)
    ·
      refine ⟨20032948270397759707876997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53421195387727359221005325 20032948270397759707876997)
      ·
        refine ⟨3756177800699579945226937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20032948270397759707876997 3756177800699579945226937)
        ·
          refine ⟨2817133350524684958920203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3756177800699579945226937 2817133350524684958920203)
          ·
            refine ⟨4225700025787027438380305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2817133350524684958920203 4225700025787027438380305)
            ·
              refine ⟨3169275019340270578785229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4225700025787027438380305 3169275019340270578785229)
              ·
                refine ⟨1188478132252601467044461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3169275019340270578785229 1188478132252601467044461)
                ·
                  refine ⟨445679299594725550141673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188478132252601467044461 445679299594725550141673)
                  ·
                    rfl

theorem cell21_1952904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 3].length) (baseStart_1952904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952904 prefixEnd_1952904 := by exact prefixLift 1952904
  have htrace : WordTrace (prefixWord ++ tailWord_1952904) baseStart_1952904 baseEnd_1952904 := by
    simpa [prefixWord, tailWord_1952904, baseEnd_1952904] using wordTrace_append hprefix tailTrace_1952904
  have hstable : (prefixWord ++ tailWord_1952904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952904).length < 2 ^ (prefixWord ++ tailWord_1952904).sum := by decide
  have hdescent : baseEnd_1952904 < baseStart_1952904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952966 : List Nat := [6, 1, 2, 2, 1, 2, 7]
def baseStart_1952966 : Nat := 118140960795 + 1952966 * 2 ^ 59
def prefixEnd_1952966 : Nat := 4983230072969 + 3 ^ 40 * 1952966 * 2
def baseEnd_1952966 : Nat := 49521494315491913345357

theorem tailTrace_1952966 : CollatzResearch.WordTrace tailWord_1952966 prefixEnd_1952966 49521494315491913345357 := by
  unfold tailWord_1952966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2225953807585787402607211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47487014561830131255620501 2225953807585787402607211)
  ·
    refine ⟨3338930711378681103910817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2225953807585787402607211 3338930711378681103910817)
    ·
      refine ⟨2504198033534010827933113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3338930711378681103910817 2504198033534010827933113)
      ·
        refine ⟨1878148525150508120949835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2504198033534010827933113 1878148525150508120949835)
        ·
          refine ⟨2817222787725762181424753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1878148525150508120949835 2817222787725762181424753)
          ·
            refine ⟨2112917090794321636068565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2817222787725762181424753 2112917090794321636068565)
            ·
              refine ⟨49521494315491913345357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2112917090794321636068565 49521494315491913345357)
              ·
                rfl

theorem cell21_1952966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 7].length) (baseStart_1952966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952966 prefixEnd_1952966 := by exact prefixLift 1952966
  have htrace : WordTrace (prefixWord ++ tailWord_1952966) baseStart_1952966 baseEnd_1952966 := by
    simpa [prefixWord, tailWord_1952966, baseEnd_1952966] using wordTrace_append hprefix tailTrace_1952966
  have hstable : (prefixWord ++ tailWord_1952966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952966).length < 2 ^ (prefixWord ++ tailWord_1952966).sum := by decide
  have hdescent : baseEnd_1952966 < baseStart_1952966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952980 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 5]
def baseStart_1952980 : Nat := 118140960795 + 1952980 * 2 ^ 59
def prefixEnd_1952980 : Nat := 4983230072969 + 3 ^ 40 * 1952980 * 2
def baseEnd_1952980 : Nat := 445696643830166306874851

theorem tailTrace_1952980 : CollatzResearch.WordTrace tailWord_1952980 prefixEnd_1952980 445696643830166306874851 := by
  unfold tailWord_1952980
  simp only [CollatzResearch.WordTrace]
  refine ⟨35615516232347238637220197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47487354976462984849626929 35615516232347238637220197)
  ·
    refine ⟨6677909293565107244478787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35615516232347238637220197 6677909293565107244478787)
    ·
      refine ⟨10016863940347660866718181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6677909293565107244478787 10016863940347660866718181)
      ·
        refine ⟨1878161988815186412509659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10016863940347660866718181 1878161988815186412509659)
        ·
          refine ⟨2817242983222779618764489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1878161988815186412509659 2817242983222779618764489)
          ·
            refine ⟨2112932237417084714073367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2817242983222779618764489 2112932237417084714073367)
            ·
              refine ⟨3169398356125627071110051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112932237417084714073367 3169398356125627071110051)
              ·
                refine ⟨4754097534188440606665077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169398356125627071110051 4754097534188440606665077)
                ·
                  refine ⟨445696643830166306874851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4754097534188440606665077 445696643830166306874851)
                  ·
                    rfl

theorem cell21_1952980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_1952980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1952980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1952980 prefixEnd_1952980 := by exact prefixLift 1952980
  have htrace : WordTrace (prefixWord ++ tailWord_1952980) baseStart_1952980 baseEnd_1952980 := by
    simpa [prefixWord, tailWord_1952980, baseEnd_1952980] using wordTrace_append hprefix tailTrace_1952980
  have hstable : (prefixWord ++ tailWord_1952980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952980).length < 2 ^ (prefixWord ++ tailWord_1952980).sum := by decide
  have hdescent : baseEnd_1952980 < baseStart_1952980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953036 : List Nat := [2, 2, 1, 2, 2, 3, 1, 4, 4]
def baseStart_1953036 : Nat := 118140960795 + 1953036 * 2 ^ 59
def prefixEnd_1953036 : Nat := 4983230072969 + 3 ^ 40 * 1953036 * 2
def baseEnd_1953036 : Nat := 445709423793122653941403

theorem tailTrace_1953036 : CollatzResearch.WordTrace tailWord_1953036 prefixEnd_1953036 445709423793122653941403 := by
  unfold tailWord_1953036
  simp only [CollatzResearch.WordTrace]
  refine ⟨35616537476245799419239481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47488716634994399225652641 35616537476245799419239481)
  ·
    refine ⟨26712403107184349564429611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35616537476245799419239481 26712403107184349564429611)
    ·
      refine ⟨40068604660776524346644417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26712403107184349564429611 40068604660776524346644417)
      ·
        refine ⟨30051453495582393259983313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40068604660776524346644417 30051453495582393259983313)
        ·
          refine ⟨22538590121686794944987485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30051453495582393259983313 22538590121686794944987485)
          ·
            refine ⟨8451971295632548104370307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22538590121686794944987485 8451971295632548104370307)
            ·
              refine ⟨12677956943448822156555461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8451971295632548104370307 12677956943448822156555461)
              ·
                refine ⟨2377116926896654154354149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12677956943448822156555461 2377116926896654154354149)
                ·
                  refine ⟨445709423793122653941403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2377116926896654154354149 445709423793122653941403)
                  ·
                    rfl

theorem cell21_1953036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_1953036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1953036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1953036 prefixEnd_1953036 := by exact prefixLift 1953036
  have htrace : WordTrace (prefixWord ++ tailWord_1953036) baseStart_1953036 baseEnd_1953036 := by
    simpa [prefixWord, tailWord_1953036, baseEnd_1953036] using wordTrace_append hprefix tailTrace_1953036
  have hstable : (prefixWord ++ tailWord_1953036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953036).length < 2 ^ (prefixWord ++ tailWord_1953036).sum := by decide
  have hdescent : baseEnd_1953036 < baseStart_1953036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953042 : List Nat := [3, 2, 4, 2, 2, 1, 1, 6]
def baseStart_1953042 : Nat := 118140960795 + 1953042 * 2 ^ 59
def prefixEnd_1953042 : Nat := 4983230072969 + 3 ^ 40 * 1953042 * 2
def baseEnd_1953042 : Nat := 148570264358289325613797

theorem tailTrace_1953042 : CollatzResearch.WordTrace tailWord_1953042 prefixEnd_1953042 148570264358289325613797 := by
  unfold tailWord_1953042
  simp only [CollatzResearch.WordTrace]
  refine ⟨17808323447617465465799345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47488862526979907908798253 17808323447617465465799345)
  ·
    refine ⟨13356242585713099099349509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17808323447617465465799345 13356242585713099099349509)
    ·
      refine ⟨2504295484821206081128033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13356242585713099099349509 2504295484821206081128033)
      ·
        refine ⟨1878221613615904560846025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2504295484821206081128033 1878221613615904560846025)
        ·
          refine ⟨1408666210211928420634519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1878221613615904560846025 1408666210211928420634519)
          ·
            refine ⟨2112999315317892630951779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408666210211928420634519 2112999315317892630951779)
            ·
              refine ⟨3169498972976838946427669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112999315317892630951779 3169498972976838946427669)
              ·
                refine ⟨148570264358289325613797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3169498972976838946427669 148570264358289325613797)
                ·
                  rfl

theorem cell21_1953042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_1953042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1953042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1953042 prefixEnd_1953042 := by exact prefixLift 1953042
  have htrace : WordTrace (prefixWord ++ tailWord_1953042) baseStart_1953042 baseEnd_1953042 := by
    simpa [prefixWord, tailWord_1953042, baseEnd_1953042] using wordTrace_append hprefix tailTrace_1953042
  have hstable : (prefixWord ++ tailWord_1953042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953042).length < 2 ^ (prefixWord ++ tailWord_1953042).sum := by decide
  have hdescent : baseEnd_1953042 < baseStart_1953042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953053 : List Nat := [1, 4, 2, 3, 1, 1, 2, 3, 4]
def baseStart_1953053 : Nat := 118140960795 + 1953053 * 2 ^ 59
def prefixEnd_1953053 : Nat := 4983230072969 + 3 ^ 40 * 1953053 * 2
def baseEnd_1953053 : Nat := 445713303424734402158035

theorem tailTrace_1953053 : CollatzResearch.WordTrace tailWord_1953053 prefixEnd_1953053 445713303424734402158035 := by
  unfold tailWord_1953053
  simp only [CollatzResearch.WordTrace]
  refine ⟨71233694993430010741847813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47489129995620007161231875 71233694993430010741847813)
  ·
    refine ⟨13356317811268127014096465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71233694993430010741847813 13356317811268127014096465)
    ·
      refine ⟨10017238358451095260572349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13356317811268127014096465 10017238358451095260572349)
      ·
        refine ⟨3756464384419160722714631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10017238358451095260572349 3756464384419160722714631)
        ·
          refine ⟨5634696576628741084071947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3756464384419160722714631 5634696576628741084071947)
          ·
            refine ⟨8452044864943111626107921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5634696576628741084071947 8452044864943111626107921)
            ·
              refine ⟨6339033648707333719580941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8452044864943111626107921 6339033648707333719580941)
              ·
                refine ⟨2377137618265250144842853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6339033648707333719580941 2377137618265250144842853)
                ·
                  refine ⟨445713303424734402158035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2377137618265250144842853 445713303424734402158035)
                  ·
                    rfl

theorem cell21_1953053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_1953053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1953053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1953053 prefixEnd_1953053 := by exact prefixLift 1953053
  have htrace : WordTrace (prefixWord ++ tailWord_1953053) baseStart_1953053 baseEnd_1953053 := by
    simpa [prefixWord, tailWord_1953053, baseEnd_1953053] using wordTrace_append hprefix tailTrace_1953053
  have hstable : (prefixWord ++ tailWord_1953053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953053).length < 2 ^ (prefixWord ++ tailWord_1953053).sum := by decide
  have hdescent : baseEnd_1953053 < baseStart_1953053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953157 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 5]
def baseStart_1953157 : Nat := 118140960795 + 1953157 * 2 ^ 59
def prefixEnd_1953157 : Nat := 4983230072969 + 3 ^ 40 * 1953157 * 2
def baseEnd_1953157 : Nat := 445737037641653332424489

theorem tailTrace_1953157 : CollatzResearch.WordTrace tailWord_1953157 prefixEnd_1953157 445737037641653332424489 := by
  unfold tailWord_1953157
  simp only [CollatzResearch.WordTrace]
  refine ⟨71237488185053236503633725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47491658790035491002422483 71237488185053236503633725)
  ·
    refine ⟨26714058069394963688862647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71237488185053236503633725 26714058069394963688862647)
    ·
      refine ⟨40071087104092445533293971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26714058069394963688862647 40071087104092445533293971)
      ·
        refine ⟨60106630656138668299940957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40071087104092445533293971 60106630656138668299940957)
        ·
          refine ⟨22539986496052000612477859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60106630656138668299940957 22539986496052000612477859)
          ·
            refine ⟨33809979744078000918716789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22539986496052000612477859 33809979744078000918716789)
            ·
              refine ⟨3169685601007312586129699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33809979744078000918716789 3169685601007312586129699)
              ·
                refine ⟨4754528401510968879194549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169685601007312586129699 4754528401510968879194549)
                ·
                  refine ⟨445737037641653332424489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4754528401510968879194549 445737037641653332424489)
                  ·
                    rfl

theorem cell21_1953157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_1953157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1953157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1953157 prefixEnd_1953157 := by exact prefixLift 1953157
  have htrace : WordTrace (prefixWord ++ tailWord_1953157) baseStart_1953157 baseEnd_1953157 := by
    simpa [prefixWord, tailWord_1953157, baseEnd_1953157] using wordTrace_append hprefix tailTrace_1953157
  have hstable : (prefixWord ++ tailWord_1953157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953157).length < 2 ^ (prefixWord ++ tailWord_1953157).sum := by decide
  have hdescent : baseEnd_1953157 < baseStart_1953157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953205 : List Nat := [1, 3, 3, 2, 2, 2, 2, 2, 4]
def baseStart_1953205 : Nat := 118140960795 + 1953205 * 2 ^ 59
def prefixEnd_1953205 : Nat := 4983230072969 + 3 ^ 40 * 1953205 * 2
def baseEnd_1953205 : Nat := 445747991895615915624391

theorem tailTrace_1953205 : CollatzResearch.WordTrace tailWord_1953205 prefixEnd_1953205 445747991895615915624391 := by
  unfold tailWord_1953205
  simp only [CollatzResearch.WordTrace]
  refine ⟨71239238888879340701381069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47492825925919560467587379 71239238888879340701381069)
  ·
    refine ⟨26714714583329752763017901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71239238888879340701381069 26714714583329752763017901)
    ·
      refine ⟨10018017968748657286131713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26714714583329752763017901 10018017968748657286131713)
      ·
        refine ⟨7513513476561492964598785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10018017968748657286131713 7513513476561492964598785)
        ·
          refine ⟨5635135107421119723449089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7513513476561492964598785 5635135107421119723449089)
          ·
            refine ⟨4226351330565839792586817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5635135107421119723449089 4226351330565839792586817)
            ·
              refine ⟨3169763497924379844440113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4226351330565839792586817 3169763497924379844440113)
              ·
                refine ⟨2377322623443284883330085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3169763497924379844440113 2377322623443284883330085)
                ·
                  refine ⟨445747991895615915624391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2377322623443284883330085 445747991895615915624391)
                  ·
                    rfl

theorem cell21_1953205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_1953205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1953205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1953205 prefixEnd_1953205 := by exact prefixLift 1953205
  have htrace : WordTrace (prefixWord ++ tailWord_1953205) baseStart_1953205 baseEnd_1953205 := by
    simpa [prefixWord, tailWord_1953205, baseEnd_1953205] using wordTrace_append hprefix tailTrace_1953205
  have hstable : (prefixWord ++ tailWord_1953205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953205).length < 2 ^ (prefixWord ++ tailWord_1953205).sum := by decide
  have hdescent : baseEnd_1953205 < baseStart_1953205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953236 : List Nat := [2, 4, 1, 2, 3, 1, 3, 5]
def baseStart_1953236 : Nat := 118140960795 + 1953236 * 2 ^ 59
def prefixEnd_1953236 : Nat := 4983230072969 + 3 ^ 40 * 1953236 * 2
def baseEnd_1953236 : Nat := 148585022172655583535887

theorem tailTrace_1953236 : CollatzResearch.WordTrace tailWord_1953236 prefixEnd_1953236 148585022172655583535887 := by
  unfold tailWord_1953236
  simp only [CollatzResearch.WordTrace]
  refine ⟨35620184775883516497879781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47493579701178021997173041 35620184775883516497879781)
  ·
    refine ⟨6678784645478159343352459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35620184775883516497879781 6678784645478159343352459)
    ·
      refine ⟨10018176968217239015028689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6678784645478159343352459 10018176968217239015028689)
      ·
        refine ⟨7513632726162929261271517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10018176968217239015028689 7513632726162929261271517)
        ·
          refine ⟨2817612272311098472976819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7513632726162929261271517 2817612272311098472976819)
          ·
            refine ⟨4226418408466647709465229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2817612272311098472976819 4226418408466647709465229)
            ·
              refine ⟨1584906903174992891049461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4226418408466647709465229 1584906903174992891049461)
              ·
                refine ⟨148585022172655583535887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1584906903174992891049461 148585022172655583535887)
                ·
                  rfl

theorem cell21_1953236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 5].length) (baseStart_1953236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1953236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1953236 prefixEnd_1953236 := by exact prefixLift 1953236
  have htrace : WordTrace (prefixWord ++ tailWord_1953236) baseStart_1953236 baseEnd_1953236 := by
    simpa [prefixWord, tailWord_1953236, baseEnd_1953236] using wordTrace_append hprefix tailTrace_1953236
  have hstable : (prefixWord ++ tailWord_1953236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953236).length < 2 ^ (prefixWord ++ tailWord_1953236).sum := by decide
  have hdescent : baseEnd_1953236 < baseStart_1953236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953247 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 6]
def baseStart_1953247 : Nat := 118140960795 + 1953247 * 2 ^ 59
def prefixEnd_1953247 : Nat := 4983230072969 + 3 ^ 40 * 1953247 * 2
def baseEnd_1953247 : Nat := 445757576867833175924305

theorem tailTrace_1953247 : CollatzResearch.WordTrace tailWord_1953247 prefixEnd_1953247 445757576867833175924305 := by
  unfold tailWord_1953247
  simp only [CollatzResearch.WordTrace]
  refine ⟨71240770754727181874409995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47493847169818121249606663 71240770754727181874409995)
  ·
    refine ⟨106861156132090772811614993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71240770754727181874409995 106861156132090772811614993)
    ·
      refine ⟨80145867099068079608711245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106861156132090772811614993 80145867099068079608711245)
      ·
        refine ⟨30054700162150529853266717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80145867099068079608711245 30054700162150529853266717)
        ·
          refine ⟨11270512560806448694975019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30054700162150529853266717 11270512560806448694975019)
          ·
            refine ⟨16905768841209673042462529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11270512560806448694975019 16905768841209673042462529)
            ·
              refine ⟨12679326630907254781846897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16905768841209673042462529 12679326630907254781846897)
              ·
                refine ⟨9509494973180441086385173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12679326630907254781846897 9509494973180441086385173)
                ·
                  refine ⟨445757576867833175924305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9509494973180441086385173 445757576867833175924305)
                  ·
                    rfl

theorem cell21_1953247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 6].length) (baseStart_1953247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1953247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1953247 prefixEnd_1953247 := by exact prefixLift 1953247
  have htrace : WordTrace (prefixWord ++ tailWord_1953247) baseStart_1953247 baseEnd_1953247 := by
    simpa [prefixWord, tailWord_1953247, baseEnd_1953247] using wordTrace_append hprefix tailTrace_1953247
  have hstable : (prefixWord ++ tailWord_1953247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953247).length < 2 ^ (prefixWord ++ tailWord_1953247).sum := by decide
  have hdescent : baseEnd_1953247 < baseStart_1953247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953264 : List Nat := [2, 1, 1, 1, 3, 4, 3, 2, 4]
def baseStart_1953264 : Nat := 118140960795 + 1953264 * 2 ^ 59
def prefixEnd_1953264 : Nat := 4983230072969 + 3 ^ 40 * 1953264 * 2
def baseEnd_1953264 : Nat := 445761456499444924140937

theorem tailTrace_1953264 : CollatzResearch.WordTrace tailWord_1953264 prefixEnd_1953264 445761456499444924140937 := by
  unfold tailWord_1953264
  simp only [CollatzResearch.WordTrace]
  refine ⟨35620695397832796888889423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47494260530443729185185897 35620695397832796888889423)
  ·
    refine ⟨53431043096749195333334135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35620695397832796888889423 53431043096749195333334135)
    ·
      refine ⟨80146564645123793000001203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53431043096749195333334135 80146564645123793000001203)
      ·
        refine ⟨120219846967685689500001805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80146564645123793000001203 120219846967685689500001805)
        ·
          refine ⟨45082442612882133562500677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120219846967685689500001805 45082442612882133562500677)
          ·
            refine ⟨8452957989915400042968877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45082442612882133562500677 8452957989915400042968877)
            ·
              refine ⟨3169859246218275016113329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8452957989915400042968877 3169859246218275016113329)
              ·
                refine ⟨2377394434663706262084997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3169859246218275016113329 2377394434663706262084997)
                ·
                  refine ⟨445761456499444924140937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2377394434663706262084997 445761456499444924140937)
                  ·
                    rfl

theorem cell21_1953264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_1953264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1953264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1953264 prefixEnd_1953264 := by exact prefixLift 1953264
  have htrace : WordTrace (prefixWord ++ tailWord_1953264) baseStart_1953264 baseEnd_1953264 := by
    simpa [prefixWord, tailWord_1953264, baseEnd_1953264] using wordTrace_append hprefix tailTrace_1953264
  have hstable : (prefixWord ++ tailWord_1953264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953264).length < 2 ^ (prefixWord ++ tailWord_1953264).sum := by decide
  have hdescent : baseEnd_1953264 < baseStart_1953264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953326 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_1953326 : Nat := 118140960795 + 1953326 * 2 ^ 59
def prefixEnd_1953326 : Nat := 4983230072969 + 3 ^ 40 * 1953326 * 2
def baseEnd_1953326 : Nat := 445775605744146594107477

theorem tailTrace_1953326 : CollatzResearch.WordTrace tailWord_1953326 prefixEnd_1953326 445775605744146594107477 := by
  unfold tailWord_1953326
  simp only [CollatzResearch.WordTrace]
  refine ⟨8905456515180122295816979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47495768080960652244357221 8905456515180122295816979)
  ·
    refine ⟨13358184772770183443725469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8905456515180122295816979 13358184772770183443725469)
    ·
      refine ⟨5009319289788818791397051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13358184772770183443725469 5009319289788818791397051)
      ·
        refine ⟨7513978934683228187095577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5009319289788818791397051 7513978934683228187095577)
        ·
          refine ⟨5635484201012421140321683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7513978934683228187095577 5635484201012421140321683)
          ·
            refine ⟨8453226301518631710482525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5635484201012421140321683 8453226301518631710482525)
            ·
              refine ⟨3169959863069486891430947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8453226301518631710482525 3169959863069486891430947)
              ·
                refine ⟨4754939794604230337146421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169959863069486891430947 4754939794604230337146421)
                ·
                  refine ⟨445775605744146594107477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4754939794604230337146421 445775605744146594107477)
                  ·
                    rfl

theorem cell21_1953326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_1953326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1953326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1953326 prefixEnd_1953326 := by exact prefixLift 1953326
  have htrace : WordTrace (prefixWord ++ tailWord_1953326) baseStart_1953326 baseEnd_1953326 := by
    simpa [prefixWord, tailWord_1953326, baseEnd_1953326] using wordTrace_append hprefix tailTrace_1953326
  have hstable : (prefixWord ++ tailWord_1953326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953326).length < 2 ^ (prefixWord ++ tailWord_1953326).sum := by decide
  have hdescent : baseEnd_1953326 < baseStart_1953326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953489 : List Nat := [1, 2, 2, 1, 2, 4, 9]
def baseStart_1953489 : Nat := 118140960795 + 1953489 * 2 ^ 59
def prefixEnd_1953489 : Nat := 4983230072969 + 3 ^ 40 * 1953489 * 2
def baseEnd_1953489 : Nat := 49534756062766059210053

theorem tailTrace_1953489 : CollatzResearch.WordTrace tailWord_1953489 prefixEnd_1953489 49534756062766059210053 := by
  unfold tailWord_1953489
  simp only [CollatzResearch.WordTrace]
  refine ⟨71249597219850457204719521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47499731479900304803146347 71249597219850457204719521)
  ·
    refine ⟨53437197914887842903539641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71249597219850457204719521 53437197914887842903539641)
    ·
      refine ⟨40077898436165882177654731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53437197914887842903539641 40077898436165882177654731)
      ·
        refine ⟨60116847654248823266482097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40077898436165882177654731 60116847654248823266482097)
        ·
          refine ⟨45087635740686617449861573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60116847654248823266482097 45087635740686617449861573)
          ·
            refine ⟨8453931701378740771849045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45087635740686617449861573 8453931701378740771849045)
            ·
              refine ⟨49534756062766059210053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8453931701378740771849045 49534756062766059210053)
              ·
                rfl

theorem cell21_1953489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 9].length) (baseStart_1953489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1953489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1953489 prefixEnd_1953489 := by exact prefixLift 1953489
  have htrace : WordTrace (prefixWord ++ tailWord_1953489) baseStart_1953489 baseEnd_1953489 := by
    simpa [prefixWord, tailWord_1953489, baseEnd_1953489] using wordTrace_append hprefix tailTrace_1953489
  have hstable : (prefixWord ++ tailWord_1953489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953489).length < 2 ^ (prefixWord ++ tailWord_1953489).sum := by decide
  have hdescent : baseEnd_1953489 < baseStart_1953489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953492 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 6]
def baseStart_1953492 : Nat := 118140960795 + 1953492 * 2 ^ 59
def prefixEnd_1953492 : Nat := 4983230072969 + 3 ^ 40 * 1953492 * 2
def baseEnd_1953492 : Nat := 445813489205767194340471

theorem tailTrace_1953492 : CollatzResearch.WordTrace tailWord_1953492 prefixEnd_1953492 445813489205767194340471 := by
  unfold tailWord_1953492
  simp only [CollatzResearch.WordTrace]
  refine ⟨35624853319419794358539365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47499804425893059144719153 35624853319419794358539365)
  ·
    refine ⟨6679659997391211442226131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35624853319419794358539365 6679659997391211442226131)
    ·
      refine ⟨10019489996086817163339197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6679659997391211442226131 10019489996086817163339197)
      ·
        refine ⟨3757308748532556436252199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10019489996086817163339197 3757308748532556436252199)
        ·
          refine ⟨5635963122798834654378299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3757308748532556436252199 5635963122798834654378299)
          ·
            refine ⟨8453944684198251981567449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5635963122798834654378299 8453944684198251981567449)
            ·
              refine ⟨6340458513148688986175587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8453944684198251981567449 6340458513148688986175587)
              ·
                refine ⟨9510687769723033479263381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6340458513148688986175587 9510687769723033479263381)
                ·
                  refine ⟨445813489205767194340471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9510687769723033479263381 445813489205767194340471)
                  ·
                    rfl

theorem cell21_1953492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_1953492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1953492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1953492 prefixEnd_1953492 := by exact prefixLift 1953492
  have htrace : WordTrace (prefixWord ++ tailWord_1953492) baseStart_1953492 baseEnd_1953492 := by
    simpa [prefixWord, tailWord_1953492, baseEnd_1953492] using wordTrace_append hprefix tailTrace_1953492
  have hstable : (prefixWord ++ tailWord_1953492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953492).length < 2 ^ (prefixWord ++ tailWord_1953492).sum := by decide
  have hdescent : baseEnd_1953492 < baseStart_1953492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953717 : List Nat := [1, 3, 3, 2, 1, 11]
def baseStart_1953717 : Nat := 118140960795 + 1953717 * 2 ^ 59
def prefixEnd_1953717 : Nat := 4983230072969 + 3 ^ 40 * 1953717 * 2
def baseEnd_1953717 : Nat := 16513512491526548262593

theorem tailTrace_1953717 : CollatzResearch.WordTrace tailWord_1953717 prefixEnd_1953717 16513512491526548262593 := by
  unfold tailWord_1953717
  simp only [CollatzResearch.WordTrace]
  refine ⟨71257913063024452144019405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47505275375349634762679603 71257913063024452144019405)
  ·
    refine ⟨26721717398634169554007277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71257913063024452144019405 26721717398634169554007277)
    ·
      refine ⟨10020644024487813582752729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26721717398634169554007277 10020644024487813582752729)
      ·
        refine ⟨7515483018365860187064547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10020644024487813582752729 7515483018365860187064547)
        ·
          refine ⟨11273224527548790280596821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7515483018365860187064547 11273224527548790280596821)
          ·
            refine ⟨16513512491526548262593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11273224527548790280596821 16513512491526548262593)
            ·
              rfl

theorem cell21_1953717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 11].length) (baseStart_1953717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1953717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1953717 prefixEnd_1953717 := by exact prefixLift 1953717
  have htrace : WordTrace (prefixWord ++ tailWord_1953717) baseStart_1953717 baseEnd_1953717 := by
    simpa [prefixWord, tailWord_1953717, baseEnd_1953717] using wordTrace_append hprefix tailTrace_1953717
  have hstable : (prefixWord ++ tailWord_1953717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953717).length < 2 ^ (prefixWord ++ tailWord_1953717).sum := by decide
  have hdescent : baseEnd_1953717 < baseStart_1953717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953782 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_1953782 : Nat := 118140960795 + 1953782 * 2 ^ 59
def prefixEnd_1953782 : Nat := 4983230072969 + 3 ^ 40 * 1953782 * 2
def baseEnd_1953782 : Nat := 445879671156791134506545

theorem tailTrace_1953782 : CollatzResearch.WordTrace tailWord_1953782 prefixEnd_1953782 445879671156791134506545 := by
  unfold tailWord_1953782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4453767737986810515320975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47506855871859312163423733 4453767737986810515320975)
  ·
    refine ⟨6680651606980215772981463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4453767737986810515320975 6680651606980215772981463)
    ·
      refine ⟨10020977410470323659472195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6680651606980215772981463 10020977410470323659472195)
      ·
        refine ⟨15031466115705485489208293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10020977410470323659472195 15031466115705485489208293)
        ·
          refine ⟨2818399896694778529226555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15031466115705485489208293 2818399896694778529226555)
          ·
            refine ⟨4227599845042167793839833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818399896694778529226555 4227599845042167793839833)
            ·
              refine ⟨3170699883781625845379875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4227599845042167793839833 3170699883781625845379875)
              ·
                refine ⟨4756049825672438768069813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3170699883781625845379875 4756049825672438768069813)
                ·
                  refine ⟨445879671156791134506545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4756049825672438768069813 445879671156791134506545)
                  ·
                    rfl

theorem cell21_1953782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_1953782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1953782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1953782 prefixEnd_1953782 := by exact prefixLift 1953782
  have htrace : WordTrace (prefixWord ++ tailWord_1953782) baseStart_1953782 baseEnd_1953782 := by
    simpa [prefixWord, tailWord_1953782, baseEnd_1953782] using wordTrace_append hprefix tailTrace_1953782
  have hstable : (prefixWord ++ tailWord_1953782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953782).length < 2 ^ (prefixWord ++ tailWord_1953782).sum := by decide
  have hdescent : baseEnd_1953782 < baseStart_1953782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953793 : List Nat := [1, 2, 4, 1, 2, 1, 2, 8]
def baseStart_1953793 : Nat := 118140960795 + 1953793 * 2 ^ 59
def prefixEnd_1953793 : Nat := 4983230072969 + 3 ^ 40 * 1953793 * 2
def baseEnd_1953793 : Nat := 148627393835552519941063

theorem tailTrace_1953793 : CollatzResearch.WordTrace tailWord_1953793 prefixEnd_1953793 148627393835552519941063 := by
  unfold tailWord_1953793
  simp only [CollatzResearch.WordTrace]
  refine ⟨71260685010749117123786033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47507123340499411415857355 71260685010749117123786033)
  ·
    refine ⟨53445513758061837842839525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71260685010749117123786033 53445513758061837842839525)
    ·
      refine ⟨10021033829636594595532411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53445513758061837842839525 10021033829636594595532411)
      ·
        refine ⟨15031550744454891893298617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10021033829636594595532411 15031550744454891893298617)
        ·
          refine ⟨11273663058341168919973963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15031550744454891893298617 11273663058341168919973963)
          ·
            refine ⟨16910494587511753379960945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11273663058341168919973963 16910494587511753379960945)
            ·
              refine ⟨12682870940633815034970709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16910494587511753379960945 12682870940633815034970709)
              ·
                refine ⟨148627393835552519941063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12682870940633815034970709 148627393835552519941063)
                ·
                  rfl

theorem cell21_1953793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 8].length) (baseStart_1953793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1953793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1953793 prefixEnd_1953793 := by exact prefixLift 1953793
  have htrace : WordTrace (prefixWord ++ tailWord_1953793) baseStart_1953793 baseEnd_1953793 := by
    simpa [prefixWord, tailWord_1953793, baseEnd_1953793] using wordTrace_append hprefix tailTrace_1953793
  have hstable : (prefixWord ++ tailWord_1953793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953793).length < 2 ^ (prefixWord ++ tailWord_1953793).sum := by decide
  have hdescent : baseEnd_1953793 < baseStart_1953793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953841 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 5]
def baseStart_1953841 : Nat := 118140960795 + 1953841 * 2 ^ 59
def prefixEnd_1953841 : Nat := 4983230072969 + 3 ^ 40 * 1953841 * 2
def baseEnd_1953841 : Nat := 445893135760620143023091

theorem tailTrace_1953841 : CollatzResearch.WordTrace tailWord_1953841 prefixEnd_1953841 445893135760620143023091 := by
  unfold tailWord_1953841
  simp only [CollatzResearch.WordTrace]
  refine ⟨71262435714575221321533377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47508290476383480881022251 71262435714575221321533377)
  ·
    refine ⟨53446826785931415991150033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71262435714575221321533377 53446826785931415991150033)
    ·
      refine ⟨40085120089448561993362525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53446826785931415991150033 40085120089448561993362525)
      ·
        refine ⟨15031920033543210747510947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40085120089448561993362525 15031920033543210747510947)
        ·
          refine ⟨22547880050314816121266421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15031920033543210747510947 22547880050314816121266421)
          ·
            refine ⟨2113863754717014011368727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22547880050314816121266421 2113863754717014011368727)
            ·
              refine ⟨3170795632075521017053091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113863754717014011368727 3170795632075521017053091)
              ·
                refine ⟨4756193448113281525579637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3170795632075521017053091 4756193448113281525579637)
                ·
                  refine ⟨445893135760620143023091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4756193448113281525579637 445893135760620143023091)
                  ·
                    rfl

theorem cell21_1953841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 5].length) (baseStart_1953841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1953841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1953841 prefixEnd_1953841 := by exact prefixLift 1953841
  have htrace : WordTrace (prefixWord ++ tailWord_1953841) baseStart_1953841 baseEnd_1953841 := by
    simpa [prefixWord, tailWord_1953841, baseEnd_1953841] using wordTrace_append hprefix tailTrace_1953841
  have hstable : (prefixWord ++ tailWord_1953841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953841).length < 2 ^ (prefixWord ++ tailWord_1953841).sum := by decide
  have hdescent : baseEnd_1953841 < baseStart_1953841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953965 : List Nat := [1, 5, 2, 1, 2, 2, 3, 1, 4]
def baseStart_1953965 : Nat := 118140960795 + 1953965 * 2 ^ 59
def prefixEnd_1953965 : Nat := 4983230072969 + 3 ^ 40 * 1953965 * 2
def baseEnd_1953965 : Nat := 445921434250023482956171

theorem tailTrace_1953965 : CollatzResearch.WordTrace tailWord_1953965 prefixEnd_1953965 445921434250023482956171 := by
  unfold tailWord_1953965
  simp only [CollatzResearch.WordTrace]
  refine ⟨71266958366125990499047349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47511305577417326999364899 71266958366125990499047349)
  ·
    refine ⟨6681277346824311609285689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71266958366125990499047349 6681277346824311609285689)
    ·
      refine ⟨5010958010118233706964267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6681277346824311609285689 5010958010118233706964267)
      ·
        refine ⟨7516437015177350560446401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5010958010118233706964267 7516437015177350560446401)
        ·
          refine ⟨5637327761383012920334801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7516437015177350560446401 5637327761383012920334801)
          ·
            refine ⟨4227995821037259690251101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5637327761383012920334801 4227995821037259690251101)
            ·
              refine ⟨1585498432888972383844163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4227995821037259690251101 1585498432888972383844163)
              ·
                refine ⟨2378247649333458575766245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1585498432888972383844163 2378247649333458575766245)
                ·
                  refine ⟨445921434250023482956171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2378247649333458575766245 445921434250023482956171)
                  ·
                    rfl

theorem cell21_1953965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_1953965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1953965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1953965 prefixEnd_1953965 := by exact prefixLift 1953965
  have htrace : WordTrace (prefixWord ++ tailWord_1953965) baseStart_1953965 baseEnd_1953965 := by
    simpa [prefixWord, tailWord_1953965, baseEnd_1953965] using wordTrace_append hprefix tailTrace_1953965
  have hstable : (prefixWord ++ tailWord_1953965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953965).length < 2 ^ (prefixWord ++ tailWord_1953965).sum := by decide
  have hdescent : baseEnd_1953965 < baseStart_1953965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954021 : List Nat := [1, 3, 1, 4, 2, 1, 1, 8]
def baseStart_1954021 : Nat := 118140960795 + 1954021 * 2 ^ 59
def prefixEnd_1954021 : Nat := 4983230072969 + 3 ^ 40 * 1954021 * 2
def baseEnd_1954021 : Nat := 148644738070993276674241

theorem tailTrace_1954021 : CollatzResearch.WordTrace tailWord_1954021 prefixEnd_1954021 148644738070993276674241 := by
  unfold tailWord_1954021
  simp only [CollatzResearch.WordTrace]
  refine ⟨71269000853923112063085917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47512667235948741375390611 71269000853923112063085917)
  ·
    refine ⟨26725875320221167023657219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71269000853923112063085917 26725875320221167023657219)
    ·
      refine ⟨40088812980331750535485829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26725875320221167023657219 40088812980331750535485829)
      ·
        refine ⟨7516652433812203225403593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40088812980331750535485829 7516652433812203225403593)
        ·
          refine ⟨5637489325359152419052695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7516652433812203225403593 5637489325359152419052695)
          ·
            refine ⟨8456233988038728628579043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5637489325359152419052695 8456233988038728628579043)
            ·
              refine ⟨12684350982058092942868565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8456233988038728628579043 12684350982058092942868565)
              ·
                refine ⟨148644738070993276674241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12684350982058092942868565 148644738070993276674241)
                ·
                  rfl

theorem cell21_1954021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 8].length) (baseStart_1954021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954021 prefixEnd_1954021 := by exact prefixLift 1954021
  have htrace : WordTrace (prefixWord ++ tailWord_1954021) baseStart_1954021 baseEnd_1954021 := by
    simpa [prefixWord, tailWord_1954021, baseEnd_1954021] using wordTrace_append hprefix tailTrace_1954021
  have hstable : (prefixWord ++ tailWord_1954021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954021).length < 2 ^ (prefixWord ++ tailWord_1954021).sum := by decide
  have hdescent : baseEnd_1954021 < baseStart_1954021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954024 : List Nat := [2, 1, 4, 1, 2, 2, 4, 1, 4]
def baseStart_1954024 : Nat := 118140960795 + 1954024 * 2 ^ 59
def prefixEnd_1954024 : Nat := 4983230072969 + 3 ^ 40 * 1954024 * 2
def baseEnd_1954024 : Nat := 445934898853852491472717

theorem tailTrace_1954024 : CollatzResearch.WordTrace tailWord_1954024 prefixEnd_1954024 445934898853852491472717 := by
  unfold tailWord_1954024
  simp only [CollatzResearch.WordTrace]
  refine ⟨35634555136456121787722563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47512740181941495716963417 35634555136456121787722563)
  ·
    refine ⟨53451832704684182681583845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35634555136456121787722563 53451832704684182681583845)
    ·
      refine ⟨10022218632128284252796971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53451832704684182681583845 10022218632128284252796971)
      ·
        refine ⟨15033327948192426379195457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10022218632128284252796971 15033327948192426379195457)
        ·
          refine ⟨11274995961144319784396593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15033327948192426379195457 11274995961144319784396593)
          ·
            refine ⟨8456246970858239838297445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11274995961144319784396593 8456246970858239838297445)
            ·
              refine ⟨1585546307035919969680771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8456246970858239838297445 1585546307035919969680771)
              ·
                refine ⟨2378319460553879954521157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1585546307035919969680771 2378319460553879954521157)
                ·
                  refine ⟨445934898853852491472717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2378319460553879954521157 445934898853852491472717)
                  ·
                    rfl

theorem cell21_1954024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 4].length) (baseStart_1954024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954024 prefixEnd_1954024 := by exact prefixLift 1954024
  have htrace : WordTrace (prefixWord ++ tailWord_1954024) baseStart_1954024 baseEnd_1954024 := by
    simpa [prefixWord, tailWord_1954024, baseEnd_1954024] using wordTrace_append hprefix tailTrace_1954024
  have hstable : (prefixWord ++ tailWord_1954024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954024).length < 2 ^ (prefixWord ++ tailWord_1954024).sum := by decide
  have hdescent : baseEnd_1954024 < baseStart_1954024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954035 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 7]
def baseStart_1954035 : Nat := 118140960795 + 1954035 * 2 ^ 59
def prefixEnd_1954035 : Nat := 4983230072969 + 3 ^ 40 * 1954035 * 2
def baseEnd_1954035 : Nat := 445937409203718916789361

theorem tailTrace_1954035 : CollatzResearch.WordTrace tailWord_1954035 prefixEnd_1954035 445937409203718916789361 := by
  unfold tailWord_1954035
  simp only [CollatzResearch.WordTrace]
  refine ⟨71269511475872392454095559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47513007650581594969397039 71269511475872392454095559)
  ·
    refine ⟨106904267213808588681143339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71269511475872392454095559 106904267213808588681143339)
    ·
      refine ⟨160356400820712883021715009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106904267213808588681143339 160356400820712883021715009)
      ·
        refine ⟨120267300615534662266286257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160356400820712883021715009 120267300615534662266286257)
        ·
          refine ⟨90200475461650996699714693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120267300615534662266286257 90200475461650996699714693)
          ·
            refine ⟨16912589149059561881196505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90200475461650996699714693 16912589149059561881196505)
            ·
              refine ⟨12684441861794671410897379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16912589149059561881196505 12684441861794671410897379)
              ·
                refine ⟨19026662792692007116346069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12684441861794671410897379 19026662792692007116346069)
                ·
                  refine ⟨445937409203718916789361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19026662792692007116346069 445937409203718916789361)
                  ·
                    rfl

theorem cell21_1954035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 7].length) (baseStart_1954035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954035 prefixEnd_1954035 := by exact prefixLift 1954035
  have htrace : WordTrace (prefixWord ++ tailWord_1954035) baseStart_1954035 baseEnd_1954035 := by
    simpa [prefixWord, tailWord_1954035, baseEnd_1954035] using wordTrace_append hprefix tailTrace_1954035
  have hstable : (prefixWord ++ tailWord_1954035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954035).length < 2 ^ (prefixWord ++ tailWord_1954035).sum := by decide
  have hdescent : baseEnd_1954035 < baseStart_1954035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954111 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 7]
def baseStart_1954111 : Nat := 118140960795 + 1954111 * 2 ^ 59
def prefixEnd_1954111 : Nat := 4983230072969 + 3 ^ 40 * 1954111 * 2
def baseEnd_1954111 : Nat := 445954753439159673522539

theorem tailTrace_1954111 : CollatzResearch.WordTrace tailWord_1954111 prefixEnd_1954111 445954753439159673522539 := by
  unfold tailWord_1954111
  simp only [CollatzResearch.WordTrace]
  refine ⟨71272283423597057433862187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47514855615731371622574791 71272283423597057433862187)
  ·
    refine ⟨106908425135395586150793281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71272283423597057433862187 106908425135395586150793281)
    ·
      refine ⟨80181318851546689613094961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106908425135395586150793281 80181318851546689613094961)
      ·
        refine ⟨60135989138660017209821221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80181318851546689613094961 60135989138660017209821221)
        ·
          refine ⟨11275497963498753226841479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60135989138660017209821221 11275497963498753226841479)
          ·
            refine ⟨16913246945248129840262219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11275497963498753226841479 16913246945248129840262219)
            ·
              refine ⟨25369870417872194760393329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16913246945248129840262219 25369870417872194760393329)
              ·
                refine ⟨19027402813404146070294997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25369870417872194760393329 19027402813404146070294997)
                ·
                  refine ⟨445954753439159673522539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19027402813404146070294997 445954753439159673522539)
                  ·
                    rfl

theorem cell21_1954111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 7].length) (baseStart_1954111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954111 prefixEnd_1954111 := by exact prefixLift 1954111
  have htrace : WordTrace (prefixWord ++ tailWord_1954111) baseStart_1954111 baseEnd_1954111 := by
    simpa [prefixWord, tailWord_1954111, baseEnd_1954111] using wordTrace_append hprefix tailTrace_1954111
  have hstable : (prefixWord ++ tailWord_1954111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954111).length < 2 ^ (prefixWord ++ tailWord_1954111).sum := by decide
  have hdescent : baseEnd_1954111 < baseStart_1954111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954128 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 5]
def baseStart_1954128 : Nat := 118140960795 + 1954128 * 2 ^ 59
def prefixEnd_1954128 : Nat := 4983230072969 + 3 ^ 40 * 1954128 * 2
def baseEnd_1954128 : Nat := 445958633070771421739171

theorem tailTrace_1954128 : CollatzResearch.WordTrace tailWord_1954128 prefixEnd_1954128 445958633070771421739171 := by
  unfold tailWord_1954128
  simp only [CollatzResearch.WordTrace]
  refine ⟨35636451732267734668615519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47515268976356979558154025 35636451732267734668615519)
  ·
    refine ⟨53454677598401602002923279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35636451732267734668615519 53454677598401602002923279)
    ·
      refine ⟨80182016397602403004384919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53454677598401602002923279 80182016397602403004384919)
      ·
        refine ⟨120273024596403604506577379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80182016397602403004384919 120273024596403604506577379)
        ·
          refine ⟨180409536894605406759866069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120273024596403604506577379 180409536894605406759866069)
          ·
            refine ⟨4228348520967314220934361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 180409536894605406759866069 4228348520967314220934361)
            ·
              refine ⟨3171261390725485665700771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4228348520967314220934361 3171261390725485665700771)
              ·
                refine ⟨4756892086088228498551157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3171261390725485665700771 4756892086088228498551157)
                ·
                  refine ⟨445958633070771421739171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4756892086088228498551157 445958633070771421739171)
                  ·
                    rfl

theorem cell21_1954128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_1954128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954128 prefixEnd_1954128 := by exact prefixLift 1954128
  have htrace : WordTrace (prefixWord ++ tailWord_1954128) baseStart_1954128 baseEnd_1954128 := by
    simpa [prefixWord, tailWord_1954128, baseEnd_1954128] using wordTrace_append hprefix tailTrace_1954128
  have hstable : (prefixWord ++ tailWord_1954128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954128).length < 2 ^ (prefixWord ++ tailWord_1954128).sum := by decide
  have hdescent : baseEnd_1954128 < baseStart_1954128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954162 : List Nat := [3, 2, 1, 2, 1, 5, 1, 3, 3]
def baseStart_1954162 : Nat := 118140960795 + 1954162 * 2 ^ 59
def prefixEnd_1954162 : Nat := 4983230072969 + 3 ^ 40 * 1954162 * 2
def baseEnd_1954162 : Nat := 445966392333994918172435

theorem tailTrace_1954162 : CollatzResearch.WordTrace tailWord_1954162 prefixEnd_1954162 445966392333994918172435 := by
  unfold tailWord_1954162
  simp only [CollatzResearch.WordTrace]
  refine ⟨17818535886603073285992185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47516095697608195429312493 17818535886603073285992185)
  ·
    refine ⟨13363901914952304964494139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17818535886603073285992185 13363901914952304964494139)
    ·
      refine ⟨20045852872428457446741209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13363901914952304964494139 20045852872428457446741209)
      ·
        refine ⟨15034389654321343085055907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20045852872428457446741209 15034389654321343085055907)
        ·
          refine ⟨22551584481482014627583861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15034389654321343085055907 22551584481482014627583861)
          ·
            refine ⟨2114211045138938871335987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22551584481482014627583861 2114211045138938871335987)
            ·
              refine ⟨3171316567708408307003981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114211045138938871335987 3171316567708408307003981)
              ·
                refine ⟨1189243712890653115126493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3171316567708408307003981 1189243712890653115126493)
                ·
                  refine ⟨445966392333994918172435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1189243712890653115126493 445966392333994918172435)
                  ·
                    rfl

theorem cell21_1954162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_1954162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954162 prefixEnd_1954162 := by exact prefixLift 1954162
  have htrace : WordTrace (prefixWord ++ tailWord_1954162) baseStart_1954162 baseEnd_1954162 := by
    simpa [prefixWord, tailWord_1954162, baseEnd_1954162] using wordTrace_append hprefix tailTrace_1954162
  have hstable : (prefixWord ++ tailWord_1954162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954162).length < 2 ^ (prefixWord ++ tailWord_1954162).sum := by decide
  have hdescent : baseEnd_1954162 < baseStart_1954162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954173 : List Nat := [1, 4, 1, 1, 2, 5, 7]
def baseStart_1954173 : Nat := 118140960795 + 1954173 * 2 ^ 59
def prefixEnd_1954173 : Nat := 4983230072969 + 3 ^ 40 * 1954173 * 2
def baseEnd_1954173 : Nat := 49552100298206815943231

theorem tailTrace_1954173 : CollatzResearch.WordTrace tailWord_1954173 prefixEnd_1954173 49552100298206815943231 := by
  unfold tailWord_1954173
  simp only [CollatzResearch.WordTrace]
  refine ⟨71274544749372442022619173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47516363166248294681746115 71274544749372442022619173)
  ·
    refine ⟨13363977140507332879241095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71274544749372442022619173 13363977140507332879241095)
    ·
      refine ⟨20045965710760999318861643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13363977140507332879241095 20045965710760999318861643)
      ·
        refine ⟨30068948566141498978292465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20045965710760999318861643 30068948566141498978292465)
        ·
          refine ⟨22551711424606124233719349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30068948566141498978292465 22551711424606124233719349)
          ·
            refine ⟨2114222946056824146911189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22551711424606124233719349 2114222946056824146911189)
            ·
              refine ⟨49552100298206815943231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2114222946056824146911189 49552100298206815943231)
              ·
                rfl

theorem cell21_1954173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 7].length) (baseStart_1954173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954173 prefixEnd_1954173 := by exact prefixLift 1954173
  have htrace : WordTrace (prefixWord ++ tailWord_1954173) baseStart_1954173 baseEnd_1954173 := by
    simpa [prefixWord, tailWord_1954173, baseEnd_1954173] using wordTrace_append hprefix tailTrace_1954173
  have hstable : (prefixWord ++ tailWord_1954173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954173).length < 2 ^ (prefixWord ++ tailWord_1954173).sum := by decide
  have hdescent : baseEnd_1954173 < baseStart_1954173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954190 : List Nat := [4, 1, 1, 4, 1, 2, 2, 6]
def baseStart_1954190 : Nat := 118140960795 + 1954190 * 2 ^ 59
def prefixEnd_1954190 : Nat := 4983230072969 + 3 ^ 40 * 1954190 * 2
def baseEnd_1954190 : Nat := 148657594105157697235237

theorem tailTrace_1954190 : CollatzResearch.WordTrace tailWord_1954190 prefixEnd_1954190 148657594105157697235237 := by
  unfold tailWord_1954190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8909395598788856740748503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47516776526873902617325349 8909395598788856740748503)
  ·
    refine ⟨13364093398183285111122755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8909395598788856740748503 13364093398183285111122755)
    ·
      refine ⟨20046140097274927666684133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13364093398183285111122755 20046140097274927666684133)
      ·
        refine ⟨3758651268239048937503275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20046140097274927666684133 3758651268239048937503275)
        ·
          refine ⟨5637976902358573406254913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3758651268239048937503275 5637976902358573406254913)
          ·
            refine ⟨4228482676768930054691185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5637976902358573406254913 4228482676768930054691185)
            ·
              refine ⟨3171362007576697541018389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4228482676768930054691185 3171362007576697541018389)
              ·
                refine ⟨148657594105157697235237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3171362007576697541018389 148657594105157697235237)
                ·
                  rfl

theorem cell21_1954190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_1954190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954190 prefixEnd_1954190 := by exact prefixLift 1954190
  have htrace : WordTrace (prefixWord ++ tailWord_1954190) baseStart_1954190 baseEnd_1954190 := by
    simpa [prefixWord, tailWord_1954190, baseEnd_1954190] using wordTrace_append hprefix tailTrace_1954190
  have hstable : (prefixWord ++ tailWord_1954190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954190).length < 2 ^ (prefixWord ++ tailWord_1954190).sum := by decide
  have hdescent : baseEnd_1954190 < baseStart_1954190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954238 : List Nat := [4, 2, 1, 1, 1, 1, 6, 2, 3]
def baseStart_1954238 : Nat := 118140960795 + 1954238 * 2 ^ 59
def prefixEnd_1954238 : Nat := 4983230072969 + 3 ^ 40 * 1954238 * 2
def baseEnd_1954238 : Nat := 445983736569435674905613

theorem tailTrace_1954238 : CollatzResearch.WordTrace tailWord_1954238 prefixEnd_1954238 445983736569435674905613 := by
  unfold tailWord_1954238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8909614436767119765466921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47517943662757972082490245 8909614436767119765466921)
  ·
    refine ⟨6682210827575339824100191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8909614436767119765466921 6682210827575339824100191)
    ·
      refine ⟨10023316241363009736150287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6682210827575339824100191 10023316241363009736150287)
      ·
        refine ⟨15034974362044514604225431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10023316241363009736150287 15034974362044514604225431)
        ·
          refine ⟨22552461543066771906338147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15034974362044514604225431 22552461543066771906338147)
          ·
            refine ⟨33828692314600157859507221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22552461543066771906338147 33828692314600157859507221)
            ·
              refine ⟨1585719952246882399664401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33828692314600157859507221 1585719952246882399664401)
              ·
                refine ⟨1189289964185161799748301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1585719952246882399664401 1189289964185161799748301)
                ·
                  refine ⟨445983736569435674905613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1189289964185161799748301 445983736569435674905613)
                  ·
                    rfl

theorem cell21_1954238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_1954238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954238 prefixEnd_1954238 := by exact prefixLift 1954238
  have htrace : WordTrace (prefixWord ++ tailWord_1954238) baseStart_1954238 baseEnd_1954238 := by
    simpa [prefixWord, tailWord_1954238, baseEnd_1954238] using wordTrace_append hprefix tailTrace_1954238
  have hstable : (prefixWord ++ tailWord_1954238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954238).length < 2 ^ (prefixWord ++ tailWord_1954238).sum := by decide
  have hdescent : baseEnd_1954238 < baseStart_1954238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954241 : List Nat := [1, 2, 7, 1, 2, 1, 1, 6]
def baseStart_1954241 : Nat := 118140960795 + 1954241 * 2 ^ 59
def prefixEnd_1954241 : Nat := 4983230072969 + 3 ^ 40 * 1954241 * 2
def baseEnd_1954241 : Nat := 148661473736769445451869

theorem tailTrace_1954241 : CollatzResearch.WordTrace tailWord_1954241 prefixEnd_1954241 148661473736769445451869 := by
  unfold tailWord_1954241
  simp only [CollatzResearch.WordTrace]
  refine ⟨71277024913126089636094577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47518016608750726424063051 71277024913126089636094577)
  ·
    refine ⟨53457768684844567227070933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71277024913126089636094577 53457768684844567227070933)
    ·
      refine ⟨1252916453551044544384475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 53457768684844567227070933 1252916453551044544384475)
      ·
        refine ⟨1879374680326566816576713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1252916453551044544384475 1879374680326566816576713)
        ·
          refine ⟨1409531010244925112432535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1879374680326566816576713 1409531010244925112432535)
          ·
            refine ⟨2114296515367387668648803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409531010244925112432535 2114296515367387668648803)
            ·
              refine ⟨3171444773051081502973205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114296515367387668648803 3171444773051081502973205)
              ·
                refine ⟨148661473736769445451869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3171444773051081502973205 148661473736769445451869)
                ·
                  rfl

theorem cell21_1954241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 6].length) (baseStart_1954241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954241 prefixEnd_1954241 := by exact prefixLift 1954241
  have htrace : WordTrace (prefixWord ++ tailWord_1954241) baseStart_1954241 baseEnd_1954241 := by
    simpa [prefixWord, tailWord_1954241, baseEnd_1954241] using wordTrace_append hprefix tailTrace_1954241
  have hstable : (prefixWord ++ tailWord_1954241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954241).length < 2 ^ (prefixWord ++ tailWord_1954241).sum := by decide
  have hdescent : baseEnd_1954241 < baseStart_1954241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954418 : List Nat := [3, 2, 1, 2, 4, 2, 1, 6]
def baseStart_1954418 : Nat := 118140960795 + 1954418 * 2 ^ 59
def prefixEnd_1954418 : Nat := 4983230072969 + 3 ^ 40 * 1954418 * 2
def baseEnd_1954418 : Nat := 148674938340598453968415

theorem tailTrace_1954418 : CollatzResearch.WordTrace tailWord_1954418 prefixEnd_1954418 148674938340598453968415 := by
  unfold tailWord_1954418
  simp only [CollatzResearch.WordTrace]
  refine ⟨17820870158371212216321977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47522320422323232576858605 17820870158371212216321977)
  ·
    refine ⟨13365652618778409162241483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17820870158371212216321977 13365652618778409162241483)
    ·
      refine ⟨20048478928167613743362225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13365652618778409162241483 20048478928167613743362225)
      ·
        refine ⟨15036359196125710307521669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20048478928167613743362225 15036359196125710307521669)
        ·
          refine ⟨2819317349273570682660313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15036359196125710307521669 2819317349273570682660313)
          ·
            refine ⟨2114488011955178011995235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2819317349273570682660313 2114488011955178011995235)
            ·
              refine ⟨3171732017932767017992853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114488011955178011995235 3171732017932767017992853)
              ·
                refine ⟨148674938340598453968415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3171732017932767017992853 148674938340598453968415)
                ·
                  rfl

theorem cell21_1954418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_1954418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954418 prefixEnd_1954418 := by exact prefixLift 1954418
  have htrace : WordTrace (prefixWord ++ tailWord_1954418) baseStart_1954418 baseEnd_1954418 := by
    simpa [prefixWord, tailWord_1954418, baseEnd_1954418] using wordTrace_append hprefix tailTrace_1954418
  have hstable : (prefixWord ++ tailWord_1954418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954418).length < 2 ^ (prefixWord ++ tailWord_1954418).sum := by decide
  have hdescent : baseEnd_1954418 < baseStart_1954418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954446 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_1954446 : Nat := 118140960795 + 1954446 * 2 ^ 59
def prefixEnd_1954446 : Nat := 4983230072969 + 3 ^ 40 * 1954446 * 2
def baseEnd_1954446 : Nat := 446031205003273535438521

theorem tailTrace_1954446 : CollatzResearch.WordTrace tailWord_1954446 prefixEnd_1954446 446031205003273535438521 := by
  unfold tailWord_1954446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8910562734672926205913399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47523001251588939764871461 8910562734672926205913399)
  ·
    refine ⟨13365844102009389308870099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8910562734672926205913399 13365844102009389308870099)
    ·
      refine ⟨20048766153014083963305149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13365844102009389308870099 20048766153014083963305149)
      ·
        refine ⟨7518287307380281486239431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20048766153014083963305149 7518287307380281486239431)
        ·
          refine ⟨11277430961070422229359147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7518287307380281486239431 11277430961070422229359147)
          ·
            refine ⟨16916146441605633344038721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11277430961070422229359147 16916146441605633344038721)
            ·
              refine ⟨12687109831204225008029041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16916146441605633344038721 12687109831204225008029041)
              ·
                refine ⟨9515332373403168756021781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12687109831204225008029041 9515332373403168756021781)
                ·
                  refine ⟨446031205003273535438521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9515332373403168756021781 446031205003273535438521)
                  ·
                    rfl

theorem cell21_1954446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_1954446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954446 prefixEnd_1954446 := by exact prefixLift 1954446
  have htrace : WordTrace (prefixWord ++ tailWord_1954446) baseStart_1954446 baseEnd_1954446 := by
    simpa [prefixWord, tailWord_1954446, baseEnd_1954446] using wordTrace_append hprefix tailTrace_1954446
  have hstable : (prefixWord ++ tailWord_1954446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954446).length < 2 ^ (prefixWord ++ tailWord_1954446).sum := by decide
  have hdescent : baseEnd_1954446 < baseStart_1954446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954522 : List Nat := [3, 1, 1, 2, 2, 2, 2, 4, 4]
def baseStart_1954522 : Nat := 118140960795 + 1954522 * 2 ^ 59
def prefixEnd_1954522 : Nat := 4983230072969 + 3 ^ 40 * 1954522 * 2
def baseEnd_1954522 : Nat := 446048549238714292171699

theorem tailTrace_1954522 : CollatzResearch.WordTrace tailWord_1954522 prefixEnd_1954522 446048549238714292171699 := by
  unfold tailWord_1954522
  simp only [CollatzResearch.WordTrace]
  refine ⟨17821818456277018656768455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47524849216738716418049213 17821818456277018656768455)
  ·
    refine ⟨26732727684415527985152683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17821818456277018656768455 26732727684415527985152683)
    ·
      refine ⟨40099091526623291977729025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26732727684415527985152683 40099091526623291977729025)
      ·
        refine ⟨30074318644967468983296769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40099091526623291977729025 30074318644967468983296769)
        ·
          refine ⟨22555738983725601737472577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30074318644967468983296769 22555738983725601737472577)
          ·
            refine ⟨16916804237794201303104433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22555738983725601737472577 16916804237794201303104433)
            ·
              refine ⟨12687603178345650977328325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16916804237794201303104433 12687603178345650977328325)
              ·
                refine ⟨2378925595939809558249061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12687603178345650977328325 2378925595939809558249061)
                ·
                  refine ⟨446048549238714292171699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2378925595939809558249061 446048549238714292171699)
                  ·
                    rfl

theorem cell21_1954522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_1954522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954522 prefixEnd_1954522 := by exact prefixLift 1954522
  have htrace : WordTrace (prefixWord ++ tailWord_1954522) baseStart_1954522 baseEnd_1954522 := by
    simpa [prefixWord, tailWord_1954522, baseEnd_1954522] using wordTrace_append hprefix tailTrace_1954522
  have hstable : (prefixWord ++ tailWord_1954522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954522).length < 2 ^ (prefixWord ++ tailWord_1954522).sum := by decide
  have hdescent : baseEnd_1954522 < baseStart_1954522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954677 : List Nat := [1, 3, 4, 1, 1, 2, 3, 3, 3]
def baseStart_1954677 : Nat := 118140960795 + 1954677 * 2 ^ 59
def prefixEnd_1954677 : Nat := 4983230072969 + 3 ^ 40 * 1954677 * 2
def baseEnd_1954677 : Nat := 446083922350468467088049

theorem tailTrace_1954677 : CollatzResearch.WordTrace tailWord_1954677 prefixEnd_1954677 446083922350468467088049 := by
  unfold tailWord_1954677
  simp only [CollatzResearch.WordTrace]
  refine ⟨71292927139546536098966285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47528618093031024065977523 71292927139546536098966285)
  ·
    refine ⟨26734847677329951037112357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71292927139546536098966285 26734847677329951037112357)
    ·
      refine ⟨5012783939499365819458567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26734847677329951037112357 5012783939499365819458567)
      ·
        refine ⟨7519175909249048729187851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5012783939499365819458567 7519175909249048729187851)
        ·
          refine ⟨11278763863873573093781777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7519175909249048729187851 11278763863873573093781777)
          ·
            refine ⟨8459072897905179820336333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11278763863873573093781777 8459072897905179820336333)
            ·
              refine ⟨3172152336714442432626125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8459072897905179820336333 3172152336714442432626125)
              ·
                refine ⟨1189557126267915912234797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3172152336714442432626125 1189557126267915912234797)
                ·
                  refine ⟨446083922350468467088049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1189557126267915912234797 446083922350468467088049)
                  ·
                    rfl

theorem cell21_1954677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_1954677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954677 prefixEnd_1954677 := by exact prefixLift 1954677
  have htrace : WordTrace (prefixWord ++ tailWord_1954677) baseStart_1954677 baseEnd_1954677 := by
    simpa [prefixWord, tailWord_1954677, baseEnd_1954677] using wordTrace_append hprefix tailTrace_1954677
  have hstable : (prefixWord ++ tailWord_1954677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954677).length < 2 ^ (prefixWord ++ tailWord_1954677).sum := by decide
  have hdescent : baseEnd_1954677 < baseStart_1954677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954742 : List Nat := [5, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_1954742 : Nat := 118140960795 + 1954742 * 2 ^ 59
def prefixEnd_1954742 : Nat := 4983230072969 + 3 ^ 40 * 1954742 * 2
def baseEnd_1954742 : Nat := 446098756236042798504583

theorem tailTrace_1954742 : CollatzResearch.WordTrace tailWord_1954742 prefixEnd_1954742 446098756236042798504583 := by
  unfold tailWord_1954742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4455956117769440762505155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47530198589540701466721653 4455956117769440762505155)
  ·
    refine ⟨6683934176654161143757733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4455956117769440762505155 6683934176654161143757733)
    ·
      refine ⟨1253237658122655214454575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6683934176654161143757733 1253237658122655214454575)
      ·
        refine ⟨1879856487183982821681863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1253237658122655214454575 1879856487183982821681863)
        ·
          refine ⟨2819784730775974232522795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1879856487183982821681863 2819784730775974232522795)
          ·
            refine ⟨4229677096163961348784193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2819784730775974232522795 4229677096163961348784193)
            ·
              refine ⟨3172257822122971011588145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4229677096163961348784193 3172257822122971011588145)
              ·
                refine ⟨2379193366592228258691109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3172257822122971011588145 2379193366592228258691109)
                ·
                  refine ⟨446098756236042798504583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2379193366592228258691109 446098756236042798504583)
                  ·
                    rfl

theorem cell21_1954742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_1954742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954742 prefixEnd_1954742 := by exact prefixLift 1954742
  have htrace : WordTrace (prefixWord ++ tailWord_1954742) baseStart_1954742 baseEnd_1954742 := by
    simpa [prefixWord, tailWord_1954742, baseEnd_1954742] using wordTrace_append hprefix tailTrace_1954742
  have hstable : (prefixWord ++ tailWord_1954742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954742).length < 2 ^ (prefixWord ++ tailWord_1954742).sum := by decide
  have hdescent : baseEnd_1954742 < baseStart_1954742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954809 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 6]
def baseStart_1954809 : Nat := 118140960795 + 1954809 * 2 ^ 59
def prefixEnd_1954809 : Nat := 4983230072969 + 3 ^ 40 * 1954809 * 2
def baseEnd_1954809 : Nat := 446114046548865570887779

theorem tailTrace_1954809 : CollatzResearch.WordTrace tailWord_1954809 prefixEnd_1954809 446114046548865570887779 := by
  unfold tailWord_1954809
  simp only [CollatzResearch.WordTrace]
  refine ⟨71297741575068322642771481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47531827716712215095180987 71297741575068322642771481)
  ·
    refine ⟨53473306181301241982078611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71297741575068322642771481 53473306181301241982078611)
    ·
      refine ⟨80209959271951862973117917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53473306181301241982078611 80209959271951862973117917)
      ·
        refine ⟨30078734726981948614919219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80209959271951862973117917 30078734726981948614919219)
        ·
          refine ⟨45118102090472922922378829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30078734726981948614919219 45118102090472922922378829)
          ·
            refine ⟨16919288283927346095892061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45118102090472922922378829 16919288283927346095892061)
            ·
              refine ⟨6344733106472754785959523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16919288283927346095892061 6344733106472754785959523)
              ·
                refine ⟨9517099659709132178939285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6344733106472754785959523 9517099659709132178939285)
                ·
                  refine ⟨446114046548865570887779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9517099659709132178939285 446114046548865570887779)
                  ·
                    rfl

theorem cell21_1954809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_1954809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954809 prefixEnd_1954809 := by exact prefixLift 1954809
  have htrace : WordTrace (prefixWord ++ tailWord_1954809) baseStart_1954809 baseEnd_1954809 := by
    simpa [prefixWord, tailWord_1954809, baseEnd_1954809] using wordTrace_append hprefix tailTrace_1954809
  have hstable : (prefixWord ++ tailWord_1954809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954809).length < 2 ^ (prefixWord ++ tailWord_1954809).sum := by decide
  have hdescent : baseEnd_1954809 < baseStart_1954809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954812 : List Nat := [2, 2, 2, 1, 2, 3, 2, 4, 3]
def baseStart_1954812 : Nat := 118140960795 + 1954812 * 2 ^ 59
def prefixEnd_1954812 : Nat := 4983230072969 + 3 ^ 40 * 1954812 * 2
def baseEnd_1954812 : Nat := 446114731189738232337773

theorem tailTrace_1954812 : CollatzResearch.WordTrace tailWord_1954812 prefixEnd_1954812 446114731189738232337773 := by
  unfold tailWord_1954812
  simp only [CollatzResearch.WordTrace]
  refine ⟨35648925497028727077565345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47531900662704969436753793 35648925497028727077565345)
  ·
    refine ⟨26736694122771545308174009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35648925497028727077565345 26736694122771545308174009)
    ·
      refine ⟨20052520592078658981130507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26736694122771545308174009 20052520592078658981130507)
      ·
        refine ⟨30078780888117988471695761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20052520592078658981130507 30078780888117988471695761)
        ·
          refine ⟨22559085666088491353771821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30078780888117988471695761 22559085666088491353771821)
          ·
            refine ⟨8459657124783184257664433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22559085666088491353771821 8459657124783184257664433)
            ·
              refine ⟨6344742843587388193248325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8459657124783184257664433 6344742843587388193248325)
              ·
                refine ⟨1189639283172635286234061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6344742843587388193248325 1189639283172635286234061)
                ·
                  refine ⟨446114731189738232337773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1189639283172635286234061 446114731189738232337773)
                  ·
                    rfl

theorem cell21_1954812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_1954812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954812 prefixEnd_1954812 := by exact prefixLift 1954812
  have htrace : WordTrace (prefixWord ++ tailWord_1954812) baseStart_1954812 baseEnd_1954812 := by
    simpa [prefixWord, tailWord_1954812, baseEnd_1954812] using wordTrace_append hprefix tailTrace_1954812
  have hstable : (prefixWord ++ tailWord_1954812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954812).length < 2 ^ (prefixWord ++ tailWord_1954812).sum := by decide
  have hdescent : baseEnd_1954812 < baseStart_1954812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954840 : List Nat := [2, 1, 2, 3, 2, 3, 1, 7]
def baseStart_1954840 : Nat := 118140960795 + 1954840 * 2 ^ 59
def prefixEnd_1954840 : Nat := 4983230072969 + 3 ^ 40 * 1954840 * 2
def baseEnd_1954840 : Nat := 148707040390405468623683

theorem tailTrace_1954840 : CollatzResearch.WordTrace tailWord_1954840 prefixEnd_1954840 148707040390405468623683 := by
  unfold tailWord_1954840
  simp only [CollatzResearch.WordTrace]
  refine ⟨35649436118978007468574987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47532581491970676624766649 35649436118978007468574987)
  ·
    refine ⟨53474154178467011202862481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35649436118978007468574987 53474154178467011202862481)
    ·
      refine ⟨40105615633850258402146861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53474154178467011202862481 40105615633850258402146861)
      ·
        refine ⟨15039605862693846900805073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40105615633850258402146861 15039605862693846900805073)
        ·
          refine ⟨11279704397020385175603805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15039605862693846900805073 11279704397020385175603805)
          ·
            refine ⟨4229889148882644440851427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11279704397020385175603805 4229889148882644440851427)
            ·
              refine ⟨6344833723323966661277141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4229889148882644440851427 6344833723323966661277141)
              ·
                refine ⟨148707040390405468623683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6344833723323966661277141 148707040390405468623683)
                ·
                  rfl

theorem cell21_1954840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 7].length) (baseStart_1954840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954840 prefixEnd_1954840 := by exact prefixLift 1954840
  have htrace : WordTrace (prefixWord ++ tailWord_1954840) baseStart_1954840 baseEnd_1954840 := by
    simpa [prefixWord, tailWord_1954840, baseEnd_1954840] using wordTrace_append hprefix tailTrace_1954840
  have hstable : (prefixWord ++ tailWord_1954840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954840).length < 2 ^ (prefixWord ++ tailWord_1954840).sum := by decide
  have hdescent : baseEnd_1954840 < baseStart_1954840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954922 : List Nat := [3, 1, 3, 2, 2, 3, 2, 2, 3]
def baseStart_1954922 : Nat := 118140960795 + 1954922 * 2 ^ 59
def prefixEnd_1954922 : Nat := 4983230072969 + 3 ^ 40 * 1954922 * 2
def baseEnd_1954922 : Nat := 446139834688402485504215

theorem tailTrace_1954922 : CollatzResearch.WordTrace tailWord_1954922 prefixEnd_1954922 446139834688402485504215 := by
  unfold tailWord_1954922
  simp only [CollatzResearch.WordTrace]
  refine ⟨17825465755914735735408755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47534575349105961961090013 17825465755914735735408755)
  ·
    refine ⟨26738198633872103603113133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17825465755914735735408755 26738198633872103603113133)
    ·
      refine ⟨10026824487702038851167425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26738198633872103603113133 10026824487702038851167425)
      ·
        refine ⟨7520118365776529138375569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10026824487702038851167425 7520118365776529138375569)
        ·
          refine ⟨5640088774332396853781677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7520118365776529138375569 5640088774332396853781677)
          ·
            refine ⟨2115033290374648820168129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5640088774332396853781677 2115033290374648820168129)
            ·
              refine ⟨1586274967780986615126097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2115033290374648820168129 1586274967780986615126097)
              ·
                refine ⟨1189706225835739961344573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1586274967780986615126097 1189706225835739961344573)
                ·
                  refine ⟨446139834688402485504215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1189706225835739961344573 446139834688402485504215)
                  ·
                    rfl

theorem cell21_1954922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_1954922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1954922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1954922 prefixEnd_1954922 := by exact prefixLift 1954922
  have htrace : WordTrace (prefixWord ++ tailWord_1954922) baseStart_1954922 baseEnd_1954922 := by
    simpa [prefixWord, tailWord_1954922, baseEnd_1954922] using wordTrace_append hprefix tailTrace_1954922
  have hstable : (prefixWord ++ tailWord_1954922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954922).length < 2 ^ (prefixWord ++ tailWord_1954922).sum := by decide
  have hdescent : baseEnd_1954922 < baseStart_1954922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955009 : List Nat := [1, 2, 6, 1, 1, 2, 1, 7]
def baseStart_1955009 : Nat := 118140960795 + 1955009 * 2 ^ 59
def prefixEnd_1955009 : Nat := 4983230072969 + 3 ^ 40 * 1955009 * 2
def baseEnd_1955009 : Nat := 148719896424569889184679

theorem tailTrace_1955009 : CollatzResearch.WordTrace tailWord_1955009 prefixEnd_1955009 148719896424569889184679 := by
  unfold tailWord_1955009
  simp only [CollatzResearch.WordTrace]
  refine ⟨71305036174343756800052081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47536690782895837866701387 71305036174343756800052081)
  ·
    refine ⟨53478777130757817600039061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71305036174343756800052081 53478777130757817600039061)
    ·
      refine ⟨2506817678004272700001831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53478777130757817600039061 2506817678004272700001831)
      ·
        refine ⟨3760226517006409050002747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2506817678004272700001831 3760226517006409050002747)
        ·
          refine ⟨5640339775509613575004121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3760226517006409050002747 5640339775509613575004121)
          ·
            refine ⟨4230254831632210181253091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5640339775509613575004121 4230254831632210181253091)
            ·
              refine ⟨6345382247448315271879637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4230254831632210181253091 6345382247448315271879637)
              ·
                refine ⟨148719896424569889184679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6345382247448315271879637 148719896424569889184679)
                ·
                  rfl

theorem cell21_1955009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 7].length) (baseStart_1955009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955009 prefixEnd_1955009 := by exact prefixLift 1955009
  have htrace : WordTrace (prefixWord ++ tailWord_1955009) baseStart_1955009 baseEnd_1955009 := by
    simpa [prefixWord, tailWord_1955009, baseEnd_1955009] using wordTrace_append hprefix tailTrace_1955009
  have hstable : (prefixWord ++ tailWord_1955009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955009).length < 2 ^ (prefixWord ++ tailWord_1955009).sum := by decide
  have hdescent : baseEnd_1955009 < baseStart_1955009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955023 : List Nat := [1, 1, 2, 1, 1, 3, 2, 7, 3]
def baseStart_1955023 : Nat := 118140960795 + 1955023 * 2 ^ 59
def prefixEnd_1955023 : Nat := 4983230072969 + 3 ^ 40 * 1955023 * 2
def baseEnd_1955023 : Nat := 446162884264448754320675

theorem tailTrace_1955023 : CollatzResearch.WordTrace tailWord_1955023 prefixEnd_1955023 446162884264448754320675 := by
  unfold tailWord_1955023
  simp only [CollatzResearch.WordTrace]
  refine ⟨71305546796293037191061723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47537031197528691460707815 71305546796293037191061723)
  ·
    refine ⟨106958320194439555786592585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71305546796293037191061723 106958320194439555786592585)
    ·
      refine ⟨80218740145829666839944439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106958320194439555786592585 80218740145829666839944439)
      ·
        refine ⟨120328110218744500259916659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80218740145829666839944439 120328110218744500259916659)
        ·
          refine ⟨180492165328116750389874989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120328110218744500259916659 180492165328116750389874989)
          ·
            refine ⟨67684561998043781396203121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180492165328116750389874989 67684561998043781396203121)
            ·
              refine ⟨50763421498532836047152341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67684561998043781396203121 50763421498532836047152341)
              ·
                refine ⟨1189767691371863344855133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 50763421498532836047152341 1189767691371863344855133)
                ·
                  refine ⟨446162884264448754320675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1189767691371863344855133 446162884264448754320675)
                  ·
                    rfl

theorem cell21_1955023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 3].length) (baseStart_1955023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955023 prefixEnd_1955023 := by exact prefixLift 1955023
  have htrace : WordTrace (prefixWord ++ tailWord_1955023) baseStart_1955023 baseEnd_1955023 := by
    simpa [prefixWord, tailWord_1955023, baseEnd_1955023] using wordTrace_append hprefix tailTrace_1955023
  have hstable : (prefixWord ++ tailWord_1955023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955023).length < 2 ^ (prefixWord ++ tailWord_1955023).sum := by decide
  have hdescent : baseEnd_1955023 < baseStart_1955023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955051 : List Nat := [1, 1, 1, 1, 2, 6, 1, 8]
def baseStart_1955051 : Nat := 118140960795 + 1955051 * 2 ^ 59
def prefixEnd_1955051 : Nat := 4983230072969 + 3 ^ 40 * 1955051 * 2
def baseEnd_1955051 : Nat := 148723091415308975951317

theorem tailTrace_1955051 : CollatzResearch.WordTrace tailWord_1955051 prefixEnd_1955051 148723091415308975951317 := by
  unfold tailWord_1955051
  simp only [CollatzResearch.WordTrace]
  refine ⟨71306568040191597973081007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47537712026794398648720671 71306568040191597973081007)
  ·
    refine ⟨106959852060287396959621511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71306568040191597973081007 106959852060287396959621511)
    ·
      refine ⟨160439778090431095439432267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106959852060287396959621511 160439778090431095439432267)
      ·
        refine ⟨240659667135646643159148401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160439778090431095439432267 240659667135646643159148401)
        ·
          refine ⟨180494750351734982369361301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240659667135646643159148401 180494750351734982369361301)
          ·
            refine ⟨8460691422737577298563811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180494750351734982369361301 8460691422737577298563811)
            ·
              refine ⟨12691037134106365947845717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8460691422737577298563811 12691037134106365947845717)
              ·
                refine ⟨148723091415308975951317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12691037134106365947845717 148723091415308975951317)
                ·
                  rfl

theorem cell21_1955051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 8].length) (baseStart_1955051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955051 prefixEnd_1955051 := by exact prefixLift 1955051
  have htrace : WordTrace (prefixWord ++ tailWord_1955051) baseStart_1955051 baseEnd_1955051 := by
    simpa [prefixWord, tailWord_1955051, baseEnd_1955051] using wordTrace_append hprefix tailTrace_1955051
  have hstable : (prefixWord ++ tailWord_1955051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955051).length < 2 ^ (prefixWord ++ tailWord_1955051).sum := by decide
  have hdescent : baseEnd_1955051 < baseStart_1955051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955178 : List Nat := [3, 1, 3, 3, 2, 2, 2, 5]
def baseStart_1955178 : Nat := 118140960795 + 1955178 * 2 ^ 59
def prefixEnd_1955178 : Nat := 4983230072969 + 3 ^ 40 * 1955178 * 2
def baseEnd_1955178 : Nat := 148732752458734309745675

theorem tailTrace_1955178 : CollatzResearch.WordTrace tailWord_1955178 prefixEnd_1955178 148732752458734309745675 := by
  unfold tailWord_1955178
  simp only [CollatzResearch.WordTrace]
  refine ⟨17827800027682874665738547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47540800073820999108636125 17827800027682874665738547)
  ·
    refine ⟨26741700041524311998607821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17827800027682874665738547 26741700041524311998607821)
    ·
      refine ⟨10028137515571616999477933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26741700041524311998607821 10028137515571616999477933)
      ·
        refine ⟨3760551568339356374804225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10028137515571616999477933 3760551568339356374804225)
        ·
          refine ⟨2820413676254517281103169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3760551568339356374804225 2820413676254517281103169)
          ·
            refine ⟨2115310257190887960827377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2820413676254517281103169 2115310257190887960827377)
            ·
              refine ⟨1586482692893165970620533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2115310257190887960827377 1586482692893165970620533)
              ·
                refine ⟨148732752458734309745675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1586482692893165970620533 148732752458734309745675)
                ·
                  rfl

theorem cell21_1955178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_1955178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955178 prefixEnd_1955178 := by exact prefixLift 1955178
  have htrace : WordTrace (prefixWord ++ tailWord_1955178) baseStart_1955178 baseEnd_1955178 := by
    simpa [prefixWord, tailWord_1955178, baseEnd_1955178] using wordTrace_append hprefix tailTrace_1955178
  have hstable : (prefixWord ++ tailWord_1955178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955178).length < 2 ^ (prefixWord ++ tailWord_1955178).sum := by decide
  have hdescent : baseEnd_1955178 < baseStart_1955178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955203 : List Nat := [1, 1, 1, 3, 5, 1, 9]
def baseStart_1955203 : Nat := 118140960795 + 1955203 * 2 ^ 59
def prefixEnd_1955203 : Nat := 4983230072969 + 3 ^ 40 * 1955203 * 2
def baseEnd_1955203 : Nat := 49578218079645382368923

theorem tailTrace_1955203 : CollatzResearch.WordTrace tailWord_1955203 prefixEnd_1955203 49578218079645382368923 := by
  unfold tailWord_1955203
  simp only [CollatzResearch.WordTrace]
  refine ⟨71312111935640927932614263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47541407957093951955076175 71312111935640927932614263)
  ·
    refine ⟨106968167903461391898921395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71312111935640927932614263 106968167903461391898921395)
    ·
      refine ⟨160452251855192087848382093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106968167903461391898921395 160452251855192087848382093)
      ·
        refine ⟨60169594445697032943143285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160452251855192087848382093 60169594445697032943143285)
        ·
          refine ⟨5640899479284096838419683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60169594445697032943143285 5640899479284096838419683)
          ·
            refine ⟨8461349218926145257629525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5640899479284096838419683 8461349218926145257629525)
            ·
              refine ⟨49578218079645382368923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8461349218926145257629525 49578218079645382368923)
              ·
                rfl

theorem cell21_1955203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 9].length) (baseStart_1955203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955203 prefixEnd_1955203 := by exact prefixLift 1955203
  have htrace : WordTrace (prefixWord ++ tailWord_1955203) baseStart_1955203 baseEnd_1955203 := by
    simpa [prefixWord, tailWord_1955203, baseEnd_1955203] using wordTrace_append hprefix tailTrace_1955203
  have hstable : (prefixWord ++ tailWord_1955203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955203).length < 2 ^ (prefixWord ++ tailWord_1955203).sum := by decide
  have hdescent : baseEnd_1955203 < baseStart_1955203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955209 : List Nat := [1, 2, 1, 1, 7, 1, 3, 2, 3]
def baseStart_1955209 : Nat := 118140960795 + 1955209 * 2 ^ 59
def prefixEnd_1955209 : Nat := 4983230072969 + 3 ^ 40 * 1955209 * 2
def baseEnd_1955209 : Nat := 446205331998553764220295

theorem tailTrace_1955209 : CollatzResearch.WordTrace tailWord_1955209 prefixEnd_1955209 446205331998553764220295 := by
  unfold tailWord_1955209
  simp only [CollatzResearch.WordTrace]
  refine ⟨71312330773619190957332681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47541553849079460638221787 71312330773619190957332681)
  ·
    refine ⟨53484248080214393217999511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71312330773619190957332681 53484248080214393217999511)
    ·
      refine ⟨80226372120321589826999267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53484248080214393217999511 80226372120321589826999267)
      ·
        refine ⟨120339558180482384740498901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80226372120321589826999267 120339558180482384740498901)
        ·
          refine ⟨2820458394855055892355443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 120339558180482384740498901 2820458394855055892355443)
          ·
            refine ⟨4230687592282583838533165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2820458394855055892355443 4230687592282583838533165)
            ·
              refine ⟨1586507847105968939449937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4230687592282583838533165 1586507847105968939449937)
              ·
                refine ⟨1189880885329476704587453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1586507847105968939449937 1189880885329476704587453)
                ·
                  refine ⟨446205331998553764220295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1189880885329476704587453 446205331998553764220295)
                  ·
                    rfl

theorem cell21_1955209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 3].length) (baseStart_1955209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955209 prefixEnd_1955209 := by exact prefixLift 1955209
  have htrace : WordTrace (prefixWord ++ tailWord_1955209) baseStart_1955209 baseEnd_1955209 := by
    simpa [prefixWord, tailWord_1955209, baseEnd_1955209] using wordTrace_append hprefix tailTrace_1955209
  have hstable : (prefixWord ++ tailWord_1955209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955209).length < 2 ^ (prefixWord ++ tailWord_1955209).sum := by decide
  have hdescent : baseEnd_1955209 < baseStart_1955209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955220 : List Nat := [2, 4, 2, 1, 2, 1, 1, 8]
def baseStart_1955220 : Nat := 118140960795 + 1955220 * 2 ^ 59
def prefixEnd_1955220 : Nat := 4983230072969 + 3 ^ 40 * 1955220 * 2
def baseEnd_1955220 : Nat := 148735947449473396512313

theorem tailTrace_1955220 : CollatzResearch.WordTrace tailWord_1955220 prefixEnd_1955220 148735947449473396512313 := by
  unfold tailWord_1955220
  simp only [CollatzResearch.WordTrace]
  refine ⟨35656365988289669917991557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47541821317719559890655409 35656365988289669917991557)
  ·
    refine ⟨6685568622804313109623417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35656365988289669917991557 6685568622804313109623417)
    ·
      refine ⟨5014176467103234832217563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6685568622804313109623417 5014176467103234832217563)
      ·
        refine ⟨7521264700654852248326345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5014176467103234832217563 7521264700654852248326345)
        ·
          refine ⟨5640948525491139186244759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7521264700654852248326345 5640948525491139186244759)
          ·
            refine ⟨8461422788236708779367139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5640948525491139186244759 8461422788236708779367139)
            ·
              refine ⟨12692134182355063169050709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8461422788236708779367139 12692134182355063169050709)
              ·
                refine ⟨148735947449473396512313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12692134182355063169050709 148735947449473396512313)
                ·
                  rfl

theorem cell21_1955220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 8].length) (baseStart_1955220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955220 prefixEnd_1955220 := by exact prefixLift 1955220
  have htrace : WordTrace (prefixWord ++ tailWord_1955220) baseStart_1955220 baseEnd_1955220 := by
    simpa [prefixWord, tailWord_1955220, baseEnd_1955220] using wordTrace_append hprefix tailTrace_1955220
  have hstable : (prefixWord ++ tailWord_1955220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955220).length < 2 ^ (prefixWord ++ tailWord_1955220).sum := by decide
  have hdescent : baseEnd_1955220 < baseStart_1955220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955248 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 6]
def baseStart_1955248 : Nat := 118140960795 + 1955248 * 2 ^ 59
def prefixEnd_1955248 : Nat := 4983230072969 + 3 ^ 40 * 1955248 * 2
def baseEnd_1955248 : Nat := 446214232329898363070215

theorem tailTrace_1955248 : CollatzResearch.WordTrace tailWord_1955248 prefixEnd_1955248 446214232329898363070215 := by
  unfold tailWord_1955248
  simp only [CollatzResearch.WordTrace]
  refine ⟨35656876610238950309001199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47542502146985267078668265 35656876610238950309001199)
  ·
    refine ⟨53485314915358425463501799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35656876610238950309001199 53485314915358425463501799)
    ·
      refine ⟨80227972373037638195252699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53485314915358425463501799 80227972373037638195252699)
      ·
        refine ⟨120341958559556457292879049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80227972373037638195252699 120341958559556457292879049)
        ·
          refine ⟨90256468919667342969659287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120341958559556457292879049 90256468919667342969659287)
          ·
            refine ⟨135384703379501014454488931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90256468919667342969659287 135384703379501014454488931)
            ·
              refine ⟨203077055069251521681733397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135384703379501014454488931 203077055069251521681733397)
              ·
                refine ⟨9519236956371165078831253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 203077055069251521681733397 9519236956371165078831253)
                ·
                  refine ⟨446214232329898363070215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9519236956371165078831253 446214232329898363070215)
                  ·
                    rfl

theorem cell21_1955248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_1955248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955248 prefixEnd_1955248 := by exact prefixLift 1955248
  have htrace : WordTrace (prefixWord ++ tailWord_1955248) baseStart_1955248 baseEnd_1955248 := by
    simpa [prefixWord, tailWord_1955248, baseEnd_1955248] using wordTrace_append hprefix tailTrace_1955248
  have hstable : (prefixWord ++ tailWord_1955248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955248).length < 2 ^ (prefixWord ++ tailWord_1955248).sum := by decide
  have hdescent : baseEnd_1955248 < baseStart_1955248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955279 : List Nat := [1, 1, 2, 1, 1, 4, 5, 6]
def baseStart_1955279 : Nat := 118140960795 + 1955279 * 2 ^ 59
def prefixEnd_1955279 : Nat := 4983230072969 + 3 ^ 40 * 1955279 * 2
def baseEnd_1955279 : Nat := 148740435650749732684495

theorem tailTrace_1955279 : CollatzResearch.WordTrace tailWord_1955279 prefixEnd_1955279 148740435650749732684495 := by
  unfold tailWord_1955279
  simp only [CollatzResearch.WordTrace]
  refine ⟨71314883883365592912380891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47543255922243728608253927 71314883883365592912380891)
  ·
    refine ⟨106972325825048389368571337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71314883883365592912380891 106972325825048389368571337)
    ·
      refine ⟨80229244368786292026428503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106972325825048389368571337 80229244368786292026428503)
      ·
        refine ⟨120343866553179438039642755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80229244368786292026428503 120343866553179438039642755)
        ·
          refine ⟨180515799829769157059464133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120343866553179438039642755 180515799829769157059464133)
          ·
            refine ⟨33846712468081716948649525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180515799829769157059464133 33846712468081716948649525)
            ·
              refine ⟨3173129293882660963935893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33846712468081716948649525 3173129293882660963935893)
              ·
                refine ⟨148740435650749732684495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3173129293882660963935893 148740435650749732684495)
                ·
                  rfl

theorem cell21_1955279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 6].length) (baseStart_1955279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955279 prefixEnd_1955279 := by exact prefixLift 1955279
  have htrace : WordTrace (prefixWord ++ tailWord_1955279) baseStart_1955279 baseEnd_1955279 := by
    simpa [prefixWord, tailWord_1955279, baseEnd_1955279] using wordTrace_append hprefix tailTrace_1955279
  have hstable : (prefixWord ++ tailWord_1955279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955279).length < 2 ^ (prefixWord ++ tailWord_1955279).sum := by decide
  have hdescent : baseEnd_1955279 < baseStart_1955279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955310 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_1955310 : Nat := 118140960795 + 1955310 * 2 ^ 59
def prefixEnd_1955310 : Nat := 4983230072969 + 3 ^ 40 * 1955310 * 2
def baseEnd_1955310 : Nat := 446228381574600033036755

theorem tailTrace_1955310 : CollatzResearch.WordTrace tailWord_1955310 prefixEnd_1955310 446228381574600033036755 := by
  unfold tailWord_1955310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8914501818281660650844923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47544009697502190137839589 8914501818281660650844923)
  ·
    refine ⟨13371752727422490976267385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8914501818281660650844923 13371752727422490976267385)
    ·
      refine ⟨10028814545566868232200539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13371752727422490976267385 10028814545566868232200539)
      ·
        refine ⟨15043221818350302348300809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10028814545566868232200539 15043221818350302348300809)
        ·
          refine ⟨11282416363762726761225607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15043221818350302348300809 11282416363762726761225607)
          ·
            refine ⟨16923624545644090141838411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11282416363762726761225607 16923624545644090141838411)
            ·
              refine ⟨25385436818466135212757617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16923624545644090141838411 25385436818466135212757617)
              ·
                refine ⟨19039077613849601409568213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25385436818466135212757617 19039077613849601409568213)
                ·
                  refine ⟨446228381574600033036755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19039077613849601409568213 446228381574600033036755)
                  ·
                    rfl

theorem cell21_1955310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_1955310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955310 prefixEnd_1955310 := by exact prefixLift 1955310
  have htrace : WordTrace (prefixWord ++ tailWord_1955310) baseStart_1955310 baseEnd_1955310 := by
    simpa [prefixWord, tailWord_1955310, baseEnd_1955310] using wordTrace_append hprefix tailTrace_1955310
  have hstable : (prefixWord ++ tailWord_1955310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955310).length < 2 ^ (prefixWord ++ tailWord_1955310).sum := by decide
  have hdescent : baseEnd_1955310 < baseStart_1955310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955434 : List Nat := [3, 1, 3, 2, 1, 3, 2, 2, 4]
def baseStart_1955434 : Nat := 118140960795 + 1955434 * 2 ^ 59
def prefixEnd_1955434 : Nat := 4983230072969 + 3 ^ 40 * 1955434 * 2
def baseEnd_1955434 : Nat := 446256680064003372969835

theorem tailTrace_1955434 : CollatzResearch.WordTrace tailWord_1955434 prefixEnd_1955434 446256680064003372969835 := by
  unfold tailWord_1955434
  simp only [CollatzResearch.WordTrace]
  refine ⟨17830134299451013596068339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47547024798536036256182237 17830134299451013596068339)
  ·
    refine ⟨26745201449176520394102509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17830134299451013596068339 26745201449176520394102509)
    ·
      refine ⟨10029450543441195147788441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26745201449176520394102509 10029450543441195147788441)
      ·
        refine ⟨7522087907580896360841331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10029450543441195147788441 7522087907580896360841331)
        ·
          refine ⟨11283131861371344541261997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7522087907580896360841331 11283131861371344541261997)
          ·
            refine ⟨4231174448014254202973249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11283131861371344541261997 4231174448014254202973249)
            ·
              refine ⟨3173380836010690652229937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4231174448014254202973249 3173380836010690652229937)
              ·
                refine ⟨2380035627008017989172453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3173380836010690652229937 2380035627008017989172453)
                ·
                  refine ⟨446256680064003372969835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2380035627008017989172453 446256680064003372969835)
                  ·
                    rfl

theorem cell21_1955434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_1955434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955434 prefixEnd_1955434 := by exact prefixLift 1955434
  have htrace : WordTrace (prefixWord ++ tailWord_1955434) baseStart_1955434 baseEnd_1955434 := by
    simpa [prefixWord, tailWord_1955434, baseEnd_1955434] using wordTrace_append hprefix tailTrace_1955434
  have hstable : (prefixWord ++ tailWord_1955434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955434).length < 2 ^ (prefixWord ++ tailWord_1955434).sum := by decide
  have hdescent : baseEnd_1955434 < baseStart_1955434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955479 : List Nat := [1, 1, 3, 3, 2, 2, 1, 5, 3]
def baseStart_1955479 : Nat := 118140960795 + 1955479 * 2 ^ 59
def prefixEnd_1955479 : Nat := 4983230072969 + 3 ^ 40 * 1955479 * 2
def baseEnd_1955479 : Nat := 446266949677093294719743

theorem tailTrace_1955479 : CollatzResearch.WordTrace tailWord_1955479 prefixEnd_1955479 446266949677093294719743 := by
  unfold tailWord_1955479
  simp only [CollatzResearch.WordTrace]
  refine ⟨71322178482641027069661491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47548118988427351379774327 71322178482641027069661491)
  ·
    refine ⟨106983267723961540604492237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71322178482641027069661491 106983267723961540604492237)
    ·
      refine ⟨40118725396485577726684589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106983267723961540604492237 40118725396485577726684589)
      ·
        refine ⟨15044522023682091647506721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40118725396485577726684589 15044522023682091647506721)
        ·
          refine ⟨11283391517761568735630041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15044522023682091647506721 11283391517761568735630041)
          ·
            refine ⟨8462543638321176551722531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11283391517761568735630041 8462543638321176551722531)
            ·
              refine ⟨12693815457481764827583797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8462543638321176551722531 12693815457481764827583797)
              ·
                refine ⟨1190045199138915452585981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12693815457481764827583797 1190045199138915452585981)
                ·
                  refine ⟨446266949677093294719743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190045199138915452585981 446266949677093294719743)
                  ·
                    rfl

theorem cell21_1955479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 3].length) (baseStart_1955479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955479 prefixEnd_1955479 := by exact prefixLift 1955479
  have htrace : WordTrace (prefixWord ++ tailWord_1955479) baseStart_1955479 baseEnd_1955479 := by
    simpa [prefixWord, tailWord_1955479, baseEnd_1955479] using wordTrace_append hprefix tailTrace_1955479
  have hstable : (prefixWord ++ tailWord_1955479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955479).length < 2 ^ (prefixWord ++ tailWord_1955479).sum := by decide
  have hdescent : baseEnd_1955479 < baseStart_1955479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955493 : List Nat := [1, 3, 1, 2, 1, 2, 5, 2, 4]
def baseStart_1955493 : Nat := 118140960795 + 1955493 * 2 ^ 59
def prefixEnd_1955493 : Nat := 4983230072969 + 3 ^ 40 * 1955493 * 2
def baseEnd_1955493 : Nat := 446270144667832381486381

theorem tailTrace_1955493 : CollatzResearch.WordTrace tailWord_1955493 prefixEnd_1955493 446270144667832381486381 := by
  unfold tailWord_1955493
  simp only [CollatzResearch.WordTrace]
  refine ⟨71322689104590307460671133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47548459403060204973780755 71322689104590307460671133)
  ·
    refine ⟨26746008414221365297751675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71322689104590307460671133 26746008414221365297751675)
    ·
      refine ⟨40119012621332047946627513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26746008414221365297751675 40119012621332047946627513)
      ·
        refine ⟨30089259465999035959970635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40119012621332047946627513 30089259465999035959970635)
        ·
          refine ⟨45133889198998553939955953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30089259465999035959970635 45133889198998553939955953)
          ·
            refine ⟨33850416899248915454966965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45133889198998553939955953 33850416899248915454966965)
            ·
              refine ⟨3173476584304585823903153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33850416899248915454966965 3173476584304585823903153)
              ·
                refine ⟨2380107438228439367927365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3173476584304585823903153 2380107438228439367927365)
                ·
                  refine ⟨446270144667832381486381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2380107438228439367927365 446270144667832381486381)
                  ·
                    rfl

theorem cell21_1955493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_1955493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955493 prefixEnd_1955493 := by exact prefixLift 1955493
  have htrace : WordTrace (prefixWord ++ tailWord_1955493) baseStart_1955493 baseEnd_1955493 := by
    simpa [prefixWord, tailWord_1955493, baseEnd_1955493] using wordTrace_append hprefix tailTrace_1955493
  have hstable : (prefixWord ++ tailWord_1955493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955493).length < 2 ^ (prefixWord ++ tailWord_1955493).sum := by decide
  have hdescent : baseEnd_1955493 < baseStart_1955493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955552 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 6]
def baseStart_1955552 : Nat := 118140960795 + 1955552 * 2 ^ 59
def prefixEnd_1955552 : Nat := 4983230072969 + 3 ^ 40 * 1955552 * 2
def baseEnd_1955552 : Nat := 446283609271661390002927

theorem tailTrace_1955552 : CollatzResearch.WordTrace tailWord_1955552 prefixEnd_1955552 446283609271661390002927 := by
  unfold tailWord_1955552
  simp only [CollatzResearch.WordTrace]
  refine ⟨35662420505688280268534455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47549894007584373691379273 35662420505688280268534455)
  ·
    refine ⟨53493630758532420402801683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35662420505688280268534455 53493630758532420402801683)
    ·
      refine ⟨80240446137798630604202525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53493630758532420402801683 80240446137798630604202525)
      ·
        refine ⟨30090167301674486476575947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80240446137798630604202525 30090167301674486476575947)
        ·
          refine ⟨45135250952511729714863921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30090167301674486476575947 45135250952511729714863921)
          ·
            refine ⟨33851438214383797286147941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45135250952511729714863921 33851438214383797286147941)
            ·
              refine ⟨6347144665196961991152739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33851438214383797286147941 6347144665196961991152739)
              ·
                refine ⟨9520716997795442986729109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6347144665196961991152739 9520716997795442986729109)
                ·
                  refine ⟨446283609271661390002927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9520716997795442986729109 446283609271661390002927)
                  ·
                    rfl

theorem cell21_1955552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_1955552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955552 prefixEnd_1955552 := by exact prefixLift 1955552
  have htrace : WordTrace (prefixWord ++ tailWord_1955552) baseStart_1955552 baseEnd_1955552 := by
    simpa [prefixWord, tailWord_1955552, baseEnd_1955552] using wordTrace_append hprefix tailTrace_1955552
  have hstable : (prefixWord ++ tailWord_1955552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955552).length < 2 ^ (prefixWord ++ tailWord_1955552).sum := by decide
  have hdescent : baseEnd_1955552 < baseStart_1955552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955569 : List Nat := [1, 2, 2, 2, 2, 4, 1, 3, 4]
def baseStart_1955569 : Nat := 118140960795 + 1955569 * 2 ^ 59
def prefixEnd_1955569 : Nat := 4983230072969 + 3 ^ 40 * 1955569 * 2
def baseEnd_1955569 : Nat := 446287488903273138219559

theorem tailTrace_1955569 : CollatzResearch.WordTrace tailWord_1955569 prefixEnd_1955569 446287488903273138219559 := by
  unfold tailWord_1955569
  simp only [CollatzResearch.WordTrace]
  refine ⟨71325461052314972440437761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47550307368209981626958507 71325461052314972440437761)
  ·
    refine ⟨53494095789236229330328321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71325461052314972440437761 53494095789236229330328321)
    ·
      refine ⟨40120571841927171997746241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53494095789236229330328321 40120571841927171997746241)
      ·
        refine ⟨30090428881445378998309681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40120571841927171997746241 30090428881445378998309681)
        ·
          refine ⟨22567821661084034248732261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30090428881445378998309681 22567821661084034248732261)
          ·
            refine ⟨4231466561453256421637299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22567821661084034248732261 4231466561453256421637299)
            ·
              refine ⟨6347199842179884632455949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231466561453256421637299 6347199842179884632455949)
              ·
                refine ⟨2380199940817456737170981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6347199842179884632455949 2380199940817456737170981)
                ·
                  refine ⟨446287488903273138219559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2380199940817456737170981 446287488903273138219559)
                  ·
                    rfl

theorem cell21_1955569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_1955569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955569 prefixEnd_1955569 := by exact prefixLift 1955569
  have htrace : WordTrace (prefixWord ++ tailWord_1955569) baseStart_1955569 baseEnd_1955569 := by
    simpa [prefixWord, tailWord_1955569, baseEnd_1955569] using wordTrace_append hprefix tailTrace_1955569
  have hstable : (prefixWord ++ tailWord_1955569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955569).length < 2 ^ (prefixWord ++ tailWord_1955569).sum := by decide
  have hdescent : baseEnd_1955569 < baseStart_1955569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955735 : List Nat := [1, 1, 3, 3, 1, 4, 2, 6]
def baseStart_1955735 : Nat := 118140960795 + 1955735 * 2 ^ 59
def prefixEnd_1955735 : Nat := 4983230072969 + 3 ^ 40 * 1955735 * 2
def baseEnd_1955735 : Nat := 148775124121631246150851

theorem tailTrace_1955735 : CollatzResearch.WordTrace tailWord_1955735 prefixEnd_1955735 148775124121631246150851 := by
  unfold tailWord_1955735
  simp only [CollatzResearch.WordTrace]
  refine ⟨71331515569713582790980659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47554343713142388527320439 71331515569713582790980659)
  ·
    refine ⟨106997273354570374186470989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71331515569713582790980659 106997273354570374186470989)
    ·
      refine ⟨40123977507963890319926621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106997273354570374186470989 40123977507963890319926621)
      ·
        refine ⟨15046491565486458869972483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40123977507963890319926621 15046491565486458869972483)
        ·
          refine ⟨22569737348229688304958725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15046491565486458869972483 22569737348229688304958725)
          ·
            refine ⟨4231825752793066557179761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22569737348229688304958725 4231825752793066557179761)
            ·
              refine ⟨3173869314594799917884821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4231825752793066557179761 3173869314594799917884821)
              ·
                refine ⟨148775124121631246150851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3173869314594799917884821 148775124121631246150851)
                ·
                  rfl

theorem cell21_1955735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 6].length) (baseStart_1955735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955735 prefixEnd_1955735 := by exact prefixLift 1955735
  have htrace : WordTrace (prefixWord ++ tailWord_1955735) baseStart_1955735 baseEnd_1955735 := by
    simpa [prefixWord, tailWord_1955735, baseEnd_1955735] using wordTrace_append hprefix tailTrace_1955735
  have hstable : (prefixWord ++ tailWord_1955735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955735).length < 2 ^ (prefixWord ++ tailWord_1955735).sum := by decide
  have hdescent : baseEnd_1955735 < baseStart_1955735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955738 : List Nat := [3, 1, 1, 4, 2, 1, 4, 1, 4]
def baseStart_1955738 : Nat := 118140960795 + 1955738 * 2 ^ 59
def prefixEnd_1955738 : Nat := 4983230072969 + 3 ^ 40 * 1955738 * 2
def baseEnd_1955738 : Nat := 446326057005766399902547

theorem tailTrace_1955738 : CollatzResearch.WordTrace tailWord_1955738 prefixEnd_1955738 446326057005766399902547 := by
  unfold tailWord_1955738
  simp only [CollatzResearch.WordTrace]
  refine ⟨17832906247175678575834967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47554416659135142868893245 17832906247175678575834967)
  ·
    refine ⟨26749359370763517863752451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17832906247175678575834967 26749359370763517863752451)
    ·
      refine ⟨40124039056145276795628677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26749359370763517863752451 40124039056145276795628677)
      ·
        refine ⟨7523257323027239399180377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40124039056145276795628677 7523257323027239399180377)
        ·
          refine ⟨5642442992270429549385283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7523257323027239399180377 5642442992270429549385283)
          ·
            refine ⟨8463664488405644324077925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5642442992270429549385283 8463664488405644324077925)
            ·
              refine ⟨1586937091576058310764611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8463664488405644324077925 1586937091576058310764611)
              ·
                refine ⟨2380405637364087466146917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1586937091576058310764611 2380405637364087466146917)
                ·
                  refine ⟨446326057005766399902547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2380405637364087466146917 446326057005766399902547)
                  ·
                    rfl

theorem cell21_1955738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_1955738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955738 prefixEnd_1955738 := by exact prefixLift 1955738
  have htrace : WordTrace (prefixWord ++ tailWord_1955738) baseStart_1955738 baseEnd_1955738 := by
    simpa [prefixWord, tailWord_1955738, baseEnd_1955738] using wordTrace_append hprefix tailTrace_1955738
  have hstable : (prefixWord ++ tailWord_1955738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955738).length < 2 ^ (prefixWord ++ tailWord_1955738).sum := by decide
  have hdescent : baseEnd_1955738 < baseStart_1955738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955749 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 5]
def baseStart_1955749 : Nat := 118140960795 + 1955749 * 2 ^ 59
def prefixEnd_1955749 : Nat := 4983230072969 + 3 ^ 40 * 1955749 * 2
def baseEnd_1955749 : Nat := 446328567355632825219191

theorem tailTrace_1955749 : CollatzResearch.WordTrace tailWord_1955749 prefixEnd_1955749 446328567355632825219191 := by
  unfold tailWord_1955749
  simp only [CollatzResearch.WordTrace]
  refine ⟨71332026191662863181990301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47554684127775242121326867 71332026191662863181990301)
  ·
    refine ⟨26749509821873573693246363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71332026191662863181990301 26749509821873573693246363)
    ·
      refine ⟨40124264732810360539869545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26749509821873573693246363 40124264732810360539869545)
      ·
        refine ⟨30093198549607770404902159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40124264732810360539869545 30093198549607770404902159)
        ·
          refine ⟨45139797824411655607353239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30093198549607770404902159 45139797824411655607353239)
          ·
            refine ⟨67709696736617483411029859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45139797824411655607353239 67709696736617483411029859)
            ·
              refine ⟨101564545104926225116544789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67709696736617483411029859 101564545104926225116544789)
              ·
                refine ⟨4760838051793416802338037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101564545104926225116544789 4760838051793416802338037)
                ·
                  refine ⟨446328567355632825219191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4760838051793416802338037 446328567355632825219191)
                  ·
                    rfl

theorem cell21_1955749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_1955749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955749 prefixEnd_1955749 := by exact prefixLift 1955749
  have htrace : WordTrace (prefixWord ++ tailWord_1955749) baseStart_1955749 baseEnd_1955749 := by
    simpa [prefixWord, tailWord_1955749, baseEnd_1955749] using wordTrace_append hprefix tailTrace_1955749
  have hstable : (prefixWord ++ tailWord_1955749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955749).length < 2 ^ (prefixWord ++ tailWord_1955749).sum := by decide
  have hdescent : baseEnd_1955749 < baseStart_1955749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955797 : List Nat := [1, 3, 2, 3, 2, 1, 2, 3, 4]
def baseStart_1955797 : Nat := 118140960795 + 1955797 * 2 ^ 59
def prefixEnd_1955797 : Nat := 4983230072969 + 3 ^ 40 * 1955797 * 2
def baseEnd_1955797 : Nat := 446339521609595408419093

theorem tailTrace_1955797 : CollatzResearch.WordTrace tailWord_1955797 prefixEnd_1955797 446339521609595408419093 := by
  unfold tailWord_1955797
  simp only [CollatzResearch.WordTrace]
  refine ⟨71333776895488967379737645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47555851263659311586491763 71333776895488967379737645)
  ·
    refine ⟨26750166335808362767401617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71333776895488967379737645 26750166335808362767401617)
    ·
      refine ⟨20062624751856272075551213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26750166335808362767401617 20062624751856272075551213)
      ·
        refine ⟨7523484281946102028331705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20062624751856272075551213 7523484281946102028331705)
        ·
          refine ⟨5642613211459576521248779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7523484281946102028331705 5642613211459576521248779)
          ·
            refine ⟨8463919817189364781873169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5642613211459576521248779 8463919817189364781873169)
            ·
              refine ⟨6347939862892023586404877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8463919817189364781873169 6347939862892023586404877)
              ·
                refine ⟨2380477448584508844901829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6347939862892023586404877 2380477448584508844901829)
                ·
                  refine ⟨446339521609595408419093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2380477448584508844901829 446339521609595408419093)
                  ·
                    rfl

theorem cell21_1955797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_1955797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955797 prefixEnd_1955797 := by exact prefixLift 1955797
  have htrace : WordTrace (prefixWord ++ tailWord_1955797) baseStart_1955797 baseEnd_1955797 := by
    simpa [prefixWord, tailWord_1955797, baseEnd_1955797] using wordTrace_append hprefix tailTrace_1955797
  have hstable : (prefixWord ++ tailWord_1955797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955797).length < 2 ^ (prefixWord ++ tailWord_1955797).sum := by decide
  have hdescent : baseEnd_1955797 < baseStart_1955797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955946 : List Nat := [3, 1, 3, 2, 12]
def baseStart_1955946 : Nat := 118140960795 + 1955946 * 2 ^ 59
def prefixEnd_1955946 : Nat := 4983230072969 + 3 ^ 40 * 1955946 * 2
def baseEnd_1955946 : Nat := 5510784264686472351055

theorem tailTrace_1955946 : CollatzResearch.WordTrace tailWord_1955946 prefixEnd_1955946 5510784264686472351055 := by
  unfold tailWord_1955946
  simp only [CollatzResearch.WordTrace]
  refine ⟨17834802842987291456727923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47559474247966110551274461 17834802842987291456727923)
  ·
    refine ⟨26752204264480937185091885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17834802842987291456727923 26752204264480937185091885)
    ·
      refine ⟨10032076599180351444409457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26752204264480937185091885 10032076599180351444409457)
      ·
        refine ⟨7524057449385263583307093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10032076599180351444409457 7524057449385263583307093)
        ·
          refine ⟨5510784264686472351055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7524057449385263583307093 5510784264686472351055)
          ·
            rfl

theorem cell21_1955946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 12].length) (baseStart_1955946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955946 prefixEnd_1955946 := by exact prefixLift 1955946
  have htrace : WordTrace (prefixWord ++ tailWord_1955946) baseStart_1955946 baseEnd_1955946 := by
    simpa [prefixWord, tailWord_1955946, baseEnd_1955946] using wordTrace_append hprefix tailTrace_1955946
  have hstable : (prefixWord ++ tailWord_1955946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955946).length < 2 ^ (prefixWord ++ tailWord_1955946).sum := by decide
  have hdescent : baseEnd_1955946 < baseStart_1955946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955949 : List Nat := [1, 5, 1, 1, 2, 1, 4, 2, 4]
def baseStart_1955949 : Nat := 118140960795 + 1955949 * 2 ^ 59
def prefixEnd_1955949 : Nat := 4983230072969 + 3 ^ 40 * 1955949 * 2
def baseEnd_1955949 : Nat := 446374210080476921885449

theorem tailTrace_1955949 : CollatzResearch.WordTrace tailWord_1955949 prefixEnd_1955949 446374210080476921885449 := by
  unfold tailWord_1955949
  simp only [CollatzResearch.WordTrace]
  refine ⟨71339320790938297339270901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47559547193958864892847267 71339320790938297339270901)
  ·
    refine ⟨6688061324150465375556647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71339320790938297339270901 6688061324150465375556647)
    ·
      refine ⟨10032091986225698063334971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6688061324150465375556647 10032091986225698063334971)
      ·
        refine ⟨15048137979338547095002457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10032091986225698063334971 15048137979338547095002457)
        ·
          refine ⟨11286103484503910321251843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15048137979338547095002457 11286103484503910321251843)
          ·
            refine ⟨16929155226755865481877765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11286103484503910321251843 16929155226755865481877765)
            ·
              refine ⟨3174216605016724777852081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16929155226755865481877765 3174216605016724777852081)
              ·
                refine ⟨2380662453762543583389061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3174216605016724777852081 2380662453762543583389061)
                ·
                  refine ⟨446374210080476921885449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2380662453762543583389061 446374210080476921885449)
                  ·
                    rfl

theorem cell21_1955949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_1955949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955949 prefixEnd_1955949 := by exact prefixLift 1955949
  have htrace : WordTrace (prefixWord ++ tailWord_1955949) baseStart_1955949 baseEnd_1955949 := by
    simpa [prefixWord, tailWord_1955949, baseEnd_1955949] using wordTrace_append hprefix tailTrace_1955949
  have hstable : (prefixWord ++ tailWord_1955949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955949).length < 2 ^ (prefixWord ++ tailWord_1955949).sum := by decide
  have hdescent : baseEnd_1955949 < baseStart_1955949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955952 : List Nat := [2, 1, 1, 1, 5, 4, 2, 2, 3]
def baseStart_1955952 : Nat := 118140960795 + 1955952 * 2 ^ 59
def prefixEnd_1955952 : Nat := 4983230072969 + 3 ^ 40 * 1955952 * 2
def baseEnd_1955952 : Nat := 446374894721349583335443

theorem tailTrace_1955952 : CollatzResearch.WordTrace tailWord_1955952 prefixEnd_1955952 446374894721349583335443 := by
  unfold tailWord_1955952
  simp only [CollatzResearch.WordTrace]
  refine ⟨35669715104963714425815055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47559620139951619234420073 35669715104963714425815055)
  ·
    refine ⟨53504572657445571638722583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35669715104963714425815055 53504572657445571638722583)
    ·
      refine ⟨80256858986168357458083875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53504572657445571638722583 80256858986168357458083875)
      ·
        refine ⟨120385288479252536187125813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80256858986168357458083875 120385288479252536187125813)
        ·
          refine ⟨11286120794929925267543045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120385288479252536187125813 11286120794929925267543045)
          ·
            refine ⟨2116147649049360987664321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11286120794929925267543045 2116147649049360987664321)
            ·
              refine ⟨1587110736787020740748241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2116147649049360987664321 1587110736787020740748241)
              ·
                refine ⟨1190333052590265555561181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587110736787020740748241 1190333052590265555561181)
                ·
                  refine ⟨446374894721349583335443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190333052590265555561181 446374894721349583335443)
                  ·
                    rfl

theorem cell21_1955952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 3].length) (baseStart_1955952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955952 prefixEnd_1955952 := by exact prefixLift 1955952
  have htrace : WordTrace (prefixWord ++ tailWord_1955952) baseStart_1955952 baseEnd_1955952 := by
    simpa [prefixWord, tailWord_1955952, baseEnd_1955952] using wordTrace_append hprefix tailTrace_1955952
  have hstable : (prefixWord ++ tailWord_1955952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955952).length < 2 ^ (prefixWord ++ tailWord_1955952).sum := by decide
  have hdescent : baseEnd_1955952 < baseStart_1955952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955977 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 5]
def baseStart_1955977 : Nat := 118140960795 + 1955977 * 2 ^ 59
def prefixEnd_1955977 : Nat := 4983230072969 + 3 ^ 40 * 1955977 * 2
def baseEnd_1955977 : Nat := 446380600061955095418725

theorem tailTrace_1955977 : CollatzResearch.WordTrace tailWord_1955977 prefixEnd_1955977 446380600061955095418725 := by
  unfold tailWord_1955977
  simp only [CollatzResearch.WordTrace]
  refine ⟨71340342034836858121290185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47560228023224572080860123 71340342034836858121290185)
  ·
    refine ⟨53505256526127643590967639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71340342034836858121290185 53505256526127643590967639)
    ·
      refine ⟨80257884789191465386451459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53505256526127643590967639 80257884789191465386451459)
      ·
        refine ⟨120386827183787198079677189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80257884789191465386451459 120386827183787198079677189)
        ·
          refine ⟨22572530096960099639939473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120386827183787198079677189 22572530096960099639939473)
          ·
            refine ⟨16929397572720074729954605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22572530096960099639939473 16929397572720074729954605)
            ·
              refine ⟨6348524089770028023732977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16929397572720074729954605 6348524089770028023732977)
              ·
                refine ⟨4761393067327521017799733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6348524089770028023732977 4761393067327521017799733)
                ·
                  refine ⟨446380600061955095418725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4761393067327521017799733 446380600061955095418725)
                  ·
                    rfl

theorem cell21_1955977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_1955977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1955977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1955977 prefixEnd_1955977 := by exact prefixLift 1955977
  have htrace : WordTrace (prefixWord ++ tailWord_1955977) baseStart_1955977 baseEnd_1955977 := by
    simpa [prefixWord, tailWord_1955977, baseEnd_1955977] using wordTrace_append hprefix tailTrace_1955977
  have hstable : (prefixWord ++ tailWord_1955977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955977).length < 2 ^ (prefixWord ++ tailWord_1955977).sum := by decide
  have hdescent : baseEnd_1955977 < baseStart_1955977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956025 : List Nat := [1, 2, 1, 4, 1, 2, 5, 1, 4]
def baseStart_1956025 : Nat := 118140960795 + 1956025 * 2 ^ 59
def prefixEnd_1956025 : Nat := 4983230072969 + 3 ^ 40 * 1956025 * 2
def baseEnd_1956025 : Nat := 446391554315917678618627

theorem tailTrace_1956025 : CollatzResearch.WordTrace tailWord_1956025 prefixEnd_1956025 446391554315917678618627 := by
  unfold tailWord_1956025
  simp only [CollatzResearch.WordTrace]
  refine ⟨71342092738662962319037529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47561395159108641546025019 71342092738662962319037529)
  ·
    refine ⟨53506569553997221739278147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71342092738662962319037529 53506569553997221739278147)
    ·
      refine ⟨80259854330995832608917221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53506569553997221739278147 80259854330995832608917221)
      ·
        refine ⟨15048722687061718614171979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80259854330995832608917221 15048722687061718614171979)
        ·
          refine ⟨22573084030592577921257969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15048722687061718614171979 22573084030592577921257969)
          ·
            refine ⟨16929813022944433440943477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22573084030592577921257969 16929813022944433440943477)
            ·
              refine ⟨1587169970901040635088451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16929813022944433440943477 1587169970901040635088451)
              ·
                refine ⟨2380754956351560952632677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587169970901040635088451 2380754956351560952632677)
                ·
                  refine ⟨446391554315917678618627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2380754956351560952632677 446391554315917678618627)
                  ·
                    rfl

theorem cell21_1956025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 4].length) (baseStart_1956025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956025 prefixEnd_1956025 := by exact prefixLift 1956025
  have htrace : WordTrace (prefixWord ++ tailWord_1956025) baseStart_1956025 baseEnd_1956025 := by
    simpa [prefixWord, tailWord_1956025, baseEnd_1956025] using wordTrace_append hprefix tailTrace_1956025
  have hstable : (prefixWord ++ tailWord_1956025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956025).length < 2 ^ (prefixWord ++ tailWord_1956025).sum := by decide
  have hdescent : baseEnd_1956025 < baseStart_1956025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956146 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 5]
def baseStart_1956146 : Nat := 118140960795 + 1956146 * 2 ^ 59
def prefixEnd_1956146 : Nat := 4983230072969 + 3 ^ 40 * 1956146 * 2
def baseEnd_1956146 : Nat := 446419168164448357101713

theorem tailTrace_1956146 : CollatzResearch.WordTrace tailWord_1956146 prefixEnd_1956146 446419168164448357101713 := by
  unfold tailWord_1956146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17836626492806149996048073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47564337314149733322794861 17836626492806149996048073)
  ·
    refine ⟨13377469869604612497036055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17836626492806149996048073 13377469869604612497036055)
    ·
      refine ⟨20066204804406918745554083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13377469869604612497036055 20066204804406918745554083)
      ·
        refine ⟨30099307206610378118331125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20066204804406918745554083 30099307206610378118331125)
        ·
          refine ⟨2821810050619722948593543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30099307206610378118331125 2821810050619722948593543)
          ·
            refine ⟨4232715075929584422890315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2821810050619722948593543 4232715075929584422890315)
            ·
              refine ⟨6349072613894376634335473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4232715075929584422890315 6349072613894376634335473)
              ·
                refine ⟨4761804460420782475751605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6349072613894376634335473 4761804460420782475751605)
                ·
                  refine ⟨446419168164448357101713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4761804460420782475751605 446419168164448357101713)
                  ·
                    rfl

theorem cell21_1956146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_1956146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956146 prefixEnd_1956146 := by exact prefixLift 1956146
  have htrace : WordTrace (prefixWord ++ tailWord_1956146) baseStart_1956146 baseEnd_1956146 := by
    simpa [prefixWord, tailWord_1956146, baseEnd_1956146] using wordTrace_append hprefix tailTrace_1956146
  have hstable : (prefixWord ++ tailWord_1956146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956146).length < 2 ^ (prefixWord ++ tailWord_1956146).sum := by decide
  have hdescent : baseEnd_1956146 < baseStart_1956146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956177 : List Nat := [1, 2, 2, 1, 4, 4, 1, 2, 4]
def baseStart_1956177 : Nat := 118140960795 + 1956177 * 2 ^ 59
def prefixEnd_1956177 : Nat := 4983230072969 + 3 ^ 40 * 1956177 * 2
def baseEnd_1956177 : Nat := 446426242786799192084983

theorem tailTrace_1956177 : CollatzResearch.WordTrace tailWord_1956177 prefixEnd_1956177 446426242786799192084983 := by
  unfold tailWord_1956177
  simp only [CollatzResearch.WordTrace]
  refine ⟨71347636634112292278570785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47565091089408194852380523 71347636634112292278570785)
  ·
    refine ⟨53510727475584219208928089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71347636634112292278570785 53510727475584219208928089)
    ·
      refine ⟨40133045606688164406696067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53510727475584219208928089 40133045606688164406696067)
      ·
        refine ⟨60199568410032246610044101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40133045606688164406696067 60199568410032246610044101)
        ·
          refine ⟨11287419076881046239383269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60199568410032246610044101 11287419076881046239383269)
          ·
            refine ⟨2116391076915196169884363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11287419076881046239383269 2116391076915196169884363)
            ·
              refine ⟨3174586615372794254826545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116391076915196169884363 3174586615372794254826545)
              ·
                refine ⟨2380939961529595691119909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3174586615372794254826545 2380939961529595691119909)
                ·
                  refine ⟨446426242786799192084983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2380939961529595691119909 446426242786799192084983)
                  ·
                    rfl

theorem cell21_1956177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 4].length) (baseStart_1956177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956177 prefixEnd_1956177 := by exact prefixLift 1956177
  have htrace : WordTrace (prefixWord ++ tailWord_1956177) baseStart_1956177 baseEnd_1956177 := by
    simpa [prefixWord, tailWord_1956177, baseEnd_1956177] using wordTrace_append hprefix tailTrace_1956177
  have hstable : (prefixWord ++ tailWord_1956177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956177).length < 2 ^ (prefixWord ++ tailWord_1956177).sum := by decide
  have hdescent : baseEnd_1956177 < baseStart_1956177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956194 : List Nat := [3, 3, 2, 1, 1, 3, 3, 1, 4]
def baseStart_1956194 : Nat := 118140960795 + 1956194 * 2 ^ 59
def prefixEnd_1956194 : Nat := 4983230072969 + 3 ^ 40 * 1956194 * 2
def baseEnd_1956194 : Nat := 446430122418410940301615

theorem tailTrace_1956194 : CollatzResearch.WordTrace tailWord_1956194 prefixEnd_1956194 446430122418410940301615 := by
  unfold tailWord_1956194
  simp only [CollatzResearch.WordTrace]
  refine ⟨17837064168762676045484909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47565504450033802787959757 17837064168762676045484909)
  ·
    refine ⟨6688899063286003517056841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17837064168762676045484909 6688899063286003517056841)
    ·
      refine ⟨5016674297464502637792631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6688899063286003517056841 5016674297464502637792631)
      ·
        refine ⟨7525011446196753956688947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5016674297464502637792631 7525011446196753956688947)
        ·
          refine ⟨11287517169295130935033421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7525011446196753956688947 11287517169295130935033421)
          ·
            refine ⟨4232818938485674100637533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11287517169295130935033421 4232818938485674100637533)
            ·
              refine ⟨1587307101932127787739075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4232818938485674100637533 1587307101932127787739075)
              ·
                refine ⟨2380960652898191681608613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587307101932127787739075 2380960652898191681608613)
                ·
                  refine ⟨446430122418410940301615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2380960652898191681608613 446430122418410940301615)
                  ·
                    rfl

theorem cell21_1956194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_1956194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956194 prefixEnd_1956194 := by exact prefixLift 1956194
  have htrace : WordTrace (prefixWord ++ tailWord_1956194) baseStart_1956194 baseEnd_1956194 := by
    simpa [prefixWord, tailWord_1956194, baseEnd_1956194] using wordTrace_append hprefix tailTrace_1956194
  have hstable : (prefixWord ++ tailWord_1956194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956194).length < 2 ^ (prefixWord ++ tailWord_1956194).sum := by decide
  have hdescent : baseEnd_1956194 < baseStart_1956194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956205 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 5]
def baseStart_1956205 : Nat := 118140960795 + 1956205 * 2 ^ 59
def prefixEnd_1956205 : Nat := 4983230072969 + 3 ^ 40 * 1956205 * 2
def baseEnd_1956205 : Nat := 446432632768277365618259

theorem tailTrace_1956205 : CollatzResearch.WordTrace tailWord_1956205 prefixEnd_1956205 446432632768277365618259 := by
  unfold tailWord_1956205
  simp only [CollatzResearch.WordTrace]
  refine ⟨71348657878010853060590069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47565771918673902040393379 71348657878010853060590069)
  ·
    refine ⟨6688936676063517474430319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71348657878010853060590069 6688936676063517474430319)
    ·
      refine ⟨10033405014095276211645479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6688936676063517474430319 10033405014095276211645479)
      ·
        refine ⟨15050107521142914317468219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10033405014095276211645479 15050107521142914317468219)
        ·
          refine ⟨22575161281714371476202329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15050107521142914317468219 22575161281714371476202329)
          ·
            refine ⟨16931370961285778607151747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22575161281714371476202329 16931370961285778607151747)
            ·
              refine ⟨25397056441928667910727621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16931370961285778607151747 25397056441928667910727621)
              ·
                refine ⟨4761948082861625233261429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25397056441928667910727621 4761948082861625233261429)
                ·
                  refine ⟨446432632768277365618259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4761948082861625233261429 446432632768277365618259)
                  ·
                    rfl

theorem cell21_1956205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_1956205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956205 prefixEnd_1956205 := by exact prefixLift 1956205
  have htrace : WordTrace (prefixWord ++ tailWord_1956205) baseStart_1956205 baseEnd_1956205 := by
    simpa [prefixWord, tailWord_1956205, baseEnd_1956205] using wordTrace_append hprefix tailTrace_1956205
  have hstable : (prefixWord ++ tailWord_1956205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956205).length < 2 ^ (prefixWord ++ tailWord_1956205).sum := by decide
  have hdescent : baseEnd_1956205 < baseStart_1956205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956214 : List Nat := [5, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_1956214 : Nat := 118140960795 + 1956214 * 2 ^ 59
def prefixEnd_1956214 : Nat := 4983230072969 + 3 ^ 40 * 1956214 * 2
def baseEnd_1956214 : Nat := 446434686690895349968241

theorem tailTrace_1956214 : CollatzResearch.WordTrace tailWord_1956214 prefixEnd_1956214 446434686690895349968241 := by
  unfold tailWord_1956214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4459311633436140474854231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47565990756652165065111797 4459311633436140474854231)
  ·
    refine ⟨6688967450154210712281347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4459311633436140474854231 6688967450154210712281347)
    ·
      refine ⟨10033451175231316068422021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6688967450154210712281347 10033451175231316068422021)
      ·
        refine ⟨1881272095355871762829129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10033451175231316068422021 1881272095355871762829129)
        ·
          refine ⟨1410954071516903822121847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1881272095355871762829129 1410954071516903822121847)
          ·
            refine ⟨2116431107275355733182771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410954071516903822121847 2116431107275355733182771)
            ·
              refine ⟨3174646660913033599774157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116431107275355733182771 3174646660913033599774157)
              ·
                refine ⟨1190492497842387599915309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3174646660913033599774157 1190492497842387599915309)
                ·
                  refine ⟨446434686690895349968241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190492497842387599915309 446434686690895349968241)
                  ·
                    rfl

theorem cell21_1956214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_1956214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956214 prefixEnd_1956214 := by exact prefixLift 1956214
  have htrace : WordTrace (prefixWord ++ tailWord_1956214) baseStart_1956214 baseEnd_1956214 := by
    simpa [prefixWord, tailWord_1956214, baseEnd_1956214] using wordTrace_append hprefix tailTrace_1956214
  have hstable : (prefixWord ++ tailWord_1956214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956214).length < 2 ^ (prefixWord ++ tailWord_1956214).sum := by decide
  have hdescent : baseEnd_1956214 < baseStart_1956214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956219 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 6]
def baseStart_1956219 : Nat := 118140960795 + 1956219 * 2 ^ 59
def prefixEnd_1956219 : Nat := 4983230072969 + 3 ^ 40 * 1956219 * 2
def baseEnd_1956219 : Nat := 446435827759016452384897

theorem tailTrace_1956219 : CollatzResearch.WordTrace tailWord_1956219 prefixEnd_1956219 446435827759016452384897 := by
  unfold tailWord_1956219
  simp only [CollatzResearch.WordTrace]
  refine ⟨71349168499960133451599711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47566112333306755634399807 71349168499960133451599711)
  ·
    refine ⟨107023752749940200177399567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71349168499960133451599711 107023752749940200177399567)
    ·
      refine ⟨160535629124910300266099351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107023752749940200177399567 160535629124910300266099351)
      ·
        refine ⟨240803443687365450399149027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160535629124910300266099351 240803443687365450399149027)
        ·
          refine ⟨361205165531048175598723541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240803443687365450399149027 361205165531048175598723541)
          ·
            refine ⟨8465746067133941615595083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 361205165531048175598723541 8465746067133941615595083)
            ·
              refine ⟨12698619100700912423392625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8465746067133941615595083 12698619100700912423392625)
              ·
                refine ⟨9523964325525684317544469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12698619100700912423392625 9523964325525684317544469)
                ·
                  refine ⟨446435827759016452384897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9523964325525684317544469 446435827759016452384897)
                  ·
                    rfl

theorem cell21_1956219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 6].length) (baseStart_1956219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956219 prefixEnd_1956219 := by exact prefixLift 1956219
  have htrace : WordTrace (prefixWord ++ tailWord_1956219) baseStart_1956219 baseEnd_1956219 := by
    simpa [prefixWord, tailWord_1956219, baseEnd_1956219] using wordTrace_append hprefix tailTrace_1956219
  have hstable : (prefixWord ++ tailWord_1956219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956219).length < 2 ^ (prefixWord ++ tailWord_1956219).sum := by decide
  have hdescent : baseEnd_1956219 < baseStart_1956219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956250 : List Nat := [3, 1, 1, 4, 1, 2, 1, 8]
def baseStart_1956250 : Nat := 118140960795 + 1956250 * 2 ^ 59
def prefixEnd_1956250 : Nat := 4983230072969 + 3 ^ 40 * 1956250 * 2
def baseEnd_1956250 : Nat := 148814300793789095789389

theorem tailTrace_1956250 : CollatzResearch.WordTrace tailWord_1956250 prefixEnd_1956250 148814300793789095789389 := by
  unfold tailWord_1956250
  simp only [CollatzResearch.WordTrace]
  refine ⟨17837574790711956436494551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47566866108565217163985469 17837574790711956436494551)
  ·
    refine ⟨26756362186067934654741827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17837574790711956436494551 26756362186067934654741827)
    ·
      refine ⟨40134543279101901982112741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26756362186067934654741827 40134543279101901982112741)
      ·
        refine ⟨7525226864831606621646139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40134543279101901982112741 7525226864831606621646139)
        ·
          refine ⟨11287840297247409932469209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7525226864831606621646139 11287840297247409932469209)
          ·
            refine ⟨8465880222935557449351907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11287840297247409932469209 8465880222935557449351907)
            ·
              refine ⟨12698820334403336174027861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8465880222935557449351907 12698820334403336174027861)
              ·
                refine ⟨148814300793789095789389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12698820334403336174027861 148814300793789095789389)
                ·
                  rfl

theorem cell21_1956250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_1956250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956250 prefixEnd_1956250 := by exact prefixLift 1956250
  have htrace : WordTrace (prefixWord ++ tailWord_1956250) baseStart_1956250 baseEnd_1956250 := by
    simpa [prefixWord, tailWord_1956250, baseEnd_1956250] using wordTrace_append hprefix tailTrace_1956250
  have hstable : (prefixWord ++ tailWord_1956250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956250).length < 2 ^ (prefixWord ++ tailWord_1956250).sum := by decide
  have hdescent : baseEnd_1956250 < baseStart_1956250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956253 : List Nat := [1, 4, 2, 1, 4, 1, 1, 3, 4]
def baseStart_1956253 : Nat := 118140960795 + 1956253 * 2 ^ 59
def prefixEnd_1956253 : Nat := 4983230072969 + 3 ^ 40 * 1956253 * 2
def baseEnd_1956253 : Nat := 446443587022239948818161

theorem tailTrace_1956253 : CollatzResearch.WordTrace tailWord_1956253 prefixEnd_1956253 446443587022239948818161 := by
  unfold tailWord_1956253
  simp only [CollatzResearch.WordTrace]
  refine ⟨71350408581836957258337413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47566939054557971505558275 71350408581836957258337413)
  ·
    refine ⟨13378201609094429485938265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71350408581836957258337413 13378201609094429485938265)
    ·
      refine ⟨10033651206820822114453699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13378201609094429485938265 10033651206820822114453699)
      ·
        refine ⟨15050476810231233171680549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10033651206820822114453699 15050476810231233171680549)
        ·
          refine ⟨2821964401918356219690103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15050476810231233171680549 2821964401918356219690103)
          ·
            refine ⟨4232946602877534329535155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2821964401918356219690103 4232946602877534329535155)
            ·
              refine ⟨6349419904316301494302733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4232946602877534329535155 6349419904316301494302733)
              ·
                refine ⟨2381032464118613060363525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6349419904316301494302733 2381032464118613060363525)
                ·
                  refine ⟨446443587022239948818161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2381032464118613060363525 446443587022239948818161)
                  ·
                    rfl

theorem cell21_1956253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_1956253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956253 prefixEnd_1956253 := by exact prefixLift 1956253
  have htrace : WordTrace (prefixWord ++ tailWord_1956253) baseStart_1956253 baseEnd_1956253 := by
    simpa [prefixWord, tailWord_1956253, baseEnd_1956253] using wordTrace_append hprefix tailTrace_1956253
  have hstable : (prefixWord ++ tailWord_1956253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956253).length < 2 ^ (prefixWord ++ tailWord_1956253).sum := by decide
  have hdescent : baseEnd_1956253 < baseStart_1956253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956298 : List Nat := [3, 1, 2, 1, 2, 2, 3, 4, 3]
def baseStart_1956298 : Nat := 118140960795 + 1956298 * 2 ^ 59
def prefixEnd_1956298 : Nat := 4983230072969 + 3 ^ 40 * 1956298 * 2
def baseEnd_1956298 : Nat := 446453856635329870568069

theorem tailTrace_1956298 : CollatzResearch.WordTrace tailWord_1956298 prefixEnd_1956298 446453856635329870568069 := by
  unfold tailWord_1956298
  simp only [CollatzResearch.WordTrace]
  refine ⟨17838012466668482485931387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47568033244449286629150365 17838012466668482485931387)
  ·
    refine ⟨26757018700002723728897081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17838012466668482485931387 26757018700002723728897081)
    ·
      refine ⟨20067764025002042796672811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26757018700002723728897081 20067764025002042796672811)
      ·
        refine ⟨30101646037503064195009217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20067764025002042796672811 30101646037503064195009217)
        ·
          refine ⟨22576234528127298146256913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30101646037503064195009217 22576234528127298146256913)
          ·
            refine ⟨16932175896095473609692685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22576234528127298146256913 16932175896095473609692685)
            ·
              refine ⟨6349565961035802603634757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16932175896095473609692685 6349565961035802603634757)
              ·
                refine ⟨1190543617694212988181517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6349565961035802603634757 1190543617694212988181517)
                ·
                  refine ⟨446453856635329870568069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190543617694212988181517 446453856635329870568069)
                  ·
                    rfl

theorem cell21_1956298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_1956298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956298 prefixEnd_1956298 := by exact prefixLift 1956298
  have htrace : WordTrace (prefixWord ++ tailWord_1956298) baseStart_1956298 baseEnd_1956298 := by
    simpa [prefixWord, tailWord_1956298, baseEnd_1956298] using wordTrace_append hprefix tailTrace_1956298
  have hstable : (prefixWord ++ tailWord_1956298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956298).length < 2 ^ (prefixWord ++ tailWord_1956298).sum := by decide
  have hdescent : baseEnd_1956298 < baseStart_1956298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956422 : List Nat := [6, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1956422 : Nat := 118140960795 + 1956422 * 2 ^ 59
def prefixEnd_1956422 : Nat := 4983230072969 + 3 ^ 40 * 1956422 * 2
def baseEnd_1956422 : Nat := 446482155124733210501149

theorem tailTrace_1956422 : CollatzResearch.WordTrace tailWord_1956422 prefixEnd_1956422 446482155124733210501149 := by
  unfold tailWord_1956422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2229892891194521847538735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47571048345483132747493013 2229892891194521847538735)
  ·
    refine ⟨3344839336791782771308103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2229892891194521847538735 3344839336791782771308103)
    ·
      refine ⟨5017259005187674156962155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3344839336791782771308103 5017259005187674156962155)
      ·
        refine ⟨7525888507781511235443233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5017259005187674156962155 7525888507781511235443233)
        ·
          refine ⟨5644416380836133426582425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7525888507781511235443233 5644416380836133426582425)
          ·
            refine ⟨4233312285627100069936819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5644416380836133426582425 4233312285627100069936819)
            ·
              refine ⟨6349968428440650104905229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233312285627100069936819 6349968428440650104905229)
              ·
                refine ⟨2381238160665243789339461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6349968428440650104905229 2381238160665243789339461)
                ·
                  refine ⟨446482155124733210501149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2381238160665243789339461 446482155124733210501149)
                  ·
                    rfl

theorem cell21_1956422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1956422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956422 prefixEnd_1956422 := by exact prefixLift 1956422
  have htrace : WordTrace (prefixWord ++ tailWord_1956422) baseStart_1956422 baseEnd_1956422 := by
    simpa [prefixWord, tailWord_1956422, baseEnd_1956422] using wordTrace_append hprefix tailTrace_1956422
  have hstable : (prefixWord ++ tailWord_1956422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956422).length < 2 ^ (prefixWord ++ tailWord_1956422).sum := by decide
  have hdescent : baseEnd_1956422 < baseStart_1956422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956526 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_1956526 : Nat := 118140960795 + 1956526 * 2 ^ 59
def prefixEnd_1956526 : Nat := 4983230072969 + 3 ^ 40 * 1956526 * 2
def baseEnd_1956526 : Nat := 446505889341652140767603

theorem tailTrace_1956526 : CollatzResearch.WordTrace tailWord_1956526 prefixEnd_1956526 446505889341652140767603 := by
  unfold tailWord_1956526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8920045713730990610378179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47573577139898616588683621 8920045713730990610378179)
  ·
    refine ⟨13380068570596485915567269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8920045713730990610378179 13380068570596485915567269)
    ·
      refine ⟨2508762856986841109168863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13380068570596485915567269 2508762856986841109168863)
      ·
        refine ⟨3763144285480261663753295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2508762856986841109168863 3763144285480261663753295)
        ·
          refine ⟨5644716428220392495629943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3763144285480261663753295 5644716428220392495629943)
          ·
            refine ⟨8467074642330588743444915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5644716428220392495629943 8467074642330588743444915)
            ·
              refine ⟨12700611963495883115167373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8467074642330588743444915 12700611963495883115167373)
              ·
                refine ⟨4762729486310956168187765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12700611963495883115167373 4762729486310956168187765)
                ·
                  refine ⟨446505889341652140767603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4762729486310956168187765 446505889341652140767603)
                  ·
                    rfl

theorem cell21_1956526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_1956526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956526 prefixEnd_1956526 := by exact prefixLift 1956526
  have htrace : WordTrace (prefixWord ++ tailWord_1956526) baseStart_1956526 baseEnd_1956526 := by
    simpa [prefixWord, tailWord_1956526, baseEnd_1956526] using wordTrace_append hprefix tailTrace_1956526
  have hstable : (prefixWord ++ tailWord_1956526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956526).length < 2 ^ (prefixWord ++ tailWord_1956526).sum := by decide
  have hdescent : baseEnd_1956526 < baseStart_1956526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956537 : List Nat := [1, 2, 1, 4, 1, 1, 1, 10]
def baseStart_1956537 : Nat := 118140960795 + 1956537 * 2 ^ 59
def prefixEnd_1956537 : Nat := 4983230072969 + 3 ^ 40 * 1956537 * 2
def baseEnd_1956537 : Nat := 148836133230506188694749

theorem tailTrace_1956537 : CollatzResearch.WordTrace tailWord_1956537 prefixEnd_1956537 148836133230506188694749 := by
  unfold tailWord_1956537
  simp only [CollatzResearch.WordTrace]
  refine ⟨71360766912808073761675865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47573844608538715841117243 71360766912808073761675865)
  ·
    refine ⟨53520575184606055321256899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71360766912808073761675865 53520575184606055321256899)
    ·
      refine ⟨80280862776909082981885349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53520575184606055321256899 80280862776909082981885349)
      ·
        refine ⟨15052661770670453059103503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80280862776909082981885349 15052661770670453059103503)
        ·
          refine ⟨22578992656005679588655255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15052661770670453059103503 22578992656005679588655255)
          ·
            refine ⟨33868488984008519382982883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22578992656005679588655255 33868488984008519382982883)
            ·
              refine ⟨50802733476012779074474325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33868488984008519382982883 50802733476012779074474325)
              ·
                refine ⟨148836133230506188694749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50802733476012779074474325 148836133230506188694749)
                ·
                  rfl

theorem cell21_1956537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 10].length) (baseStart_1956537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956537 prefixEnd_1956537 := by exact prefixLift 1956537
  have htrace : WordTrace (prefixWord ++ tailWord_1956537) baseStart_1956537 baseEnd_1956537 := by
    simpa [prefixWord, tailWord_1956537, baseEnd_1956537] using wordTrace_append hprefix tailTrace_1956537
  have hstable : (prefixWord ++ tailWord_1956537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956537).length < 2 ^ (prefixWord ++ tailWord_1956537).sum := by decide
  have hdescent : baseEnd_1956537 < baseStart_1956537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956554 : List Nat := [3, 1, 2, 1, 4, 2, 1, 7]
def baseStart_1956554 : Nat := 118140960795 + 1956554 * 2 ^ 59
def prefixEnd_1956554 : Nat := 4983230072969 + 3 ^ 40 * 1956554 * 2
def baseEnd_1956554 : Nat := 148837426441043438100293

theorem tailTrace_1956554 : CollatzResearch.WordTrace tailWord_1956554 prefixEnd_1956554 148837426441043438100293 := by
  unfold tailWord_1956554
  simp only [CollatzResearch.WordTrace]
  refine ⟨17840346738436621416261179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47574257969164323776696477 17840346738436621416261179)
  ·
    refine ⟨26760520107654932124391769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17840346738436621416261179 26760520107654932124391769)
    ·
      refine ⟨20070390080741199093293827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26760520107654932124391769 20070390080741199093293827)
      ·
        refine ⟨30105585121111798639940741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20070390080741199093293827 30105585121111798639940741)
        ·
          refine ⟨5644797210208462244988889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30105585121111798639940741 5644797210208462244988889)
          ·
            refine ⟨4233597907656346683741667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5644797210208462244988889 4233597907656346683741667)
            ·
              refine ⟨6350396861484520025612501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233597907656346683741667 6350396861484520025612501)
              ·
                refine ⟨148837426441043438100293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6350396861484520025612501 148837426441043438100293)
                ·
                  rfl

theorem cell21_1956554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_1956554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956554 prefixEnd_1956554 := by exact prefixLift 1956554
  have htrace : WordTrace (prefixWord ++ tailWord_1956554) baseStart_1956554 baseEnd_1956554 := by
    simpa [prefixWord, tailWord_1956554, baseEnd_1956554] using wordTrace_append hprefix tailTrace_1956554
  have hstable : (prefixWord ++ tailWord_1956554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956554).length < 2 ^ (prefixWord ++ tailWord_1956554).sum := by decide
  have hdescent : baseEnd_1956554 < baseStart_1956554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956585 : List Nat := [1, 2, 1, 1, 1, 2, 4, 6, 3]
def baseStart_1956585 : Nat := 118140960795 + 1956585 * 2 ^ 59
def prefixEnd_1956585 : Nat := 4983230072969 + 3 ^ 40 * 1956585 * 2
def baseEnd_1956585 : Nat := 446519353945481149284149

theorem tailTrace_1956585 : CollatzResearch.WordTrace tailWord_1956585 prefixEnd_1956585 446519353945481149284149 := by
  unfold tailWord_1956585
  simp only [CollatzResearch.WordTrace]
  refine ⟨71362517616634177959423209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47575011744422785306282139 71362517616634177959423209)
  ·
    refine ⟨53521888212475633469567407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71362517616634177959423209 53521888212475633469567407)
    ·
      refine ⟨80282832318713450204351111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53521888212475633469567407 80282832318713450204351111)
      ·
        refine ⟨120424248478070175306526667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80282832318713450204351111 120424248478070175306526667)
        ·
          refine ⟨180636372717105262959790001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120424248478070175306526667 180636372717105262959790001)
          ·
            refine ⟨135477279537828947219842501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180636372717105262959790001 135477279537828947219842501)
            ·
              refine ⟨25401989913342927603720469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135477279537828947219842501 25401989913342927603720469)
              ·
                refine ⟨1190718277187949731424397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25401989913342927603720469 1190718277187949731424397)
                ·
                  refine ⟨446519353945481149284149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190718277187949731424397 446519353945481149284149)
                  ·
                    rfl

theorem cell21_1956585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 3].length) (baseStart_1956585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956585 prefixEnd_1956585 := by exact prefixLift 1956585
  have htrace : WordTrace (prefixWord ++ tailWord_1956585) baseStart_1956585 baseEnd_1956585 := by
    simpa [prefixWord, tailWord_1956585, baseEnd_1956585] using wordTrace_append hprefix tailTrace_1956585
  have hstable : (prefixWord ++ tailWord_1956585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956585).length < 2 ^ (prefixWord ++ tailWord_1956585).sum := by decide
  have hdescent : baseEnd_1956585 < baseStart_1956585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956661 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 5]
def baseStart_1956661 : Nat := 118140960795 + 1956661 * 2 ^ 59
def prefixEnd_1956661 : Nat := 4983230072969 + 3 ^ 40 * 1956661 * 2
def baseEnd_1956661 : Nat := 446536698180921906017327

theorem tailTrace_1956661 : CollatzResearch.WordTrace tailWord_1956661 prefixEnd_1956661 446536698180921906017327 := by
  unfold tailWord_1956661
  simp only [CollatzResearch.WordTrace]
  refine ⟨71365289564358842939189837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47576859709572561959459891 71365289564358842939189837)
  ·
    refine ⟨26761983586634566102196189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71365289564358842939189837 26761983586634566102196189)
    ·
      refine ⟨10035743844987962288323571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26761983586634566102196189 10035743844987962288323571)
      ·
        refine ⟨15053615767481943432485357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10035743844987962288323571 15053615767481943432485357)
        ·
          refine ⟨5645105912805728787182009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15053615767481943432485357 5645105912805728787182009)
          ·
            refine ⟨4233829434604296590386507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5645105912805728787182009 4233829434604296590386507)
            ·
              refine ⟨6350744151906444885579761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233829434604296590386507 6350744151906444885579761)
              ·
                refine ⟨4763058113929833664184821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6350744151906444885579761 4763058113929833664184821)
                ·
                  refine ⟨446536698180921906017327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4763058113929833664184821 446536698180921906017327)
                  ·
                    rfl

theorem cell21_1956661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_1956661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956661 prefixEnd_1956661 := by exact prefixLift 1956661
  have htrace : WordTrace (prefixWord ++ tailWord_1956661) baseStart_1956661 baseEnd_1956661 := by
    simpa [prefixWord, tailWord_1956661, baseEnd_1956661] using wordTrace_append hprefix tailTrace_1956661
  have hstable : (prefixWord ++ tailWord_1956661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956661).length < 2 ^ (prefixWord ++ tailWord_1956661).sum := by decide
  have hdescent : baseEnd_1956661 < baseStart_1956661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956692 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 6]
def baseStart_1956692 : Nat := 118140960795 + 1956692 * 2 ^ 59
def prefixEnd_1956692 : Nat := 4983230072969 + 3 ^ 40 * 1956692 * 2
def baseEnd_1956692 : Nat := 446543772803272741000597

theorem tailTrace_1956692 : CollatzResearch.WordTrace tailWord_1956692 prefixEnd_1956692 446543772803272741000597 := by
  unfold tailWord_1956692
  simp only [CollatzResearch.WordTrace]
  refine ⟨35683210113623267616784165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47577613484831023489045553 35683210113623267616784165)
  ·
    refine ⟨6690601896304362678147031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35683210113623267616784165 6690601896304362678147031)
    ·
      refine ⟨10035902844456544017220547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6690601896304362678147031 10035902844456544017220547)
      ·
        refine ⟨15053854266684816025830821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10035902844456544017220547 15053854266684816025830821)
        ·
          refine ⟨2822597675003403004843279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15053854266684816025830821 2822597675003403004843279)
          ·
            refine ⟨4233896512505104507264919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822597675003403004843279 4233896512505104507264919)
            ·
              refine ⟨6350844768757656760897379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233896512505104507264919 6350844768757656760897379)
              ·
                refine ⟨9526267153136485141346069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6350844768757656760897379 9526267153136485141346069)
                ·
                  refine ⟨446543772803272741000597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9526267153136485141346069 446543772803272741000597)
                  ·
                    rfl

theorem cell21_1956692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_1956692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956692 prefixEnd_1956692 := by exact prefixLift 1956692
  have htrace : WordTrace (prefixWord ++ tailWord_1956692) baseStart_1956692 baseEnd_1956692 := by
    simpa [prefixWord, tailWord_1956692, baseEnd_1956692] using wordTrace_append hprefix tailTrace_1956692
  have hstable : (prefixWord ++ tailWord_1956692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956692).length < 2 ^ (prefixWord ++ tailWord_1956692).sum := by decide
  have hdescent : baseEnd_1956692 < baseStart_1956692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956720 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 5]
def baseStart_1956720 : Nat := 118140960795 + 1956720 * 2 ^ 59
def prefixEnd_1956720 : Nat := 4983230072969 + 3 ^ 40 * 1956720 * 2
def baseEnd_1956720 : Nat := 446550162784750914533873

theorem tailTrace_1956720 : CollatzResearch.WordTrace tailWord_1956720 prefixEnd_1956720 446550162784750914533873 := by
  unfold tailWord_1956720
  simp only [CollatzResearch.WordTrace]
  refine ⟨35683720735572548007793807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47578294314096730677058409 35683720735572548007793807)
  ·
    refine ⟨53525581103358822011690711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35683720735572548007793807 53525581103358822011690711)
    ·
      refine ⟨80288371655038233017536067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53525581103358822011690711 80288371655038233017536067)
      ·
        refine ⟨120432557482557349526304101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80288371655038233017536067 120432557482557349526304101)
        ·
          refine ⟨22581104527979503036182019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120432557482557349526304101 22581104527979503036182019)
          ·
            refine ⟨33871656791969254554273029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22581104527979503036182019 33871656791969254554273029)
            ·
              refine ⟨6350935648494235228926193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33871656791969254554273029 6350935648494235228926193)
              ·
                refine ⟨4763201736370676421694645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6350935648494235228926193 4763201736370676421694645)
                ·
                  refine ⟨446550162784750914533873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4763201736370676421694645 446550162784750914533873)
                  ·
                    rfl

theorem cell21_1956720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_1956720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956720 prefixEnd_1956720 := by exact prefixLift 1956720
  have htrace : WordTrace (prefixWord ++ tailWord_1956720) baseStart_1956720 baseEnd_1956720 := by
    simpa [prefixWord, tailWord_1956720, baseEnd_1956720] using wordTrace_append hprefix tailTrace_1956720
  have hstable : (prefixWord ++ tailWord_1956720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956720).length < 2 ^ (prefixWord ++ tailWord_1956720).sum := by decide
  have hdescent : baseEnd_1956720 < baseStart_1956720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956768 : List Nat := [2, 1, 1, 4, 1, 1, 6, 1, 4]
def baseStart_1956768 : Nat := 118140960795 + 1956768 * 2 ^ 59
def prefixEnd_1956768 : Nat := 4983230072969 + 3 ^ 40 * 1956768 * 2
def baseEnd_1956768 : Nat := 446561117038713497733775

theorem tailTrace_1956768 : CollatzResearch.WordTrace tailWord_1956768 prefixEnd_1956768 446561117038713497733775 := by
  unfold tailWord_1956768
  simp only [CollatzResearch.WordTrace]
  refine ⟨35684596087485600106667479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47579461449980800142223305 35684596087485600106667479)
  ·
    refine ⟨53526894131228400160001219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35684596087485600106667479 53526894131228400160001219)
    ·
      refine ⟨80290341196842600240001829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53526894131228400160001219 80290341196842600240001829)
      ·
        refine ⟨15054438974407987545000343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80290341196842600240001829 15054438974407987545000343)
        ·
          refine ⟨22581658461611981317500515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15054438974407987545000343 22581658461611981317500515)
          ·
            refine ⟨33872487692417971976250773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22581658461611981317500515 33872487692417971976250773)
            ·
              refine ⟨1587772860582092436386755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33872487692417971976250773 1587772860582092436386755)
              ·
                refine ⟨2381659290873138654580133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587772860582092436386755 2381659290873138654580133)
                ·
                  refine ⟨446561117038713497733775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2381659290873138654580133 446561117038713497733775)
                  ·
                    rfl

theorem cell21_1956768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 4].length) (baseStart_1956768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956768 prefixEnd_1956768 := by exact prefixLift 1956768
  have htrace : WordTrace (prefixWord ++ tailWord_1956768) baseStart_1956768 baseEnd_1956768 := by
    simpa [prefixWord, tailWord_1956768, baseEnd_1956768] using wordTrace_append hprefix tailTrace_1956768
  have hstable : (prefixWord ++ tailWord_1956768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956768).length < 2 ^ (prefixWord ++ tailWord_1956768).sum := by decide
  have hdescent : baseEnd_1956768 < baseStart_1956768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956872 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 5]
def baseStart_1956872 : Nat := 118140960795 + 1956872 * 2 ^ 59
def prefixEnd_1956872 : Nat := 4983230072969 + 3 ^ 40 * 1956872 * 2
def baseEnd_1956872 : Nat := 446584851255632428000229

theorem tailTrace_1956872 : CollatzResearch.WordTrace tailWord_1956872 prefixEnd_1956872 446584851255632428000229 := by
  unfold tailWord_1956872
  simp only [CollatzResearch.WordTrace]
  refine ⟨35686492683297212987560435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47581990244396283983413913 35686492683297212987560435)
  ·
    refine ⟨53529739024945819481340653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35686492683297212987560435 53529739024945819481340653)
    ·
      refine ⟨20073652134354682305502745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53529739024945819481340653 20073652134354682305502745)
      ·
        refine ⟨15055239100766011729127059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20073652134354682305502745 15055239100766011729127059)
        ·
          refine ⟨22582858651149017593690589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15055239100766011729127059 22582858651149017593690589)
          ·
            refine ⟨8468571994180881597633971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22582858651149017593690589 8468571994180881597633971)
            ·
              refine ⟨12702857991271322396450957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8468571994180881597633971 12702857991271322396450957)
              ·
                refine ⟨4763571746726745898669109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12702857991271322396450957 4763571746726745898669109)
                ·
                  refine ⟨446584851255632428000229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4763571746726745898669109 446584851255632428000229)
                  ·
                    rfl

theorem cell21_1956872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_1956872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956872 prefixEnd_1956872 := by exact prefixLift 1956872
  have htrace : WordTrace (prefixWord ++ tailWord_1956872) baseStart_1956872 baseEnd_1956872 := by
    simpa [prefixWord, tailWord_1956872, baseEnd_1956872] using wordTrace_append hprefix tailTrace_1956872
  have hstable : (prefixWord ++ tailWord_1956872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956872).length < 2 ^ (prefixWord ++ tailWord_1956872).sum := by decide
  have hdescent : baseEnd_1956872 < baseStart_1956872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956892 : List Nat := [2, 2, 3, 1, 5, 1, 2, 5]
def baseStart_1956892 : Nat := 118140960795 + 1956892 * 2 ^ 59
def prefixEnd_1956892 : Nat := 4983230072969 + 3 ^ 40 * 1956892 * 2
def baseEnd_1956892 : Nat := 148863138509372279222285

theorem tailTrace_1956892 : CollatzResearch.WordTrace tailWord_1956892 prefixEnd_1956892 148863138509372279222285 := by
  unfold tailWord_1956892
  simp only [CollatzResearch.WordTrace]
  refine ⟨35686857413260984695424465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47582476551014646260565953 35686857413260984695424465)
  ·
    refine ⟨26765143059945738521568349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35686857413260984695424465 26765143059945738521568349)
    ·
      refine ⟨10036928647479651945588131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26765143059945738521568349 10036928647479651945588131)
      ·
        refine ⟨15055392971219477918382197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10036928647479651945588131 15055392971219477918382197)
        ·
          refine ⟨1411443091051826054848331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15055392971219477918382197 1411443091051826054848331)
          ·
            refine ⟨2117164636577739082272497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411443091051826054848331 2117164636577739082272497)
            ·
              refine ⟨1587873477433304311704373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117164636577739082272497 1587873477433304311704373)
              ·
                refine ⟨148863138509372279222285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1587873477433304311704373 148863138509372279222285)
                ·
                  rfl

theorem cell21_1956892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 5].length) (baseStart_1956892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956892 prefixEnd_1956892 := by exact prefixLift 1956892
  have htrace : WordTrace (prefixWord ++ tailWord_1956892) baseStart_1956892 baseEnd_1956892 := by
    simpa [prefixWord, tailWord_1956892, baseEnd_1956892] using wordTrace_append hprefix tailTrace_1956892
  have hstable : (prefixWord ++ tailWord_1956892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956892).length < 2 ^ (prefixWord ++ tailWord_1956892).sum := by decide
  have hdescent : baseEnd_1956892 < baseStart_1956892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956948 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 5]
def baseStart_1956948 : Nat := 118140960795 + 1956948 * 2 ^ 59
def prefixEnd_1956948 : Nat := 4983230072969 + 3 ^ 40 * 1956948 * 2
def baseEnd_1956948 : Nat := 446602195491073184733407

theorem tailTrace_1956948 : CollatzResearch.WordTrace tailWord_1956948 prefixEnd_1956948 446602195491073184733407 := by
  unfold tailWord_1956948
  simp only [CollatzResearch.WordTrace]
  refine ⟨35687878657159545477443749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47583838209546060636591665 35687878657159545477443749)
  ·
    refine ⟨6691477248217414777020703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35687878657159545477443749 6691477248217414777020703)
    ·
      refine ⟨10037215872326122165531055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6691477248217414777020703 10037215872326122165531055)
      ·
        refine ⟨15055823808489183248296583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10037215872326122165531055 15055823808489183248296583)
        ·
          refine ⟨22583735712733774872444875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15055823808489183248296583 22583735712733774872444875)
          ·
            refine ⟨33875603569100662308667313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22583735712733774872444875 33875603569100662308667313)
            ·
              refine ⟨25406702676825496731500485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33875603569100662308667313 25406702676825496731500485)
              ·
                refine ⟨4763756751904780637156341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25406702676825496731500485 4763756751904780637156341)
                ·
                  refine ⟨446602195491073184733407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4763756751904780637156341 446602195491073184733407)
                  ·
                    rfl

theorem cell21_1956948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_1956948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956948 prefixEnd_1956948 := by exact prefixLift 1956948
  have htrace : WordTrace (prefixWord ++ tailWord_1956948) baseStart_1956948 baseEnd_1956948 := by
    simpa [prefixWord, tailWord_1956948, baseEnd_1956948] using wordTrace_append hprefix tailTrace_1956948
  have hstable : (prefixWord ++ tailWord_1956948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956948).length < 2 ^ (prefixWord ++ tailWord_1956948).sum := by decide
  have hdescent : baseEnd_1956948 < baseStart_1956948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956965 : List Nat := [1, 3, 1, 3, 2, 1, 2, 5, 3]
def baseStart_1956965 : Nat := 118140960795 + 1956965 * 2 ^ 59
def prefixEnd_1956965 : Nat := 4983230072969 + 3 ^ 40 * 1956965 * 2
def baseEnd_1956965 : Nat := 446606075122684932950039

theorem tailTrace_1956965 : CollatzResearch.WordTrace tailWord_1956965 prefixEnd_1956965 446606075122684932950039 := by
  unfold tailWord_1956965
  simp only [CollatzResearch.WordTrace]
  refine ⟨71376377355257502858256349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47584251570171668572170899 71376377355257502858256349)
  ·
    refine ⟨26766141508221563571846131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71376377355257502858256349 26766141508221563571846131)
    ·
      refine ⟨40149212262332345357769197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26766141508221563571846131 40149212262332345357769197)
      ·
        refine ⟨15055954598374629509163449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40149212262332345357769197 15055954598374629509163449)
        ·
          refine ⟨11291965948780972131872587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15055954598374629509163449 11291965948780972131872587)
          ·
            refine ⟨16937948923171458197808881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11291965948780972131872587 16937948923171458197808881)
            ·
              refine ⟨12703461692378593648356661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16937948923171458197808881 12703461692378593648356661)
              ·
                refine ⟨1190949533660493154533437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12703461692378593648356661 1190949533660493154533437)
                ·
                  refine ⟨446606075122684932950039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190949533660493154533437 446606075122684932950039)
                  ·
                    rfl

theorem cell21_1956965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_1956965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956965 prefixEnd_1956965 := by exact prefixLift 1956965
  have htrace : WordTrace (prefixWord ++ tailWord_1956965) baseStart_1956965 baseEnd_1956965 := by
    simpa [prefixWord, tailWord_1956965, baseEnd_1956965] using wordTrace_append hprefix tailTrace_1956965
  have hstable : (prefixWord ++ tailWord_1956965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956965).length < 2 ^ (prefixWord ++ tailWord_1956965).sum := by decide
  have hdescent : baseEnd_1956965 < baseStart_1956965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956982 : List Nat := [5, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_1956982 : Nat := 118140960795 + 1956982 * 2 ^ 59
def prefixEnd_1956982 : Nat := 4983230072969 + 3 ^ 40 * 1956982 * 2
def baseEnd_1956982 : Nat := 446609954754296681166671

theorem tailTrace_1956982 : CollatzResearch.WordTrace tailWord_1956982 prefixEnd_1956982 446609954754296681166671 := by
  unfold tailWord_1956982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4461062337262244672601575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47584664930797276507750133 4461062337262244672601575)
  ·
    refine ⟨6691593505893367008902363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4461062337262244672601575 6691593505893367008902363)
    ·
      refine ⟨10037390258840050513353545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6691593505893367008902363 10037390258840050513353545)
      ·
        refine ⟨7528042694130037885015159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10037390258840050513353545 7528042694130037885015159)
        ·
          refine ⟨11292064041195056827522739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7528042694130037885015159 11292064041195056827522739)
          ·
            refine ⟨16938096061792585241284109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11292064041195056827522739 16938096061792585241284109)
            ·
              refine ⟨6351786023172219465481541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16938096061792585241284109 6351786023172219465481541)
              ·
                refine ⟨1190959879344791149777789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6351786023172219465481541 1190959879344791149777789)
                ·
                  refine ⟨446609954754296681166671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190959879344791149777789 446609954754296681166671)
                  ·
                    rfl

theorem cell21_1956982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_1956982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1956982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1956982 prefixEnd_1956982 := by exact prefixLift 1956982
  have htrace : WordTrace (prefixWord ++ tailWord_1956982) baseStart_1956982 baseEnd_1956982 := by
    simpa [prefixWord, tailWord_1956982, baseEnd_1956982] using wordTrace_append hprefix tailTrace_1956982
  have hstable : (prefixWord ++ tailWord_1956982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956982).length < 2 ^ (prefixWord ++ tailWord_1956982).sum := by decide
  have hdescent : baseEnd_1956982 < baseStart_1956982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957041 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 5]
def baseStart_1957041 : Nat := 118140960795 + 1957041 * 2 ^ 59
def prefixEnd_1957041 : Nat := 4983230072969 + 3 ^ 40 * 1957041 * 2
def baseEnd_1957041 : Nat := 446623419358125689683217

theorem tailTrace_1957041 : CollatzResearch.WordTrace tailWord_1957041 prefixEnd_1957041 446623419358125689683217 := by
  unfold tailWord_1957041
  simp only [CollatzResearch.WordTrace]
  refine ⟨71379149302982167838022977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47586099535321445225348651 71379149302982167838022977)
  ·
    refine ⟨53534361977236625878517233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71379149302982167838022977 53534361977236625878517233)
    ·
      refine ⟨40150771482927469408887925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53534361977236625878517233 40150771482927469408887925)
      ·
        refine ⟨3764134826524450257083243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40150771482927469408887925 3764134826524450257083243)
        ·
          refine ⟨5646202239786675385624865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3764134826524450257083243 5646202239786675385624865)
          ·
            refine ⟨4234651679840006539218649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5646202239786675385624865 4234651679840006539218649)
            ·
              refine ⟨3175988759880004904413987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4234651679840006539218649 3175988759880004904413987)
              ·
                refine ⟨4763983139820007356620981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3175988759880004904413987 4763983139820007356620981)
                ·
                  refine ⟨446623419358125689683217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4763983139820007356620981 446623419358125689683217)
                  ·
                    rfl

theorem cell21_1957041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_1957041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957041 prefixEnd_1957041 := by exact prefixLift 1957041
  have htrace : WordTrace (prefixWord ++ tailWord_1957041) baseStart_1957041 baseEnd_1957041 := by
    simpa [prefixWord, tailWord_1957041, baseEnd_1957041] using wordTrace_append hprefix tailTrace_1957041
  have hstable : (prefixWord ++ tailWord_1957041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957041).length < 2 ^ (prefixWord ++ tailWord_1957041).sum := by decide
  have hdescent : baseEnd_1957041 < baseStart_1957041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957100 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 5]
def baseStart_1957100 : Nat := 118140960795 + 1957100 * 2 ^ 59
def prefixEnd_1957100 : Nat := 4983230072969 + 3 ^ 40 * 1957100 * 2
def baseEnd_1957100 : Nat := 446636883961954698199763

theorem tailTrace_1957100 : CollatzResearch.WordTrace tailWord_1957100 prefixEnd_1957100 446636883961954698199763 := by
  unfold tailWord_1957100
  simp only [CollatzResearch.WordTrace]
  refine ⟨35690650604884210457210377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47587534139845613942947169 35690650604884210457210377)
  ·
    refine ⟨26767987953663157842907783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35690650604884210457210377 26767987953663157842907783)
    ·
      refine ⟨40151981930494736764361675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26767987953663157842907783 40151981930494736764361675)
      ·
        refine ⟨60227972895742105146542513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40151981930494736764361675 60227972895742105146542513)
        ·
          refine ⟨45170979671806578859906885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60227972895742105146542513 45170979671806578859906885)
          ·
            refine ⟨8469558688463733536232541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45170979671806578859906885 8469558688463733536232541)
            ·
              refine ⟨3176084508173900076087203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8469558688463733536232541 3176084508173900076087203)
              ·
                refine ⟨4764126762260850114130805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3176084508173900076087203 4764126762260850114130805)
                ·
                  refine ⟨446636883961954698199763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4764126762260850114130805 446636883961954698199763)
                  ·
                    rfl

theorem cell21_1957100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_1957100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957100 prefixEnd_1957100 := by exact prefixLift 1957100
  have htrace : WordTrace (prefixWord ++ tailWord_1957100) baseStart_1957100 baseEnd_1957100 := by
    simpa [prefixWord, tailWord_1957100, baseEnd_1957100] using wordTrace_append hprefix tailTrace_1957100
  have hstable : (prefixWord ++ tailWord_1957100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957100).length < 2 ^ (prefixWord ++ tailWord_1957100).sum := by decide
  have hdescent : baseEnd_1957100 < baseStart_1957100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957106 : List Nat := [3, 2, 1, 3, 4, 1, 2, 1, 4]
def baseStart_1957106 : Nat := 118140960795 + 1957106 * 2 ^ 59
def prefixEnd_1957106 : Nat := 4983230072969 + 3 ^ 40 * 1957106 * 2
def baseEnd_1957106 : Nat := 446638253243700021099751

theorem tailTrace_1957106 : CollatzResearch.WordTrace tailWord_1957106 prefixEnd_1957106 446638253243700021099751 := by
  unfold tailWord_1957106
  simp only [CollatzResearch.WordTrace]
  refine ⟨17845380011936670984784793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47587680031831122626092781 17845380011936670984784793)
  ·
    refine ⟨13384035008952503238588595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17845380011936670984784793 13384035008952503238588595)
    ·
      refine ⟨20076052513428754857882893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13384035008952503238588595 20076052513428754857882893)
      ·
        refine ⟨7528519692535783071706085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20076052513428754857882893 7528519692535783071706085)
        ·
          refine ⟨1411597442350459325944891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7528519692535783071706085 1411597442350459325944891)
          ·
            refine ⟨2117396163525688988917337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411597442350459325944891 2117396163525688988917337)
            ·
              refine ⟨1588047122644266741688003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117396163525688988917337 1588047122644266741688003)
              ·
                refine ⟨2382070683966400112532005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588047122644266741688003 2382070683966400112532005)
                ·
                  refine ⟨446638253243700021099751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2382070683966400112532005 446638253243700021099751)
                  ·
                    rfl

theorem cell21_1957106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_1957106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957106 prefixEnd_1957106 := by exact prefixLift 1957106
  have htrace : WordTrace (prefixWord ++ tailWord_1957106) baseStart_1957106 baseEnd_1957106 := by
    simpa [prefixWord, tailWord_1957106, baseEnd_1957106] using wordTrace_append hprefix tailTrace_1957106
  have hstable : (prefixWord ++ tailWord_1957106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957106).length < 2 ^ (prefixWord ++ tailWord_1957106).sum := by decide
  have hdescent : baseEnd_1957106 < baseStart_1957106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957151 : List Nat := [1, 1, 2, 4, 4, 2, 2, 2, 3]
def baseStart_1957151 : Nat := 118140960795 + 1957151 * 2 ^ 59
def prefixEnd_1957151 : Nat := 4983230072969 + 3 ^ 40 * 1957151 * 2
def baseEnd_1957151 : Nat := 446648522856789942849659

theorem tailTrace_1957151 : CollatzResearch.WordTrace tailWord_1957151 prefixEnd_1957151 446648522856789942849659 := by
  unfold tailWord_1957151
  simp only [CollatzResearch.WordTrace]
  refine ⟨71383161332583656624527307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47588774221722437749684871 71383161332583656624527307)
  ·
    refine ⟨107074741998875484936790961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71383161332583656624527307 107074741998875484936790961)
    ·
      refine ⟨80306056499156613702593221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107074741998875484936790961 80306056499156613702593221)
      ·
        refine ⟨15057385593591865069236229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80306056499156613702593221 15057385593591865069236229)
        ·
          refine ⟨2823259798798474700481793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15057385593591865069236229 2823259798798474700481793)
          ·
            refine ⟨2117444849098856025361345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2823259798798474700481793 2117444849098856025361345)
            ·
              refine ⟨1588083636824142019021009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117444849098856025361345 1588083636824142019021009)
              ·
                refine ⟨1191062727618106514265757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1588083636824142019021009 1191062727618106514265757)
                ·
                  refine ⟨446648522856789942849659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1191062727618106514265757 446648522856789942849659)
                  ·
                    rfl

theorem cell21_1957151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 3].length) (baseStart_1957151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957151 prefixEnd_1957151 := by exact prefixLift 1957151
  have htrace : WordTrace (prefixWord ++ tailWord_1957151) baseStart_1957151 baseEnd_1957151 := by
    simpa [prefixWord, tailWord_1957151, baseEnd_1957151] using wordTrace_append hprefix tailTrace_1957151
  have hstable : (prefixWord ++ tailWord_1957151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957151).length < 2 ^ (prefixWord ++ tailWord_1957151).sum := by decide
  have hdescent : baseEnd_1957151 < baseStart_1957151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957162 : List Nat := [3, 1, 4, 2, 1, 1, 3, 6]
def baseStart_1957162 : Nat := 118140960795 + 1957162 * 2 ^ 59
def prefixEnd_1957162 : Nat := 4983230072969 + 3 ^ 40 * 1957162 * 2
def baseEnd_1957162 : Nat := 148883677735552122722101

theorem tailTrace_1957162 : CollatzResearch.WordTrace tailWord_1957162 prefixEnd_1957162 148883677735552122722101 := by
  unfold tailWord_1957162
  simp only [CollatzResearch.WordTrace]
  refine ⟨17845890633885951375794435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47589041690362537002118493 17845890633885951375794435)
  ·
    refine ⟨26768835950828927063691653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17845890633885951375794435 26768835950828927063691653)
    ·
      refine ⟨5019156740780423824442185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26768835950828927063691653 5019156740780423824442185)
      ·
        refine ⟨3764367555585317868331639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5019156740780423824442185 3764367555585317868331639)
        ·
          refine ⟨5646551333377976802497459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3764367555585317868331639 5646551333377976802497459)
          ·
            refine ⟨8469827000066965203746189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5646551333377976802497459 8469827000066965203746189)
            ·
              refine ⟨3176185125025111951404821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8469827000066965203746189 3176185125025111951404821)
              ·
                refine ⟨148883677735552122722101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3176185125025111951404821 148883677735552122722101)
                ·
                  rfl

theorem cell21_1957162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_1957162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957162 prefixEnd_1957162 := by exact prefixLift 1957162
  have htrace : WordTrace (prefixWord ++ tailWord_1957162) baseStart_1957162 baseEnd_1957162 := by
    simpa [prefixWord, tailWord_1957162, baseEnd_1957162] using wordTrace_append hprefix tailTrace_1957162
  have hstable : (prefixWord ++ tailWord_1957162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957162).length < 2 ^ (prefixWord ++ tailWord_1957162).sum := by decide
  have hdescent : baseEnd_1957162 < baseStart_1957162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957207 : List Nat := [1, 1, 3, 2, 3, 2, 3, 2, 4]
def baseStart_1957207 : Nat := 118140960795 + 1957207 * 2 ^ 59
def prefixEnd_1957207 : Nat := 4983230072969 + 3 ^ 40 * 1957207 * 2
def baseEnd_1957207 : Nat := 446661302819746289916211

theorem tailTrace_1957207 : CollatzResearch.WordTrace tailWord_1957207 prefixEnd_1957207 446661302819746289916211 := by
  unfold tailWord_1957207
  simp only [CollatzResearch.WordTrace]
  refine ⟨71385203820380778188565875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47590135880253852125710583 71385203820380778188565875)
  ·
    refine ⟨107077805730571167282848813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71385203820380778188565875 107077805730571167282848813)
    ·
      refine ⟨40154177148964187731068305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107077805730571167282848813 40154177148964187731068305)
      ·
        refine ⟨30115632861723140798301229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40154177148964187731068305 30115632861723140798301229)
        ·
          refine ⟨11293362323146177799362961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30115632861723140798301229 11293362323146177799362961)
          ·
            refine ⟨8470021742359633349522221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11293362323146177799362961 8470021742359633349522221)
            ·
              refine ⟨3176258153384862506070833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8470021742359633349522221 3176258153384862506070833)
              ·
                refine ⟨2382193615038646879553125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3176258153384862506070833 2382193615038646879553125)
                ·
                  refine ⟨446661302819746289916211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2382193615038646879553125 446661302819746289916211)
                  ·
                    rfl

theorem cell21_1957207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 4].length) (baseStart_1957207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957207 prefixEnd_1957207 := by exact prefixLift 1957207
  have htrace : WordTrace (prefixWord ++ tailWord_1957207) baseStart_1957207 baseEnd_1957207 := by
    simpa [prefixWord, tailWord_1957207, baseEnd_1957207] using wordTrace_append hprefix tailTrace_1957207
  have hstable : (prefixWord ++ tailWord_1957207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957207).length < 2 ^ (prefixWord ++ tailWord_1957207).sum := by decide
  have hdescent : baseEnd_1957207 < baseStart_1957207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957328 : List Nat := [2, 1, 1, 1, 1, 2, 2, 8, 3]
def baseStart_1957328 : Nat := 118140960795 + 1957328 * 2 ^ 59
def prefixEnd_1957328 : Nat := 4983230072969 + 3 ^ 40 * 1957328 * 2
def baseEnd_1957328 : Nat := 446688916668276968399297

theorem tailTrace_1957328 : CollatzResearch.WordTrace tailWord_1957328 prefixEnd_1957328 446688916668276968399297 := by
  unfold tailWord_1957328
  simp only [CollatzResearch.WordTrace]
  refine ⟨35694808526471207926860319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47593078035294943902480425 35694808526471207926860319)
  ·
    refine ⟨53542212789706811890290479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35694808526471207926860319 53542212789706811890290479)
    ·
      refine ⟨80313319184560217835435719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53542212789706811890290479 80313319184560217835435719)
      ·
        refine ⟨120469978776840326753153579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80313319184560217835435719 120469978776840326753153579)
        ·
          refine ⟨180704968165260490129730369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120469978776840326753153579 180704968165260490129730369)
          ·
            refine ⟨135528726123945367597297777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180704968165260490129730369 135528726123945367597297777)
            ·
              refine ⟨101646544592959025697973333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135528726123945367597297777 101646544592959025697973333)
              ·
                refine ⟨1191170444448738582398125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 101646544592959025697973333 1191170444448738582398125)
                ·
                  refine ⟨446688916668276968399297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1191170444448738582398125 446688916668276968399297)
                  ·
                    rfl

theorem cell21_1957328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 3].length) (baseStart_1957328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957328 prefixEnd_1957328 := by exact prefixLift 1957328
  have htrace : WordTrace (prefixWord ++ tailWord_1957328) baseStart_1957328 baseEnd_1957328 := by
    simpa [prefixWord, tailWord_1957328, baseEnd_1957328] using wordTrace_append hprefix tailTrace_1957328
  have hstable : (prefixWord ++ tailWord_1957328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957328).length < 2 ^ (prefixWord ++ tailWord_1957328).sum := by decide
  have hdescent : baseEnd_1957328 < baseStart_1957328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957362 : List Nat := [3, 2, 1, 4, 1, 2, 2, 3, 3]
def baseStart_1957362 : Nat := 118140960795 + 1957362 * 2 ^ 59
def prefixEnd_1957362 : Nat := 4983230072969 + 3 ^ 40 * 1957362 * 2
def baseEnd_1957362 : Nat := 446696675931500464832561

theorem tailTrace_1957362 : CollatzResearch.WordTrace tailWord_1957362 prefixEnd_1957362 446696675931500464832561 := by
  unfold tailWord_1957362
  simp only [CollatzResearch.WordTrace]
  refine ⟨17847714283704809915114585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47593904756546159773638893 17847714283704809915114585)
  ·
    refine ⟨13385785712778607436335939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17847714283704809915114585 13385785712778607436335939)
    ·
      refine ⟨20078678569167911154503909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13385785712778607436335939 20078678569167911154503909)
      ·
        refine ⟨3764752231718983341469483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20078678569167911154503909 3764752231718983341469483)
        ·
          refine ⟨5647128347578475012204225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3764752231718983341469483 5647128347578475012204225)
          ·
            refine ⟨4235346260683856259153169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5647128347578475012204225 4235346260683856259153169)
            ·
              refine ⟨3176509695512892194364877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4235346260683856259153169 3176509695512892194364877)
              ·
                refine ⟨1191191135817334572886829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3176509695512892194364877 1191191135817334572886829)
                ·
                  refine ⟨446696675931500464832561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1191191135817334572886829 446696675931500464832561)
                  ·
                    rfl

theorem cell21_1957362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_1957362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957362 prefixEnd_1957362 := by exact prefixLift 1957362
  have htrace : WordTrace (prefixWord ++ tailWord_1957362) baseStart_1957362 baseEnd_1957362 := by
    simpa [prefixWord, tailWord_1957362, baseEnd_1957362] using wordTrace_append hprefix tailTrace_1957362
  have hstable : (prefixWord ++ tailWord_1957362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957362).length < 2 ^ (prefixWord ++ tailWord_1957362).sum := by decide
  have hdescent : baseEnd_1957362 < baseStart_1957362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957401 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 10]
def baseStart_1957401 : Nat := 118140960795 + 1957401 * 2 ^ 59
def prefixEnd_1957401 : Nat := 4983230072969 + 3 ^ 40 * 1957401 * 2
def baseEnd_1957401 : Nat := 446705576262845063682481

theorem tailTrace_1957401 : CollatzResearch.WordTrace tailWord_1957401 prefixEnd_1957401 446705576262845063682481 := by
  unfold tailWord_1957401
  simp only [CollatzResearch.WordTrace]
  refine ⟨71392279581677949321128057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47594853054451966214085371 71392279581677949321128057)
  ·
    refine ⟨53544209686258461990846043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71392279581677949321128057 53544209686258461990846043)
    ·
      refine ⟨80316314529387692986269065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53544209686258461990846043 80316314529387692986269065)
      ·
        refine ⟨60237235897040769739701799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80316314529387692986269065 60237235897040769739701799)
        ·
          refine ⟨90355853845561154609552699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60237235897040769739701799 90355853845561154609552699)
          ·
            refine ⟨135533780768341731914329049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90355853845561154609552699 135533780768341731914329049)
            ·
              refine ⟨101650335576256298935746787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135533780768341731914329049 101650335576256298935746787)
              ·
                refine ⟨152475503364384448403620181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101650335576256298935746787 152475503364384448403620181)
                ·
                  refine ⟨446705576262845063682481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 152475503364384448403620181 446705576262845063682481)
                  ·
                    rfl

theorem cell21_1957401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_1957401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957401 prefixEnd_1957401 := by exact prefixLift 1957401
  have htrace : WordTrace (prefixWord ++ tailWord_1957401) baseStart_1957401 baseEnd_1957401 := by
    simpa [prefixWord, tailWord_1957401, baseEnd_1957401] using wordTrace_append hprefix tailTrace_1957401
  have hstable : (prefixWord ++ tailWord_1957401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957401).length < 2 ^ (prefixWord ++ tailWord_1957401).sum := by decide
  have hdescent : baseEnd_1957401 < baseStart_1957401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957418 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 8]
def baseStart_1957418 : Nat := 118140960795 + 1957418 * 2 ^ 59
def prefixEnd_1957418 : Nat := 4983230072969 + 3 ^ 40 * 1957418 * 2
def baseEnd_1957418 : Nat := 446709455894456811899113

theorem tailTrace_1957418 : CollatzResearch.WordTrace tailWord_1957418 prefixEnd_1957418 446709455894456811899113 := by
  unfold tailWord_1957418
  simp only [CollatzResearch.WordTrace]
  refine ⟨17848224905654090306124227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47595266415077574149664605 17848224905654090306124227)
  ·
    refine ⟨26772337358481135459186341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17848224905654090306124227 26772337358481135459186341)
    ·
      refine ⟨5019813254715212898597439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26772337358481135459186341 5019813254715212898597439)
      ·
        refine ⟨7529719882072819347896159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5019813254715212898597439 7529719882072819347896159)
        ·
          refine ⟨11294579823109229021844239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7529719882072819347896159 11294579823109229021844239)
          ·
            refine ⟨16941869734663843532766359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11294579823109229021844239 16941869734663843532766359)
            ·
              refine ⟨25412804601995765299149539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16941869734663843532766359 25412804601995765299149539)
              ·
                refine ⟨38119206902993647948724309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25412804601995765299149539 38119206902993647948724309)
                ·
                  refine ⟨446709455894456811899113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38119206902993647948724309 446709455894456811899113)
                  ·
                    rfl

theorem cell21_1957418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_1957418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957418 prefixEnd_1957418 := by exact prefixLift 1957418
  have htrace : WordTrace (prefixWord ++ tailWord_1957418) baseStart_1957418 baseEnd_1957418 := by
    simpa [prefixWord, tailWord_1957418, baseEnd_1957418] using wordTrace_append hprefix tailTrace_1957418
  have hstable : (prefixWord ++ tailWord_1957418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957418).length < 2 ^ (prefixWord ++ tailWord_1957418).sum := by decide
  have hdescent : baseEnd_1957418 < baseStart_1957418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957432 : List Nat := [2, 1, 2, 1, 4, 2, 9]
def baseStart_1957432 : Nat := 118140960795 + 1957432 * 2 ^ 59
def prefixEnd_1957432 : Nat := 4983230072969 + 3 ^ 40 * 1957432 * 2
def baseEnd_1957432 : Nat := 49634738987243988740639

theorem tailTrace_1957432 : CollatzResearch.WordTrace tailWord_1957432 prefixEnd_1957432 49634738987243988740639 := by
  unfold tailWord_1957432
  simp only [CollatzResearch.WordTrace]
  refine ⟨35696705122282820807753275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47595606829710427743671033 35696705122282820807753275)
  ·
    refine ⟨53545057683424231211629913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35696705122282820807753275 53545057683424231211629913)
    ·
      refine ⟨40158793262568173408722435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53545057683424231211629913 40158793262568173408722435)
      ·
        refine ⟨60238189893852260113083653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40158793262568173408722435 60238189893852260113083653)
        ·
          refine ⟨11294660605097298771203185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60238189893852260113083653 11294660605097298771203185)
          ·
            refine ⟨8470995453822974078402389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11294660605097298771203185 8470995453822974078402389)
            ·
              refine ⟨49634738987243988740639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8470995453822974078402389 49634738987243988740639)
              ·
                rfl

theorem cell21_1957432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 9].length) (baseStart_1957432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957432 prefixEnd_1957432 := by exact prefixLift 1957432
  have htrace : WordTrace (prefixWord ++ tailWord_1957432) baseStart_1957432 baseEnd_1957432 := by
    simpa [prefixWord, tailWord_1957432, baseEnd_1957432] using wordTrace_append hprefix tailTrace_1957432
  have hstable : (prefixWord ++ tailWord_1957432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957432).length < 2 ^ (prefixWord ++ tailWord_1957432).sum := by decide
  have hdescent : baseEnd_1957432 < baseStart_1957432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957452 : List Nat := [2, 2, 1, 3, 1, 5, 2, 1, 4]
def baseStart_1957452 : Nat := 118140960795 + 1957452 * 2 ^ 59
def prefixEnd_1957452 : Nat := 4983230072969 + 3 ^ 40 * 1957452 * 2
def baseEnd_1957452 : Nat := 446717215157680308332377

theorem tailTrace_1957452 : CollatzResearch.WordTrace tailWord_1957452 prefixEnd_1957452 446717215157680308332377 := by
  unfold tailWord_1957452
  simp only [CollatzResearch.WordTrace]
  refine ⟨35697069852246592515617305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47596093136328790020823073 35697069852246592515617305)
  ·
    refine ⟨26772802389184944386712979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35697069852246592515617305 26772802389184944386712979)
    ·
      refine ⟨40159203583777416580069469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26772802389184944386712979 40159203583777416580069469)
      ·
        refine ⟨15059701343916531217526051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40159203583777416580069469 15059701343916531217526051)
        ·
          refine ⟨22589552015874796826289077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15059701343916531217526051 22589552015874796826289077)
          ·
            refine ⟨2117770501488262202464601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22589552015874796826289077 2117770501488262202464601)
            ·
              refine ⟨1588327876116196651848451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117770501488262202464601 1588327876116196651848451)
              ·
                refine ⟨2382491814174294977772677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588327876116196651848451 2382491814174294977772677)
                ·
                  refine ⟨446717215157680308332377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2382491814174294977772677 446717215157680308332377)
                  ·
                    rfl

theorem cell21_1957452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_1957452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957452 prefixEnd_1957452 := by exact prefixLift 1957452
  have htrace : WordTrace (prefixWord ++ tailWord_1957452) baseStart_1957452 baseEnd_1957452 := by
    simpa [prefixWord, tailWord_1957452, baseEnd_1957452] using wordTrace_append hprefix tailTrace_1957452
  have hstable : (prefixWord ++ tailWord_1957452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957452).length < 2 ^ (prefixWord ++ tailWord_1957452).sum := by decide
  have hdescent : baseEnd_1957452 < baseStart_1957452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957601 : List Nat := [1, 2, 3, 1, 5, 2, 7]
def baseStart_1957601 : Nat := 118140960795 + 1957601 * 2 ^ 59
def prefixEnd_1957601 : Nat := 4983230072969 + 3 ^ 40 * 1957601 * 2
def baseEnd_1957601 : Nat := 49639024331965462260971

theorem tailTrace_1957601 : CollatzResearch.WordTrace tailWord_1957601 prefixEnd_1957601 49639024331965462260971 := by
  unfold tailWord_1957601
  simp only [CollatzResearch.WordTrace]
  refine ⟨71399574180953383478408657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47599716120635588985605771 71399574180953383478408657)
  ·
    refine ⟨53549680635715037608806493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71399574180953383478408657 53549680635715037608806493)
    ·
      refine ⟨20081130238393139103302435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53549680635715037608806493 20081130238393139103302435)
      ·
        refine ⟨30121695357589708654953653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20081130238393139103302435 30121695357589708654953653)
        ·
          refine ⟨2823908939774035186401905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30121695357589708654953653 2823908939774035186401905)
          ·
            refine ⟨2117931704830526389801429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2823908939774035186401905 2117931704830526389801429)
            ·
              refine ⟨49639024331965462260971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2117931704830526389801429 49639024331965462260971)
              ·
                rfl

theorem cell21_1957601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 7].length) (baseStart_1957601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957601 prefixEnd_1957601 := by exact prefixLift 1957601
  have htrace : WordTrace (prefixWord ++ tailWord_1957601) baseStart_1957601 baseEnd_1957601 := by
    simpa [prefixWord, tailWord_1957601, baseEnd_1957601] using wordTrace_append hprefix tailTrace_1957601
  have hstable : (prefixWord ++ tailWord_1957601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957601).length < 2 ^ (prefixWord ++ tailWord_1957601).sum := by decide
  have hdescent : baseEnd_1957601 < baseStart_1957601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957607 : List Nat := [1, 1, 5, 4, 1, 1, 3, 2, 3]
def baseStart_1957607 : Nat := 118140960795 + 1957607 * 2 ^ 59
def prefixEnd_1957607 : Nat := 4983230072969 + 3 ^ 40 * 1957607 * 2
def baseEnd_1957607 : Nat := 446752588269434483248727

theorem tailTrace_1957607 : CollatzResearch.WordTrace tailWord_1957607 prefixEnd_1957607 446752588269434483248727 := by
  unfold tailWord_1957607
  simp only [CollatzResearch.WordTrace]
  refine ⟨71399793018931646503127075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47599862012621097668751383 71399793018931646503127075)
  ·
    refine ⟨107099689528397469754690613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71399793018931646503127075 107099689528397469754690613)
    ·
      refine ⟨10040595893287262789502245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107099689528397469754690613 10040595893287262789502245)
      ·
        refine ⟨1882611729991361773031671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10040595893287262789502245 1882611729991361773031671)
        ·
          refine ⟨2823917594987042659547507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1882611729991361773031671 2823917594987042659547507)
          ·
            refine ⟨4235876392480563989321261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2823917594987042659547507 4235876392480563989321261)
            ·
              refine ⟨1588453647180211495995473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4235876392480563989321261 1588453647180211495995473)
              ·
                refine ⟨1191340235385158621996605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1588453647180211495995473 1191340235385158621996605)
                ·
                  refine ⟨446752588269434483248727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1191340235385158621996605 446752588269434483248727)
                  ·
                    rfl

theorem cell21_1957607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 3].length) (baseStart_1957607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957607 prefixEnd_1957607 := by exact prefixLift 1957607
  have htrace : WordTrace (prefixWord ++ tailWord_1957607) baseStart_1957607 baseEnd_1957607 := by
    simpa [prefixWord, tailWord_1957607, baseEnd_1957607] using wordTrace_append hprefix tailTrace_1957607
  have hstable : (prefixWord ++ tailWord_1957607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957607).length < 2 ^ (prefixWord ++ tailWord_1957607).sum := by decide
  have hdescent : baseEnd_1957607 < baseStart_1957607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957629 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 8]
def baseStart_1957629 : Nat := 118140960795 + 1957629 * 2 ^ 59
def prefixEnd_1957629 : Nat := 4983230072969 + 3 ^ 40 * 1957629 * 2
def baseEnd_1957629 : Nat := 446757608969167333882015

theorem tailTrace_1957629 : CollatzResearch.WordTrace tailWord_1957629 prefixEnd_1957629 446757608969167333882015 := by
  unfold tailWord_1957629
  simp only [CollatzResearch.WordTrace]
  refine ⟨71400595424851944260427941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47600396949901296173618627 71400595424851944260427941)
  ·
    refine ⟨13387611642159739548830239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71400595424851944260427941 13387611642159739548830239)
    ·
      refine ⟨20081417463239609323245359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13387611642159739548830239 20081417463239609323245359)
      ·
        refine ⟨30122126194859413984868039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20081417463239609323245359 30122126194859413984868039)
        ·
          refine ⟨45183189292289120977302059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30122126194859413984868039 45183189292289120977302059)
          ·
            refine ⟨67774783938433681465953089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45183189292289120977302059 67774783938433681465953089)
            ·
              refine ⟨50831087953825261099464817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67774783938433681465953089 50831087953825261099464817)
              ·
                refine ⟨38123315965368945824598613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50831087953825261099464817 38123315965368945824598613)
                ·
                  refine ⟨446757608969167333882015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38123315965368945824598613 446757608969167333882015)
                  ·
                    rfl

theorem cell21_1957629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_1957629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957629 prefixEnd_1957629 := by exact prefixLift 1957629
  have htrace : WordTrace (prefixWord ++ tailWord_1957629) baseStart_1957629 baseEnd_1957629 := by
    simpa [prefixWord, tailWord_1957629, baseEnd_1957629] using wordTrace_append hprefix tailTrace_1957629
  have hstable : (prefixWord ++ tailWord_1957629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957629).length < 2 ^ (prefixWord ++ tailWord_1957629).sum := by decide
  have hdescent : baseEnd_1957629 < baseStart_1957629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957694 : List Nat := [4, 2, 1, 2, 2, 2, 3, 5]
def baseStart_1957694 : Nat := 118140960795 + 1957694 * 2 ^ 59
def prefixEnd_1957694 : Nat := 4983230072969 + 3 ^ 40 * 1957694 * 2
def baseEnd_1957694 : Nat := 148924147618247221766183

theorem tailTrace_1957694 : CollatzResearch.WordTrace tailWord_1957694 prefixEnd_1957694 148924147618247221766183 := by
  unfold tailWord_1957694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8925370771202057545193017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47601977446410973574362757 8925370771202057545193017)
  ·
    refine ⟨6694028078401543158894763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8925370771202057545193017 6694028078401543158894763)
    ·
      refine ⟨10041042117602314738342145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6694028078401543158894763 10041042117602314738342145)
      ·
        refine ⟨7530781588201736053756609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10041042117602314738342145 7530781588201736053756609)
        ·
          refine ⟨5648086191151302040317457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7530781588201736053756609 5648086191151302040317457)
          ·
            refine ⟨4236064643363476530238093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5648086191151302040317457 4236064643363476530238093)
            ·
              refine ⟨1588524241261303698839285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4236064643363476530238093 1588524241261303698839285)
              ·
                refine ⟨148924147618247221766183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1588524241261303698839285 148924147618247221766183)
                ·
                  rfl

theorem cell21_1957694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_1957694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957694 prefixEnd_1957694 := by exact prefixLift 1957694
  have htrace : WordTrace (prefixWord ++ tailWord_1957694) baseStart_1957694 baseEnd_1957694 := by
    simpa [prefixWord, tailWord_1957694, baseEnd_1957694] using wordTrace_append hprefix tailTrace_1957694
  have hstable : (prefixWord ++ tailWord_1957694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957694).length < 2 ^ (prefixWord ++ tailWord_1957694).sum := by decide
  have hdescent : baseEnd_1957694 < baseStart_1957694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957705 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 6]
def baseStart_1957705 : Nat := 118140960795 + 1957705 * 2 ^ 59
def prefixEnd_1957705 : Nat := 4983230072969 + 3 ^ 40 * 1957705 * 2
def baseEnd_1957705 : Nat := 446774953204608090615193

theorem tailTrace_1957705 : CollatzResearch.WordTrace tailWord_1957705 prefixEnd_1957705 446774953204608090615193 := by
  unfold tailWord_1957705
  simp only [CollatzResearch.WordTrace]
  refine ⟨71403367372576609240194569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47602244915051072826796379 71403367372576609240194569)
  ·
    refine ⟨53552525529432456930145927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71403367372576609240194569 53552525529432456930145927)
    ·
      refine ⟨80328788294148685395218891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53552525529432456930145927 80328788294148685395218891)
      ·
        refine ⟨120493182441223028092828337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80328788294148685395218891 120493182441223028092828337)
        ·
          refine ⟨90369886830917271069621253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120493182441223028092828337 90369886830917271069621253)
          ·
            refine ⟨16944353780796988325553985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90369886830917271069621253 16944353780796988325553985)
            ·
              refine ⟨12708265335597741244165489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16944353780796988325553985 12708265335597741244165489)
              ·
                refine ⟨9531199001698305933124117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12708265335597741244165489 9531199001698305933124117)
                ·
                  refine ⟨446774953204608090615193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9531199001698305933124117 446774953204608090615193)
                  ·
                    rfl

theorem cell21_1957705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_1957705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957705 prefixEnd_1957705 := by exact prefixLift 1957705
  have htrace : WordTrace (prefixWord ++ tailWord_1957705) baseStart_1957705 baseEnd_1957705 := by
    simpa [prefixWord, tailWord_1957705, baseEnd_1957705] using wordTrace_append hprefix tailTrace_1957705
  have hstable : (prefixWord ++ tailWord_1957705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957705).length < 2 ^ (prefixWord ++ tailWord_1957705).sum := by decide
  have hdescent : baseEnd_1957705 < baseStart_1957705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957736 : List Nat := [2, 1, 4, 2, 1, 1, 2, 8]
def baseStart_1957736 : Nat := 118140960795 + 1957736 * 2 ^ 59
def prefixEnd_1957736 : Nat := 4983230072969 + 3 ^ 40 * 1957736 * 2
def baseEnd_1957736 : Nat := 148927342608986308532821

theorem tailTrace_1957736 : CollatzResearch.WordTrace tailWord_1957736 prefixEnd_1957736 148927342608986308532821 := by
  unfold tailWord_1957736
  simp only [CollatzResearch.WordTrace]
  refine ⟨35702249017732150767286531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47602998690309534356382041 35702249017732150767286531)
  ·
    refine ⟨53553373526598226150929797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35702249017732150767286531 53553373526598226150929797)
    ·
      refine ⟨10041257536237167403299337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53553373526598226150929797 10041257536237167403299337)
      ·
        refine ⟨7530943152177875552474503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10041257536237167403299337 7530943152177875552474503)
        ·
          refine ⟨11296414728266813328711755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7530943152177875552474503 11296414728266813328711755)
          ·
            refine ⟨16944622092400219993067633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11296414728266813328711755 16944622092400219993067633)
            ·
              refine ⟨12708466569300164994800725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16944622092400219993067633 12708466569300164994800725)
              ·
                refine ⟨148927342608986308532821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12708466569300164994800725 148927342608986308532821)
                ·
                  rfl

theorem cell21_1957736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 8].length) (baseStart_1957736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957736 prefixEnd_1957736 := by exact prefixLift 1957736
  have htrace : WordTrace (prefixWord ++ tailWord_1957736) baseStart_1957736 baseEnd_1957736 := by
    simpa [prefixWord, tailWord_1957736, baseEnd_1957736] using wordTrace_append hprefix tailTrace_1957736
  have hstable : (prefixWord ++ tailWord_1957736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957736).length < 2 ^ (prefixWord ++ tailWord_1957736).sum := by decide
  have hdescent : baseEnd_1957736 < baseStart_1957736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957770 : List Nat := [3, 1, 2, 4, 3, 1, 7]
def baseStart_1957770 : Nat := 118140960795 + 1957770 * 2 ^ 59
def prefixEnd_1957770 : Nat := 4983230072969 + 3 ^ 40 * 1957770 * 2
def baseEnd_1957770 : Nat := 49643309676686935781303

theorem tailTrace_1957770 : CollatzResearch.WordTrace tailWord_1957770 prefixEnd_1957770 49643309676686935781303 := by
  unfold tailWord_1957770
  simp only [CollatzResearch.WordTrace]
  refine ⟨17851434529335281335327691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47603825411560750227540509 17851434529335281335327691)
  ·
    refine ⟨26777151794002922002991537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17851434529335281335327691 26777151794002922002991537)
    ·
      refine ⟨20082863845502191502243653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26777151794002922002991537 20082863845502191502243653)
      ·
        refine ⟨3765536971031660906670685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20082863845502191502243653 3765536971031660906670685)
        ·
          refine ⟨1412076364136872840001507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3765536971031660906670685 1412076364136872840001507)
          ·
            refine ⟨2118114546205309260002261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412076364136872840001507 2118114546205309260002261)
            ·
              refine ⟨49643309676686935781303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2118114546205309260002261 49643309676686935781303)
              ·
                rfl

theorem cell21_1957770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 7].length) (baseStart_1957770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957770 prefixEnd_1957770 := by exact prefixLift 1957770
  have htrace : WordTrace (prefixWord ++ tailWord_1957770) baseStart_1957770 baseEnd_1957770 := by
    simpa [prefixWord, tailWord_1957770, baseEnd_1957770] using wordTrace_append hprefix tailTrace_1957770
  have hstable : (prefixWord ++ tailWord_1957770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957770).length < 2 ^ (prefixWord ++ tailWord_1957770).sum := by decide
  have hdescent : baseEnd_1957770 < baseStart_1957770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957781 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 6]
def baseStart_1957781 : Nat := 118140960795 + 1957781 * 2 ^ 59
def prefixEnd_1957781 : Nat := 4983230072969 + 3 ^ 40 * 1957781 * 2
def baseEnd_1957781 : Nat := 446792297440048847348371

theorem tailTrace_1957781 : CollatzResearch.WordTrace tailWord_1957781 prefixEnd_1957781 446792297440048847348371 := by
  unfold tailWord_1957781
  simp only [CollatzResearch.WordTrace]
  refine ⟨71406139320301274219961197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47604092880200849479974131 71406139320301274219961197)
  ·
    refine ⟨26777302245112977832485449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71406139320301274219961197 26777302245112977832485449)
    ·
      refine ⟨20082976683834733374364087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26777302245112977832485449 20082976683834733374364087)
      ·
        refine ⟨30124465025752100061546131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20082976683834733374364087 30124465025752100061546131)
        ·
          refine ⟨45186697538628150092319197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30124465025752100061546131 45186697538628150092319197)
          ·
            refine ⟨16945011576985556284619699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45186697538628150092319197 16945011576985556284619699)
            ·
              refine ⟨25417517365478334426929549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16945011576985556284619699 25417517365478334426929549)
              ·
                refine ⟨9531569012054375410098581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25417517365478334426929549 9531569012054375410098581)
                ·
                  refine ⟨446792297440048847348371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9531569012054375410098581 446792297440048847348371)
                  ·
                    rfl

theorem cell21_1957781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_1957781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957781 prefixEnd_1957781 := by exact prefixLift 1957781
  have htrace : WordTrace (prefixWord ++ tailWord_1957781) baseStart_1957781 baseEnd_1957781 := by
    simpa [prefixWord, tailWord_1957781, baseEnd_1957781] using wordTrace_append hprefix tailTrace_1957781
  have hstable : (prefixWord ++ tailWord_1957781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957781).length < 2 ^ (prefixWord ++ tailWord_1957781).sum := by decide
  have hdescent : baseEnd_1957781 < baseStart_1957781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957790 : List Nat := [4, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1957790 : Nat := 118140960795 + 1957790 * 2 ^ 59
def prefixEnd_1957790 : Nat := 4983230072969 + 3 ^ 40 * 1957790 * 2
def baseEnd_1957790 : Nat := 446794351362666831698353

theorem tailTrace_1957790 : CollatzResearch.WordTrace tailWord_1957790 prefixEnd_1957790 446794351362666831698353 := by
  unfold tailWord_1957790
  simp only [CollatzResearch.WordTrace]
  refine ⟨8925808447158583594629853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47604311718179112504692549 8925808447158583594629853)
  ·
    refine ⟨3347178167684468847986195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8925808447158583594629853 3347178167684468847986195)
    ·
      refine ⟨5020767251526703271979293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3347178167684468847986195 5020767251526703271979293)
      ·
        refine ⟨1882787719322513726992235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5020767251526703271979293 1882787719322513726992235)
        ·
          refine ⟨2824181578983770590488353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1882787719322513726992235 2824181578983770590488353)
          ·
            refine ⟨2118136184237827942866265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2824181578983770590488353 2118136184237827942866265)
            ·
              refine ⟨1588602138178370957149699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2118136184237827942866265 1588602138178370957149699)
              ·
                refine ⟨2382903207267556435724549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588602138178370957149699 2382903207267556435724549)
                ·
                  refine ⟨446794351362666831698353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2382903207267556435724549 446794351362666831698353)
                  ·
                    rfl

theorem cell21_1957790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1957790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957790 prefixEnd_1957790 := by exact prefixLift 1957790
  have htrace : WordTrace (prefixWord ++ tailWord_1957790) baseStart_1957790 baseEnd_1957790 := by
    simpa [prefixWord, tailWord_1957790, baseEnd_1957790] using wordTrace_append hprefix tailTrace_1957790
  have hstable : (prefixWord ++ tailWord_1957790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957790).length < 2 ^ (prefixWord ++ tailWord_1957790).sum := by decide
  have hdescent : baseEnd_1957790 < baseStart_1957790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957936 : List Nat := [2, 1, 1, 1, 2, 5, 3, 3, 3]
def baseStart_1957936 : Nat := 118140960795 + 1957936 * 2 ^ 59
def prefixEnd_1957936 : Nat := 4983230072969 + 3 ^ 40 * 1957936 * 2
def baseEnd_1957936 : Nat := 446827670551803022264721

theorem tailTrace_1957936 : CollatzResearch.WordTrace tailWord_1957936 prefixEnd_1957936 446827670551803022264721 := by
  unfold tailWord_1957936
  simp only [CollatzResearch.WordTrace]
  refine ⟨35705896317369867845926831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47607861756493157127902441 35705896317369867845926831)
  ·
    refine ⟨53558844476054801768890247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35705896317369867845926831 53558844476054801768890247)
    ·
      refine ⟨80338266714082202653335371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53558844476054801768890247 80338266714082202653335371)
      ·
        refine ⟨120507400071123303980003057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80338266714082202653335371 120507400071123303980003057)
        ·
          refine ⟨90380550053342477985002293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120507400071123303980003057 90380550053342477985002293)
          ·
            refine ⟨8473176567500857311093965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90380550053342477985002293 8473176567500857311093965)
            ·
              refine ⟨3177441212812821491660237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8473176567500857311093965 3177441212812821491660237)
              ·
                refine ⟨1191540454804808059372589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3177441212812821491660237 1191540454804808059372589)
                ·
                  refine ⟨446827670551803022264721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1191540454804808059372589 446827670551803022264721)
                  ·
                    rfl

theorem cell21_1957936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 3].length) (baseStart_1957936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957936 prefixEnd_1957936 := by exact prefixLift 1957936
  have htrace : WordTrace (prefixWord ++ tailWord_1957936) baseStart_1957936 baseEnd_1957936 := by
    simpa [prefixWord, tailWord_1957936, baseEnd_1957936] using wordTrace_append hprefix tailTrace_1957936
  have hstable : (prefixWord ++ tailWord_1957936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957936).length < 2 ^ (prefixWord ++ tailWord_1957936).sum := by decide
  have hdescent : baseEnd_1957936 < baseStart_1957936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957978 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 7]
def baseStart_1957978 : Nat := 118140960795 + 1957978 * 2 ^ 59
def prefixEnd_1957978 : Nat := 4983230072969 + 3 ^ 40 * 1957978 * 2
def baseEnd_1957978 : Nat := 446837255524020282564635

theorem tailTrace_1957978 : CollatzResearch.WordTrace tailWord_1957978 prefixEnd_1957978 446837255524020282564635 := by
  unfold tailWord_1957978
  simp only [CollatzResearch.WordTrace]
  refine ⟨17853331125146894216220647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47608883000391717909921725 17853331125146894216220647)
  ·
    refine ⟨26779996687720341324330971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17853331125146894216220647 26779996687720341324330971)
    ·
      refine ⟨40169995031580511986496457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26779996687720341324330971 40169995031580511986496457)
      ·
        refine ⟨30127496273685383989872343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40169995031580511986496457 30127496273685383989872343)
        ·
          refine ⟨45191244410528075984808515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30127496273685383989872343 45191244410528075984808515)
          ·
            refine ⟨67786866615792113977212773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45191244410528075984808515 67786866615792113977212773)
            ·
              refine ⟨12710037490461021370727395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67786866615792113977212773 12710037490461021370727395)
              ·
                refine ⟨19065056235691532056091093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12710037490461021370727395 19065056235691532056091093)
                ·
                  refine ⟨446837255524020282564635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19065056235691532056091093 446837255524020282564635)
                  ·
                    rfl

theorem cell21_1957978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_1957978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957978 prefixEnd_1957978 := by exact prefixLift 1957978
  have htrace : WordTrace (prefixWord ++ tailWord_1957978) baseStart_1957978 baseEnd_1957978 := by
    simpa [prefixWord, tailWord_1957978, baseEnd_1957978] using wordTrace_append hprefix tailTrace_1957978
  have hstable : (prefixWord ++ tailWord_1957978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957978).length < 2 ^ (prefixWord ++ tailWord_1957978).sum := by decide
  have hdescent : baseEnd_1957978 < baseStart_1957978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1957981 : List Nat := [1, 4, 4, 1, 1, 1, 2, 7]
def baseStart_1957981 : Nat := 118140960795 + 1957981 * 2 ^ 59
def prefixEnd_1957981 : Nat := 4983230072969 + 3 ^ 40 * 1957981 * 2
def baseEnd_1957981 : Nat := 148945980054964314671543

theorem tailTrace_1957981 : CollatzResearch.WordTrace tailWord_1957981 prefixEnd_1957981 148945980054964314671543 := by
  unfold tailWord_1957981
  simp only [CollatzResearch.WordTrace]
  refine ⟨71413433919576708377241797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47608955946384472251494531 71413433919576708377241797)
  ·
    refine ⟨13390018859920632820732837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71413433919576708377241797 13390018859920632820732837)
    ·
      refine ⟨2510628536235118653887407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13390018859920632820732837 2510628536235118653887407)
      ·
        refine ⟨3765942804352677980831111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2510628536235118653887407 3765942804352677980831111)
        ·
          refine ⟨5648914206529016971246667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3765942804352677980831111 5648914206529016971246667)
          ·
            refine ⟨8473371309793525456870001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5648914206529016971246667 8473371309793525456870001)
            ·
              refine ⟨6355028482345144092652501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8473371309793525456870001 6355028482345144092652501)
              ·
                refine ⟨148945980054964314671543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6355028482345144092652501 148945980054964314671543)
                ·
                  rfl

theorem cell21_1957981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 7].length) (baseStart_1957981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1957981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1957981 prefixEnd_1957981 := by exact prefixLift 1957981
  have htrace : WordTrace (prefixWord ++ tailWord_1957981) baseStart_1957981 baseEnd_1957981 := by
    simpa [prefixWord, tailWord_1957981, baseEnd_1957981] using wordTrace_append hprefix tailTrace_1957981
  have hstable : (prefixWord ++ tailWord_1957981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1957981).length < 2 ^ (prefixWord ++ tailWord_1957981).sum := by decide
  have hdescent : baseEnd_1957981 < baseStart_1957981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1957981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958012 : List Nat := [2, 2, 2, 1, 1, 5, 1, 4, 3]
def baseStart_1958012 : Nat := 118140960795 + 1958012 * 2 ^ 59
def prefixEnd_1958012 : Nat := 4983230072969 + 3 ^ 40 * 1958012 * 2
def baseEnd_1958012 : Nat := 446845014787243778997899

theorem tailTrace_1958012 : CollatzResearch.WordTrace tailWord_1958012 prefixEnd_1958012 446845014787243778997899 := by
  unfold tailWord_1958012
  simp only [CollatzResearch.WordTrace]
  refine ⟨35707282291232200335810145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47609709721642933781080193 35707282291232200335810145)
  ·
    refine ⟨26780461718424150251857609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35707282291232200335810145 26780461718424150251857609)
    ·
      refine ⟨20085346288818112688893207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26780461718424150251857609 20085346288818112688893207)
      ·
        refine ⟨30128019433227169033339811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20085346288818112688893207 30128019433227169033339811)
        ·
          refine ⟨45192029149840753550009717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30128019433227169033339811 45192029149840753550009717)
          ·
            refine ⟨4236752732797570645313411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45192029149840753550009717 4236752732797570645313411)
            ·
              refine ⟨6355129099196355967970117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4236752732797570645313411 6355129099196355967970117)
              ·
                refine ⟨1191586706099316743994397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6355129099196355967970117 1191586706099316743994397)
                ·
                  refine ⟨446845014787243778997899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1191586706099316743994397 446845014787243778997899)
                  ·
                    rfl

theorem cell21_1958012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_1958012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958012 prefixEnd_1958012 := by exact prefixLift 1958012
  have htrace : WordTrace (prefixWord ++ tailWord_1958012) baseStart_1958012 baseEnd_1958012 := by
    simpa [prefixWord, tailWord_1958012, baseEnd_1958012] using wordTrace_append hprefix tailTrace_1958012
  have hstable : (prefixWord ++ tailWord_1958012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958012).length < 2 ^ (prefixWord ++ tailWord_1958012).sum := by decide
  have hdescent : baseEnd_1958012 < baseStart_1958012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958026 : List Nat := [3, 1, 2, 3, 1, 2, 2, 3, 4]
def baseStart_1958026 : Nat := 118140960795 + 1958026 * 2 ^ 59
def prefixEnd_1958026 : Nat := 4983230072969 + 3 ^ 40 * 1958026 * 2
def baseEnd_1958026 : Nat := 446848209777982865764537

theorem tailTrace_1958026 : CollatzResearch.WordTrace tailWord_1958026 prefixEnd_1958026 446848209777982865764537 := by
  unfold tailWord_1958026
  simp only [CollatzResearch.WordTrace]
  refine ⟨17853768801103420265657483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47610050136275787375086621 17853768801103420265657483)
  ·
    refine ⟨26780653201655130398486225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17853768801103420265657483 26780653201655130398486225)
    ·
      refine ⟨20085489901241347798864669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26780653201655130398486225 20085489901241347798864669)
      ·
        refine ⟨7532058712965505424574251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20085489901241347798864669 7532058712965505424574251)
        ·
          refine ⟨11298088069448258136861377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7532058712965505424574251 11298088069448258136861377)
          ·
            refine ⟨8473566052086193602646033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11298088069448258136861377 8473566052086193602646033)
            ·
              refine ⟨6355174539064645201984525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8473566052086193602646033 6355174539064645201984525)
              ·
                refine ⟨2383190452149241950744197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6355174539064645201984525 2383190452149241950744197)
                ·
                  refine ⟨446848209777982865764537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2383190452149241950744197 446848209777982865764537)
                  ·
                    rfl

theorem cell21_1958026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_1958026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958026 prefixEnd_1958026 := by exact prefixLift 1958026
  have htrace : WordTrace (prefixWord ++ tailWord_1958026) baseStart_1958026 baseEnd_1958026 := by
    simpa [prefixWord, tailWord_1958026, baseEnd_1958026] using wordTrace_append hprefix tailTrace_1958026
  have hstable : (prefixWord ++ tailWord_1958026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958026).length < 2 ^ (prefixWord ++ tailWord_1958026).sum := by decide
  have hdescent : baseEnd_1958026 < baseStart_1958026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958046 : List Nat := [4, 3, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1958046 : Nat := 118140960795 + 1958046 * 2 ^ 59
def prefixEnd_1958046 : Nat := 4983230072969 + 3 ^ 40 * 1958046 * 2
def baseEnd_1958046 : Nat := 446852774050467275431163

theorem tailTrace_1958046 : CollatzResearch.WordTrace tailWord_1958046 prefixEnd_1958046 446852774050467275431163 := by
  unfold tailWord_1958046
  simp only [CollatzResearch.WordTrace]
  refine ⟨8926975583042653059794749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47610536442894149652238661 8926975583042653059794749)
  ·
    refine ⟨3347615843640994897423031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8926975583042653059794749 3347615843640994897423031)
    ·
      refine ⟨5021423765461492346134547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3347615843640994897423031 5021423765461492346134547)
      ·
        refine ⟨7532135648192238519201821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5021423765461492346134547 7532135648192238519201821)
        ·
          refine ⟨2824550868072089444700683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7532135648192238519201821 2824550868072089444700683)
          ·
            refine ⟨4236826302108134167051025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824550868072089444700683 4236826302108134167051025)
            ·
              refine ⟨3177619726581100625288269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4236826302108134167051025 3177619726581100625288269)
              ·
                refine ⟨1191607397467912734483101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3177619726581100625288269 1191607397467912734483101)
                ·
                  refine ⟨446852774050467275431163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1191607397467912734483101 446852774050467275431163)
                  ·
                    rfl

theorem cell21_1958046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1958046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958046 prefixEnd_1958046 := by exact prefixLift 1958046
  have htrace : WordTrace (prefixWord ++ tailWord_1958046) baseStart_1958046 baseEnd_1958046 := by
    simpa [prefixWord, tailWord_1958046, baseEnd_1958046] using wordTrace_append hprefix tailTrace_1958046
  have hstable : (prefixWord ++ tailWord_1958046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958046).length < 2 ^ (prefixWord ++ tailWord_1958046).sum := by decide
  have hdescent : baseEnd_1958046 < baseStart_1958046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958071 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 5]
def baseStart_1958071 : Nat := 118140960795 + 1958071 * 2 ^ 59
def prefixEnd_1958071 : Nat := 4983230072969 + 3 ^ 40 * 1958071 * 2
def baseEnd_1958071 : Nat := 446858479391072787514445

theorem tailTrace_1958071 : CollatzResearch.WordTrace tailWord_1958071 prefixEnd_1958071 446858479391072787514445 := by
  unfold tailWord_1958071
  simp only [CollatzResearch.WordTrace]
  refine ⟨71416716489250653748018067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47611144326167102498678711 71416716489250653748018067)
  ·
    refine ⟨107125074733875980622027101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71416716489250653748018067 107125074733875980622027101)
    ·
      refine ⟨40171903025203492733260163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107125074733875980622027101 40171903025203492733260163)
      ·
        refine ⟨60257854537805239099890245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40171903025203492733260163 60257854537805239099890245)
        ·
          refine ⟨11298347725838482331229421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60257854537805239099890245 11298347725838482331229421)
          ·
            refine ⟨4236880397189430874211033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11298347725838482331229421 4236880397189430874211033)
            ·
              refine ⟨3177660297892073155658275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4236880397189430874211033 3177660297892073155658275)
              ·
                refine ⟨4766490446838109733487413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3177660297892073155658275 4766490446838109733487413)
                ·
                  refine ⟨446858479391072787514445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4766490446838109733487413 446858479391072787514445)
                  ·
                    rfl

theorem cell21_1958071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 5].length) (baseStart_1958071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958071 prefixEnd_1958071 := by exact prefixLift 1958071
  have htrace : WordTrace (prefixWord ++ tailWord_1958071) baseStart_1958071 baseEnd_1958071 := by
    simpa [prefixWord, tailWord_1958071, baseEnd_1958071] using wordTrace_append hprefix tailTrace_1958071
  have hstable : (prefixWord ++ tailWord_1958071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958071).length < 2 ^ (prefixWord ++ tailWord_1958071).sum := by decide
  have hdescent : baseEnd_1958071 < baseStart_1958071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958085 : List Nat := [1, 3, 1, 1, 1, 1, 4, 5, 4]
def baseStart_1958085 : Nat := 118140960795 + 1958085 * 2 ^ 59
def prefixEnd_1958085 : Nat := 4983230072969 + 3 ^ 40 * 1958085 * 2
def baseEnd_1958085 : Nat := 446861674381811874281083

theorem tailTrace_1958085 : CollatzResearch.WordTrace tailWord_1958085 prefixEnd_1958085 446861674381811874281083 := by
  unfold tailWord_1958085
  simp only [CollatzResearch.WordTrace]
  refine ⟨71417227111199934139027709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47611484740799956092685139 71417227111199934139027709)
  ·
    refine ⟨26781460166699975302135391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71417227111199934139027709 26781460166699975302135391)
    ·
      refine ⟨40172190250049962953203087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26781460166699975302135391 40172190250049962953203087)
      ·
        refine ⟨60258285375074944429804631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40172190250049962953203087 60258285375074944429804631)
        ·
          refine ⟨90387428062612416644706947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60258285375074944429804631 90387428062612416644706947)
          ·
            refine ⟨135581142093918624967060421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90387428062612416644706947 135581142093918624967060421)
            ·
              refine ⟨25421464142609742181323829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135581142093918624967060421 25421464142609742181323829)
              ·
                refine ⟨2383262263369663329499109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25421464142609742181323829 2383262263369663329499109)
                ·
                  refine ⟨446861674381811874281083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2383262263369663329499109 446861674381811874281083)
                  ·
                    rfl

theorem cell21_1958085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_1958085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958085 prefixEnd_1958085 := by exact prefixLift 1958085
  have htrace : WordTrace (prefixWord ++ tailWord_1958085) baseStart_1958085 baseEnd_1958085 := by
    simpa [prefixWord, tailWord_1958085, baseEnd_1958085] using wordTrace_append hprefix tailTrace_1958085
  have hstable : (prefixWord ++ tailWord_1958085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958085).length < 2 ^ (prefixWord ++ tailWord_1958085).sum := by decide
  have hdescent : baseEnd_1958085 < baseStart_1958085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958175 : List Nat := [1, 1, 2, 4, 3, 10]
def baseStart_1958175 : Nat := 118140960795 + 1958175 * 2 ^ 59
def prefixEnd_1958175 : Nat := 4983230072969 + 3 ^ 40 * 1958175 * 2
def baseEnd_1958175 : Nat := 16551193096592285843737

theorem tailTrace_1958175 : CollatzResearch.WordTrace tailWord_1958175 prefixEnd_1958175 16551193096592285843737 := by
  unfold tailWord_1958175
  simp only [CollatzResearch.WordTrace]
  refine ⟨71420509680873879509803979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47613673120582586339869319 71420509680873879509803979)
  ·
    refine ⟨107130764521310819264705969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71420509680873879509803979 107130764521310819264705969)
    ·
      refine ⟨80348073390983114448529477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107130764521310819264705969 80348073390983114448529477)
      ·
        refine ⟨15065263760809333959099277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80348073390983114448529477 15065263760809333959099277)
        ·
          refine ⟨5649473910303500234662229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15065263760809333959099277 5649473910303500234662229)
          ·
            refine ⟨16551193096592285843737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5649473910303500234662229 16551193096592285843737)
            ·
              rfl

theorem cell21_1958175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 10].length) (baseStart_1958175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958175 prefixEnd_1958175 := by exact prefixLift 1958175
  have htrace : WordTrace (prefixWord ++ tailWord_1958175) baseStart_1958175 baseEnd_1958175 := by
    simpa [prefixWord, tailWord_1958175, baseEnd_1958175] using wordTrace_append hprefix tailTrace_1958175
  have hstable : (prefixWord ++ tailWord_1958175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958175).length < 2 ^ (prefixWord ++ tailWord_1958175).sum := by decide
  have hdescent : baseEnd_1958175 < baseStart_1958175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958178 : List Nat := [3, 3, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1958178 : Nat := 118140960795 + 1958178 * 2 ^ 59
def prefixEnd_1958178 : Nat := 4983230072969 + 3 ^ 40 * 1958178 * 2
def baseEnd_1958178 : Nat := 446882898248864379230893

theorem tailTrace_1958178 : CollatzResearch.WordTrace tailWord_1958178 prefixEnd_1958178 446882898248864379230893 := by
  unfold tailWord_1958178
  simp only [CollatzResearch.WordTrace]
  refine ⟨17855154774965752755540797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47613746066575340681442125 17855154774965752755540797)
  ·
    refine ⟨6695683040612157283327799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17855154774965752755540797 6695683040612157283327799)
    ·
      refine ⟨10043524560918235924991699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6695683040612157283327799 10043524560918235924991699)
      ·
        refine ⟨15065286841377353887487549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10043524560918235924991699 15065286841377353887487549)
        ·
          refine ⟨5649482565516507707807831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15065286841377353887487549 5649482565516507707807831)
          ·
            refine ⟨8474223848274761561711747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5649482565516507707807831 8474223848274761561711747)
            ·
              refine ⟨12711335772412142342567621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8474223848274761561711747 12711335772412142342567621)
              ·
                refine ⟨2383375457327276689231429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12711335772412142342567621 2383375457327276689231429)
                ·
                  refine ⟨446882898248864379230893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2383375457327276689231429 446882898248864379230893)
                  ·
                    rfl

theorem cell21_1958178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1958178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958178 prefixEnd_1958178 := by exact prefixLift 1958178
  have htrace : WordTrace (prefixWord ++ tailWord_1958178) baseStart_1958178 baseEnd_1958178 := by
    simpa [prefixWord, tailWord_1958178, baseEnd_1958178] using wordTrace_append hprefix tailTrace_1958178
  have hstable : (prefixWord ++ tailWord_1958178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958178).length < 2 ^ (prefixWord ++ tailWord_1958178).sum := by decide
  have hdescent : baseEnd_1958178 < baseStart_1958178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958305 : List Nat := [1, 2, 3, 5, 2, 1, 2, 1, 4]
def baseStart_1958305 : Nat := 118140960795 + 1958305 * 2 ^ 59
def prefixEnd_1958305 : Nat := 4983230072969 + 3 ^ 40 * 1958305 * 2
def baseEnd_1958305 : Nat := 446911881379140380613967

theorem tailTrace_1958305 : CollatzResearch.WordTrace tailWord_1958305 prefixEnd_1958305 446911881379140380613967 := by
  unfold tailWord_1958305
  simp only [CollatzResearch.WordTrace]
  refine ⟨71425251170402911712036369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47616834113601941141357579 71425251170402911712036369)
  ·
    refine ⟨53568938377802183784027277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71425251170402911712036369 53568938377802183784027277)
    ·
      refine ⟨20088351891675818919010229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53568938377802183784027277 20088351891675818919010229)
      ·
        refine ⟨1883282989844608023657209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20088351891675818919010229 1883282989844608023657209)
        ·
          refine ⟨1412462242383456017742907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1883282989844608023657209 1412462242383456017742907)
          ·
            refine ⟨2118693363575184026614361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412462242383456017742907 2118693363575184026614361)
            ·
              refine ⟨1589020022681388019960771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2118693363575184026614361 1589020022681388019960771)
              ·
                refine ⟨2383530034022082029941157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589020022681388019960771 2383530034022082029941157)
                ·
                  refine ⟨446911881379140380613967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2383530034022082029941157 446911881379140380613967)
                  ·
                    rfl

theorem cell21_1958305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 4].length) (baseStart_1958305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958305 prefixEnd_1958305 := by exact prefixLift 1958305
  have htrace : WordTrace (prefixWord ++ tailWord_1958305) baseStart_1958305 baseEnd_1958305 := by
    simpa [prefixWord, tailWord_1958305, baseEnd_1958305] using wordTrace_append hprefix tailTrace_1958305
  have hstable : (prefixWord ++ tailWord_1958305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958305).length < 2 ^ (prefixWord ++ tailWord_1958305).sum := by decide
  have hdescent : baseEnd_1958305 < baseStart_1958305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958327 : List Nat := [1, 1, 3, 1, 3, 3, 2, 7]
def baseStart_1958327 : Nat := 118140960795 + 1958327 * 2 ^ 59
def prefixEnd_1958327 : Nat := 4983230072969 + 3 ^ 40 * 1958327 * 2
def baseEnd_1958327 : Nat := 148972300692957743749085

theorem tailTrace_1958327 : CollatzResearch.WordTrace tailWord_1958327 prefixEnd_1958327 148972300692957743749085 := by
  unfold tailWord_1958327
  simp only [CollatzResearch.WordTrace]
  refine ⟨71426053576323209469337235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47617369050882139646224823 71426053576323209469337235)
  ·
    refine ⟨107139080364484814204005853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71426053576323209469337235 107139080364484814204005853)
    ·
      refine ⟨40177155136681805326502195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107139080364484814204005853 40177155136681805326502195)
      ·
        refine ⟨60265732705022707989753293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40177155136681805326502195 60265732705022707989753293)
        ·
          refine ⟨22599649764383515496157485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60265732705022707989753293 22599649764383515496157485)
          ·
            refine ⟨8474868661643818311059057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22599649764383515496157485 8474868661643818311059057)
            ·
              refine ⟨6356151496232863733294293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8474868661643818311059057 6356151496232863733294293)
              ·
                refine ⟨148972300692957743749085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6356151496232863733294293 148972300692957743749085)
                ·
                  rfl

theorem cell21_1958327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 7].length) (baseStart_1958327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958327 prefixEnd_1958327 := by exact prefixLift 1958327
  have htrace : WordTrace (prefixWord ++ tailWord_1958327) baseStart_1958327 baseEnd_1958327 := by
    simpa [prefixWord, tailWord_1958327, baseEnd_1958327] using wordTrace_append hprefix tailTrace_1958327
  have hstable : (prefixWord ++ tailWord_1958327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958327).length < 2 ^ (prefixWord ++ tailWord_1958327).sum := by decide
  have hdescent : baseEnd_1958327 < baseStart_1958327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958372 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 10]
def baseStart_1958372 : Nat := 118140960795 + 1958372 * 2 ^ 59
def prefixEnd_1958372 : Nat := 4983230072969 + 3 ^ 40 * 1958372 * 2
def baseEnd_1958372 : Nat := 446927171691963152997163

theorem tailTrace_1958372 : CollatzResearch.WordTrace tailWord_1958372 prefixEnd_1958372 446927171691963152997163 := by
  unfold tailWord_1958372
  simp only [CollatzResearch.WordTrace]
  refine ⟨35713847430580091077362685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47618463240773454769816913 35713847430580091077362685)
  ·
    refine ⟨13392692786467534154011007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35713847430580091077362685 13392692786467534154011007)
    ·
      refine ⟨20089039179701301231016511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13392692786467534154011007 20089039179701301231016511)
      ·
        refine ⟨30133558769551951846524767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20089039179701301231016511 30133558769551951846524767)
        ·
          refine ⟨45200338154327927769787151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30133558769551951846524767 45200338154327927769787151)
          ·
            refine ⟨67800507231491891654680727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45200338154327927769787151 67800507231491891654680727)
            ·
              refine ⟨101700760847237837482021091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67800507231491891654680727 101700760847237837482021091)
              ·
                refine ⟨152551141270856756223031637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101700760847237837482021091 152551141270856756223031637)
                ·
                  refine ⟨446927171691963152997163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 152551141270856756223031637 446927171691963152997163)
                  ·
                    rfl

theorem cell21_1958372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_1958372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958372 prefixEnd_1958372 := by exact prefixLift 1958372
  have htrace : WordTrace (prefixWord ++ tailWord_1958372) baseStart_1958372 baseEnd_1958372 := by
    simpa [prefixWord, tailWord_1958372, baseEnd_1958372] using wordTrace_append hprefix tailTrace_1958372
  have hstable : (prefixWord ++ tailWord_1958372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958372).length < 2 ^ (prefixWord ++ tailWord_1958372).sum := by decide
  have hdescent : baseEnd_1958372 < baseStart_1958372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958448 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 6]
def baseStart_1958448 : Nat := 118140960795 + 1958448 * 2 ^ 59
def prefixEnd_1958448 : Nat := 4983230072969 + 3 ^ 40 * 1958448 * 2
def baseEnd_1958448 : Nat := 446944515927403909730341

theorem tailTrace_1958448 : CollatzResearch.WordTrace tailWord_1958448 prefixEnd_1958448 446944515927403909730341 := by
  unfold tailWord_1958448
  simp only [CollatzResearch.WordTrace]
  refine ⟨35715233404442423567245999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47620311205923231422994665 35715233404442423567245999)
  ·
    refine ⟨53572850106663635350868999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35715233404442423567245999 53572850106663635350868999)
    ·
      refine ⟨80359275159995453026303499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53572850106663635350868999 80359275159995453026303499)
      ·
        refine ⟨120538912739993179539455249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80359275159995453026303499 120538912739993179539455249)
        ·
          refine ⟨90404184554994884654591437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120538912739993179539455249 90404184554994884654591437)
          ·
            refine ⟨33901569208123081745471789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90404184554994884654591437 33901569208123081745471789)
            ·
              refine ⟨12713088453046155654551921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33901569208123081745471789 12713088453046155654551921)
              ·
                refine ⟨9534816339784616740913941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12713088453046155654551921 9534816339784616740913941)
                ·
                  refine ⟨446944515927403909730341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9534816339784616740913941 446944515927403909730341)
                  ·
                    rfl

theorem cell21_1958448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_1958448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958448 prefixEnd_1958448 := by exact prefixLift 1958448
  have htrace : WordTrace (prefixWord ++ tailWord_1958448) baseStart_1958448 baseEnd_1958448 := by
    simpa [prefixWord, tailWord_1958448, baseEnd_1958448] using wordTrace_append hprefix tailTrace_1958448
  have hstable : (prefixWord ++ tailWord_1958448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958448).length < 2 ^ (prefixWord ++ tailWord_1958448).sum := by decide
  have hdescent : baseEnd_1958448 < baseStart_1958448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958465 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 6]
def baseStart_1958465 : Nat := 118140960795 + 1958465 * 2 ^ 59
def prefixEnd_1958465 : Nat := 4983230072969 + 3 ^ 40 * 1958465 * 2
def baseEnd_1958465 : Nat := 446948395559015657946973

theorem tailTrace_1958465 : CollatzResearch.WordTrace tailWord_1958465 prefixEnd_1958465 446948395559015657946973 := by
  unfold tailWord_1958465
  simp only [CollatzResearch.WordTrace]
  refine ⟨71431086849823259037860849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47620724566548839358573899 71431086849823259037860849)
  ·
    refine ⟨53573315137367444278395637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71431086849823259037860849 53573315137367444278395637)
    ·
      refine ⟨5022498294128197901099591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53573315137367444278395637 5022498294128197901099591)
      ·
        refine ⟨7533747441192296851649387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5022498294128197901099591 7533747441192296851649387)
        ·
          refine ⟨11300621161788445277474081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7533747441192296851649387 11300621161788445277474081)
          ·
            refine ⟨8475465871341333958105561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11300621161788445277474081 8475465871341333958105561)
            ·
              refine ⟨6356599403506000468579171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8475465871341333958105561 6356599403506000468579171)
              ·
                refine ⟨9534899105259000702868757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6356599403506000468579171 9534899105259000702868757)
                ·
                  refine ⟨446948395559015657946973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9534899105259000702868757 446948395559015657946973)
                  ·
                    rfl

theorem cell21_1958465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_1958465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958465 prefixEnd_1958465 := by exact prefixLift 1958465
  have htrace : WordTrace (prefixWord ++ tailWord_1958465) baseStart_1958465 baseEnd_1958465 := by
    simpa [prefixWord, tailWord_1958465, baseEnd_1958465] using wordTrace_append hprefix tailTrace_1958465
  have hstable : (prefixWord ++ tailWord_1958465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958465).length < 2 ^ (prefixWord ++ tailWord_1958465).sum := by decide
  have hdescent : baseEnd_1958465 < baseStart_1958465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958524 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 6]
def baseStart_1958524 : Nat := 118140960795 + 1958524 * 2 ^ 59
def prefixEnd_1958524 : Nat := 4983230072969 + 3 ^ 40 * 1958524 * 2
def baseEnd_1958524 : Nat := 446961860162844666463519

theorem tailTrace_1958524 : CollatzResearch.WordTrace tailWord_1958524 prefixEnd_1958524 446961860162844666463519 := by
  unfold tailWord_1958524
  simp only [CollatzResearch.WordTrace]
  refine ⟨35716619378304756057129313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47622159171073008076172417 35716619378304756057129313)
  ·
    refine ⟨26787464533728567042846985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35716619378304756057129313 26787464533728567042846985)
    ·
      refine ⟨20090598400296425282135239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26787464533728567042846985 20090598400296425282135239)
      ·
        refine ⟨30135897600444637923202859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20090598400296425282135239 30135897600444637923202859)
        ·
          refine ⟨45203846400666956884804289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30135897600444637923202859 45203846400666956884804289)
          ·
            refine ⟨33902884800500217663603217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45203846400666956884804289 33902884800500217663603217)
            ·
              refine ⟨25427163600375163247702413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33902884800500217663603217 25427163600375163247702413)
              ·
                refine ⟨9535186350140686217888405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25427163600375163247702413 9535186350140686217888405)
                ·
                  refine ⟨446961860162844666463519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9535186350140686217888405 446961860162844666463519)
                  ·
                    rfl

theorem cell21_1958524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_1958524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958524 prefixEnd_1958524 := by exact prefixLift 1958524
  have htrace : WordTrace (prefixWord ++ tailWord_1958524) baseStart_1958524 baseEnd_1958524 := by
    simpa [prefixWord, tailWord_1958524, baseEnd_1958524] using wordTrace_append hprefix tailTrace_1958524
  have hstable : (prefixWord ++ tailWord_1958524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958524).length < 2 ^ (prefixWord ++ tailWord_1958524).sum := by decide
  have hdescent : baseEnd_1958524 < baseStart_1958524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958586 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 5]
def baseStart_1958586 : Nat := 118140960795 + 1958586 * 2 ^ 59
def prefixEnd_1958586 : Nat := 4983230072969 + 3 ^ 40 * 1958586 * 2
def baseEnd_1958586 : Nat := 446976009407546336430059

theorem tailTrace_1958586 : CollatzResearch.WordTrace tailWord_1958586 prefixEnd_1958586 446976009407546336430059 := by
  unfold tailWord_1958586
  simp only [CollatzResearch.WordTrace]
  refine ⟨17858875020596224175753903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47623666721589931135343741 17858875020596224175753903)
  ·
    refine ⟨26788312530894336263630855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17858875020596224175753903 26788312530894336263630855)
    ·
      refine ⟨40182468796341504395446283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26788312530894336263630855 40182468796341504395446283)
      ·
        refine ⟨60273703194512256593169425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40182468796341504395446283 60273703194512256593169425)
        ·
          refine ⟨45205277395884192444877069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60273703194512256593169425 45205277395884192444877069)
          ·
            refine ⟨16951979023456572166828901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45205277395884192444877069 16951979023456572166828901)
            ·
              refine ⟨3178496066898107281280419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16951979023456572166828901 3178496066898107281280419)
              ·
                refine ⟨4767744100347160921920629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178496066898107281280419 4767744100347160921920629)
                ·
                  refine ⟨446976009407546336430059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4767744100347160921920629 446976009407546336430059)
                  ·
                    rfl

theorem cell21_1958586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_1958586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958586 prefixEnd_1958586 := by exact prefixLift 1958586
  have htrace : WordTrace (prefixWord ++ tailWord_1958586) baseStart_1958586 baseEnd_1958586 := by
    simpa [prefixWord, tailWord_1958586, baseEnd_1958586] using wordTrace_append hprefix tailTrace_1958586
  have hstable : (prefixWord ++ tailWord_1958586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958586).length < 2 ^ (prefixWord ++ tailWord_1958586).sum := by decide
  have hdescent : baseEnd_1958586 < baseStart_1958586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958693 : List Nat := [1, 3, 1, 2, 3, 1, 4, 2, 4]
def baseStart_1958693 : Nat := 118140960795 + 1958693 * 2 ^ 59
def prefixEnd_1958693 : Nat := 4983230072969 + 3 ^ 40 * 1958693 * 2
def baseEnd_1958693 : Nat := 447000428265337928146507

theorem tailTrace_1958693 : CollatzResearch.WordTrace tailWord_1958693 prefixEnd_1958693 447000428265337928146507 := by
  unfold tailWord_1958693
  simp only [CollatzResearch.WordTrace]
  refine ⟨71439402692997253977160733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47626268461998169318107155 71439402692997253977160733)
  ·
    refine ⟨26789776009873970241435275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71439402692997253977160733 26789776009873970241435275)
    ·
      refine ⟨40184664014810955362152913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26789776009873970241435275 40184664014810955362152913)
      ·
        refine ⟨30138498011108216521614685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40184664014810955362152913 30138498011108216521614685)
        ·
          refine ⟨11301936754165581195605507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30138498011108216521614685 11301936754165581195605507)
          ·
            refine ⟨16952905131248371793408261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11301936754165581195605507 16952905131248371793408261)
            ·
              refine ⟨3178669712109069711264049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16952905131248371793408261 3178669712109069711264049)
              ·
                refine ⟨2384002284081802283448037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3178669712109069711264049 2384002284081802283448037)
                ·
                  refine ⟨447000428265337928146507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2384002284081802283448037 447000428265337928146507)
                  ·
                    rfl

theorem cell21_1958693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_1958693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958693 prefixEnd_1958693 := by exact prefixLift 1958693
  have htrace : WordTrace (prefixWord ++ tailWord_1958693) baseStart_1958693 baseEnd_1958693 := by
    simpa [prefixWord, tailWord_1958693, baseEnd_1958693] using wordTrace_append hprefix tailTrace_1958693
  have hstable : (prefixWord ++ tailWord_1958693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958693).length < 2 ^ (prefixWord ++ tailWord_1958693).sum := by decide
  have hdescent : baseEnd_1958693 < baseStart_1958693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958707 : List Nat := [1, 1, 1, 2, 6, 1, 3, 6]
def baseStart_1958707 : Nat := 118140960795 + 1958707 * 2 ^ 59
def prefixEnd_1958707 : Nat := 4983230072969 + 3 ^ 40 * 1958707 * 2
def baseEnd_1958707 : Nat := 149001207752025671637715

theorem tailTrace_1958707 : CollatzResearch.WordTrace tailWord_1958707 prefixEnd_1958707 149001207752025671637715 := by
  unfold tailWord_1958707
  simp only [CollatzResearch.WordTrace]
  refine ⟨71439913314946534368170375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47626608876631022912113583 71439913314946534368170375)
  ·
    refine ⟨107159869972419801552255563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71439913314946534368170375 107159869972419801552255563)
    ·
      refine ⟨160739804958629702328383345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107159869972419801552255563 160739804958629702328383345)
      ·
        refine ⟨120554853718972276746287509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160739804958629702328383345 120554853718972276746287509)
        ·
          refine ⟨5651008768076825472482227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120554853718972276746287509 5651008768076825472482227)
          ·
            refine ⟨8476513152115238208723341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5651008768076825472482227 8476513152115238208723341)
            ·
              refine ⟨3178692432043214328271253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8476513152115238208723341 3178692432043214328271253)
              ·
                refine ⟨149001207752025671637715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3178692432043214328271253 149001207752025671637715)
                ·
                  rfl

theorem cell21_1958707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 6].length) (baseStart_1958707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958707 prefixEnd_1958707 := by exact prefixLift 1958707
  have htrace : WordTrace (prefixWord ++ tailWord_1958707) baseStart_1958707 baseEnd_1958707 := by
    simpa [prefixWord, tailWord_1958707, baseEnd_1958707] using wordTrace_append hprefix tailTrace_1958707
  have hstable : (prefixWord ++ tailWord_1958707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958707).length < 2 ^ (prefixWord ++ tailWord_1958707).sum := by decide
  have hdescent : baseEnd_1958707 < baseStart_1958707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958752 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 6]
def baseStart_1958752 : Nat := 118140960795 + 1958752 * 2 ^ 59
def prefixEnd_1958752 : Nat := 4983230072969 + 3 ^ 40 * 1958752 * 2
def baseEnd_1958752 : Nat := 447013892869166936663053

theorem tailTrace_1958752 : CollatzResearch.WordTrace tailWord_1958752 prefixEnd_1958752 447013892869166936663053 := by
  unfold tailWord_1958752
  simp only [CollatzResearch.WordTrace]
  refine ⟨35720777299891753526779255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47627703066522338035705673 35720777299891753526779255)
  ·
    refine ⟨53581165949837630290168883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35720777299891753526779255 53581165949837630290168883)
    ·
      refine ⟨80371748924756445435253325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53581165949837630290168883 80371748924756445435253325)
      ·
        refine ⟨30139405846783667038219997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80371748924756445435253325 30139405846783667038219997)
        ·
          refine ⟨11302277192543875139332499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30139405846783667038219997 11302277192543875139332499)
          ·
            refine ⟨16953415788815812708998749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11302277192543875139332499 16953415788815812708998749)
            ·
              refine ⟨6357530920805929765874531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16953415788815812708998749 6357530920805929765874531)
              ·
                refine ⟨9536296381208894648811797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6357530920805929765874531 9536296381208894648811797)
                ·
                  refine ⟨447013892869166936663053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9536296381208894648811797 447013892869166936663053)
                  ·
                    rfl

theorem cell21_1958752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_1958752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958752 prefixEnd_1958752 := by exact prefixLift 1958752
  have htrace : WordTrace (prefixWord ++ tailWord_1958752) baseStart_1958752 baseEnd_1958752 := by
    simpa [prefixWord, tailWord_1958752, baseEnd_1958752] using wordTrace_append hprefix tailTrace_1958752
  have hstable : (prefixWord ++ tailWord_1958752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958752).length < 2 ^ (prefixWord ++ tailWord_1958752).sum := by decide
  have hdescent : baseEnd_1958752 < baseStart_1958752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958755 : List Nat := [1, 1, 1, 5, 3, 1, 2, 4, 3]
def baseStart_1958755 : Nat := 118140960795 + 1958755 * 2 ^ 59
def prefixEnd_1958755 : Nat := 4983230072969 + 3 ^ 40 * 1958755 * 2
def baseEnd_1958755 : Nat := 447014577510039598113047

theorem tailTrace_1958755 : CollatzResearch.WordTrace tailWord_1958755 prefixEnd_1958755 447014577510039598113047 := by
  unfold tailWord_1958755
  simp only [CollatzResearch.WordTrace]
  refine ⟨71441664018772638565917719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47627776012515092377278479 71441664018772638565917719)
  ·
    refine ⟨107162496028158957848876579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71441664018772638565917719 107162496028158957848876579)
    ·
      refine ⟨160743744042238436773314869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107162496028158957848876579 160743744042238436773314869)
      ·
        refine ⟨15069726003959853447498269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160743744042238436773314869 15069726003959853447498269)
        ·
          refine ⟨5651147251484945042811851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15069726003959853447498269 5651147251484945042811851)
          ·
            refine ⟨8476720877227417564217777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5651147251484945042811851 8476720877227417564217777)
            ·
              refine ⟨6357540657920563173163333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8476720877227417564217777 6357540657920563173163333)
              ·
                refine ⟨1192038873360105594968125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6357540657920563173163333 1192038873360105594968125)
                ·
                  refine ⟨447014577510039598113047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1192038873360105594968125 447014577510039598113047)
                  ·
                    rfl

theorem cell21_1958755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 3].length) (baseStart_1958755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958755 prefixEnd_1958755 := by exact prefixLift 1958755
  have htrace : WordTrace (prefixWord ++ tailWord_1958755) baseStart_1958755 baseEnd_1958755 := by
    simpa [prefixWord, tailWord_1958755, baseEnd_1958755] using wordTrace_append hprefix tailTrace_1958755
  have hstable : (prefixWord ++ tailWord_1958755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958755).length < 2 ^ (prefixWord ++ tailWord_1958755).sum := by decide
  have hdescent : baseEnd_1958755 < baseStart_1958755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958783 : List Nat := [1, 1, 2, 2, 1, 1, 8, 5]
def baseStart_1958783 : Nat := 118140960795 + 1958783 * 2 ^ 59
def prefixEnd_1958783 : Nat := 4983230072969 + 3 ^ 40 * 1958783 * 2
def baseEnd_1958783 : Nat := 149006989163839257215441

theorem tailTrace_1958783 : CollatzResearch.WordTrace tailWord_1958783 prefixEnd_1958783 149006989163839257215441 := by
  unfold tailWord_1958783
  simp only [CollatzResearch.WordTrace]
  refine ⟨71442685262671199347937003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47628456841780799565291335 71442685262671199347937003)
  ·
    refine ⟨107164027894006799021905505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71442685262671199347937003 107164027894006799021905505)
    ·
      refine ⟨80373020920505099266429129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107164027894006799021905505 80373020920505099266429129)
      ·
        refine ⟨60279765690378824449821847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80373020920505099266429129 60279765690378824449821847)
        ·
          refine ⟨90419648535568236674732771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60279765690378824449821847 90419648535568236674732771)
          ·
            refine ⟨135629472803352355012099157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90419648535568236674732771 135629472803352355012099157)
            ·
              refine ⟨1589407884414285410298037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 135629472803352355012099157 1589407884414285410298037)
              ·
                refine ⟨149006989163839257215441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1589407884414285410298037 149006989163839257215441)
                ·
                  rfl

theorem cell21_1958783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 5].length) (baseStart_1958783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958783 prefixEnd_1958783 := by exact prefixLift 1958783
  have htrace : WordTrace (prefixWord ++ tailWord_1958783) baseStart_1958783 baseEnd_1958783 := by
    simpa [prefixWord, tailWord_1958783, baseEnd_1958783] using wordTrace_append hprefix tailTrace_1958783
  have hstable : (prefixWord ++ tailWord_1958783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958783).length < 2 ^ (prefixWord ++ tailWord_1958783).sum := by decide
  have hdescent : baseEnd_1958783 < baseStart_1958783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958828 : List Nat := [2, 2, 1, 1, 1, 1, 2, 7, 4]
def baseStart_1958828 : Nat := 118140960795 + 1958828 * 2 ^ 59
def prefixEnd_1958828 : Nat := 4983230072969 + 3 ^ 40 * 1958828 * 2
def baseEnd_1958828 : Nat := 447031237104607693396231

theorem tailTrace_1958828 : CollatzResearch.WordTrace tailWord_1958828 prefixEnd_1958828 447031237104607693396231 := by
  unfold tailWord_1958828
  simp only [CollatzResearch.WordTrace]
  refine ⟨35722163273754086016662569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47629551031672114688883425 35722163273754086016662569)
  ·
    refine ⟨26791622455315564512496927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35722163273754086016662569 26791622455315564512496927)
    ·
      refine ⟨40187433682973346768745391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26791622455315564512496927 40187433682973346768745391)
      ·
        refine ⟨60281150524460020153118087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40187433682973346768745391 60281150524460020153118087)
        ·
          refine ⟨90421725786690030229677131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60281150524460020153118087 90421725786690030229677131)
          ·
            refine ⟨135632588680035045344515697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90421725786690030229677131 135632588680035045344515697)
            ·
              refine ⟨101724441510026284008386773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135632588680035045344515697 101724441510026284008386773)
              ·
                refine ⟨2384166597891241031446565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 101724441510026284008386773 2384166597891241031446565)
                ·
                  refine ⟨447031237104607693396231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2384166597891241031446565 447031237104607693396231)
                  ·
                    rfl

theorem cell21_1958828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_1958828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958828 prefixEnd_1958828 := by exact prefixLift 1958828
  have htrace : WordTrace (prefixWord ++ tailWord_1958828) baseStart_1958828 baseEnd_1958828 := by
    simpa [prefixWord, tailWord_1958828, baseEnd_1958828] using wordTrace_append hprefix tailTrace_1958828
  have hstable : (prefixWord ++ tailWord_1958828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958828).length < 2 ^ (prefixWord ++ tailWord_1958828).sum := by decide
  have hdescent : baseEnd_1958828 < baseStart_1958828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958842 : List Nat := [3, 1, 1, 1, 2, 1, 3, 9]
def baseStart_1958842 : Nat := 118140960795 + 1958842 * 2 ^ 59
def prefixEnd_1958842 : Nat := 4983230072969 + 3 ^ 40 * 1958842 * 2
def baseEnd_1958842 : Nat := 149011477365115593387623

theorem tailTrace_1958842 : CollatzResearch.WordTrace tailWord_1958842 prefixEnd_1958842 149011477365115593387623 := by
  unfold tailWord_1958842
  simp only [CollatzResearch.WordTrace]
  refine ⟨17861209292364363106083695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47629891446304968282889853 17861209292364363106083695)
  ·
    refine ⟨26791813938546544659125543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17861209292364363106083695 26791813938546544659125543)
    ·
      refine ⟨40187720907819816988688315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26791813938546544659125543 40187720907819816988688315)
      ·
        refine ⟨60281581361729725483032473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40187720907819816988688315 60281581361729725483032473)
        ·
          refine ⟨45211186021297294112274355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60281581361729725483032473 45211186021297294112274355)
          ·
            refine ⟨67816779031945941168411533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45211186021297294112274355 67816779031945941168411533)
            ·
              refine ⟨25431292136979727938154325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67816779031945941168411533 25431292136979727938154325)
              ·
                refine ⟨149011477365115593387623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25431292136979727938154325 149011477365115593387623)
                ·
                  rfl

theorem cell21_1958842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_1958842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958842 prefixEnd_1958842 := by exact prefixLift 1958842
  have htrace : WordTrace (prefixWord ++ tailWord_1958842) baseStart_1958842 baseEnd_1958842 := by
    simpa [prefixWord, tailWord_1958842, baseEnd_1958842] using wordTrace_append hprefix tailTrace_1958842
  have hstable : (prefixWord ++ tailWord_1958842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958842).length < 2 ^ (prefixWord ++ tailWord_1958842).sum := by decide
  have hdescent : baseEnd_1958842 < baseStart_1958842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958890 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 5]
def baseStart_1958890 : Nat := 118140960795 + 1958890 * 2 ^ 59
def prefixEnd_1958890 : Nat := 4983230072969 + 3 ^ 40 * 1958890 * 2
def baseEnd_1958890 : Nat := 447045386349309363362771

theorem tailTrace_1958890 : CollatzResearch.WordTrace tailWord_1958890 prefixEnd_1958890 447045386349309363362771 := by
  unfold tailWord_1958890
  simp only [CollatzResearch.WordTrace]
  refine ⟨17861646968320889155520531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47631058582189037748054749 17861646968320889155520531)
  ·
    refine ⟨26792470452481333733280797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17861646968320889155520531 26792470452481333733280797)
    ·
      refine ⟨10047176419680500149980299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26792470452481333733280797 10047176419680500149980299)
      ·
        refine ⟨15070764629520750224970449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10047176419680500149980299 15070764629520750224970449)
        ·
          refine ⟨11303073472140562668727837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15070764629520750224970449 11303073472140562668727837)
          ·
            refine ⟨4238652552052711000772939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11303073472140562668727837 4238652552052711000772939)
            ·
              refine ⟨6357978828079066501159409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4238652552052711000772939 6357978828079066501159409)
              ·
                refine ⟨4768484121059299875869557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6357978828079066501159409 4768484121059299875869557)
                ·
                  refine ⟨447045386349309363362771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4768484121059299875869557 447045386349309363362771)
                  ·
                    rfl

theorem cell21_1958890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_1958890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958890 prefixEnd_1958890 := by exact prefixLift 1958890
  have htrace : WordTrace (prefixWord ++ tailWord_1958890) baseStart_1958890 baseEnd_1958890 := by
    simpa [prefixWord, tailWord_1958890, baseEnd_1958890] using wordTrace_append hprefix tailTrace_1958890
  have hstable : (prefixWord ++ tailWord_1958890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958890).length < 2 ^ (prefixWord ++ tailWord_1958890).sum := by decide
  have hdescent : baseEnd_1958890 < baseStart_1958890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1958949 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 5]
def baseStart_1958949 : Nat := 118140960795 + 1958949 * 2 ^ 59
def prefixEnd_1958949 : Nat := 4983230072969 + 3 ^ 40 * 1958949 * 2
def baseEnd_1958949 : Nat := 447058850953138371879317

theorem tailTrace_1958949 : CollatzResearch.WordTrace tailWord_1958949 prefixEnd_1958949 447058850953138371879317 := by
  unfold tailWord_1958949
  simp only [CollatzResearch.WordTrace]
  refine ⟨71448739780069809698479901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47632493186713206465653267 71448739780069809698479901)
  ·
    refine ⟨26793277417526178636929963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71448739780069809698479901 26793277417526178636929963)
    ·
      refine ⟨40189916126289267955394945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26793277417526178636929963 40189916126289267955394945)
      ·
        refine ⟨30142437094716950966546209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40189916126289267955394945 30142437094716950966546209)
        ·
          refine ⟨22606827821037713224909657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30142437094716950966546209 22606827821037713224909657)
          ·
            refine ⟨16955120865778284918682243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22606827821037713224909657 16955120865778284918682243)
            ·
              refine ⟨25432681298667427378023365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16955120865778284918682243 25432681298667427378023365)
              ·
                refine ⟨4768627743500142633379381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25432681298667427378023365 4768627743500142633379381)
                ·
                  refine ⟨447058850953138371879317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4768627743500142633379381 447058850953138371879317)
                  ·
                    rfl

theorem cell21_1958949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_1958949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1958949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1958949 prefixEnd_1958949 := by exact prefixLift 1958949
  have htrace : WordTrace (prefixWord ++ tailWord_1958949) baseStart_1958949 baseEnd_1958949 := by
    simpa [prefixWord, tailWord_1958949, baseEnd_1958949] using wordTrace_append hprefix tailTrace_1958949
  have hstable : (prefixWord ++ tailWord_1958949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1958949).length < 2 ^ (prefixWord ++ tailWord_1958949).sum := by decide
  have hdescent : baseEnd_1958949 < baseStart_1958949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1958949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959101 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 5]
def baseStart_1959101 : Nat := 118140960795 + 1959101 * 2 ^ 59
def prefixEnd_1959101 : Nat := 4983230072969 + 3 ^ 40 * 1959101 * 2
def baseEnd_1959101 : Nat := 447093539424019885345673

theorem tailTrace_1959101 : CollatzResearch.WordTrace tailWord_1959101 prefixEnd_1959101 447093539424019885345673 := by
  unfold tailWord_1959101
  simp only [CollatzResearch.WordTrace]
  refine ⟨71454283675519139658013157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47636189117012759772008771 71454283675519139658013157)
  ·
    refine ⟨13397678189159838685877467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71454283675519139658013157 13397678189159838685877467)
    ·
      refine ⟨20096517283739758028816201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13397678189159838685877467 20096517283739758028816201)
      ·
        refine ⟨15072387962804818521612151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20096517283739758028816201 15072387962804818521612151)
        ·
          refine ⟨22608581944207227782418227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15072387962804818521612151 22608581944207227782418227)
          ·
            refine ⟨33912872916310841673627341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22608581944207227782418227 33912872916310841673627341)
            ·
              refine ⟨12717327343616565627610253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33912872916310841673627341 12717327343616565627610253)
              ·
                refine ⟨4768997753856212110353845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12717327343616565627610253 4768997753856212110353845)
                ·
                  refine ⟨447093539424019885345673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4768997753856212110353845 447093539424019885345673)
                  ·
                    rfl

theorem cell21_1959101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_1959101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1959101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1959101 prefixEnd_1959101 := by exact prefixLift 1959101
  have htrace : WordTrace (prefixWord ++ tailWord_1959101) baseStart_1959101 baseEnd_1959101 := by
    simpa [prefixWord, tailWord_1959101, baseEnd_1959101] using wordTrace_append hprefix tailTrace_1959101
  have hstable : (prefixWord ++ tailWord_1959101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959101).length < 2 ^ (prefixWord ++ tailWord_1959101).sum := by decide
  have hdescent : baseEnd_1959101 < baseStart_1959101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959146 : List Nat := [3, 1, 3, 1, 1, 3, 9]
def baseStart_1959146 : Nat := 118140960795 + 1959146 * 2 ^ 59
def prefixEnd_1959146 : Nat := 4983230072969 + 3 ^ 40 * 1959146 * 2
def baseEnd_1959146 : Nat := 49678201004123311899509

theorem tailTrace_1959146 : CollatzResearch.WordTrace tailWord_1959146 prefixEnd_1959146 49678201004123311899509 := by
  unfold tailWord_1959146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17863981240089028085850323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47637283306904074895600861 17863981240089028085850323)
  ·
    refine ⟨26795971860133542128775485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17863981240089028085850323 26795971860133542128775485)
    ·
      refine ⟨10048489447550078298290807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26795971860133542128775485 10048489447550078298290807)
      ·
        refine ⟨15072734171325117447436211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10048489447550078298290807 15072734171325117447436211)
        ·
          refine ⟨22609101256987676171154317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15072734171325117447436211 22609101256987676171154317)
          ·
            refine ⟨8478412971370378564182869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22609101256987676171154317 8478412971370378564182869)
            ·
              refine ⟨49678201004123311899509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8478412971370378564182869 49678201004123311899509)
              ·
                rfl

theorem cell21_1959146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 9].length) (baseStart_1959146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1959146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1959146 prefixEnd_1959146 := by exact prefixLift 1959146
  have htrace : WordTrace (prefixWord ++ tailWord_1959146) baseStart_1959146 baseEnd_1959146 := by
    simpa [prefixWord, tailWord_1959146, baseEnd_1959146] using wordTrace_append hprefix tailTrace_1959146
  have hstable : (prefixWord ++ tailWord_1959146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959146).length < 2 ^ (prefixWord ++ tailWord_1959146).sum := by decide
  have hdescent : baseEnd_1959146 < baseStart_1959146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959166 : List Nat := [4, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_1959166 : Nat := 118140960795 + 1959166 * 2 ^ 59
def prefixEnd_1959166 : Nat := 4983230072969 + 3 ^ 40 * 1959166 * 2
def baseEnd_1959166 : Nat := 447108373309594216762207

theorem tailTrace_1959166 : CollatzResearch.WordTrace tailWord_1959166 prefixEnd_1959166 447108373309594216762207 := by
  unfold tailWord_1959166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8932081802535456969891169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47637769613522437172752901 8932081802535456969891169)
  ·
    refine ⟨6699061351901592727418377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8932081802535456969891169 6699061351901592727418377)
    ·
      refine ⟨5024296013926194545563783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6699061351901592727418377 5024296013926194545563783)
      ·
        refine ⟨7536444020889291818345675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5024296013926194545563783 7536444020889291818345675)
        ·
          refine ⟨11304666031333937727518513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7536444020889291818345675 11304666031333937727518513)
          ·
            refine ⟨8478499523500453295638885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11304666031333937727518513 8478499523500453295638885)
            ·
              refine ⟨1589718660656334992932291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8478499523500453295638885 1589718660656334992932291)
              ·
                refine ⟨2384577990984502489398437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589718660656334992932291 2384577990984502489398437)
                ·
                  refine ⟨447108373309594216762207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2384577990984502489398437 447108373309594216762207)
                  ·
                    rfl

theorem cell21_1959166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_1959166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1959166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1959166 prefixEnd_1959166 := by exact prefixLift 1959166
  have htrace : WordTrace (prefixWord ++ tailWord_1959166) baseStart_1959166 baseEnd_1959166 := by
    simpa [prefixWord, tailWord_1959166, baseEnd_1959166] using wordTrace_append hprefix tailTrace_1959166
  have hstable : (prefixWord ++ tailWord_1959166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959166).length < 2 ^ (prefixWord ++ tailWord_1959166).sum := by decide
  have hdescent : baseEnd_1959166 < baseStart_1959166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959239 : List Nat := [1, 1, 4, 1, 2, 4, 3, 5]
def baseStart_1959239 : Nat := 118140960795 + 1959239 * 2 ^ 59
def prefixEnd_1959239 : Nat := 4983230072969 + 3 ^ 40 * 1959239 * 2
def baseEnd_1959239 : Nat := 149041677634720770681797

theorem tailTrace_1959239 : CollatzResearch.WordTrace tailWord_1959239 prefixEnd_1959239 149041677634720770681797 := by
  unfold tailWord_1959239
  simp only [CollatzResearch.WordTrace]
  refine ⟨71459316949019189226536771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47639544632679459484357847 71459316949019189226536771)
  ·
    refine ⟨107188975423528783839805157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71459316949019189226536771 107188975423528783839805157)
    ·
      refine ⟨20097932891911646969963467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107188975423528783839805157 20097932891911646969963467)
      ·
        refine ⟨30146899337867470454945201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20097932891911646969963467 30146899337867470454945201)
        ·
          refine ⟨22610174503400602841208901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30146899337867470454945201 22610174503400602841208901)
          ·
            refine ⟨4239407719387613032726669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22610174503400602841208901 4239407719387613032726669)
            ·
              refine ⟨1589777894770354887272501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4239407719387613032726669 1589777894770354887272501)
              ·
                refine ⟨149041677634720770681797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1589777894770354887272501 149041677634720770681797)
                ·
                  rfl

theorem cell21_1959239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 5].length) (baseStart_1959239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1959239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1959239 prefixEnd_1959239 := by exact prefixLift 1959239
  have htrace : WordTrace (prefixWord ++ tailWord_1959239) baseStart_1959239 baseEnd_1959239 := by
    simpa [prefixWord, tailWord_1959239, baseEnd_1959239] using wordTrace_append hprefix tailTrace_1959239
  have hstable : (prefixWord ++ tailWord_1959239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959239).length < 2 ^ (prefixWord ++ tailWord_1959239).sum := by decide
  have hdescent : baseEnd_1959239 < baseStart_1959239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959245 : List Nat := [1, 6, 1, 3, 1, 1, 2, 3, 3]
def baseStart_1959245 : Nat := 118140960795 + 1959245 * 2 ^ 59
def prefixEnd_1959245 : Nat := 4983230072969 + 3 ^ 40 * 1959245 * 2
def baseEnd_1959245 : Nat := 447126402185907634945379

theorem tailTrace_1959245 : CollatzResearch.WordTrace tailWord_1959245 prefixEnd_1959245 447126402185907634945379 := by
  unfold tailWord_1959245
  simp only [CollatzResearch.WordTrace]
  refine ⟨71459535786997452251255189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47639690524664968167503459 71459535786997452251255189)
  ·
    refine ⟨3349665740015505574277587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71459535786997452251255189 3349665740015505574277587)
    ·
      refine ⟨5024498610023258361416381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3349665740015505574277587 5024498610023258361416381)
      ·
        refine ⟨1884186978758721885531143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5024498610023258361416381 1884186978758721885531143)
        ·
          refine ⟨2826280468138082828296715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884186978758721885531143 2826280468138082828296715)
          ·
            refine ⟨4239420702207124242445073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2826280468138082828296715 4239420702207124242445073)
            ·
              refine ⟨3179565526655343181833805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4239420702207124242445073 3179565526655343181833805)
              ·
                refine ⟨1192337072495753693187677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3179565526655343181833805 1192337072495753693187677)
                ·
                  refine ⟨447126402185907634945379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1192337072495753693187677 447126402185907634945379)
                  ·
                    rfl

theorem cell21_1959245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_1959245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1959245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1959245 prefixEnd_1959245 := by exact prefixLift 1959245
  have htrace : WordTrace (prefixWord ++ tailWord_1959245) baseStart_1959245 baseEnd_1959245 := by
    simpa [prefixWord, tailWord_1959245, baseEnd_1959245] using wordTrace_append hprefix tailTrace_1959245
  have hstable : (prefixWord ++ tailWord_1959245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959245).length < 2 ^ (prefixWord ++ tailWord_1959245).sum := by decide
  have hdescent : baseEnd_1959245 < baseStart_1959245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959433 : List Nat := [1, 2, 1, 1, 3, 1, 12]
def baseStart_1959433 : Nat := 118140960795 + 1959433 * 2 ^ 59
def prefixEnd_1959433 : Nat := 4983230072969 + 3 ^ 40 * 1959433 * 2
def baseEnd_1959433 : Nat := 49685478483029009534629

theorem tailTrace_1959433 : CollatzResearch.WordTrace tailWord_1959433 prefixEnd_1959433 49685478483029009534629 := by
  unfold tailWord_1959433
  simp only [CollatzResearch.WordTrace]
  refine ⟨71466392710316360359098953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47644261806877573572732635 71466392710316360359098953)
  ·
    refine ⟨53599794532737270269324215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71466392710316360359098953 53599794532737270269324215)
    ·
      refine ⟨80399691799105905403986323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53599794532737270269324215 80399691799105905403986323)
      ·
        refine ⟨120599537698658858105979485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80399691799105905403986323 120599537698658858105979485)
        ·
          refine ⟨45224826636997071789742307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120599537698658858105979485 45224826636997071789742307)
          ·
            refine ⟨67837239955495607684613461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45224826636997071789742307 67837239955495607684613461)
            ·
              refine ⟨49685478483029009534629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 67837239955495607684613461 49685478483029009534629)
              ·
                rfl

theorem cell21_1959433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 12].length) (baseStart_1959433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1959433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1959433 prefixEnd_1959433 := by exact prefixLift 1959433
  have htrace : WordTrace (prefixWord ++ tailWord_1959433) baseStart_1959433 baseEnd_1959433 := by
    simpa [prefixWord, tailWord_1959433, baseEnd_1959433] using wordTrace_append hprefix tailTrace_1959433
  have hstable : (prefixWord ++ tailWord_1959433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959433).length < 2 ^ (prefixWord ++ tailWord_1959433).sum := by decide
  have hdescent : baseEnd_1959433 < baseStart_1959433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959436 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 6]
def baseStart_1959436 : Nat := 118140960795 + 1959436 * 2 ^ 59
def prefixEnd_1959436 : Nat := 4983230072969 + 3 ^ 40 * 1959436 * 2
def baseEnd_1959436 : Nat := 447169990988133747261655

theorem tailTrace_1959436 : CollatzResearch.WordTrace tailWord_1959436 prefixEnd_1959436 447169990988133747261655 := by
  unfold tailWord_1959436
  simp only [CollatzResearch.WordTrace]
  refine ⟨35733251064652745935729081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47644334752870327914305441 35733251064652745935729081)
  ·
    refine ⟨26799938298489559451796811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35733251064652745935729081 26799938298489559451796811)
    ·
      refine ⟨40199907447734339177695217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26799938298489559451796811 40199907447734339177695217)
      ·
        refine ⟨30149930585800754383271413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40199907447734339177695217 30149930585800754383271413)
        ·
          refine ⟨2826555992418820723431695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30149930585800754383271413 2826555992418820723431695)
          ·
            refine ⟨4239833988628231085147543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2826555992418820723431695 4239833988628231085147543)
            ·
              refine ⟨6359750982942346627721315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4239833988628231085147543 6359750982942346627721315)
              ·
                refine ⟨9539626474413519941581973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6359750982942346627721315 9539626474413519941581973)
                ·
                  refine ⟨447169990988133747261655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9539626474413519941581973 447169990988133747261655)
                  ·
                    rfl

theorem cell21_1959436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_1959436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1959436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1959436 prefixEnd_1959436 := by exact prefixLift 1959436
  have htrace : WordTrace (prefixWord ++ tailWord_1959436) baseStart_1959436 baseEnd_1959436 := by
    simpa [prefixWord, tailWord_1959436, baseEnd_1959436] using wordTrace_append hprefix tailTrace_1959436
  have hstable : (prefixWord ++ tailWord_1959436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959436).length < 2 ^ (prefixWord ++ tailWord_1959436).sum := by decide
  have hdescent : baseEnd_1959436 < baseStart_1959436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959453 : List Nat := [1, 4, 2, 2, 1, 1, 5, 1, 4]
def baseStart_1959453 : Nat := 118140960795 + 1959453 * 2 ^ 59
def prefixEnd_1959453 : Nat := 4983230072969 + 3 ^ 40 * 1959453 * 2
def baseEnd_1959453 : Nat := 447173870619745495478287

theorem tailTrace_1959453 : CollatzResearch.WordTrace tailWord_1959453 prefixEnd_1959453 447173870619745495478287 := by
  unfold tailWord_1959453
  simp only [CollatzResearch.WordTrace]
  refine ⟨71467122170243903774827013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47644748113495935849884675 71467122170243903774827013)
  ·
    refine ⟨13400085406920731957780065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71467122170243903774827013 13400085406920731957780065)
    ·
      refine ⟨10050064055190548968335049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13400085406920731957780065 10050064055190548968335049)
      ·
        refine ⟨7537548041392911726251287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10050064055190548968335049 7537548041392911726251287)
        ·
          refine ⟨11306322062089367589376931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7537548041392911726251287 11306322062089367589376931)
          ·
            refine ⟨16959483093134051384065397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11306322062089367589376931 16959483093134051384065397)
            ·
              refine ⟨1589951539981317317256131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16959483093134051384065397 1589951539981317317256131)
              ·
                refine ⟨2384927309971975975884197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589951539981317317256131 2384927309971975975884197)
                ·
                  refine ⟨447173870619745495478287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2384927309971975975884197 447173870619745495478287)
                  ·
                    rfl

theorem cell21_1959453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_1959453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1959453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1959453 prefixEnd_1959453 := by exact prefixLift 1959453
  have htrace : WordTrace (prefixWord ++ tailWord_1959453) baseStart_1959453 baseEnd_1959453 := by
    simpa [prefixWord, tailWord_1959453, baseEnd_1959453] using wordTrace_append hprefix tailTrace_1959453
  have hstable : (prefixWord ++ tailWord_1959453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959453).length < 2 ^ (prefixWord ++ tailWord_1959453).sum := by decide
  have hdescent : baseEnd_1959453 < baseStart_1959453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959560 : List Nat := [2, 1, 3, 5, 1, 2, 1, 6]
def baseStart_1959560 : Nat := 118140960795 + 1959560 * 2 ^ 59
def prefixEnd_1959560 : Nat := 4983230072969 + 3 ^ 40 * 1959560 * 2
def baseEnd_1959560 : Nat := 149066096492512362398245

theorem tailTrace_1959560 : CollatzResearch.WordTrace tailWord_1959560 prefixEnd_1959560 149066096492512362398245 := by
  unfold tailWord_1959560
  simp only [CollatzResearch.WordTrace]
  refine ⟨35735512390428130524486067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47647349853904174032648089 35735512390428130524486067)
  ·
    refine ⟨53603268585642195786729101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35735512390428130524486067 53603268585642195786729101)
    ·
      refine ⟨20101225719615823420023413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53603268585642195786729101 20101225719615823420023413)
      ·
        refine ⟨1884489911213983445627195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20101225719615823420023413 1884489911213983445627195)
        ·
          refine ⟨2826734866820975168440793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884489911213983445627195 2826734866820975168440793)
          ·
            refine ⟨2120051150115731376330595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2826734866820975168440793 2120051150115731376330595)
            ·
              refine ⟨3180076725173597064495893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120051150115731376330595 3180076725173597064495893)
              ·
                refine ⟨149066096492512362398245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3180076725173597064495893 149066096492512362398245)
                ·
                  rfl

theorem cell21_1959560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 6].length) (baseStart_1959560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1959560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1959560 prefixEnd_1959560 := by exact prefixLift 1959560
  have htrace : WordTrace (prefixWord ++ tailWord_1959560) baseStart_1959560 baseEnd_1959560 := by
    simpa [prefixWord, tailWord_1959560, baseEnd_1959560] using wordTrace_append hprefix tailTrace_1959560
  have hstable : (prefixWord ++ tailWord_1959560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959560).length < 2 ^ (prefixWord ++ tailWord_1959560).sum := by decide
  have hdescent : baseEnd_1959560 < baseStart_1959560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959636 : List Nat := [2, 4, 1, 3, 1, 3, 2, 5]
def baseStart_1959636 : Nat := 118140960795 + 1959636 * 2 ^ 59
def prefixEnd_1959636 : Nat := 4983230072969 + 3 ^ 40 * 1959636 * 2
def baseEnd_1959636 : Nat := 149071877904325947975971

theorem tailTrace_1959636 : CollatzResearch.WordTrace tailWord_1959636 prefixEnd_1959636 149071877904325947975971 := by
  unfold tailWord_1959636
  simp only [CollatzResearch.WordTrace]
  refine ⟨35736898364290463014369381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47649197819053950685825841 35736898364290463014369381)
  ·
    refine ⟨6700668443304461815194259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35736898364290463014369381 6700668443304461815194259)
    ·
      refine ⟨10051002664956692722791389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6700668443304461815194259 10051002664956692722791389)
      ·
        refine ⟨3769125999358759771046771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10051002664956692722791389 3769125999358759771046771)
        ·
          refine ⟨5653688999038139656570157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3769125999358759771046771 5653688999038139656570157)
          ·
            refine ⟨2120133374639302371213809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5653688999038139656570157 2120133374639302371213809)
            ·
              refine ⟨1590100030979476778410357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2120133374639302371213809 1590100030979476778410357)
              ·
                refine ⟨149071877904325947975971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1590100030979476778410357 149071877904325947975971)
                ·
                  rfl

theorem cell21_1959636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 5].length) (baseStart_1959636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1959636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1959636 prefixEnd_1959636 := by exact prefixLift 1959636
  have htrace : WordTrace (prefixWord ++ tailWord_1959636) baseStart_1959636 baseEnd_1959636 := by
    simpa [prefixWord, tailWord_1959636, baseEnd_1959636] using wordTrace_append hprefix tailTrace_1959636
  have hstable : (prefixWord ++ tailWord_1959636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959636).length < 2 ^ (prefixWord ++ tailWord_1959636).sum := by decide
  have hdescent : baseEnd_1959636 < baseStart_1959636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959692 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 5]
def baseStart_1959692 : Nat := 118140960795 + 1959692 * 2 ^ 59
def prefixEnd_1959692 : Nat := 4983230072969 + 3 ^ 40 * 1959692 * 2
def baseEnd_1959692 : Nat := 447228413675934190994465

theorem tailTrace_1959692 : CollatzResearch.WordTrace tailWord_1959692 prefixEnd_1959692 447228413675934190994465 := by
  unfold tailWord_1959692
  simp only [CollatzResearch.WordTrace]
  refine ⟨35737919608189023796388665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47650559477585365061851553 35737919608189023796388665)
  ·
    refine ⟨26803439706141767847291499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35737919608189023796388665 26803439706141767847291499)
    ·
      refine ⟨40205159559212651770937249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26803439706141767847291499 40205159559212651770937249)
      ·
        refine ⟨30153869669409488828202937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40205159559212651770937249 30153869669409488828202937)
        ·
          refine ⟨22615402252057116621152203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30153869669409488828202937 22615402252057116621152203)
          ·
            refine ⟨33923103378085674931728305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22615402252057116621152203 33923103378085674931728305)
            ·
              refine ⟨25442327533564256198796229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33923103378085674931728305 25442327533564256198796229)
              ·
                refine ⟨4770436412543298037274293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25442327533564256198796229 4770436412543298037274293)
                ·
                  refine ⟨447228413675934190994465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4770436412543298037274293 447228413675934190994465)
                  ·
                    rfl

theorem cell21_1959692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_1959692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1959692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1959692 prefixEnd_1959692 := by exact prefixLift 1959692
  have htrace : WordTrace (prefixWord ++ tailWord_1959692) baseStart_1959692 baseEnd_1959692 := by
    simpa [prefixWord, tailWord_1959692, baseEnd_1959692] using wordTrace_append hprefix tailTrace_1959692
  have hstable : (prefixWord ++ tailWord_1959692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959692).length < 2 ^ (prefixWord ++ tailWord_1959692).sum := by decide
  have hdescent : baseEnd_1959692 < baseStart_1959692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959754 : List Nat := [3, 1, 2, 1, 1, 1, 7, 5]
def baseStart_1959754 : Nat := 118140960795 + 1959754 * 2 ^ 59
def prefixEnd_1959754 : Nat := 4983230072969 + 3 ^ 40 * 1959754 * 2
def baseEnd_1959754 : Nat := 149080854306878620320335

theorem tailTrace_1959754 : CollatzResearch.WordTrace tailWord_1959754 prefixEnd_1959754 149080854306878620320335 := by
  unfold tailWord_1959754
  simp only [CollatzResearch.WordTrace]
  refine ⟨17869525135538358045383579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47652067028102288121022877 17869525135538358045383579)
  ·
    refine ⟨26804287703307537068075369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17869525135538358045383579 26804287703307537068075369)
    ·
      refine ⟨20103215777480652801056527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26804287703307537068075369 20103215777480652801056527)
      ·
        refine ⟨30154823666220979201584791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20103215777480652801056527 30154823666220979201584791)
        ·
          refine ⟨45232235499331468802377187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30154823666220979201584791 45232235499331468802377187)
          ·
            refine ⟨67848353248997203203565781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45232235499331468802377187 67848353248997203203565781)
            ·
              refine ⟨1590195779273371950083573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 67848353248997203203565781 1590195779273371950083573)
              ·
                refine ⟨149080854306878620320335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1590195779273371950083573 149080854306878620320335)
                ·
                  rfl

theorem cell21_1959754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_1959754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1959754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1959754 prefixEnd_1959754 := by exact prefixLift 1959754
  have htrace : WordTrace (prefixWord ++ tailWord_1959754) baseStart_1959754 baseEnd_1959754 := by
    simpa [prefixWord, tailWord_1959754, baseEnd_1959754] using wordTrace_append hprefix tailTrace_1959754
  have hstable : (prefixWord ++ tailWord_1959754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959754).length < 2 ^ (prefixWord ++ tailWord_1959754).sum := by decide
  have hdescent : baseEnd_1959754 < baseStart_1959754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959813 : List Nat := [1, 3, 1, 1, 3, 2, 3, 7]
def baseStart_1959813 : Nat := 118140960795 + 1959813 * 2 ^ 59
def prefixEnd_1959813 : Nat := 4983230072969 + 3 ^ 40 * 1959813 * 2
def baseEnd_1959813 : Nat := 149085342508154956492517

theorem tailTrace_1959813 : CollatzResearch.WordTrace tailWord_1959813 prefixEnd_1959813 149085342508154956492517 := by
  unfold tailWord_1959813
  simp only [CollatzResearch.WordTrace]
  refine ⟨71480252448939685257932093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47653501632626456838621395 71480252448939685257932093)
  ·
    refine ⟨26805094668352381971724535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71480252448939685257932093 26805094668352381971724535)
    ·
      refine ⟨40207642002528572957586803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26805094668352381971724535 40207642002528572957586803)
      ·
        refine ⟨60311463003792859436380205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40207642002528572957586803 60311463003792859436380205)
        ·
          refine ⟨22616798626422322288642577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60311463003792859436380205 22616798626422322288642577)
          ·
            refine ⟨16962598969816741716481933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22616798626422322288642577 16962598969816741716481933)
            ·
              refine ⟨6360974613681278143680725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16962598969816741716481933 6360974613681278143680725)
              ·
                refine ⟨149085342508154956492517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6360974613681278143680725 149085342508154956492517)
                ·
                  rfl

theorem cell21_1959813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 7].length) (baseStart_1959813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1959813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1959813 prefixEnd_1959813 := by exact prefixLift 1959813
  have htrace : WordTrace (prefixWord ++ tailWord_1959813) baseStart_1959813 baseEnd_1959813 := by
    simpa [prefixWord, tailWord_1959813, baseEnd_1959813] using wordTrace_append hprefix tailTrace_1959813
  have hstable : (prefixWord ++ tailWord_1959813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959813).length < 2 ^ (prefixWord ++ tailWord_1959813).sum := by decide
  have hdescent : baseEnd_1959813 < baseStart_1959813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959892 : List Nat := [2, 4, 1, 2, 1, 1, 4, 2, 4]
def baseStart_1959892 : Nat := 118140960795 + 1959892 * 2 ^ 59
def prefixEnd_1959892 : Nat := 4983230072969 + 3 ^ 40 * 1959892 * 2
def baseEnd_1959892 : Nat := 447274056400778287660723

theorem tailTrace_1959892 : CollatzResearch.WordTrace tailWord_1959892 prefixEnd_1959892 447274056400778287660723 := by
  unfold tailWord_1959892
  simp only [CollatzResearch.WordTrace]
  refine ⟨35741566907826740875028965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47655422543768987833371953 35741566907826740875028965)
  ·
    refine ⟨6701543795217513914067931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35741566907826740875028965 6701543795217513914067931)
    ·
      refine ⟨10052315692826270871101897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6701543795217513914067931 10052315692826270871101897)
      ·
        refine ⟨7539236769619703153326423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10052315692826270871101897 7539236769619703153326423)
        ·
          refine ⟨11308855154429554729989635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7539236769619703153326423 11308855154429554729989635)
          ·
            refine ⟨16963282731644332094984453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11308855154429554729989635 16963282731644332094984453)
            ·
              refine ⟨3180615512183312267809585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16963282731644332094984453 3180615512183312267809585)
              ·
                refine ⟨2385461634137484200857189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3180615512183312267809585 2385461634137484200857189)
                ·
                  refine ⟨447274056400778287660723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2385461634137484200857189 447274056400778287660723)
                  ·
                    rfl

theorem cell21_1959892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_1959892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1959892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1959892 prefixEnd_1959892 := by exact prefixLift 1959892
  have htrace : WordTrace (prefixWord ++ tailWord_1959892) baseStart_1959892 baseEnd_1959892 := by
    simpa [prefixWord, tailWord_1959892, baseEnd_1959892] using wordTrace_append hprefix tailTrace_1959892
  have hstable : (prefixWord ++ tailWord_1959892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959892).length < 2 ^ (prefixWord ++ tailWord_1959892).sum := by decide
  have hdescent : baseEnd_1959892 < baseStart_1959892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959979 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 7]
def baseStart_1959979 : Nat := 118140960795 + 1959979 * 2 ^ 59
def prefixEnd_1959979 : Nat := 4983230072969 + 3 ^ 40 * 1959979 * 2
def baseEnd_1959979 : Nat := 447293910986085469710545

theorem tailTrace_1959979 : CollatzResearch.WordTrace tailWord_1959979 prefixEnd_1959979 447293910986085469710545 := by
  unfold tailWord_1959979
  simp only [CollatzResearch.WordTrace]
  refine ⟨71486306966338295608474991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47657537977558863738983327 71486306966338295608474991)
  ·
    refine ⟨107229460449507443412712487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71486306966338295608474991 107229460449507443412712487)
    ·
      refine ⟨160844190674261165119068731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107229460449507443412712487 160844190674261165119068731)
      ·
        refine ⟨241266286011391747678603097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160844190674261165119068731 241266286011391747678603097)
        ·
          refine ⟨180949714508543810758952323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241266286011391747678603097 180949714508543810758952323)
          ·
            refine ⟨271424571762815716138428485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180949714508543810758952323 271424571762815716138428485)
            ·
              refine ⟨50892107205527946775955341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271424571762815716138428485 50892107205527946775955341)
              ·
                refine ⟨19084540202072980040983253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50892107205527946775955341 19084540202072980040983253)
                ·
                  refine ⟨447293910986085469710545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19084540202072980040983253 447293910986085469710545)
                  ·
                    rfl

theorem cell21_1959979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 7].length) (baseStart_1959979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1959979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1959979 prefixEnd_1959979 := by exact prefixLift 1959979
  have htrace : WordTrace (prefixWord ++ tailWord_1959979) baseStart_1959979 baseEnd_1959979 := by
    simpa [prefixWord, tailWord_1959979, baseEnd_1959979] using wordTrace_append hprefix tailTrace_1959979
  have hstable : (prefixWord ++ tailWord_1959979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959979).length < 2 ^ (prefixWord ++ tailWord_1959979).sum := by decide
  have hdescent : baseEnd_1959979 < baseStart_1959979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959982 : List Nat := [4, 1, 3, 1, 1, 3, 1, 7]
def baseStart_1959982 : Nat := 118140960795 + 1959982 * 2 ^ 59
def prefixEnd_1959982 : Nat := 4983230072969 + 3 ^ 40 * 1959982 * 2
def baseEnd_1959982 : Nat := 149098198542319377053513

theorem tailTrace_1959982 : CollatzResearch.WordTrace tailWord_1959982 prefixEnd_1959982 149098198542319377053513 := by
  unfold tailWord_1959982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8935802048165928390104275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47657610923551618080556133 8935802048165928390104275)
  ·
    refine ⟨13403703072248892585156413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8935802048165928390104275 13403703072248892585156413)
    ·
      refine ⟨5026388652093334719433655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13403703072248892585156413 5026388652093334719433655)
      ·
        refine ⟨7539582978140002079150483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5026388652093334719433655 7539582978140002079150483)
        ·
          refine ⟨11309374467210003118725725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7539582978140002079150483 11309374467210003118725725)
          ·
            refine ⟨4241015425203751169522147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11309374467210003118725725 4241015425203751169522147)
            ·
              refine ⟨6361523137805626754283221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241015425203751169522147 6361523137805626754283221)
              ·
                refine ⟨149098198542319377053513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6361523137805626754283221 149098198542319377053513)
                ·
                  rfl

theorem cell21_1959982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_1959982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1959982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1959982 prefixEnd_1959982 := by exact prefixLift 1959982
  have htrace : WordTrace (prefixWord ++ tailWord_1959982) baseStart_1959982 baseEnd_1959982 := by
    simpa [prefixWord, tailWord_1959982, baseEnd_1959982] using wordTrace_append hprefix tailTrace_1959982
  have hstable : (prefixWord ++ tailWord_1959982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959982).length < 2 ^ (prefixWord ++ tailWord_1959982).sum := by decide
  have hdescent : baseEnd_1959982 < baseStart_1959982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1959988 : List Nat := [2, 5, 1, 2, 2, 2, 1, 3, 3]
def baseStart_1959988 : Nat := 118140960795 + 1959988 * 2 ^ 59
def prefixEnd_1959988 : Nat := 4983230072969 + 3 ^ 40 * 1959988 * 2
def baseEnd_1959988 : Nat := 447295964908703454060527

theorem tailTrace_1959988 : CollatzResearch.WordTrace tailWord_1959988 prefixEnd_1959988 447295964908703454060527 := by
  unfold tailWord_1959988
  simp only [CollatzResearch.WordTrace]
  refine ⟨35743317611652845072776309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47657756815537126763701745 35743317611652845072776309)
  ·
    refine ⟨3350936026092454225572779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35743317611652845072776309 3350936026092454225572779)
    ·
      refine ⟨5026404039138681338359169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3350936026092454225572779 5026404039138681338359169)
      ·
        refine ⟨3769803029354011003769377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5026404039138681338359169 3769803029354011003769377)
        ·
          refine ⟨2827352272015508252827033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3769803029354011003769377 2827352272015508252827033)
          ·
            refine ⟨2120514204011631189620275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2827352272015508252827033 2120514204011631189620275)
            ·
              refine ⟨3180771306017446784430413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120514204011631189620275 3180771306017446784430413)
              ·
                refine ⟨1192789239756542544161405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3180771306017446784430413 1192789239756542544161405)
                ·
                  refine ⟨447295964908703454060527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1192789239756542544161405 447295964908703454060527)
                  ·
                    rfl

theorem cell21_1959988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_1959988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1959988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1959988 prefixEnd_1959988 := by exact prefixLift 1959988
  have htrace : WordTrace (prefixWord ++ tailWord_1959988) baseStart_1959988 baseEnd_1959988 := by
    simpa [prefixWord, tailWord_1959988, baseEnd_1959988] using wordTrace_append hprefix tailTrace_1959988
  have hstable : (prefixWord ++ tailWord_1959988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1959988).length < 2 ^ (prefixWord ++ tailWord_1959988).sum := by decide
  have hdescent : baseEnd_1959988 < baseStart_1959988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1959988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960193 : List Nat := [1, 2, 4, 1, 1, 2, 4, 6]
def baseStart_1960193 : Nat := 118140960795 + 1960193 * 2 ^ 59
def prefixEnd_1960193 : Nat := 4983230072969 + 3 ^ 40 * 1960193 * 2
def baseEnd_1960193 : Nat := 149114249567222884381147

theorem tailTrace_1960193 : CollatzResearch.WordTrace tailWord_1960193 prefixEnd_1960193 149114249567222884381147 := by
  unfold tailWord_1960193
  simp only [CollatzResearch.WordTrace]
  refine ⟨71494112187563010156765233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47662741458375340104510155 71494112187563010156765233)
  ·
    refine ⟨53620584140672257617573925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71494112187563010156765233 53620584140672257617573925)
    ·
      refine ⟨10053859526376048303295111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53620584140672257617573925 10053859526376048303295111)
      ·
        refine ⟨15080789289564072454942667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10053859526376048303295111 15080789289564072454942667)
        ·
          refine ⟨22621183934346108682414001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15080789289564072454942667 22621183934346108682414001)
          ·
            refine ⟨16965887950759581511810501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22621183934346108682414001 16965887950759581511810501)
            ·
              refine ⟨3181103990767421533464469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16965887950759581511810501 3181103990767421533464469)
              ·
                refine ⟨149114249567222884381147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3181103990767421533464469 149114249567222884381147)
                ·
                  rfl

theorem cell21_1960193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 6].length) (baseStart_1960193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960193 prefixEnd_1960193 := by exact prefixLift 1960193
  have htrace : WordTrace (prefixWord ++ tailWord_1960193) baseStart_1960193 baseEnd_1960193 := by
    simpa [prefixWord, tailWord_1960193, baseEnd_1960193] using wordTrace_append hprefix tailTrace_1960193
  have hstable : (prefixWord ++ tailWord_1960193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960193).length < 2 ^ (prefixWord ++ tailWord_1960193).sum := by decide
  have hdescent : baseEnd_1960193 < baseStart_1960193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960196 : List Nat := [2, 3, 2, 2, 3, 1, 1, 3, 4]
def baseStart_1960196 : Nat := 118140960795 + 1960196 * 2 ^ 59
def prefixEnd_1960196 : Nat := 4983230072969 + 3 ^ 40 * 1960196 * 2
def baseEnd_1960196 : Nat := 447343433342541314593435

theorem tailTrace_1960196 : CollatzResearch.WordTrace tailWord_1960196 prefixEnd_1960196 447343433342541314593435 := by
  unfold tailWord_1960196
  simp only [CollatzResearch.WordTrace]
  refine ⟨35747110803276070834562221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47662814404368094446082961 35747110803276070834562221)
  ·
    refine ⟨13405166551228526562960833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35747110803276070834562221 13405166551228526562960833)
    ·
      refine ⟨10053874913421394922220625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13405166551228526562960833 10053874913421394922220625)
      ·
        refine ⟨7540406185066046191665469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10053874913421394922220625 7540406185066046191665469)
        ·
          refine ⟨2827652319399767321874551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7540406185066046191665469 2827652319399767321874551)
          ·
            refine ⟨4241478479099650982811827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827652319399767321874551 4241478479099650982811827)
            ·
              refine ⟨6362217718649476474217741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241478479099650982811827 6362217718649476474217741)
              ·
                refine ⟨2385831644493553677831653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6362217718649476474217741 2385831644493553677831653)
                ·
                  refine ⟨447343433342541314593435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2385831644493553677831653 447343433342541314593435)
                  ·
                    rfl

theorem cell21_1960196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_1960196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960196 prefixEnd_1960196 := by exact prefixLift 1960196
  have htrace : WordTrace (prefixWord ++ tailWord_1960196) baseStart_1960196 baseEnd_1960196 := by
    simpa [prefixWord, tailWord_1960196, baseEnd_1960196] using wordTrace_append hprefix tailTrace_1960196
  have hstable : (prefixWord ++ tailWord_1960196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960196).length < 2 ^ (prefixWord ++ tailWord_1960196).sum := by decide
  have hdescent : baseEnd_1960196 < baseStart_1960196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960207 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 5]
def baseStart_1960207 : Nat := 118140960795 + 1960207 * 2 ^ 59
def prefixEnd_1960207 : Nat := 4983230072969 + 3 ^ 40 * 1960207 * 2
def baseEnd_1960207 : Nat := 447345943692407739910079

theorem tailTrace_1960207 : CollatzResearch.WordTrace tailWord_1960207 prefixEnd_1960207 447345943692407739910079 := by
  unfold tailWord_1960207
  simp only [CollatzResearch.WordTrace]
  refine ⟨71494622809512290547774875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47663081873008193698516583 71494622809512290547774875)
  ·
    refine ⟨107241934214268435821662313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71494622809512290547774875 107241934214268435821662313)
    ·
      refine ⟨80431450660701326866246735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107241934214268435821662313 80431450660701326866246735)
      ·
        refine ⟨120647175991051990299370103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80431450660701326866246735 120647175991051990299370103)
        ·
          refine ⟨180970763986577985449055155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120647175991051990299370103 180970763986577985449055155)
          ·
            refine ⟨271456145979866978173582733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180970763986577985449055155 271456145979866978173582733)
            ·
              refine ⟨101796054742450116815093525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271456145979866978173582733 101796054742450116815093525)
              ·
                refine ⟨4771690066052349225707509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101796054742450116815093525 4771690066052349225707509)
                ·
                  refine ⟨447345943692407739910079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4771690066052349225707509 447345943692407739910079)
                  ·
                    rfl

theorem cell21_1960207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 5].length) (baseStart_1960207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960207 prefixEnd_1960207 := by exact prefixLift 1960207
  have htrace : WordTrace (prefixWord ++ tailWord_1960207) baseStart_1960207 baseEnd_1960207 := by
    simpa [prefixWord, tailWord_1960207, baseEnd_1960207] using wordTrace_append hprefix tailTrace_1960207
  have hstable : (prefixWord ++ tailWord_1960207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960207).length < 2 ^ (prefixWord ++ tailWord_1960207).sum := by decide
  have hdescent : baseEnd_1960207 < baseStart_1960207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960334 : List Nat := [4, 1, 1, 4, 1, 1, 3, 3, 3]
def baseStart_1960334 : Nat := 118140960795 + 1960334 * 2 ^ 59
def prefixEnd_1960334 : Nat := 4983230072969 + 3 ^ 40 * 1960334 * 2
def baseEnd_1960334 : Nat := 447374926822683741293153

theorem tailTrace_1960334 : CollatzResearch.WordTrace tailWord_1960334 prefixEnd_1960334 447374926822683741293153 := by
  unfold tailWord_1960334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8937406860006523904706007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47666169920034794158432037 8937406860006523904706007)
  ·
    refine ⟨13406110290009785857059011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8937406860006523904706007 13406110290009785857059011)
    ·
      refine ⟨20109165435014678785588517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13406110290009785857059011 20109165435014678785588517)
      ·
        refine ⟨3770468519065252272297847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20109165435014678785588517 3770468519065252272297847)
        ·
          refine ⟨5655702778597878408446771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3770468519065252272297847 5655702778597878408446771)
          ·
            refine ⟨8483554167896817612670157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5655702778597878408446771 8483554167896817612670157)
            ·
              refine ⟨3181332812961306604751309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8483554167896817612670157 3181332812961306604751309)
              ·
                refine ⟨1192999804860489976781741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3181332812961306604751309 1192999804860489976781741)
                ·
                  refine ⟨447374926822683741293153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1192999804860489976781741 447374926822683741293153)
                  ·
                    rfl

theorem cell21_1960334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_1960334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960334 prefixEnd_1960334 := by exact prefixLift 1960334
  have htrace : WordTrace (prefixWord ++ tailWord_1960334) baseStart_1960334 baseEnd_1960334 := by
    simpa [prefixWord, tailWord_1960334, baseEnd_1960334] using wordTrace_append hprefix tailTrace_1960334
  have hstable : (prefixWord ++ tailWord_1960334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960334).length < 2 ^ (prefixWord ++ tailWord_1960334).sum := by decide
  have hdescent : baseEnd_1960334 < baseStart_1960334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960435 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 5]
def baseStart_1960435 : Nat := 118140960795 + 1960435 * 2 ^ 59
def prefixEnd_1960435 : Nat := 4983230072969 + 3 ^ 40 * 1960435 * 2
def baseEnd_1960435 : Nat := 447397976398730010109613

theorem tailTrace_1960435 : CollatzResearch.WordTrace tailWord_1960435 prefixEnd_1960435 447397976398730010109613 := by
  unfold tailWord_1960435
  simp only [CollatzResearch.WordTrace]
  refine ⟨71502938652686285487074759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47668625768457523658049839 71502938652686285487074759)
  ·
    refine ⟨107254407979029428230612139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71502938652686285487074759 107254407979029428230612139)
    ·
      refine ⟨160881611968544142345918209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107254407979029428230612139 160881611968544142345918209)
      ·
        refine ⟨120661208976408106759438657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160881611968544142345918209 120661208976408106759438657)
        ·
          refine ⟨90495906732306080069578993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120661208976408106759438657 90495906732306080069578993)
          ·
            refine ⟨67871930049229560052184245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90495906732306080069578993 67871930049229560052184245)
            ·
              refine ⟨6362993442115271254892273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67871930049229560052184245 6362993442115271254892273)
              ·
                refine ⟨4772245081586453441169205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6362993442115271254892273 4772245081586453441169205)
                ·
                  refine ⟨447397976398730010109613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4772245081586453441169205 447397976398730010109613)
                  ·
                    rfl

theorem cell21_1960435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 5].length) (baseStart_1960435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960435 prefixEnd_1960435 := by exact prefixLift 1960435
  have htrace : WordTrace (prefixWord ++ tailWord_1960435) baseStart_1960435 baseEnd_1960435 := by
    simpa [prefixWord, tailWord_1960435, baseEnd_1960435] using wordTrace_append hprefix tailTrace_1960435
  have hstable : (prefixWord ++ tailWord_1960435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960435).length < 2 ^ (prefixWord ++ tailWord_1960435).sum := by decide
  have hdescent : baseEnd_1960435 < baseStart_1960435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960438 : List Nat := [5, 1, 1, 1, 2, 1, 5, 5]
def baseStart_1960438 : Nat := 118140960795 + 1960438 * 2 ^ 59
def prefixEnd_1960438 : Nat := 4983230072969 + 3 ^ 40 * 1960438 * 2
def baseEnd_1960438 : Nat := 149132887013200890519869

theorem tailTrace_1960438 : CollatzResearch.WordTrace tailWord_1960438 prefixEnd_1960438 149132887013200890519869 := by
  unfold tailWord_1960438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4468940504479713562464623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47668698714450277999622645 4468940504479713562464623)
  ·
    refine ⟨6703410756719570343696935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4468940504479713562464623 6703410756719570343696935)
    ·
      refine ⟨10055116135079355515545403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6703410756719570343696935 10055116135079355515545403)
      ·
        refine ⟨15082674202619033273318105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10055116135079355515545403 15082674202619033273318105)
        ·
          refine ⟨11312005651964274954988579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15082674202619033273318105 11312005651964274954988579)
          ·
            refine ⟨16968008477946412432482869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11312005651964274954988579 16968008477946412432482869)
            ·
              refine ⟨1590750794807476165545269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16968008477946412432482869 1590750794807476165545269)
              ·
                refine ⟨149132887013200890519869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1590750794807476165545269 149132887013200890519869)
                ·
                  rfl

theorem cell21_1960438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_1960438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960438 prefixEnd_1960438 := by exact prefixLift 1960438
  have htrace : WordTrace (prefixWord ++ tailWord_1960438) baseStart_1960438 baseEnd_1960438 := by
    simpa [prefixWord, tailWord_1960438, baseEnd_1960438] using wordTrace_append hprefix tailTrace_1960438
  have hstable : (prefixWord ++ tailWord_1960438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960438).length < 2 ^ (prefixWord ++ tailWord_1960438).sum := by decide
  have hdescent : baseEnd_1960438 < baseStart_1960438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960497 : List Nat := [1, 2, 2, 3, 1, 1, 6, 5]
def baseStart_1960497 : Nat := 118140960795 + 1960497 * 2 ^ 59
def prefixEnd_1960497 : Nat := 4983230072969 + 3 ^ 40 * 1960497 * 2
def baseEnd_1960497 : Nat := 149137375214477226692051

theorem tailTrace_1960497 : CollatzResearch.WordTrace tailWord_1960497 prefixEnd_1960497 149137375214477226692051 := by
  unfold tailWord_1960497
  simp only [CollatzResearch.WordTrace]
  refine ⟨71505199978461670075831745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47670133318974446717221163 71505199978461670075831745)
  ·
    refine ⟨53628899983846252556873809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71505199978461670075831745 53628899983846252556873809)
    ·
      refine ⟨40221674987884689417655357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53628899983846252556873809 40221674987884689417655357)
      ·
        refine ⟨15083128120456758531620759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40221674987884689417655357 15083128120456758531620759)
        ·
          refine ⟨22624692180685137797431139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15083128120456758531620759 22624692180685137797431139)
          ·
            refine ⟨33937038271027706696146709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22624692180685137797431139 33937038271027706696146709)
            ·
              refine ⟨1590798668954423751381877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33937038271027706696146709 1590798668954423751381877)
              ·
                refine ⟨149137375214477226692051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1590798668954423751381877 149137375214477226692051)
                ·
                  rfl

theorem cell21_1960497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 5].length) (baseStart_1960497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960497 prefixEnd_1960497 := by exact prefixLift 1960497
  have htrace : WordTrace (prefixWord ++ tailWord_1960497) baseStart_1960497 baseEnd_1960497 := by
    simpa [prefixWord, tailWord_1960497, baseEnd_1960497] using wordTrace_append hprefix tailTrace_1960497
  have hstable : (prefixWord ++ tailWord_1960497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960497).length < 2 ^ (prefixWord ++ tailWord_1960497).sum := by decide
  have hdescent : baseEnd_1960497 < baseStart_1960497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960556 : List Nat := [2, 2, 1, 1, 3, 1, 4, 7]
def baseStart_1960556 : Nat := 118140960795 + 1960556 * 2 ^ 59
def prefixEnd_1960556 : Nat := 4983230072969 + 3 ^ 40 * 1960556 * 2
def baseEnd_1960556 : Nat := 149141863415753562864233

theorem tailTrace_1960556 : CollatzResearch.WordTrace tailWord_1960556 prefixEnd_1960556 149141863415753562864233 := by
  unfold tailWord_1960556
  simp only [CollatzResearch.WordTrace]
  refine ⟨35753675942623961576114761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47671567923498615434819681 35753675942623961576114761)
  ·
    refine ⟨26815256956967971182086071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35753675942623961576114761 26815256956967971182086071)
    ·
      refine ⟨40222885435451956773129107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26815256956967971182086071 40222885435451956773129107)
      ·
        refine ⟨60334328153177935159693661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40222885435451956773129107 60334328153177935159693661)
        ·
          refine ⟨22625373057441725684885123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60334328153177935159693661 22625373057441725684885123)
          ·
            refine ⟨33938059586162588527327685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22625373057441725684885123 33938059586162588527327685)
            ·
              refine ⟨6363386172405485348873941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33938059586162588527327685 6363386172405485348873941)
              ·
                refine ⟨149141863415753562864233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6363386172405485348873941 149141863415753562864233)
                ·
                  rfl

theorem cell21_1960556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 7].length) (baseStart_1960556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960556 prefixEnd_1960556 := by exact prefixLift 1960556
  have htrace : WordTrace (prefixWord ++ tailWord_1960556) baseStart_1960556 baseEnd_1960556 := by
    simpa [prefixWord, tailWord_1960556, baseEnd_1960556] using wordTrace_append hprefix tailTrace_1960556
  have hstable : (prefixWord ++ tailWord_1960556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960556).length < 2 ^ (prefixWord ++ tailWord_1960556).sum := by decide
  have hdescent : baseEnd_1960556 < baseStart_1960556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960573 : List Nat := [1, 4, 1, 1, 6, 8]
def baseStart_1960573 : Nat := 118140960795 + 1960573 * 2 ^ 59
def prefixEnd_1960573 : Nat := 4983230072969 + 3 ^ 40 * 1960573 * 2
def baseEnd_1960573 : Nat := 16571461847365645807753

theorem tailTrace_1960573 : CollatzResearch.WordTrace tailWord_1960573 prefixEnd_1960573 16571461847365645807753 := by
  unfold tailWord_1960573
  simp only [CollatzResearch.WordTrace]
  refine ⟨71507971926186335055598373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47671981284124223370398915 71507971926186335055598373)
  ·
    refine ⟨13407744736159937822924695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71507971926186335055598373 13407744736159937822924695)
    ·
      refine ⟨20111617104239906734387043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13407744736159937822924695 20111617104239906734387043)
      ·
        refine ⟨30167425656359860101580565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20111617104239906734387043 30167425656359860101580565)
        ·
          refine ⟨1414098077641868442261589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30167425656359860101580565 1414098077641868442261589)
          ·
            refine ⟨16571461847365645807753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1414098077641868442261589 16571461847365645807753)
            ·
              rfl

theorem cell21_1960573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 8].length) (baseStart_1960573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960573 prefixEnd_1960573 := by exact prefixLift 1960573
  have htrace : WordTrace (prefixWord ++ tailWord_1960573) baseStart_1960573 baseEnd_1960573 := by
    simpa [prefixWord, tailWord_1960573, baseEnd_1960573] using wordTrace_append hprefix tailTrace_1960573
  have hstable : (prefixWord ++ tailWord_1960573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960573).length < 2 ^ (prefixWord ++ tailWord_1960573).sum := by decide
  have hdescent : baseEnd_1960573 < baseStart_1960573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960604 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 5]
def baseStart_1960604 : Nat := 118140960795 + 1960604 * 2 ^ 59
def prefixEnd_1960604 : Nat := 4983230072969 + 3 ^ 40 * 1960604 * 2
def baseEnd_1960604 : Nat := 447436544501223271792601

theorem tailTrace_1960604 : CollatzResearch.WordTrace tailWord_1960604 prefixEnd_1960604 447436544501223271792601 := by
  unfold tailWord_1960604
  simp only [CollatzResearch.WordTrace]
  refine ⟨35754551294537013674988433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47672735059382684899984577 35754551294537013674988433)
  ·
    refine ⟨26815913470902760256241325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35754551294537013674988433 26815913470902760256241325)
    ·
      refine ⟨10055967551588535096090497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26815913470902760256241325 10055967551588535096090497)
      ·
        refine ⟨7541975663691401322067873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10055967551588535096090497 7541975663691401322067873)
        ·
          refine ⟨5656481747768550991550905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7541975663691401322067873 5656481747768550991550905)
          ·
            refine ⟨4242361310826413243663179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5656481747768550991550905 4242361310826413243663179)
            ·
              refine ⟨6363541966239619865494769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4242361310826413243663179 6363541966239619865494769)
              ·
                refine ⟨4772656474679714899121077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6363541966239619865494769 4772656474679714899121077)
                ·
                  refine ⟨447436544501223271792601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4772656474679714899121077 447436544501223271792601)
                  ·
                    rfl

theorem cell21_1960604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_1960604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960604 prefixEnd_1960604 := by exact prefixLift 1960604
  have htrace : WordTrace (prefixWord ++ tailWord_1960604) baseStart_1960604 baseEnd_1960604 := by
    simpa [prefixWord, tailWord_1960604, baseEnd_1960604] using wordTrace_append hprefix tailTrace_1960604
  have hstable : (prefixWord ++ tailWord_1960604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960604).length < 2 ^ (prefixWord ++ tailWord_1960604).sum := by decide
  have hdescent : baseEnd_1960604 < baseStart_1960604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960621 : List Nat := [1, 5, 2, 1, 1, 2, 1, 5, 3]
def baseStart_1960621 : Nat := 118140960795 + 1960621 * 2 ^ 59
def prefixEnd_1960621 : Nat := 4983230072969 + 3 ^ 40 * 1960621 * 2
def baseEnd_1960621 : Nat := 447440424132835020009233

theorem tailTrace_1960621 : CollatzResearch.WordTrace tailWord_1960621 prefixEnd_1960621 447440424132835020009233 := by
  unfold tailWord_1960621
  simp only [CollatzResearch.WordTrace]
  refine ⟨71509722630012439253345717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47673148420008292835563811 71509722630012439253345717)
  ·
    refine ⟨6704036496563666180001161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71509722630012439253345717 6704036496563666180001161)
    ·
      refine ⟨5028027372422749635000871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6704036496563666180001161 5028027372422749635000871)
      ·
        refine ⟨7542041058634124452501307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5028027372422749635000871 7542041058634124452501307)
        ·
          refine ⟨11313061587951186678751961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7542041058634124452501307 11313061587951186678751961)
          ·
            refine ⟨8484796190963390009063971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11313061587951186678751961 8484796190963390009063971)
            ·
              refine ⟨12727194286445085013595957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8484796190963390009063971 12727194286445085013595957)
              ·
                refine ⟨1193174464354226720024621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12727194286445085013595957 1193174464354226720024621)
                ·
                  refine ⟨447440424132835020009233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193174464354226720024621 447440424132835020009233)
                  ·
                    rfl

theorem cell21_1960621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_1960621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960621 prefixEnd_1960621 := by exact prefixLift 1960621
  have htrace : WordTrace (prefixWord ++ tailWord_1960621) baseStart_1960621 baseEnd_1960621 := by
    simpa [prefixWord, tailWord_1960621, baseEnd_1960621] using wordTrace_append hprefix tailTrace_1960621
  have hstable : (prefixWord ++ tailWord_1960621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960621).length < 2 ^ (prefixWord ++ tailWord_1960621).sum := by decide
  have hdescent : baseEnd_1960621 < baseStart_1960621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960652 : List Nat := [2, 2, 1, 5, 1, 2, 3, 1, 4]
def baseStart_1960652 : Nat := 118140960795 + 1960652 * 2 ^ 59
def prefixEnd_1960652 : Nat := 4983230072969 + 3 ^ 40 * 1960652 * 2
def baseEnd_1960652 : Nat := 447447498755185854992503

theorem tailTrace_1960652 : CollatzResearch.WordTrace tailWord_1960652 prefixEnd_1960652 447447498755185854992503 := by
  unfold tailWord_1960652
  simp only [CollatzResearch.WordTrace]
  refine ⟨35755426646450065773862105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47673902195266754365149473 35755426646450065773862105)
  ·
    refine ⟨26816569984837549330396579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35755426646450065773862105 26816569984837549330396579)
    ·
      refine ⟨40224854977256323995594869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26816569984837549330396579 40224854977256323995594869)
      ·
        refine ⟨3771080154117780374587019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40224854977256323995594869 3771080154117780374587019)
        ·
          refine ⟨5656620231176670561880529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3771080154117780374587019 5656620231176670561880529)
          ·
            refine ⟨4242465173382502921410397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5656620231176670561880529 4242465173382502921410397)
            ·
              refine ⟨1590924440018438595528899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4242465173382502921410397 1590924440018438595528899)
              ·
                refine ⟨2386386660027657893293349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1590924440018438595528899 2386386660027657893293349)
                ·
                  refine ⟨447447498755185854992503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2386386660027657893293349 447447498755185854992503)
                  ·
                    rfl

theorem cell21_1960652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_1960652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960652 prefixEnd_1960652 := by exact prefixLift 1960652
  have htrace : WordTrace (prefixWord ++ tailWord_1960652) baseStart_1960652 baseEnd_1960652 := by
    simpa [prefixWord, tailWord_1960652, baseEnd_1960652] using wordTrace_append hprefix tailTrace_1960652
  have hstable : (prefixWord ++ tailWord_1960652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960652).length < 2 ^ (prefixWord ++ tailWord_1960652).sum := by decide
  have hdescent : baseEnd_1960652 < baseStart_1960652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960663 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 5]
def baseStart_1960663 : Nat := 118140960795 + 1960663 * 2 ^ 59
def prefixEnd_1960663 : Nat := 4983230072969 + 3 ^ 40 * 1960663 * 2
def baseEnd_1960663 : Nat := 447450009105052280309147

theorem tailTrace_1960663 : CollatzResearch.WordTrace tailWord_1960663 prefixEnd_1960663 447450009105052280309147 := by
  unfold tailWord_1960663
  simp only [CollatzResearch.WordTrace]
  refine ⟨71511254495860280426374643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47674169663906853617583095 71511254495860280426374643)
  ·
    refine ⟨107266881743790420639561965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71511254495860280426374643 107266881743790420639561965)
    ·
      refine ⟨40225080653921407739835737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107266881743790420639561965 40225080653921407739835737)
      ·
        refine ⟨30168810490441055804876803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40225080653921407739835737 30168810490441055804876803)
        ·
          refine ⟨45253215735661583707315205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30168810490441055804876803 45253215735661583707315205)
          ·
            refine ⟨8484977950436546945121601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45253215735661583707315205 8484977950436546945121601)
            ·
              refine ⟨6363733462827410208841201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8484977950436546945121601 6363733462827410208841201)
              ·
                refine ⟨4772800097120557656630901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6363733462827410208841201 4772800097120557656630901)
                ·
                  refine ⟨447450009105052280309147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4772800097120557656630901 447450009105052280309147)
                  ·
                    rfl

theorem cell21_1960663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 5].length) (baseStart_1960663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960663 prefixEnd_1960663 := by exact prefixLift 1960663
  have htrace : WordTrace (prefixWord ++ tailWord_1960663) baseStart_1960663 baseEnd_1960663 := by
    simpa [prefixWord, tailWord_1960663, baseEnd_1960663] using wordTrace_append hprefix tailTrace_1960663
  have hstable : (prefixWord ++ tailWord_1960663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960663).length < 2 ^ (prefixWord ++ tailWord_1960663).sum := by decide
  have hdescent : baseEnd_1960663 < baseStart_1960663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960694 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_1960694 : Nat := 118140960795 + 1960694 * 2 ^ 59
def prefixEnd_1960694 : Nat := 4983230072969 + 3 ^ 40 * 1960694 * 2
def baseEnd_1960694 : Nat := 447457083727403115292417

theorem tailTrace_1960694 : CollatzResearch.WordTrace tailWord_1960694 prefixEnd_1960694 447457083727403115292417 := by
  unfold tailWord_1960694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4469524072421748295047071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47674923439165315147168757 4469524072421748295047071)
  ·
    refine ⟨6704286108632622442570607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4469524072421748295047071 6704286108632622442570607)
    ·
      refine ⟨10056429162948933663855911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6704286108632622442570607 10056429162948933663855911)
      ·
        refine ⟨15084643744423400495783867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10056429162948933663855911 15084643744423400495783867)
        ·
          refine ⟨22626965616635100743675801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15084643744423400495783867 22626965616635100743675801)
          ·
            refine ⟨16970224212476325557756851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22626965616635100743675801 16970224212476325557756851)
            ·
              refine ⟨25455336318714488336635277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16970224212476325557756851 25455336318714488336635277)
              ·
                refine ⟨9545751119517933126238229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25455336318714488336635277 9545751119517933126238229)
                ·
                  refine ⟨447457083727403115292417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9545751119517933126238229 447457083727403115292417)
                  ·
                    rfl

theorem cell21_1960694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_1960694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960694 prefixEnd_1960694 := by exact prefixLift 1960694
  have htrace : WordTrace (prefixWord ++ tailWord_1960694) baseStart_1960694 baseEnd_1960694 := by
    simpa [prefixWord, tailWord_1960694, baseEnd_1960694] using wordTrace_append hprefix tailTrace_1960694
  have hstable : (prefixWord ++ tailWord_1960694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960694).length < 2 ^ (prefixWord ++ tailWord_1960694).sum := by decide
  have hdescent : baseEnd_1960694 < baseStart_1960694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960711 : List Nat := [1, 1, 4, 4, 1, 2, 1, 3, 4]
def baseStart_1960711 : Nat := 118140960795 + 1960711 * 2 ^ 59
def prefixEnd_1960711 : Nat := 4983230072969 + 3 ^ 40 * 1960711 * 2
def baseEnd_1960711 : Nat := 447460963359014863509049

theorem tailTrace_1960711 : CollatzResearch.WordTrace tailWord_1960711 prefixEnd_1960711 447460963359014863509049 := by
  unfold tailWord_1960711
  simp only [CollatzResearch.WordTrace]
  refine ⟨71513005199686384624121987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47675336799790923082747991 71513005199686384624121987)
  ·
    refine ⟨107269507799529576936182981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71513005199686384624121987 107269507799529576936182981)
    ·
      refine ⟨20113032712411795675534309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107269507799529576936182981 20113032712411795675534309)
      ·
        refine ⟨3771193633577211689162683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20113032712411795675534309 3771193633577211689162683)
        ·
          refine ⟨5656790450365817533744025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3771193633577211689162683 5656790450365817533744025)
          ·
            refine ⟨4242592837774363150308019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5656790450365817533744025 4242592837774363150308019)
            ·
              refine ⟨6363889256661544725462029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4242592837774363150308019 6363889256661544725462029)
              ·
                refine ⟨2386458471248079272048261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6363889256661544725462029 2386458471248079272048261)
                ·
                  refine ⟨447460963359014863509049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2386458471248079272048261 447460963359014863509049)
                  ·
                    rfl

theorem cell21_1960711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 4].length) (baseStart_1960711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960711 prefixEnd_1960711 := by exact prefixLift 1960711
  have htrace : WordTrace (prefixWord ++ tailWord_1960711) baseStart_1960711 baseEnd_1960711 := by
    simpa [prefixWord, tailWord_1960711, baseEnd_1960711] using wordTrace_append hprefix tailTrace_1960711
  have hstable : (prefixWord ++ tailWord_1960711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960711).length < 2 ^ (prefixWord ++ tailWord_1960711).sum := by decide
  have hdescent : baseEnd_1960711 < baseStart_1960711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960866 : List Nat := [3, 3, 1, 2, 2, 2, 3, 2, 3]
def baseStart_1960866 : Nat := 118140960795 + 1960866 * 2 ^ 59
def prefixEnd_1960866 : Nat := 4983230072969 + 3 ^ 40 * 1960866 * 2
def baseEnd_1960866 : Nat := 447496336470769038425399

theorem tailTrace_1960866 : CollatzResearch.WordTrace tailWord_1960866 prefixEnd_1960866 447496336470769038425399 := by
  unfold tailWord_1960866
  simp only [CollatzResearch.WordTrace]
  refine ⟨17879664628531211524003613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47679105676083230730676301 17879664628531211524003613)
  ·
    refine ⟨6704874235699204321501355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17879664628531211524003613 6704874235699204321501355)
    ·
      refine ⟨10057311353548806482252033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6704874235699204321501355 10057311353548806482252033)
      ·
        refine ⟨7542983515161604861689025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10057311353548806482252033 7542983515161604861689025)
        ·
          refine ⟨5657237636371203646266769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7542983515161604861689025 5657237636371203646266769)
          ·
            refine ⟨4242928227278402734700077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5657237636371203646266769 4242928227278402734700077)
            ·
              refine ⟨1591098085229401025512529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4242928227278402734700077 1591098085229401025512529)
              ·
                refine ⟨1193323563922050769134397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1591098085229401025512529 1193323563922050769134397)
                ·
                  refine ⟨447496336470769038425399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193323563922050769134397 447496336470769038425399)
                  ·
                    rfl

theorem cell21_1960866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_1960866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960866 prefixEnd_1960866 := by exact prefixLift 1960866
  have htrace : WordTrace (prefixWord ++ tailWord_1960866) baseStart_1960866 baseEnd_1960866 := by
    simpa [prefixWord, tailWord_1960866, baseEnd_1960866] using wordTrace_append hprefix tailTrace_1960866
  have hstable : (prefixWord ++ tailWord_1960866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960866).length < 2 ^ (prefixWord ++ tailWord_1960866).sum := by decide
  have hdescent : baseEnd_1960866 < baseStart_1960866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960908 : List Nat := [2, 2, 1, 4, 1, 1, 2, 5, 3]
def baseStart_1960908 : Nat := 118140960795 + 1960908 * 2 ^ 59
def prefixEnd_1960908 : Nat := 4983230072969 + 3 ^ 40 * 1960908 * 2
def baseEnd_1960908 : Nat := 447505921442986298725313

theorem tailTrace_1960908 : CollatzResearch.WordTrace tailWord_1960908 prefixEnd_1960908 447505921442986298725313 := by
  unfold tailWord_1960908
  simp only [CollatzResearch.WordTrace]
  refine ⟨35760095189986343634521689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47680126919981791512695585 35760095189986343634521689)
  ·
    refine ⟨26820071392489757725891267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35760095189986343634521689 26820071392489757725891267)
    ·
      refine ⟨40230107088734636588836901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26820071392489757725891267 40230107088734636588836901)
      ·
        refine ⟨7543145079137744360406919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40230107088734636588836901 7543145079137744360406919)
        ·
          refine ⟨11314717618706616540610379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7543145079137744360406919 11314717618706616540610379)
          ·
            refine ⟨16972076428059924810915569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11314717618706616540610379 16972076428059924810915569)
            ·
              refine ⟨12729057321044943608186677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16972076428059924810915569 12729057321044943608186677)
              ·
                refine ⟨1193349123847963463267501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12729057321044943608186677 1193349123847963463267501)
                ·
                  refine ⟨447505921442986298725313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193349123847963463267501 447505921442986298725313)
                  ·
                    rfl

theorem cell21_1960908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_1960908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960908 prefixEnd_1960908 := by exact prefixLift 1960908
  have htrace : WordTrace (prefixWord ++ tailWord_1960908) baseStart_1960908 baseEnd_1960908 := by
    simpa [prefixWord, tailWord_1960908, baseEnd_1960908] using wordTrace_append hprefix tailTrace_1960908
  have hstable : (prefixWord ++ tailWord_1960908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960908).length < 2 ^ (prefixWord ++ tailWord_1960908).sum := by decide
  have hdescent : baseEnd_1960908 < baseStart_1960908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960922 : List Nat := [3, 1, 1, 2, 4, 1, 1, 4, 4]
def baseStart_1960922 : Nat := 118140960795 + 1960922 * 2 ^ 59
def prefixEnd_1960922 : Nat := 4983230072969 + 3 ^ 40 * 1960922 * 2
def baseEnd_1960922 : Nat := 447509116433725385491951

theorem tailTrace_1960922 : CollatzResearch.WordTrace tailWord_1960922 prefixEnd_1960922 447509116433725385491951 := by
  unfold tailWord_1960922
  simp only [CollatzResearch.WordTrace]
  refine ⟨17880175250480491915013255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47680467334614645106702013 17880175250480491915013255)
  ·
    refine ⟨26820262875720737872519883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17880175250480491915013255 26820262875720737872519883)
    ·
      refine ⟨40230394313581106808779825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26820262875720737872519883 40230394313581106808779825)
      ·
        refine ⟨30172795735185830106584869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40230394313581106808779825 30172795735185830106584869)
        ·
          refine ⟨5657399200347343144984663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30172795735185830106584869 5657399200347343144984663)
          ·
            refine ⟨8486098800521014717476995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5657399200347343144984663 8486098800521014717476995)
            ·
              refine ⟨12729148200781522076215493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8486098800521014717476995 12729148200781522076215493)
              ·
                refine ⟨2386715287646535389290405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12729148200781522076215493 2386715287646535389290405)
                ·
                  refine ⟨447509116433725385491951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2386715287646535389290405 447509116433725385491951)
                  ·
                    rfl

theorem cell21_1960922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_1960922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960922 prefixEnd_1960922 := by exact prefixLift 1960922
  have htrace : WordTrace (prefixWord ++ tailWord_1960922) baseStart_1960922 baseEnd_1960922 := by
    simpa [prefixWord, tailWord_1960922, baseEnd_1960922] using wordTrace_append hprefix tailTrace_1960922
  have hstable : (prefixWord ++ tailWord_1960922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960922).length < 2 ^ (prefixWord ++ tailWord_1960922).sum := by decide
  have hdescent : baseEnd_1960922 < baseStart_1960922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960925 : List Nat := [1, 4, 3, 1, 2, 2, 1, 4, 3]
def baseStart_1960925 : Nat := 118140960795 + 1960925 * 2 ^ 59
def prefixEnd_1960925 : Nat := 4983230072969 + 3 ^ 40 * 1960925 * 2
def baseEnd_1960925 : Nat := 447509801074598046941945

theorem tailTrace_1960925 : CollatzResearch.WordTrace tailWord_1960925 prefixEnd_1960925 447509801074598046941945 := by
  unfold tailWord_1960925
  simp only [CollatzResearch.WordTrace]
  refine ⟨71520810420911099172412229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47680540280607399448274819 71520810420911099172412229)
  ·
    refine ⟨13410151953920831094827293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71520810420911099172412229 13410151953920831094827293)
    ·
      refine ⟨5028806982720311660560235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13410151953920831094827293 5028806982720311660560235)
      ·
        refine ⟨7543210474080467490840353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5028806982720311660560235 7543210474080467490840353)
        ·
          refine ⟨5657407855560350618130265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7543210474080467490840353 5657407855560350618130265)
          ·
            refine ⟨4243055891670262963597699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5657407855560350618130265 4243055891670262963597699)
            ·
              refine ⟨6364583837505394445396549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4243055891670262963597699 6364583837505394445396549)
              ·
                refine ⟨1193359469532261458511853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6364583837505394445396549 1193359469532261458511853)
                ·
                  refine ⟨447509801074598046941945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193359469532261458511853 447509801074598046941945)
                  ·
                    rfl

theorem cell21_1960925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_1960925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960925 prefixEnd_1960925 := by exact prefixLift 1960925
  have htrace : WordTrace (prefixWord ++ tailWord_1960925) baseStart_1960925 baseEnd_1960925 := by
    simpa [prefixWord, tailWord_1960925, baseEnd_1960925] using wordTrace_append hprefix tailTrace_1960925
  have hstable : (prefixWord ++ tailWord_1960925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960925).length < 2 ^ (prefixWord ++ tailWord_1960925).sum := by decide
  have hdescent : baseEnd_1960925 < baseStart_1960925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960936 : List Nat := [2, 1, 4, 1, 1, 1, 5, 6]
def baseStart_1960936 : Nat := 118140960795 + 1960936 * 2 ^ 59
def prefixEnd_1960936 : Nat := 4983230072969 + 3 ^ 40 * 1960936 * 2
def baseEnd_1960936 : Nat := 149170770474821490752863

theorem tailTrace_1960936 : CollatzResearch.WordTrace tailWord_1960936 prefixEnd_1960936 149170770474821490752863 := by
  unfold tailWord_1960936
  simp only [CollatzResearch.WordTrace]
  refine ⟨35760605811935624025531331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47680807749247498700708441 35760605811935624025531331)
  ·
    refine ⟨53640908717903436038296997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35760605811935624025531331 53640908717903436038296997)
    ·
      refine ⟨10057670384606894257180687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53640908717903436038296997 10057670384606894257180687)
      ·
        refine ⟨15086505576910341385771031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10057670384606894257180687 15086505576910341385771031)
        ·
          refine ⟨22629758365365512078656547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15086505576910341385771031 22629758365365512078656547)
          ·
            refine ⟨33944637548048268117984821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22629758365365512078656547 33944637548048268117984821)
            ·
              refine ⟨3182309770129525136061077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33944637548048268117984821 3182309770129525136061077)
              ·
                refine ⟨149170770474821490752863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3182309770129525136061077 149170770474821490752863)
                ·
                  rfl

theorem cell21_1960936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 6].length) (baseStart_1960936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960936 prefixEnd_1960936 := by exact prefixLift 1960936
  have htrace : WordTrace (prefixWord ++ tailWord_1960936) baseStart_1960936 baseEnd_1960936 := by
    simpa [prefixWord, tailWord_1960936, baseEnd_1960936] using wordTrace_append hprefix tailTrace_1960936
  have hstable : (prefixWord ++ tailWord_1960936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960936).length < 2 ^ (prefixWord ++ tailWord_1960936).sum := by decide
  have hdescent : baseEnd_1960936 < baseStart_1960936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960984 : List Nat := [2, 1, 2, 3, 2, 2, 2, 4, 3]
def baseStart_1960984 : Nat := 118140960795 + 1960984 * 2 ^ 59
def prefixEnd_1960984 : Nat := 4983230072969 + 3 ^ 40 * 1960984 * 2
def baseEnd_1960984 : Nat := 447523265678427055458491

theorem tailTrace_1960984 : CollatzResearch.WordTrace tailWord_1960984 prefixEnd_1960984 447523265678427055458491 := by
  unfold tailWord_1960984
  simp only [CollatzResearch.WordTrace]
  refine ⟨35761481163848676124405003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47681974885131568165873337 35761481163848676124405003)
  ·
    refine ⟨53642221745773014186607505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35761481163848676124405003 53642221745773014186607505)
    ·
      refine ⟨40231666309329760639955629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53642221745773014186607505 40231666309329760639955629)
      ·
        refine ⟨15086874865998660239983361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40231666309329760639955629 15086874865998660239983361)
        ·
          refine ⟨11315156149498995179987521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15086874865998660239983361 11315156149498995179987521)
          ·
            refine ⟨8486367112124246384990641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11315156149498995179987521 8486367112124246384990641)
            ·
              refine ⟨6364775334093184788742981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8486367112124246384990641 6364775334093184788742981)
              ·
                refine ⟨1193395375142472147889309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6364775334093184788742981 1193395375142472147889309)
                ·
                  refine ⟨447523265678427055458491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193395375142472147889309 447523265678427055458491)
                  ·
                    rfl

theorem cell21_1960984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 3].length) (baseStart_1960984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1960984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1960984 prefixEnd_1960984 := by exact prefixLift 1960984
  have htrace : WordTrace (prefixWord ++ tailWord_1960984) baseStart_1960984 baseEnd_1960984 := by
    simpa [prefixWord, tailWord_1960984, baseEnd_1960984] using wordTrace_append hprefix tailTrace_1960984
  have hstable : (prefixWord ++ tailWord_1960984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960984).length < 2 ^ (prefixWord ++ tailWord_1960984).sum := by decide
  have hdescent : baseEnd_1960984 < baseStart_1960984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961071 : List Nat := [1, 1, 2, 1, 3, 3, 1, 9]
def baseStart_1961071 : Nat := 118140960795 + 1961071 * 2 ^ 59
def prefixEnd_1961071 : Nat := 4983230072969 + 3 ^ 40 * 1961071 * 2
def baseEnd_1961071 : Nat := 149181040087911412502771

theorem tailTrace_1961071 : CollatzResearch.WordTrace tailWord_1961071 prefixEnd_1961071 149181040087911412502771 := by
  unfold tailWord_1961071
  simp only [CollatzResearch.WordTrace]
  refine ⟨71526135478382166107227067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47684090318921444071484711 71526135478382166107227067)
  ·
    refine ⟨107289203217573249160840601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71526135478382166107227067 107289203217573249160840601)
    ·
      refine ⟨80466902413179936870630451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107289203217573249160840601 80466902413179936870630451)
      ·
        refine ⟨120700353619769905305945677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80466902413179936870630451 120700353619769905305945677)
        ·
          refine ⟨45262632607413714489729629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120700353619769905305945677 45262632607413714489729629)
          ·
            refine ⟨16973487227780142933648611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45262632607413714489729629 16973487227780142933648611)
            ·
              refine ⟨25460230841670214400472917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16973487227780142933648611 25460230841670214400472917)
              ·
                refine ⟨149181040087911412502771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25460230841670214400472917 149181040087911412502771)
                ·
                  rfl

theorem cell21_1961071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 9].length) (baseStart_1961071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961071 prefixEnd_1961071 := by exact prefixLift 1961071
  have htrace : WordTrace (prefixWord ++ tailWord_1961071) baseStart_1961071 baseEnd_1961071 := by
    simpa [prefixWord, tailWord_1961071, baseEnd_1961071] using wordTrace_append hprefix tailTrace_1961071
  have hstable : (prefixWord ++ tailWord_1961071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961071).length < 2 ^ (prefixWord ++ tailWord_1961071).sum := by decide
  have hdescent : baseEnd_1961071 < baseStart_1961071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961122 : List Nat := [3, 3, 1, 3, 2, 1, 3, 5]
def baseStart_1961122 : Nat := 118140960795 + 1961122 * 2 ^ 59
def prefixEnd_1961122 : Nat := 4983230072969 + 3 ^ 40 * 1961122 * 2
def baseEnd_1961122 : Nat := 149184919719523160719403

theorem tailTrace_1961122 : CollatzResearch.WordTrace tailWord_1961122 prefixEnd_1961122 149184919719523160719403 := by
  unfold tailWord_1961122
  simp only [CollatzResearch.WordTrace]
  refine ⟨17881998900299350454333405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47685330400798267878222413 17881998900299350454333405)
  ·
    refine ⟨6705749587612256420375027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17881998900299350454333405 6705749587612256420375027)
    ·
      refine ⟨10058624381418384630562541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6705749587612256420375027 10058624381418384630562541)
      ·
        refine ⟨3771984143031894236460953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10058624381418384630562541 3771984143031894236460953)
        ·
          refine ⟨2828988107273920677345715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3771984143031894236460953 2828988107273920677345715)
          ·
            refine ⟨4243482160910881016018573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2828988107273920677345715 4243482160910881016018573)
            ·
              refine ⟨1591305810341580381006965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4243482160910881016018573 1591305810341580381006965)
              ·
                refine ⟨149184919719523160719403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1591305810341580381006965 149184919719523160719403)
                ·
                  rfl

theorem cell21_1961122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_1961122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961122 prefixEnd_1961122 := by exact prefixLift 1961122
  have htrace : WordTrace (prefixWord ++ tailWord_1961122) baseStart_1961122 baseEnd_1961122 := by
    simpa [prefixWord, tailWord_1961122, baseEnd_1961122] using wordTrace_append hprefix tailTrace_1961122
  have hstable : (prefixWord ++ tailWord_1961122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961122).length < 2 ^ (prefixWord ++ tailWord_1961122).sum := by decide
  have hdescent : baseEnd_1961122 < baseStart_1961122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961142 : List Nat := [5, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_1961142 : Nat := 118140960795 + 1961142 * 2 ^ 59
def prefixEnd_1961142 : Nat := 4983230072969 + 3 ^ 40 * 1961142 * 2
def baseEnd_1961142 : Nat := 447559323431053891824835

theorem tailTrace_1961142 : CollatzResearch.WordTrace tailWord_1961142 prefixEnd_1961142 447559323431053891824835 := by
  unfold tailWord_1961142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4470545316320309077066355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47685816707416630155374453 4470545316320309077066355)
  ·
    refine ⟨6705817974480463615599533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4470545316320309077066355 6705817974480463615599533)
    ·
      refine ⟨2514681740430173855849825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6705817974480463615599533 2514681740430173855849825)
      ·
        refine ⟨1886011305322630391887369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2514681740430173855849825 1886011305322630391887369)
        ·
          refine ⟨1414508478991972793915527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1886011305322630391887369 1414508478991972793915527)
          ·
            refine ⟨2121762718487959190873291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1414508478991972793915527 2121762718487959190873291)
            ·
              refine ⟨3182644077731938786309937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121762718487959190873291 3182644077731938786309937)
              ·
                refine ⟨2386983058298954089732453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3182644077731938786309937 2386983058298954089732453)
                ·
                  refine ⟨447559323431053891824835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2386983058298954089732453 447559323431053891824835)
                  ·
                    rfl

theorem cell21_1961142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_1961142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961142 prefixEnd_1961142 := by exact prefixLift 1961142
  have htrace : WordTrace (prefixWord ++ tailWord_1961142) baseStart_1961142 baseEnd_1961142 := by
    simpa [prefixWord, tailWord_1961142, baseEnd_1961142] using wordTrace_append hprefix tailTrace_1961142
  have hstable : (prefixWord ++ tailWord_1961142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961142).length < 2 ^ (prefixWord ++ tailWord_1961142).sum := by decide
  have hdescent : baseEnd_1961142 < baseStart_1961142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961150 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_1961150 : Nat := 118140960795 + 1961150 * 2 ^ 59
def prefixEnd_1961150 : Nat := 4983230072969 + 3 ^ 40 * 1961150 * 2
def baseEnd_1961150 : Nat := 447561149140047655691485

theorem tailTrace_1961150 : CollatzResearch.WordTrace tailWord_1961150 prefixEnd_1961150 447561149140047655691485 := by
  unfold tailWord_1961150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8941127105636995324919113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47686011230063975066235269 8941127105636995324919113)
  ·
    refine ⟨6705845329227746493689335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8941127105636995324919113 6705845329227746493689335)
    ·
      refine ⟨10058767993841619740534003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6705845329227746493689335 10058767993841619740534003)
      ·
        refine ⟨15088151990762429610801005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10058767993841619740534003 15088151990762429610801005)
        ·
          refine ⟨5658056996535911104050377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15088151990762429610801005 5658056996535911104050377)
          ·
            refine ⟨4243542747401933328037783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5658056996535911104050377 4243542747401933328037783)
            ·
              refine ⟨6365314121102899992056675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4243542747401933328037783 6365314121102899992056675)
              ·
                refine ⟨9547971181654349988085013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6365314121102899992056675 9547971181654349988085013)
                ·
                  refine ⟨447561149140047655691485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9547971181654349988085013 447561149140047655691485)
                  ·
                    rfl

theorem cell21_1961150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_1961150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961150 prefixEnd_1961150 := by exact prefixLift 1961150
  have htrace : WordTrace (prefixWord ++ tailWord_1961150) baseStart_1961150 baseEnd_1961150 := by
    simpa [prefixWord, tailWord_1961150, baseEnd_1961150] using wordTrace_append hprefix tailTrace_1961150
  have hstable : (prefixWord ++ tailWord_1961150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961150).length < 2 ^ (prefixWord ++ tailWord_1961150).sum := by decide
  have hdescent : baseEnd_1961150 < baseStart_1961150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961153 : List Nat := [1, 2, 6, 1, 1, 1, 2, 4, 3]
def baseStart_1961153 : Nat := 118140960795 + 1961153 * 2 ^ 59
def prefixEnd_1961153 : Nat := 4983230072969 + 3 ^ 40 * 1961153 * 2
def baseEnd_1961153 : Nat := 447561833780920317141479

theorem tailTrace_1961153 : CollatzResearch.WordTrace tailWord_1961153 prefixEnd_1961153 447561833780920317141479 := by
  unfold tailWord_1961153
  simp only [CollatzResearch.WordTrace]
  refine ⟨71529126264085094111712113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47686084176056729407808075 71529126264085094111712113)
  ·
    refine ⟨53646844698063820583784085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71529126264085094111712113 53646844698063820583784085)
    ·
      refine ⟨2514695845221741589864879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53646844698063820583784085 2514695845221741589864879)
      ·
        refine ⟨3772043767832612384797319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2514695845221741589864879 3772043767832612384797319)
        ·
          refine ⟨5658065651748918577195979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3772043767832612384797319 5658065651748918577195979)
          ·
            refine ⟨8487098477623377865793969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5658065651748918577195979 8487098477623377865793969)
            ·
              refine ⟨6365323858217533399345477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8487098477623377865793969 6365323858217533399345477)
              ·
                refine ⟨1193498223415787512377277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6365323858217533399345477 1193498223415787512377277)
                ·
                  refine ⟨447561833780920317141479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193498223415787512377277 447561833780920317141479)
                  ·
                    rfl

theorem cell21_1961153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 3].length) (baseStart_1961153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961153 prefixEnd_1961153 := by exact prefixLift 1961153
  have htrace : WordTrace (prefixWord ++ tailWord_1961153) baseStart_1961153 baseEnd_1961153 := by
    simpa [prefixWord, tailWord_1961153, baseEnd_1961153] using wordTrace_append hprefix tailTrace_1961153
  have hstable : (prefixWord ++ tailWord_1961153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961153).length < 2 ^ (prefixWord ++ tailWord_1961153).sum := by decide
  have hdescent : baseEnd_1961153 < baseStart_1961153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961181 : List Nat := [1, 4, 3, 2, 2, 1, 1, 7]
def baseStart_1961181 : Nat := 118140960795 + 1961181 * 2 ^ 59
def prefixEnd_1961181 : Nat := 4983230072969 + 3 ^ 40 * 1961181 * 2
def baseEnd_1961181 : Nat := 149189407920799496891585

theorem tailTrace_1961181 : CollatzResearch.WordTrace tailWord_1961181 prefixEnd_1961181 149189407920799496891585 := by
  unfold tailWord_1961181
  simp only [CollatzResearch.WordTrace]
  refine ⟨71530147507983654893731397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47686765005322436595820931 71530147507983654893731397)
  ·
    refine ⟨13411902657746935292574637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71530147507983654893731397 13411902657746935292574637)
    ·
      refine ⟨5029463496655100734715489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13411902657746935292574637 5029463496655100734715489)
      ·
        refine ⟨3772097622491325551036617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5029463496655100734715489 3772097622491325551036617)
        ·
          refine ⟨2829073216868494163277463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3772097622491325551036617 2829073216868494163277463)
          ·
            refine ⟨4243609825302741244916195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829073216868494163277463 4243609825302741244916195)
            ·
              refine ⟨6365414737954111867374293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4243609825302741244916195 6365414737954111867374293)
              ·
                refine ⟨149189407920799496891585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6365414737954111867374293 149189407920799496891585)
                ·
                  rfl

theorem cell21_1961181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 7].length) (baseStart_1961181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961181 prefixEnd_1961181 := by exact prefixLift 1961181
  have htrace : WordTrace (prefixWord ++ tailWord_1961181) baseStart_1961181 baseEnd_1961181 := by
    simpa [prefixWord, tailWord_1961181, baseEnd_1961181] using wordTrace_append hprefix tailTrace_1961181
  have hstable : (prefixWord ++ tailWord_1961181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961181).length < 2 ^ (prefixWord ++ tailWord_1961181).sum := by decide
  have hdescent : baseEnd_1961181 < baseStart_1961181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961204 : List Nat := [2, 6, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1961204 : Nat := 118140960795 + 1961204 * 2 ^ 59
def prefixEnd_1961204 : Nat := 4983230072969 + 3 ^ 40 * 1961204 * 2
def baseEnd_1961204 : Nat := 447573472675755561791375

theorem tailTrace_1961204 : CollatzResearch.WordTrace tailWord_1961204 prefixEnd_1961204 447573472675755561791375 := by
  unfold tailWord_1961204
  simp only [CollatzResearch.WordTrace]
  refine ⟨35765493193450164910909333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47687324257933553214545777 35765493193450164910909333)
  ·
    refine ⟨1676507493442976480198875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35765493193450164910909333 1676507493442976480198875)
    ·
      refine ⟨2514761240164464720298313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1676507493442976480198875 2514761240164464720298313)
      ·
        refine ⟨1886070930123348540223735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2514761240164464720298313 1886070930123348540223735)
        ·
          refine ⟨2829106395185022810335603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886070930123348540223735 2829106395185022810335603)
          ·
            refine ⟨4243659592777534215503405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829106395185022810335603 4243659592777534215503405)
            ·
              refine ⟨1591372347291575330813777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4243659592777534215503405 1591372347291575330813777)
              ·
                refine ⟨1193529260468681498110333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1591372347291575330813777 1193529260468681498110333)
                ·
                  refine ⟨447573472675755561791375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193529260468681498110333 447573472675755561791375)
                  ·
                    rfl

theorem cell21_1961204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1961204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961204 prefixEnd_1961204 := by exact prefixLift 1961204
  have htrace : WordTrace (prefixWord ++ tailWord_1961204) baseStart_1961204 baseEnd_1961204 := by
    simpa [prefixWord, tailWord_1961204, baseEnd_1961204] using wordTrace_append hprefix tailTrace_1961204
  have hstable : (prefixWord ++ tailWord_1961204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961204).length < 2 ^ (prefixWord ++ tailWord_1961204).sum := by decide
  have hdescent : baseEnd_1961204 < baseStart_1961204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961209 : List Nat := [1, 2, 1, 3, 1, 1, 4, 4, 4]
def baseStart_1961209 : Nat := 118140960795 + 1961209 * 2 ^ 59
def prefixEnd_1961209 : Nat := 4983230072969 + 3 ^ 40 * 1961209 * 2
def baseEnd_1961209 : Nat := 447574613743876664208031

theorem tailTrace_1961209 : CollatzResearch.WordTrace tailWord_1961209 prefixEnd_1961209 447574613743876664208031 := by
  unfold tailWord_1961209
  simp only [CollatzResearch.WordTrace]
  refine ⟨71531168751882215675750681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47687445834588143783833787 71531168751882215675750681)
  ·
    refine ⟨53648376563911661756813011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71531168751882215675750681 53648376563911661756813011)
    ·
      refine ⟨80472564845867492635219517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53648376563911661756813011 80472564845867492635219517)
      ·
        refine ⟨30177211817200309738207319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80472564845867492635219517 30177211817200309738207319)
        ·
          refine ⟨45265817725800464607310979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30177211817200309738207319 45265817725800464607310979)
          ·
            refine ⟨67898726588700696910966469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45265817725800464607310979 67898726588700696910966469)
            ·
              refine ⟨12731011235381380670806213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67898726588700696910966469 12731011235381380670806213)
              ·
                refine ⟨2387064606634008875776165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12731011235381380670806213 2387064606634008875776165)
                ·
                  refine ⟨447574613743876664208031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2387064606634008875776165 447574613743876664208031)
                  ·
                    rfl

theorem cell21_1961209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_1961209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961209 prefixEnd_1961209 := by exact prefixLift 1961209
  have htrace : WordTrace (prefixWord ++ tailWord_1961209) baseStart_1961209 baseEnd_1961209 := by
    simpa [prefixWord, tailWord_1961209, baseEnd_1961209] using wordTrace_append hprefix tailTrace_1961209
  have hstable : (prefixWord ++ tailWord_1961209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961209).length < 2 ^ (prefixWord ++ tailWord_1961209).sum := by decide
  have hdescent : baseEnd_1961209 < baseStart_1961209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961212 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 5]
def baseStart_1961212 : Nat := 118140960795 + 1961212 * 2 ^ 59
def prefixEnd_1961212 : Nat := 4983230072969 + 3 ^ 40 * 1961212 * 2
def baseEnd_1961212 : Nat := 447575298384749325658025

theorem tailTrace_1961212 : CollatzResearch.WordTrace tailWord_1961212 prefixEnd_1961212 447575298384749325658025 := by
  unfold tailWord_1961212
  simp only [CollatzResearch.WordTrace]
  refine ⟨35765639085435673594054945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47687518780580898125406593 35765639085435673594054945)
  ·
    refine ⟨26824229314076755195541209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35765639085435673594054945 26824229314076755195541209)
    ·
      refine ⟨20118171985557566396655907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26824229314076755195541209 20118171985557566396655907)
      ·
        refine ⟨30177257978336349594983861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20118171985557566396655907 30177257978336349594983861)
        ·
          refine ⟨2829117935469032774529737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30177257978336349594983861 2829117935469032774529737)
          ·
            refine ⟨2121838451601774580897303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2829117935469032774529737 2121838451601774580897303)
            ·
              refine ⟨3182757677402661871345955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121838451601774580897303 3182757677402661871345955)
              ·
                refine ⟨4774136516103992807018933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3182757677402661871345955 4774136516103992807018933)
                ·
                  refine ⟨447575298384749325658025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4774136516103992807018933 447575298384749325658025)
                  ·
                    rfl

theorem cell21_1961212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_1961212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961212 prefixEnd_1961212 := by exact prefixLift 1961212
  have htrace : WordTrace (prefixWord ++ tailWord_1961212) baseStart_1961212 baseEnd_1961212 := by
    simpa [prefixWord, tailWord_1961212, baseEnd_1961212] using wordTrace_append hprefix tailTrace_1961212
  have hstable : (prefixWord ++ tailWord_1961212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961212).length < 2 ^ (prefixWord ++ tailWord_1961212).sum := by decide
  have hdescent : baseEnd_1961212 < baseStart_1961212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961319 : List Nat := [1, 1, 5, 1, 4, 2, 1, 2, 4]
def baseStart_1961319 : Nat := 118140960795 + 1961319 * 2 ^ 59
def prefixEnd_1961319 : Nat := 4983230072969 + 3 ^ 40 * 1961319 * 2
def baseEnd_1961319 : Nat := 447599717242540917374473

theorem tailTrace_1961319 : CollatzResearch.WordTrace tailWord_1961319 prefixEnd_1961319 447599717242540917374473 := by
  unfold tailWord_1961319
  simp only [CollatzResearch.WordTrace]
  refine ⟨71535180781483704462255011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47690120520989136308170007 71535180781483704462255011)
  ·
    refine ⟨107302771172225556693382517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71535180781483704462255011 107302771172225556693382517)
    ·
      refine ⟨10059634797396145940004611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107302771172225556693382517 10059634797396145940004611)
      ·
        refine ⟨15089452196094218910006917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10059634797396145940004611 15089452196094218910006917)
        ·
          refine ⟨2829272286767666045626297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15089452196094218910006917 2829272286767666045626297)
          ·
            refine ⟨2121954215075749534219723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2829272286767666045626297 2121954215075749534219723)
            ·
              refine ⟨3182931322613624301329585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121954215075749534219723 3182931322613624301329585)
              ·
                refine ⟨2387198491960218225997189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3182931322613624301329585 2387198491960218225997189)
                ·
                  refine ⟨447599717242540917374473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2387198491960218225997189 447599717242540917374473)
                  ·
                    rfl

theorem cell21_1961319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 4].length) (baseStart_1961319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961319 prefixEnd_1961319 := by exact prefixLift 1961319
  have htrace : WordTrace (prefixWord ++ tailWord_1961319) baseStart_1961319 baseEnd_1961319 := by
    simpa [prefixWord, tailWord_1961319, baseEnd_1961319] using wordTrace_append hprefix tailTrace_1961319
  have hstable : (prefixWord ++ tailWord_1961319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961319).length < 2 ^ (prefixWord ++ tailWord_1961319).sum := by decide
  have hdescent : baseEnd_1961319 < baseStart_1961319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961375 : List Nat := [1, 1, 2, 5, 1, 2, 9]
def baseStart_1961375 : Nat := 118140960795 + 1961375 * 2 ^ 59
def prefixEnd_1961375 : Nat := 4983230072969 + 3 ^ 40 * 1961375 * 2
def baseEnd_1961375 : Nat := 49734721911721918271225

theorem tailTrace_1961375 : CollatzResearch.WordTrace tailWord_1961375 prefixEnd_1961375 49734721911721918271225 := by
  unfold tailWord_1961375
  simp only [CollatzResearch.WordTrace]
  refine ⟨71537223269280826026293579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47691482179520550684195719 71537223269280826026293579)
  ·
    refine ⟨107305834903921239039440369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71537223269280826026293579 107305834903921239039440369)
    ·
      refine ⟨80479376177940929279580277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107305834903921239039440369 80479376177940929279580277)
      ·
        refine ⟨7544941516681962119960651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80479376177940929279580277 7544941516681962119960651)
        ·
          refine ⟨11317412275022943179940977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7544941516681962119960651 11317412275022943179940977)
          ·
            refine ⟨8488059206267207384955733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11317412275022943179940977 8488059206267207384955733)
            ·
              refine ⟨49734721911721918271225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8488059206267207384955733 49734721911721918271225)
              ·
                rfl

theorem cell21_1961375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 9].length) (baseStart_1961375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961375 prefixEnd_1961375 := by exact prefixLift 1961375
  have htrace : WordTrace (prefixWord ++ tailWord_1961375) baseStart_1961375 baseEnd_1961375 := by
    simpa [prefixWord, tailWord_1961375, baseEnd_1961375] using wordTrace_append hprefix tailTrace_1961375
  have hstable : (prefixWord ++ tailWord_1961375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961375).length < 2 ^ (prefixWord ++ tailWord_1961375).sum := by decide
  have hdescent : baseEnd_1961375 < baseStart_1961375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961406 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1961406 : Nat := 118140960795 + 1961406 * 2 ^ 59
def prefixEnd_1961406 : Nat := 4983230072969 + 3 ^ 40 * 1961406 * 2
def baseEnd_1961406 : Nat := 447619571827848099424295

theorem tailTrace_1961406 : CollatzResearch.WordTrace tailWord_1961406 prefixEnd_1961406 447619571827848099424295 := by
  unfold tailWord_1961406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8942294241521064790084009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47692235954779012213781381 8942294241521064790084009)
  ·
    refine ⟨6706720681140798592563007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8942294241521064790084009 6706720681140798592563007)
    ·
      refine ⟨10060081021711197888844511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6706720681140798592563007 10060081021711197888844511)
      ·
        refine ⟨15090121532566796833266767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10060081021711197888844511 15090121532566796833266767)
        ·
          refine ⟨22635182298850195249900151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15090121532566796833266767 22635182298850195249900151)
          ·
            refine ⟨33952773448275292874850227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22635182298850195249900151 33952773448275292874850227)
            ·
              refine ⟨50929160172412939312275341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33952773448275292874850227 50929160172412939312275341)
              ·
                refine ⟨19098435064654852242103253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50929160172412939312275341 19098435064654852242103253)
                ·
                  refine ⟨447619571827848099424295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19098435064654852242103253 447619571827848099424295)
                  ·
                    rfl

theorem cell21_1961406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1961406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961406 prefixEnd_1961406 := by exact prefixLift 1961406
  have htrace : WordTrace (prefixWord ++ tailWord_1961406) baseStart_1961406 baseEnd_1961406 := by
    simpa [prefixWord, tailWord_1961406, baseEnd_1961406] using wordTrace_append hprefix tailTrace_1961406
  have hstable : (prefixWord ++ tailWord_1961406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961406).length < 2 ^ (prefixWord ++ tailWord_1961406).sum := by decide
  have hdescent : baseEnd_1961406 < baseStart_1961406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961527 : List Nat := [1, 1, 3, 1, 2, 5, 1, 7]
def baseStart_1961527 : Nat := 118140960795 + 1961527 * 2 ^ 59
def prefixEnd_1961527 : Nat := 4983230072969 + 3 ^ 40 * 1961527 * 2
def baseEnd_1961527 : Nat := 149215728558792925969127

theorem tailTrace_1961527 : CollatzResearch.WordTrace tailWord_1961527 prefixEnd_1961527 149215728558792925969127 := by
  unfold tailWord_1961527
  simp only [CollatzResearch.WordTrace]
  refine ⟨71542767164730155985826835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47695178109820103990551223 71542767164730155985826835)
  ·
    refine ⟨107314150747095233978740253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71542767164730155985826835 107314150747095233978740253)
    ·
      refine ⟨40242806530160712742027595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107314150747095233978740253 40242806530160712742027595)
      ·
        refine ⟨60364209795241069113041393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40242806530160712742027595 60364209795241069113041393)
        ·
          refine ⟨45273157346430801834781045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60364209795241069113041393 45273157346430801834781045)
          ·
            refine ⟨4244358501227887672010723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45273157346430801834781045 4244358501227887672010723)
            ·
              refine ⟨6366537751841831508016085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4244358501227887672010723 6366537751841831508016085)
              ·
                refine ⟨149215728558792925969127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6366537751841831508016085 149215728558792925969127)
                ·
                  rfl

theorem cell21_1961527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 7].length) (baseStart_1961527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961527 prefixEnd_1961527 := by exact prefixLift 1961527
  have htrace : WordTrace (prefixWord ++ tailWord_1961527) baseStart_1961527 baseEnd_1961527 := by
    simpa [prefixWord, tailWord_1961527, baseEnd_1961527] using wordTrace_append hprefix tailTrace_1961527
  have hstable : (prefixWord ++ tailWord_1961527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961527).length < 2 ^ (prefixWord ++ tailWord_1961527).sum := by decide
  have hdescent : baseEnd_1961527 < baseStart_1961527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961533 : List Nat := [1, 4, 1, 3, 3, 2, 1, 3, 3]
def baseStart_1961533 : Nat := 118140960795 + 1961533 * 2 ^ 59
def prefixEnd_1961533 : Nat := 4983230072969 + 3 ^ 40 * 1961533 * 2
def baseEnd_1961533 : Nat := 447648554958124100807369

theorem tailTrace_1961533 : CollatzResearch.WordTrace tailWord_1961533 prefixEnd_1961533 447648554958124100807369 := by
  unfold tailWord_1961533
  simp only [CollatzResearch.WordTrace]
  refine ⟨71542986002708419010545253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47695324001805612673696835 71542986002708419010545253)
  ·
    refine ⟨13414309875507828564477235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71542986002708419010545253 13414309875507828564477235)
    ·
      refine ⟨20121464813261742846715853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13414309875507828564477235 20121464813261742846715853)
      ·
        refine ⟨7545549304973153567518445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20121464813261742846715853 7545549304973153567518445)
        ·
          refine ⟨2829580989364932587819417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7545549304973153567518445 2829580989364932587819417)
          ·
            refine ⟨2122185742023699440864563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2829580989364932587819417 2122185742023699440864563)
            ·
              refine ⟨3183278613035549161296845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122185742023699440864563 3183278613035549161296845)
              ·
                refine ⟨1193729479888330935486317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3183278613035549161296845 1193729479888330935486317)
                ·
                  refine ⟨447648554958124100807369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193729479888330935486317 447648554958124100807369)
                  ·
                    rfl

theorem cell21_1961533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_1961533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961533 prefixEnd_1961533 := by exact prefixLift 1961533
  have htrace : WordTrace (prefixWord ++ tailWord_1961533) baseStart_1961533 baseEnd_1961533 := by
    simpa [prefixWord, tailWord_1961533, baseEnd_1961533] using wordTrace_append hprefix tailTrace_1961533
  have hstable : (prefixWord ++ tailWord_1961533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961533).length < 2 ^ (prefixWord ++ tailWord_1961533).sum := by decide
  have hdescent : baseEnd_1961533 < baseStart_1961533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961651 : List Nat := [1, 1, 1, 2, 3, 3, 4, 3, 3]
def baseStart_1961651 : Nat := 118140960795 + 1961651 * 2 ^ 59
def prefixEnd_1961651 : Nat := 4983230072969 + 3 ^ 40 * 1961651 * 2
def baseEnd_1961651 : Nat := 447675484165782117840461

theorem tailTrace_1961651 : CollatzResearch.WordTrace tailWord_1961651 prefixEnd_1961651 447675484165782117840461 := by
  unfold tailWord_1961651
  simp only [CollatzResearch.WordTrace]
  refine ⟨71547289816280925163340807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47698193210853950108893871 71547289816280925163340807)
  ·
    refine ⟨107320934724421387745011211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71547289816280925163340807 107320934724421387745011211)
    ·
      refine ⟨160981402086632081617516817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107320934724421387745011211 160981402086632081617516817)
      ·
        refine ⟨120736051564974061213137613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160981402086632081617516817 120736051564974061213137613)
        ·
          refine ⟨45276019336865272954926605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120736051564974061213137613 45276019336865272954926605)
          ·
            refine ⟨16978507251324477358097477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45276019336865272954926605 16978507251324477358097477)
            ·
              refine ⟨3183470109623339504643277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16978507251324477358097477 3183470109623339504643277)
              ·
                refine ⟨1193801291108752314241229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3183470109623339504643277 1193801291108752314241229)
                ·
                  refine ⟨447675484165782117840461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193801291108752314241229 447675484165782117840461)
                  ·
                    rfl

theorem cell21_1961651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 3].length) (baseStart_1961651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961651 prefixEnd_1961651 := by exact prefixLift 1961651
  have htrace : WordTrace (prefixWord ++ tailWord_1961651) baseStart_1961651 baseEnd_1961651 := by
    simpa [prefixWord, tailWord_1961651, baseEnd_1961651] using wordTrace_append hprefix tailTrace_1961651
  have hstable : (prefixWord ++ tailWord_1961651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961651).length < 2 ^ (prefixWord ++ tailWord_1961651).sum := by decide
  have hdescent : baseEnd_1961651 < baseStart_1961651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961724 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 6]
def baseStart_1961724 : Nat := 118140960795 + 1961724 * 2 ^ 59
def prefixEnd_1961724 : Nat := 4983230072969 + 3 ^ 40 * 1961724 * 2
def baseEnd_1961724 : Nat := 447692143760350213123645

theorem tailTrace_1961724 : CollatzResearch.WordTrace tailWord_1961724 prefixEnd_1961724 447692143760350213123645 := by
  unfold tailWord_1961724
  simp only [CollatzResearch.WordTrace]
  refine ⟨35774976172508229315374113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47699968230010972420498817 35774976172508229315374113)
  ·
    refine ⟨26831232129381171986530585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35774976172508229315374113 26831232129381171986530585)
    ·
      refine ⟨20123424097035878989897939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26831232129381171986530585 20123424097035878989897939)
      ·
        refine ⟨30185136145553818484846909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20123424097035878989897939 30185136145553818484846909)
        ·
          refine ⟨11319426054582681931817591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30185136145553818484846909 11319426054582681931817591)
          ·
            refine ⟨16979139081874022897726387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11319426054582681931817591 16979139081874022897726387)
            ·
              refine ⟨25468708622811034346589581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16979139081874022897726387 25468708622811034346589581)
              ·
                refine ⟨9550765733554137879971093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25468708622811034346589581 9550765733554137879971093)
                ·
                  refine ⟨447692143760350213123645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9550765733554137879971093 447692143760350213123645)
                  ·
                    rfl

theorem cell21_1961724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_1961724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961724 prefixEnd_1961724 := by exact prefixLift 1961724
  have htrace : WordTrace (prefixWord ++ tailWord_1961724) baseStart_1961724 baseEnd_1961724 := by
    simpa [prefixWord, tailWord_1961724, baseEnd_1961724] using wordTrace_append hprefix tailTrace_1961724
  have hstable : (prefixWord ++ tailWord_1961724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961724).length < 2 ^ (prefixWord ++ tailWord_1961724).sum := by decide
  have hdescent : baseEnd_1961724 < baseStart_1961724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961834 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 6]
def baseStart_1961834 : Nat := 118140960795 + 1961834 * 2 ^ 59
def prefixEnd_1961834 : Nat := 4983230072969 + 3 ^ 40 * 1961834 * 2
def baseEnd_1961834 : Nat := 447717247259014466290087

theorem tailTrace_1961834 : CollatzResearch.WordTrace tailWord_1961834 prefixEnd_1961834 447717247259014466290087 := by
  unfold tailWord_1961834
  simp only [CollatzResearch.WordTrace]
  refine ⟨17888491093654486854313139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47702642916411964944835037 17888491093654486854313139)
  ·
    refine ⟨26832736640481730281469709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17888491093654486854313139 26832736640481730281469709)
    ·
      refine ⟨10062276240180648855551141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26832736640481730281469709 10062276240180648855551141)
      ·
        refine ⟨1886676795033871660415839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10062276240180648855551141 1886676795033871660415839)
        ·
          refine ⟨2830015192550807490623759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886676795033871660415839 2830015192550807490623759)
          ·
            refine ⟨4245022788826211235935639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830015192550807490623759 4245022788826211235935639)
            ·
              refine ⟨6367534183239316853903459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4245022788826211235935639 6367534183239316853903459)
              ·
                refine ⟨9551301274858975280855189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6367534183239316853903459 9551301274858975280855189)
                ·
                  refine ⟨447717247259014466290087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9551301274858975280855189 447717247259014466290087)
                  ·
                    rfl

theorem cell21_1961834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_1961834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961834 prefixEnd_1961834 := by exact prefixLift 1961834
  have htrace : WordTrace (prefixWord ++ tailWord_1961834) baseStart_1961834 baseEnd_1961834 := by
    simpa [prefixWord, tailWord_1961834, baseEnd_1961834] using wordTrace_append hprefix tailTrace_1961834
  have hstable : (prefixWord ++ tailWord_1961834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961834).length < 2 ^ (prefixWord ++ tailWord_1961834).sum := by decide
  have hdescent : baseEnd_1961834 < baseStart_1961834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961879 : List Nat := [1, 1, 3, 3, 1, 3, 3, 3, 3]
def baseStart_1961879 : Nat := 118140960795 + 1961879 * 2 ^ 59
def prefixEnd_1961879 : Nat := 4983230072969 + 3 ^ 40 * 1961879 * 2
def baseEnd_1961879 : Nat := 447727516872104388039995

theorem tailTrace_1961879 : CollatzResearch.WordTrace tailWord_1961879 prefixEnd_1961879 447727516872104388039995 := by
  unfold tailWord_1961879
  simp only [CollatzResearch.WordTrace]
  refine ⟨71555605659454920102640691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47703737106303280068427127 71555605659454920102640691)
  ·
    refine ⟨107333408489182380153961037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71555605659454920102640691 107333408489182380153961037)
    ·
      refine ⟨40250028183443392557735389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107333408489182380153961037 40250028183443392557735389)
      ·
        refine ⟨15093760568791272209150771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40250028183443392557735389 15093760568791272209150771)
        ·
          refine ⟨22640640853186908313726157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15093760568791272209150771 22640640853186908313726157)
          ·
            refine ⟨8490240319945090617647309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22640640853186908313726157 8490240319945090617647309)
            ·
              refine ⟨3183840119979408981617741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8490240319945090617647309 3183840119979408981617741)
              ·
                refine ⟨1193940044992278368106653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3183840119979408981617741 1193940044992278368106653)
                ·
                  refine ⟨447727516872104388039995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193940044992278368106653 447727516872104388039995)
                  ·
                    rfl

theorem cell21_1961879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 3].length) (baseStart_1961879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961879 prefixEnd_1961879 := by exact prefixLift 1961879
  have htrace : WordTrace (prefixWord ++ tailWord_1961879) baseStart_1961879 baseEnd_1961879 := by
    simpa [prefixWord, tailWord_1961879, baseEnd_1961879] using wordTrace_append hprefix tailTrace_1961879
  have hstable : (prefixWord ++ tailWord_1961879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961879).length < 2 ^ (prefixWord ++ tailWord_1961879).sum := by decide
  have hdescent : baseEnd_1961879 < baseStart_1961879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961902 : List Nat := [4, 1, 5, 1, 2, 1, 2, 1, 4]
def baseStart_1961902 : Nat := 118140960795 + 1961902 * 2 ^ 59
def prefixEnd_1961902 : Nat := 4983230072969 + 3 ^ 40 * 1961902 * 2
def baseEnd_1961902 : Nat := 447732765785461459156615

theorem tailTrace_1961902 : CollatzResearch.WordTrace tailWord_1961902 prefixEnd_1961902 447732765785461459156615 := by
  unfold tailWord_1961902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8944555567296449378840995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47704296358914396687151973 8944555567296449378840995)
  ·
    refine ⟨13416833350944674068261493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8944555567296449378840995 13416833350944674068261493)
    ·
      refine ⟨1257828126651063193899515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13416833350944674068261493 1257828126651063193899515)
      ·
        refine ⟨1886742189976594790849273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257828126651063193899515 1886742189976594790849273)
        ·
          refine ⟨1415056642482446093136955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1886742189976594790849273 1415056642482446093136955)
          ·
            refine ⟨2122584963723669139705433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415056642482446093136955 2122584963723669139705433)
            ·
              refine ⟨1591938722792751854779075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2122584963723669139705433 1591938722792751854779075)
              ·
                refine ⟨2387908084189127782168613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1591938722792751854779075 2387908084189127782168613)
                ·
                  refine ⟨447732765785461459156615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2387908084189127782168613 447732765785461459156615)
                  ·
                    rfl

theorem cell21_1961902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_1961902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961902 prefixEnd_1961902 := by exact prefixLift 1961902
  have htrace : WordTrace (prefixWord ++ tailWord_1961902) baseStart_1961902 baseEnd_1961902 := by
    simpa [prefixWord, tailWord_1961902, baseEnd_1961902] using wordTrace_append hprefix tailTrace_1961902
  have hstable : (prefixWord ++ tailWord_1961902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961902).length < 2 ^ (prefixWord ++ tailWord_1961902).sum := by decide
  have hdescent : baseEnd_1961902 < baseStart_1961902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961955 : List Nat := [1, 1, 1, 6, 1, 3, 1, 4, 3]
def baseStart_1961955 : Nat := 118140960795 + 1961955 * 2 ^ 59
def prefixEnd_1961955 : Nat := 4983230072969 + 3 ^ 40 * 1961955 * 2
def baseEnd_1961955 : Nat := 447744861107545144773173

theorem tailTrace_1961955 : CollatzResearch.WordTrace tailWord_1961955 prefixEnd_1961955 447744861107545144773173 := by
  unfold tailWord_1961955
  simp only [CollatzResearch.WordTrace]
  refine ⟨71558377607179585082407319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47705585071453056721604879 71558377607179585082407319)
  ·
    refine ⟨107337566410769377623610979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71558377607179585082407319 107337566410769377623610979)
    ·
      refine ⟨161006349616154066435416469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107337566410769377623610979 161006349616154066435416469)
      ·
        refine ⟨7547172638257221864160147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 161006349616154066435416469 7547172638257221864160147)
        ·
          refine ⟨11320758957385832796240221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7547172638257221864160147 11320758957385832796240221)
          ·
            refine ⟨4245284609019687298590083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11320758957385832796240221 4245284609019687298590083)
            ·
              refine ⟨6367926913529530947885125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4245284609019687298590083 6367926913529530947885125)
              ·
                refine ⟨1193986296286787052728461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6367926913529530947885125 1193986296286787052728461)
                ·
                  refine ⟨447744861107545144773173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1193986296286787052728461 447744861107545144773173)
                  ·
                    rfl

theorem cell21_1961955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 3].length) (baseStart_1961955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1961955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1961955 prefixEnd_1961955 := by exact prefixLift 1961955
  have htrace : WordTrace (prefixWord ++ tailWord_1961955) baseStart_1961955 baseEnd_1961955 := by
    simpa [prefixWord, tailWord_1961955, baseEnd_1961955] using wordTrace_append hprefix tailTrace_1961955
  have hstable : (prefixWord ++ tailWord_1961955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961955).length < 2 ^ (prefixWord ++ tailWord_1961955).sum := by decide
  have hdescent : baseEnd_1961955 < baseStart_1961955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962149 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 5]
def baseStart_1962149 : Nat := 118140960795 + 1962149 * 2 ^ 59
def prefixEnd_1962149 : Nat := 4983230072969 + 3 ^ 40 * 1962149 * 2
def baseEnd_1962149 : Nat := 447789134550643918539443

theorem tailTrace_1962149 : CollatzResearch.WordTrace tailWord_1962149 prefixEnd_1962149 447789134550643918539443 := by
  unfold tailWord_1962149
  simp only [CollatzResearch.WordTrace]
  refine ⟨71565453368476756214969501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47710302245651170809979667 71565453368476756214969501)
  ·
    refine ⟨26837045013178783580613563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71565453368476756214969501 26837045013178783580613563)
    ·
      refine ⟨40255567519768175370920345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26837045013178783580613563 40255567519768175370920345)
      ·
        refine ⟨30191675639826131528190259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40255567519768175370920345 30191675639826131528190259)
        ·
          refine ⟨45287513459739197292285389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30191675639826131528190259 45287513459739197292285389)
          ·
            refine ⟨16982817547402198984607021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45287513459739197292285389 16982817547402198984607021)
            ·
              refine ⟨6368556580275824619227633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16982817547402198984607021 6368556580275824619227633)
              ·
                refine ⟨4776417435206868464420725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6368556580275824619227633 4776417435206868464420725)
                ·
                  refine ⟨447789134550643918539443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4776417435206868464420725 447789134550643918539443)
                  ·
                    rfl

theorem cell21_1962149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_1962149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1962149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1962149 prefixEnd_1962149 := by exact prefixLift 1962149
  have htrace : WordTrace (prefixWord ++ tailWord_1962149) baseStart_1962149 baseEnd_1962149 := by
    simpa [prefixWord, tailWord_1962149, baseEnd_1962149] using wordTrace_append hprefix tailTrace_1962149
  have hstable : (prefixWord ++ tailWord_1962149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962149).length < 2 ^ (prefixWord ++ tailWord_1962149).sum := by decide
  have hdescent : baseEnd_1962149 < baseStart_1962149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962163 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 6]
def baseStart_1962163 : Nat := 118140960795 + 1962163 * 2 ^ 59
def prefixEnd_1962163 : Nat := 4983230072969 + 3 ^ 40 * 1962163 * 2
def baseEnd_1962163 : Nat := 447792329541383005306081

theorem tailTrace_1962163 : CollatzResearch.WordTrace tailWord_1962163 prefixEnd_1962163 447792329541383005306081 := by
  unfold tailWord_1962163
  simp only [CollatzResearch.WordTrace]
  refine ⟨71565963990426036605979143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47710642660284024403986095 71565963990426036605979143)
  ·
    refine ⟨107348945985639054908968715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71565963990426036605979143 107348945985639054908968715)
    ·
      refine ⟨161023418978458582363453073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107348945985639054908968715 161023418978458582363453073)
      ·
        refine ⟨120767564233843936772589805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161023418978458582363453073 120767564233843936772589805)
        ·
          refine ⟨45287836587691476289721177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120767564233843936772589805 45287836587691476289721177)
          ·
            refine ⟨33965877440768607217290883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45287836587691476289721177 33965877440768607217290883)
            ·
              refine ⟨50948816161152910825936325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33965877440768607217290883 50948816161152910825936325)
              ·
                refine ⟨9552903030216170779863061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50948816161152910825936325 9552903030216170779863061)
                ·
                  refine ⟨447792329541383005306081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9552903030216170779863061 447792329541383005306081)
                  ·
                    rfl

theorem cell21_1962163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 6].length) (baseStart_1962163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1962163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1962163 prefixEnd_1962163 := by exact prefixLift 1962163
  have htrace : WordTrace (prefixWord ++ tailWord_1962163) baseStart_1962163 baseEnd_1962163 := by
    simpa [prefixWord, tailWord_1962163, baseEnd_1962163] using wordTrace_append hprefix tailTrace_1962163
  have hstable : (prefixWord ++ tailWord_1962163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962163).length < 2 ^ (prefixWord ++ tailWord_1962163).sum := by decide
  have hdescent : baseEnd_1962163 < baseStart_1962163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962239 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 6]
def baseStart_1962239 : Nat := 118140960795 + 1962239 * 2 ^ 59
def prefixEnd_1962239 : Nat := 4983230072969 + 3 ^ 40 * 1962239 * 2
def baseEnd_1962239 : Nat := 447809673776823762039259

theorem tailTrace_1962239 : CollatzResearch.WordTrace tailWord_1962239 prefixEnd_1962239 447809673776823762039259 := by
  unfold tailWord_1962239
  simp only [CollatzResearch.WordTrace]
  refine ⟨71568735938150701585745771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47712490625433801057163847 71568735938150701585745771)
  ·
    refine ⟨107353103907226052378618657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71568735938150701585745771 107353103907226052378618657)
    ·
      refine ⟨80514827930419539283963993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107353103907226052378618657 80514827930419539283963993)
      ·
        refine ⟨60386120947814654462972995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80514827930419539283963993 60386120947814654462972995)
        ·
          refine ⟨90579181421721981694459493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60386120947814654462972995 90579181421721981694459493)
          ·
            refine ⟨16983596516572871567711155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90579181421721981694459493 16983596516572871567711155)
            ·
              refine ⟨25475394774859307351566733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16983596516572871567711155 25475394774859307351566733)
              ·
                refine ⟨9553273040572240256837525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25475394774859307351566733 9553273040572240256837525)
                ·
                  refine ⟨447809673776823762039259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9553273040572240256837525 447809673776823762039259)
                  ·
                    rfl

theorem cell21_1962239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 6].length) (baseStart_1962239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1962239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1962239 prefixEnd_1962239 := by exact prefixLift 1962239
  have htrace : WordTrace (prefixWord ++ tailWord_1962239) baseStart_1962239 baseEnd_1962239 := by
    simpa [prefixWord, tailWord_1962239, baseEnd_1962239] using wordTrace_append hprefix tailTrace_1962239
  have hstable : (prefixWord ++ tailWord_1962239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962239).length < 2 ^ (prefixWord ++ tailWord_1962239).sum := by decide
  have hdescent : baseEnd_1962239 < baseStart_1962239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962377 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 5]
def baseStart_1962377 : Nat := 118140960795 + 1962377 * 2 ^ 59
def prefixEnd_1962377 : Nat := 4983230072969 + 3 ^ 40 * 1962377 * 2
def baseEnd_1962377 : Nat := 447841167256966188738977

theorem tailTrace_1962377 : CollatzResearch.WordTrace tailWord_1962377 prefixEnd_1962377 447841167256966188738977 := by
  unfold tailWord_1962377
  simp only [CollatzResearch.WordTrace]
  refine ⟨71573769211650751154269385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47715846141100500769512923 71573769211650751154269385)
  ·
    refine ⟨53680326908738063365702039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71573769211650751154269385 53680326908738063365702039)
    ·
      refine ⟨80520490363107095048553059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53680326908738063365702039 80520490363107095048553059)
      ·
        refine ⟨120780735544660642572829589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80520490363107095048553059 120780735544660642572829589)
        ·
          refine ⟨5661596978655967620601387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120780735544660642572829589 5661596978655967620601387)
          ·
            refine ⟨8492395467983951430902081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5661596978655967620601387 8492395467983951430902081)
            ·
              refine ⟨6369296600987963573176561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8492395467983951430902081 6369296600987963573176561)
              ·
                refine ⟨4776972450740972679882421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6369296600987963573176561 4776972450740972679882421)
                ·
                  refine ⟨447841167256966188738977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4776972450740972679882421 447841167256966188738977)
                  ·
                    rfl

theorem cell21_1962377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_1962377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1962377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1962377 prefixEnd_1962377 := by exact prefixLift 1962377
  have htrace : WordTrace (prefixWord ++ tailWord_1962377) baseStart_1962377 baseEnd_1962377 := by
    simpa [prefixWord, tailWord_1962377, baseEnd_1962377] using wordTrace_append hprefix tailTrace_1962377
  have hstable : (prefixWord ++ tailWord_1962377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962377).length < 2 ^ (prefixWord ++ tailWord_1962377).sum := by decide
  have hdescent : baseEnd_1962377 < baseStart_1962377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962391 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 6]
def baseStart_1962391 : Nat := 118140960795 + 1962391 * 2 ^ 59
def prefixEnd_1962391 : Nat := 4983230072969 + 3 ^ 40 * 1962391 * 2
def baseEnd_1962391 : Nat := 447844362247705275505615

theorem tailTrace_1962391 : CollatzResearch.WordTrace tailWord_1962391 prefixEnd_1962391 447844362247705275505615 := by
  unfold tailWord_1962391
  simp only [CollatzResearch.WordTrace]
  refine ⟨71574279833600031545279027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47716186555733354363519351 71574279833600031545279027)
  ·
    refine ⟨107361419750400047317918541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71574279833600031545279027 107361419750400047317918541)
    ·
      refine ⟨40260532406400017744219453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107361419750400047317918541 40260532406400017744219453)
      ·
        refine ⟨15097699652400006654082295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40260532406400017744219453 15097699652400006654082295)
        ·
          refine ⟨22646549478600009981123443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15097699652400006654082295 22646549478600009981123443)
          ·
            refine ⟨33969824217900014971685165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22646549478600009981123443 33969824217900014971685165)
            ·
              refine ⟨12738684081712505614381937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33969824217900014971685165 12738684081712505614381937)
              ·
                refine ⟨9554013061284379210786453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12738684081712505614381937 9554013061284379210786453)
                ·
                  refine ⟨447844362247705275505615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9554013061284379210786453 447844362247705275505615)
                  ·
                    rfl

theorem cell21_1962391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 6].length) (baseStart_1962391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1962391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1962391 prefixEnd_1962391 := by exact prefixLift 1962391
  have htrace : WordTrace (prefixWord ++ tailWord_1962391) baseStart_1962391 baseEnd_1962391 := by
    simpa [prefixWord, tailWord_1962391, baseEnd_1962391] using wordTrace_append hprefix tailTrace_1962391
  have hstable : (prefixWord ++ tailWord_1962391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962391).length < 2 ^ (prefixWord ++ tailWord_1962391).sum := by decide
  have hdescent : baseEnd_1962391 < baseStart_1962391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962425 : List Nat := [1, 2, 1, 4, 3, 1, 4, 1, 4]
def baseStart_1962425 : Nat := 118140960795 + 1962425 * 2 ^ 59
def prefixEnd_1962425 : Nat := 4983230072969 + 3 ^ 40 * 1962425 * 2
def baseEnd_1962425 : Nat := 447852121510928771938879

theorem tailTrace_1962425 : CollatzResearch.WordTrace tailWord_1962425 prefixEnd_1962425 447852121510928771938879 := by
  unfold tailWord_1962425
  simp only [CollatzResearch.WordTrace]
  refine ⟨71575519915476855352016729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47717013276984570234677819 71575519915476855352016729)
  ·
    refine ⟨53681639936607641514012547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71575519915476855352016729 53681639936607641514012547)
    ·
      refine ⟨80522459904911462271018821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53681639936607641514012547 80522459904911462271018821)
      ·
        refine ⟨15097961232170899175816029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80522459904911462271018821 15097961232170899175816029)
        ·
          refine ⟨5661735462064087190931011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15097961232170899175816029 5661735462064087190931011)
          ·
            refine ⟨8492603193096130786396517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5661735462064087190931011 8492603193096130786396517)
            ·
              refine ⟨1592363098705524522449347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8492603193096130786396517 1592363098705524522449347)
              ·
                refine ⟨2388544648058286783674021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592363098705524522449347 2388544648058286783674021)
                ·
                  refine ⟨447852121510928771938879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2388544648058286783674021 447852121510928771938879)
                  ·
                    rfl

theorem cell21_1962425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 4].length) (baseStart_1962425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1962425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1962425 prefixEnd_1962425 := by exact prefixLift 1962425
  have htrace : WordTrace (prefixWord ++ tailWord_1962425) baseStart_1962425 baseEnd_1962425 := by
    simpa [prefixWord, tailWord_1962425, baseEnd_1962425] using wordTrace_append hprefix tailTrace_1962425
  have hstable : (prefixWord ++ tailWord_1962425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962425).length < 2 ^ (prefixWord ++ tailWord_1962425).sum := by decide
  have hdescent : baseEnd_1962425 < baseStart_1962425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962529 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 5]
def baseStart_1962529 : Nat := 118140960795 + 1962529 * 2 ^ 59
def prefixEnd_1962529 : Nat := 4983230072969 + 3 ^ 40 * 1962529 * 2
def baseEnd_1962529 : Nat := 447875855727847702205333

theorem tailTrace_1962529 : CollatzResearch.WordTrace tailWord_1962529 prefixEnd_1962529 447875855727847702205333 := by
  unfold tailWord_1962529
  simp only [CollatzResearch.WordTrace]
  refine ⟨71579313107100081113802641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47719542071400054075868427 71579313107100081113802641)
  ·
    refine ⟨53684484830325060835351981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71579313107100081113802641 53684484830325060835351981)
    ·
      refine ⟨20131681811371897813256993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53684484830325060835351981 20131681811371897813256993)
      ·
        refine ⟨15098761358528923359942745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20131681811371897813256993 15098761358528923359942745)
        ·
          refine ⟨11324071018896692519957059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15098761358528923359942745 11324071018896692519957059)
          ·
            refine ⟨16986106528345038779935589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11324071018896692519957059 16986106528345038779935589)
            ·
              refine ⟨3184894974064694771237923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16986106528345038779935589 3184894974064694771237923)
              ·
                refine ⟨4777342461097042156856885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3184894974064694771237923 4777342461097042156856885)
                ·
                  refine ⟨447875855727847702205333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4777342461097042156856885 447875855727847702205333)
                  ·
                    rfl

theorem cell21_1962529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_1962529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1962529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1962529 prefixEnd_1962529 := by exact prefixLift 1962529
  have htrace : WordTrace (prefixWord ++ tailWord_1962529) baseStart_1962529 baseEnd_1962529 := by
    simpa [prefixWord, tailWord_1962529, baseEnd_1962529] using wordTrace_append hprefix tailTrace_1962529
  have hstable : (prefixWord ++ tailWord_1962529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962529).length < 2 ^ (prefixWord ++ tailWord_1962529).sum := by decide
  have hdescent : baseEnd_1962529 < baseStart_1962529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962535 : List Nat := [1, 1, 7, 2, 1, 1, 3, 1, 4]
def baseStart_1962535 : Nat := 118140960795 + 1962535 * 2 ^ 59
def prefixEnd_1962535 : Nat := 4983230072969 + 3 ^ 40 * 1962535 * 2
def baseEnd_1962535 : Nat := 447877225009593025105321

theorem tailTrace_1962535 : CollatzResearch.WordTrace tailWord_1962535 prefixEnd_1962535 447877225009593025105321 := by
  unfold tailWord_1962535
  simp only [CollatzResearch.WordTrace]
  refine ⟨71579531945078344138521059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47719687963385562759014039 71579531945078344138521059)
  ·
    refine ⟨107369297917617516207781589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71579531945078344138521059 107369297917617516207781589)
    ·
      refine ⟨2516467919944160536119881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 107369297917617516207781589 2516467919944160536119881)
      ·
        refine ⟨1887350939958120402089911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2516467919944160536119881 1887350939958120402089911)
        ·
          refine ⟨2831026409937180603134867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1887350939958120402089911 2831026409937180603134867)
          ·
            refine ⟨4246539614905770904702301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831026409937180603134867 4246539614905770904702301)
            ·
              refine ⟨1592452355589664089263363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4246539614905770904702301 1592452355589664089263363)
              ·
                refine ⟨2388678533384496133895045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592452355589664089263363 2388678533384496133895045)
                ·
                  refine ⟨447877225009593025105321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2388678533384496133895045 447877225009593025105321)
                  ·
                    rfl

theorem cell21_1962535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 4].length) (baseStart_1962535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1962535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1962535 prefixEnd_1962535 := by exact prefixLift 1962535
  have htrace : WordTrace (prefixWord ++ tailWord_1962535) baseStart_1962535 baseEnd_1962535 := by
    simpa [prefixWord, tailWord_1962535, baseEnd_1962535] using wordTrace_append hprefix tailTrace_1962535
  have hstable : (prefixWord ++ tailWord_1962535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962535).length < 2 ^ (prefixWord ++ tailWord_1962535).sum := by decide
  have hdescent : baseEnd_1962535 < baseStart_1962535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962594 : List Nat := [3, 3, 2, 3, 1, 1, 1, 3, 4]
def baseStart_1962594 : Nat := 118140960795 + 1962594 * 2 ^ 59
def prefixEnd_1962594 : Nat := 4983230072969 + 3 ^ 40 * 1962594 * 2
def baseEnd_1962594 : Nat := 447890689613422033621867

theorem tailTrace_1962594 : CollatzResearch.WordTrace tailWord_1962594 prefixEnd_1962594 447890689613422033621867 := by
  unfold tailWord_1962594
  simp only [CollatzResearch.WordTrace]
  refine ⟨17895420962966149303729709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47721122567909731476612557 17895420962966149303729709)
  ·
    refine ⟨6710782861112305988898641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17895420962966149303729709 6710782861112305988898641)
    ·
      refine ⟨5033087145834229491673981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6710782861112305988898641 5033087145834229491673981)
      ·
        refine ⟨1887407679687836059377743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5033087145834229491673981 1887407679687836059377743)
        ·
          refine ⟨2831111519531754089066615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1887407679687836059377743 2831111519531754089066615)
          ·
            refine ⟨4246667279297631133599923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831111519531754089066615 4246667279297631133599923)
            ·
              refine ⟨6370000918946446700399885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4246667279297631133599923 6370000918946446700399885)
              ·
                refine ⟨2388750344604917512649957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6370000918946446700399885 2388750344604917512649957)
                ·
                  refine ⟨447890689613422033621867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2388750344604917512649957 447890689613422033621867)
                  ·
                    rfl

theorem cell21_1962594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_1962594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1962594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1962594 prefixEnd_1962594 := by exact prefixLift 1962594
  have htrace : WordTrace (prefixWord ++ tailWord_1962594) baseStart_1962594 baseEnd_1962594 := by
    simpa [prefixWord, tailWord_1962594, baseEnd_1962594] using wordTrace_append hprefix tailTrace_1962594
  have hstable : (prefixWord ++ tailWord_1962594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962594).length < 2 ^ (prefixWord ++ tailWord_1962594).sum := by decide
  have hdescent : baseEnd_1962594 < baseStart_1962594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962695 : List Nat := [1, 1, 4, 1, 1, 1, 2, 6, 4]
def baseStart_1962695 : Nat := 118140960795 + 1962695 * 2 ^ 59
def prefixEnd_1962695 : Nat := 4983230072969 + 3 ^ 40 * 1962695 * 2
def baseEnd_1962695 : Nat := 447913739189468302438327

theorem tailTrace_1962695 : CollatzResearch.WordTrace tailWord_1962695 prefixEnd_1962695 447913739189468302438327 := by
  unfold tailWord_1962695
  simp only [CollatzResearch.WordTrace]
  refine ⟨71585367624498691464345539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47723578416332460976230359 71585367624498691464345539)
  ·
    refine ⟨107378051436748037196518309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71585367624498691464345539 107378051436748037196518309)
    ·
      refine ⟨20133384644390256974347183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107378051436748037196518309 20133384644390256974347183)
      ·
        refine ⟨30200076966585385461520775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20133384644390256974347183 30200076966585385461520775)
        ·
          refine ⟨45300115449878078192281163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30200076966585385461520775 45300115449878078192281163)
          ·
            refine ⟨67950173174817117288421745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45300115449878078192281163 67950173174817117288421745)
            ·
              refine ⟨50962629881112837966316309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67950173174817117288421745 50962629881112837966316309)
              ·
                refine ⟨2388873275677164279671077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50962629881112837966316309 2388873275677164279671077)
                ·
                  refine ⟨447913739189468302438327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2388873275677164279671077 447913739189468302438327)
                  ·
                    rfl

theorem cell21_1962695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 4].length) (baseStart_1962695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1962695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1962695 prefixEnd_1962695 := by exact prefixLift 1962695
  have htrace : WordTrace (prefixWord ++ tailWord_1962695) baseStart_1962695 baseEnd_1962695 := by
    simpa [prefixWord, tailWord_1962695, baseEnd_1962695] using wordTrace_append hprefix tailTrace_1962695
  have hstable : (prefixWord ++ tailWord_1962695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962695).length < 2 ^ (prefixWord ++ tailWord_1962695).sum := by decide
  have hdescent : baseEnd_1962695 < baseStart_1962695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962698 : List Nat := [3, 1, 2, 1, 4, 1, 2, 4, 3]
def baseStart_1962698 : Nat := 118140960795 + 1962698 * 2 ^ 59
def prefixEnd_1962698 : Nat := 4983230072969 + 3 ^ 40 * 1962698 * 2
def baseEnd_1962698 : Nat := 447914423830340963888321

theorem tailTrace_1962698 : CollatzResearch.WordTrace tailWord_1962698 prefixEnd_1962698 447914423830340963888321 := by
  unfold tailWord_1962698
  simp only [CollatzResearch.WordTrace]
  refine ⟨17896369260871955744176187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47723651362325215317803165 17896369260871955744176187)
  ·
    refine ⟨26844553891307933616264281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17896369260871955744176187 26844553891307933616264281)
    ·
      refine ⟨20133415418480950212198211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26844553891307933616264281 20133415418480950212198211)
      ·
        refine ⟨30200123127721425318297317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20133415418480950212198211 30200123127721425318297317)
        ·
          refine ⟨5662523086447767247180747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30200123127721425318297317 5662523086447767247180747)
          ·
            refine ⟨8493784629671650870771121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5662523086447767247180747 8493784629671650870771121)
            ·
              refine ⟨6370338472253738153078341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8493784629671650870771121 6370338472253738153078341)
              ·
                refine ⟨1194438463547575903702189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6370338472253738153078341 1194438463547575903702189)
                ·
                  refine ⟨447914423830340963888321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194438463547575903702189 447914423830340963888321)
                  ·
                    rfl

theorem cell21_1962698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_1962698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1962698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1962698 prefixEnd_1962698 := by exact prefixLift 1962698
  have htrace : WordTrace (prefixWord ++ tailWord_1962698) baseStart_1962698 baseEnd_1962698 := by
    simpa [prefixWord, tailWord_1962698, baseEnd_1962698] using wordTrace_append hprefix tailTrace_1962698
  have hstable : (prefixWord ++ tailWord_1962698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962698).length < 2 ^ (prefixWord ++ tailWord_1962698).sum := by decide
  have hdescent : baseEnd_1962698 < baseStart_1962698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962757 : List Nat := [1, 3, 1, 1, 2, 1, 1, 8, 3]
def baseStart_1962757 : Nat := 118140960795 + 1962757 * 2 ^ 59
def prefixEnd_1962757 : Nat := 4983230072969 + 3 ^ 40 * 1962757 * 2
def baseEnd_1962757 : Nat := 447927888434169972404867

theorem tailTrace_1962757 : CollatzResearch.WordTrace tailWord_1962757 prefixEnd_1962757 447927888434169972404867 := by
  unfold tailWord_1962757
  simp only [CollatzResearch.WordTrace]
  refine ⟨71587628950274076053102525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47725085966849384035401683 71587628950274076053102525)
  ·
    refine ⟨26845360856352778519913447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71587628950274076053102525 26845360856352778519913447)
    ·
      refine ⟨40268041284529167779870171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26845360856352778519913447 40268041284529167779870171)
      ·
        refine ⟨60402061926793751669805257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40268041284529167779870171 60402061926793751669805257)
        ·
          refine ⟨45301546445095313752353943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60402061926793751669805257 45301546445095313752353943)
          ·
            refine ⟨67952319667642970628530915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45301546445095313752353943 67952319667642970628530915)
            ·
              refine ⟨101928479501464455942796373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67952319667642970628530915 101928479501464455942796373)
              ·
                refine ⟨1194474369157786593079645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 101928479501464455942796373 1194474369157786593079645)
                ·
                  refine ⟨447927888434169972404867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194474369157786593079645 447927888434169972404867)
                  ·
                    rfl

theorem cell21_1962757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_1962757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1962757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1962757 prefixEnd_1962757 := by exact prefixLift 1962757
  have htrace : WordTrace (prefixWord ++ tailWord_1962757) baseStart_1962757 baseEnd_1962757 := by
    simpa [prefixWord, tailWord_1962757, baseEnd_1962757] using wordTrace_append hprefix tailTrace_1962757
  have hstable : (prefixWord ++ tailWord_1962757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962757).length < 2 ^ (prefixWord ++ tailWord_1962757).sum := by decide
  have hdescent : baseEnd_1962757 < baseStart_1962757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962771 : List Nat := [1, 1, 1, 2, 1, 3, 5, 3, 4]
def baseStart_1962771 : Nat := 118140960795 + 1962771 * 2 ^ 59
def prefixEnd_1962771 : Nat := 4983230072969 + 3 ^ 40 * 1962771 * 2
def baseEnd_1962771 : Nat := 447931083424909059171505

theorem tailTrace_1962771 : CollatzResearch.WordTrace tailWord_1962771 prefixEnd_1962771 447931083424909059171505 := by
  unfold tailWord_1962771
  simp only [CollatzResearch.WordTrace]
  refine ⟨71588139572223356444112167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47725426381482237629408111 71588139572223356444112167)
  ·
    refine ⟨107382209358335034666168251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71588139572223356444112167 107382209358335034666168251)
    ·
      refine ⟨161073314037502551999252377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107382209358335034666168251 161073314037502551999252377)
      ·
        refine ⟨120804985528126913999439283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161073314037502551999252377 120804985528126913999439283)
        ·
          refine ⟨181207478292190370999158925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120804985528126913999439283 181207478292190370999158925)
          ·
            refine ⟨67952804359571389124684597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181207478292190370999158925 67952804359571389124684597)
            ·
              refine ⟨6370575408709817730439181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67952804359571389124684597 6370575408709817730439181)
              ·
                refine ⟨2388965778266181648914693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6370575408709817730439181 2388965778266181648914693)
                ·
                  refine ⟨447931083424909059171505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2388965778266181648914693 447931083424909059171505)
                  ·
                    rfl

theorem cell21_1962771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 4].length) (baseStart_1962771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1962771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1962771 prefixEnd_1962771 := by exact prefixLift 1962771
  have htrace : WordTrace (prefixWord ++ tailWord_1962771) baseStart_1962771 baseEnd_1962771 := by
    simpa [prefixWord, tailWord_1962771, baseEnd_1962771] using wordTrace_append hprefix tailTrace_1962771
  have hstable : (prefixWord ++ tailWord_1962771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962771).length < 2 ^ (prefixWord ++ tailWord_1962771).sum := by decide
  have hdescent : baseEnd_1962771 < baseStart_1962771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962785 : List Nat := [1, 2, 3, 2, 1, 2, 1, 9]
def baseStart_1962785 : Nat := 118140960795 + 1962785 * 2 ^ 59
def prefixEnd_1962785 : Nat := 4983230072969 + 3 ^ 40 * 1962785 * 2
def baseEnd_1962785 : Nat := 149311426138549381979381

theorem tailTrace_1962785 : CollatzResearch.WordTrace tailWord_1962785 prefixEnd_1962785 149311426138549381979381 := by
  unfold tailWord_1962785
  simp only [CollatzResearch.WordTrace]
  refine ⟨71588650194172636835121809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47725766796115091223414539 71588650194172636835121809)
  ·
    refine ⟨53691487645629477626341357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71588650194172636835121809 53691487645629477626341357)
    ·
      refine ⟨20134307867111054109878009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53691487645629477626341357 20134307867111054109878009)
      ·
        refine ⟨15100730900333290582408507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20134307867111054109878009 15100730900333290582408507)
        ·
          refine ⟨22651096350499935873612761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15100730900333290582408507 22651096350499935873612761)
          ·
            refine ⟨16988322262874951905209571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22651096350499935873612761 16988322262874951905209571)
            ·
              refine ⟨25482483394312427857814357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16988322262874951905209571 25482483394312427857814357)
              ·
                refine ⟨149311426138549381979381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25482483394312427857814357 149311426138549381979381)
                ·
                  rfl

theorem cell21_1962785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 9].length) (baseStart_1962785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1962785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1962785 prefixEnd_1962785 := by exact prefixLift 1962785
  have htrace : WordTrace (prefixWord ++ tailWord_1962785) baseStart_1962785 baseEnd_1962785 := by
    simpa [prefixWord, tailWord_1962785, baseEnd_1962785] using wordTrace_append hprefix tailTrace_1962785
  have hstable : (prefixWord ++ tailWord_1962785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962785).length < 2 ^ (prefixWord ++ tailWord_1962785).sum := by decide
  have hdescent : baseEnd_1962785 < baseStart_1962785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962833 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 5]
def baseStart_1962833 : Nat := 118140960795 + 1962833 * 2 ^ 59
def prefixEnd_1962833 : Nat := 4983230072969 + 3 ^ 40 * 1962833 * 2
def baseEnd_1962833 : Nat := 447945232669610729138045

theorem tailTrace_1962833 : CollatzResearch.WordTrace tailWord_1962833 prefixEnd_1962833 447945232669610729138045 := by
  unfold tailWord_1962833
  simp only [CollatzResearch.WordTrace]
  refine ⟨71590400897998741032869153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47726933931999160688579435 71590400897998741032869153)
  ·
    refine ⟨53692800673499055774651865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71590400897998741032869153 53692800673499055774651865)
    ·
      refine ⟨40269600505124291830988899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53692800673499055774651865 40269600505124291830988899)
      ·
        refine ⟨60404400757686437746483349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40269600505124291830988899 60404400757686437746483349)
        ·
          refine ⟨2831456285516551769366407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60404400757686437746483349 2831456285516551769366407)
          ·
            refine ⟨4247184428274827654049611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831456285516551769366407 4247184428274827654049611)
            ·
              refine ⟨6370776642412241481074417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4247184428274827654049611 6370776642412241481074417)
              ·
                refine ⟨4778082481809181110805813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6370776642412241481074417 4778082481809181110805813)
                ·
                  refine ⟨447945232669610729138045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4778082481809181110805813 447945232669610729138045)
                  ·
                    rfl

theorem cell21_1962833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_1962833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1962833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1962833 prefixEnd_1962833 := by exact prefixLift 1962833
  have htrace : WordTrace (prefixWord ++ tailWord_1962833) baseStart_1962833 baseEnd_1962833 := by
    simpa [prefixWord, tailWord_1962833, baseEnd_1962833] using wordTrace_append hprefix tailTrace_1962833
  have hstable : (prefixWord ++ tailWord_1962833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962833).length < 2 ^ (prefixWord ++ tailWord_1962833).sum := by decide
  have hdescent : baseEnd_1962833 < baseStart_1962833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962892 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 5]
def baseStart_1962892 : Nat := 118140960795 + 1962892 * 2 ^ 59
def prefixEnd_1962892 : Nat := 4983230072969 + 3 ^ 40 * 1962892 * 2
def baseEnd_1962892 : Nat := 447958697273439737654591

theorem tailTrace_1962892 : CollatzResearch.WordTrace tailWord_1962892 prefixEnd_1962892 447958697273439737654591 := by
  unfold tailWord_1962892
  simp only [CollatzResearch.WordTrace]
  refine ⟨35796276402392497054633465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47728368536523329406177953 35796276402392497054633465)
  ·
    refine ⟨26847207301794372790975099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35796276402392497054633465 26847207301794372790975099)
    ·
      refine ⟨40270810952691559186462649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26847207301794372790975099 40270810952691559186462649)
      ·
        refine ⟨30203108214518669389846987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40270810952691559186462649 30203108214518669389846987)
        ·
          refine ⟨45304662321778004084770481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30203108214518669389846987 45304662321778004084770481)
          ·
            refine ⟨33978496741333503063577861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45304662321778004084770481 33978496741333503063577861)
            ·
              refine ⟨6370968139000031824420849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33978496741333503063577861 6370968139000031824420849)
              ·
                refine ⟨4778226104250023868315637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6370968139000031824420849 4778226104250023868315637)
                ·
                  refine ⟨447958697273439737654591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4778226104250023868315637 447958697273439737654591)
                  ·
                    rfl

theorem cell21_1962892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_1962892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1962892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1962892 prefixEnd_1962892 := by exact prefixLift 1962892
  have htrace : WordTrace (prefixWord ++ tailWord_1962892) baseStart_1962892 baseEnd_1962892 := by
    simpa [prefixWord, tailWord_1962892, baseEnd_1962892] using wordTrace_append hprefix tailTrace_1962892
  have hstable : (prefixWord ++ tailWord_1962892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962892).length < 2 ^ (prefixWord ++ tailWord_1962892).sum := by decide
  have hdescent : baseEnd_1962892 < baseStart_1962892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962937 : List Nat := [1, 2, 1, 4, 2, 2, 1, 8]
def baseStart_1962937 : Nat := 118140960795 + 1962937 * 2 ^ 59
def prefixEnd_1962937 : Nat := 4983230072969 + 3 ^ 40 * 1962937 * 2
def baseEnd_1962937 : Nat := 149322988962176553134833

theorem tailTrace_1962937 : CollatzResearch.WordTrace tailWord_1962937 prefixEnd_1962937 149322988962176553134833 := by
  unfold tailWord_1962937
  simp only [CollatzResearch.WordTrace]
  refine ⟨71594194089621966794655065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47729462726414644529770043 71594194089621966794655065)
  ·
    refine ⟨53695645567216475095991299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71594194089621966794655065 53695645567216475095991299)
    ·
      refine ⟨80543468350824712643986949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53695645567216475095991299 80543468350824712643986949)
      ·
        refine ⟨15101900315779633620747553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80543468350824712643986949 15101900315779633620747553)
        ·
          refine ⟨11326425236834725215560665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15101900315779633620747553 11326425236834725215560665)
          ·
            refine ⟨8494818927626043911670499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11326425236834725215560665 8494818927626043911670499)
            ·
              refine ⟨12742228391439065867505749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8494818927626043911670499 12742228391439065867505749)
              ·
                refine ⟨149322988962176553134833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12742228391439065867505749 149322988962176553134833)
                ·
                  rfl

theorem cell21_1962937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 8].length) (baseStart_1962937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1962937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1962937 prefixEnd_1962937 := by exact prefixLift 1962937
  have htrace : WordTrace (prefixWord ++ tailWord_1962937) baseStart_1962937 baseEnd_1962937 := by
    simpa [prefixWord, tailWord_1962937, baseEnd_1962937] using wordTrace_append hprefix tailTrace_1962937
  have hstable : (prefixWord ++ tailWord_1962937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962937).length < 2 ^ (prefixWord ++ tailWord_1962937).sum := by decide
  have hdescent : baseEnd_1962937 < baseStart_1962937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963027 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 9]
def baseStart_1963027 : Nat := 118140960795 + 1963027 * 2 ^ 59
def prefixEnd_1963027 : Nat := 4983230072969 + 3 ^ 40 * 1963027 * 2
def baseEnd_1963027 : Nat := 447989506112709502904315

theorem tailTrace_1963027 : CollatzResearch.WordTrace tailWord_1963027 prefixEnd_1963027 447989506112709502904315 := by
  unfold tailWord_1963027
  simp only [CollatzResearch.WordTrace]
  refine ⟨71597476659295912165431335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47731651106197274776954223 71597476659295912165431335)
  ·
    refine ⟨107396214988943868248147003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71597476659295912165431335 107396214988943868248147003)
    ·
      refine ⟨161094322483415802372220505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107396214988943868248147003 161094322483415802372220505)
      ·
        refine ⟨120820741862561851779165379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161094322483415802372220505 120820741862561851779165379)
        ·
          refine ⟨181231112793842777668748069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120820741862561851779165379 181231112793842777668748069)
          ·
            refine ⟨33980833648845520812890263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181231112793842777668748069 33980833648845520812890263)
            ·
              refine ⟨50971250473268281219335395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33980833648845520812890263 50971250473268281219335395)
              ·
                refine ⟨76456875709902421829003093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50971250473268281219335395 76456875709902421829003093)
                ·
                  refine ⟨447989506112709502904315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76456875709902421829003093 447989506112709502904315)
                  ·
                    rfl

theorem cell21_1963027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 9].length) (baseStart_1963027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963027 prefixEnd_1963027 := by exact prefixLift 1963027
  have htrace : WordTrace (prefixWord ++ tailWord_1963027) baseStart_1963027 baseEnd_1963027 := by
    simpa [prefixWord, tailWord_1963027, baseEnd_1963027] using wordTrace_append hprefix tailTrace_1963027
  have hstable : (prefixWord ++ tailWord_1963027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963027).length < 2 ^ (prefixWord ++ tailWord_1963027).sum := by decide
  have hdescent : baseEnd_1963027 < baseStart_1963027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963106 : List Nat := [3, 3, 2, 2, 1, 1, 1, 8]
def baseStart_1963106 : Nat := 118140960795 + 1963106 * 2 ^ 59
def prefixEnd_1963106 : Nat := 4983230072969 + 3 ^ 40 * 1963106 * 2
def baseEnd_1963106 : Nat := 149335844996340973695829

theorem tailTrace_1963106 : CollatzResearch.WordTrace tailWord_1963106 prefixEnd_1963106 149335844996340973695829 := by
  unfold tailWord_1963106
  simp only [CollatzResearch.WordTrace]
  refine ⟨17900089506502427164389293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47733572017339805771704781 17900089506502427164389293)
  ·
    refine ⟨6712533564938410186645985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17900089506502427164389293 6712533564938410186645985)
    ·
      refine ⟨5034400173703807639984489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6712533564938410186645985 5034400173703807639984489)
      ·
        refine ⟨3775800130277855729988367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5034400173703807639984489 3775800130277855729988367)
        ·
          refine ⟨5663700195416783594982551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3775800130277855729988367 5663700195416783594982551)
          ·
            refine ⟨8495550293125175392473827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5663700195416783594982551 8495550293125175392473827)
            ·
              refine ⟨12743325439687763088710741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8495550293125175392473827 12743325439687763088710741)
              ·
                refine ⟨149335844996340973695829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12743325439687763088710741 149335844996340973695829)
                ·
                  rfl

theorem cell21_1963106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_1963106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963106 prefixEnd_1963106 := by exact prefixLift 1963106
  have htrace : WordTrace (prefixWord ++ tailWord_1963106) baseStart_1963106 baseEnd_1963106 := by
    simpa [prefixWord, tailWord_1963106, baseEnd_1963106] using wordTrace_append hprefix tailTrace_1963106
  have hstable : (prefixWord ++ tailWord_1963106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963106).length < 2 ^ (prefixWord ++ tailWord_1963106).sum := by decide
  have hdescent : baseEnd_1963106 < baseStart_1963106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963154 : List Nat := [3, 2, 3, 1, 1, 3, 1, 4, 3]
def baseStart_1963154 : Nat := 118140960795 + 1963154 * 2 ^ 59
def prefixEnd_1963154 : Nat := 4983230072969 + 3 ^ 40 * 1963154 * 2
def baseEnd_1963154 : Nat := 448018489242985504287389

theorem tailTrace_1963154 : CollatzResearch.WordTrace tailWord_1963154 prefixEnd_1963154 448018489242985504287389 := by
  unfold tailWord_1963154
  simp only [CollatzResearch.WordTrace]
  refine ⟨17900527182458953213826129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47734739153223875236869677 17900527182458953213826129)
  ·
    refine ⟨13425395386844214910369597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17900527182458953213826129 13425395386844214910369597)
    ·
      refine ⟨5034523270066580591388599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13425395386844214910369597 5034523270066580591388599)
      ·
        refine ⟨7551784905099870887082899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5034523270066580591388599 7551784905099870887082899)
        ·
          refine ⟨11327677357649806330624349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7551784905099870887082899 11327677357649806330624349)
          ·
            refine ⟨4247879009118677373984131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11327677357649806330624349 4247879009118677373984131)
            ·
              refine ⟨6371818513678016060976197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4247879009118677373984131 6371818513678016060976197)
              ·
                refine ⟨1194715971314628011433037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6371818513678016060976197 1194715971314628011433037)
                ·
                  refine ⟨448018489242985504287389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194715971314628011433037 448018489242985504287389)
                  ·
                    rfl

theorem cell21_1963154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_1963154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963154 prefixEnd_1963154 := by exact prefixLift 1963154
  have htrace : WordTrace (prefixWord ++ tailWord_1963154) baseStart_1963154 baseEnd_1963154 := by
    simpa [prefixWord, tailWord_1963154, baseEnd_1963154] using wordTrace_append hprefix tailTrace_1963154
  have hstable : (prefixWord ++ tailWord_1963154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963154).length < 2 ^ (prefixWord ++ tailWord_1963154).sum := by decide
  have hdescent : baseEnd_1963154 < baseStart_1963154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963247 : List Nat := [1, 1, 2, 1, 8, 1, 1, 3, 3]
def baseStart_1963247 : Nat := 118140960795 + 1963247 * 2 ^ 59
def prefixEnd_1963247 : Nat := 4983230072969 + 3 ^ 40 * 1963247 * 2
def baseEnd_1963247 : Nat := 448039713110038009237199

theorem tailTrace_1963247 : CollatzResearch.WordTrace tailWord_1963247 prefixEnd_1963247 448039713110038009237199 := by
  unfold tailWord_1963247
  simp only [CollatzResearch.WordTrace]
  refine ⟨71605500718498889738439995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47737000478999259825626663 71605500718498889738439995)
  ·
    refine ⟨107408251077748334607659993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71605500718498889738439995 107408251077748334607659993)
    ·
      refine ⟨80556188308311250955744995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107408251077748334607659993 80556188308311250955744995)
      ·
        refine ⟨120834282462466876433617493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80556188308311250955744995 120834282462466876433617493)
        ·
          refine ⟨1416026747607033708206455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 120834282462466876433617493 1416026747607033708206455)
          ·
            refine ⟨2124040121410550562309683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416026747607033708206455 2124040121410550562309683)
            ·
              refine ⟨3186060182115825843464525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124040121410550562309683 3186060182115825843464525)
              ·
                refine ⟨1194772568293434691299197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3186060182115825843464525 1194772568293434691299197)
                ·
                  refine ⟨448039713110038009237199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194772568293434691299197 448039713110038009237199)
                  ·
                    rfl

theorem cell21_1963247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 3].length) (baseStart_1963247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963247 prefixEnd_1963247 := by exact prefixLift 1963247
  have htrace : WordTrace (prefixWord ++ tailWord_1963247) baseStart_1963247 baseEnd_1963247 := by
    simpa [prefixWord, tailWord_1963247, baseEnd_1963247] using wordTrace_append hprefix tailTrace_1963247
  have hstable : (prefixWord ++ tailWord_1963247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963247).length < 2 ^ (prefixWord ++ tailWord_1963247).sum := by decide
  have hdescent : baseEnd_1963247 < baseStart_1963247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963331 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 5]
def baseStart_1963331 : Nat := 118140960795 + 1963331 * 2 ^ 59
def prefixEnd_1963331 : Nat := 4983230072969 + 3 ^ 40 * 1963331 * 2
def baseEnd_1963331 : Nat := 448058883054472529837027

theorem tailTrace_1963331 : CollatzResearch.WordTrace tailWord_1963331 prefixEnd_1963331 448058883054472529837027 := by
  unfold tailWord_1963331
  simp only [CollatzResearch.WordTrace]
  refine ⟨71608564450194572084497847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47739042966796381389665231 71608564450194572084497847)
  ·
    refine ⟨107412846675291858126746771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71608564450194572084497847 107412846675291858126746771)
    ·
      refine ⟨161119270012937787190120157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107412846675291858126746771 161119270012937787190120157)
      ·
        refine ⟨60419726254851670196295059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161119270012937787190120157 60419726254851670196295059)
        ·
          refine ⟨90629589382277505294442589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60419726254851670196295059 90629589382277505294442589)
          ·
            refine ⟨33986096018354064485415971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90629589382277505294442589 33986096018354064485415971)
            ·
              refine ⟨50979144027531096728123957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33986096018354064485415971 50979144027531096728123957)
              ·
                refine ⟨4779294752581040318261621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50979144027531096728123957 4779294752581040318261621)
                ·
                  refine ⟨448058883054472529837027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4779294752581040318261621 448058883054472529837027)
                  ·
                    rfl

theorem cell21_1963331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 5].length) (baseStart_1963331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963331 prefixEnd_1963331 := by exact prefixLift 1963331
  have htrace : WordTrace (prefixWord ++ tailWord_1963331) baseStart_1963331 baseEnd_1963331 := by
    simpa [prefixWord, tailWord_1963331, baseEnd_1963331] using wordTrace_append hprefix tailTrace_1963331
  have hstable : (prefixWord ++ tailWord_1963331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963331).length < 2 ^ (prefixWord ++ tailWord_1963331).sum := by decide
  have hdescent : baseEnd_1963331 < baseStart_1963331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963348 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 5]
def baseStart_1963348 : Nat := 118140960795 + 1963348 * 2 ^ 59
def prefixEnd_1963348 : Nat := 4983230072969 + 3 ^ 40 * 1963348 * 2
def baseEnd_1963348 : Nat := 448062762686084278053659

theorem tailTrace_1963348 : CollatzResearch.WordTrace tailWord_1963348 prefixEnd_1963348 448062762686084278053659 := by
  unfold tailWord_1963348
  simp only [CollatzResearch.WordTrace]
  refine ⟨35804592245566491993933349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47739456327421989325244465 35804592245566491993933349)
  ·
    refine ⟨6713361046043717248862503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35804592245566491993933349 6713361046043717248862503)
    ·
      refine ⟨10070041569065575873293755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6713361046043717248862503 10070041569065575873293755)
      ·
        refine ⟨15105062353598363809940633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10070041569065575873293755 15105062353598363809940633)
        ·
          refine ⟨11328796765198772857455475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15105062353598363809940633 11328796765198772857455475)
          ·
            refine ⟨16993195147798159286183213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11328796765198772857455475 16993195147798159286183213)
            ·
              refine ⟨6372448180424309732318705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16993195147798159286183213 6372448180424309732318705)
              ·
                refine ⟨4779336135318232299239029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6372448180424309732318705 4779336135318232299239029)
                ·
                  refine ⟨448062762686084278053659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4779336135318232299239029 448062762686084278053659)
                  ·
                    rfl

theorem cell21_1963348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_1963348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963348 prefixEnd_1963348 := by exact prefixLift 1963348
  have htrace : WordTrace (prefixWord ++ tailWord_1963348) baseStart_1963348 baseEnd_1963348 := by
    simpa [prefixWord, tailWord_1963348, baseEnd_1963348] using wordTrace_append hprefix tailTrace_1963348
  have hstable : (prefixWord ++ tailWord_1963348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963348).length < 2 ^ (prefixWord ++ tailWord_1963348).sum := by decide
  have hdescent : baseEnd_1963348 < baseStart_1963348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963365 : List Nat := [1, 3, 1, 3, 1, 2, 4, 3, 3]
def baseStart_1963365 : Nat := 118140960795 + 1963365 * 2 ^ 59
def prefixEnd_1963365 : Nat := 4983230072969 + 3 ^ 40 * 1963365 * 2
def baseEnd_1963365 : Nat := 448066642317696026270291

theorem tailTrace_1963365 : CollatzResearch.WordTrace tailWord_1963365 prefixEnd_1963365 448066642317696026270291 := by
  unfold tailWord_1963365
  simp only [CollatzResearch.WordTrace]
  refine ⟨71609804532071395891235549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47739869688047597260823699 71609804532071395891235549)
  ·
    refine ⟨26853676699526773459213331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71609804532071395891235549 26853676699526773459213331)
    ·
      refine ⟨40280515049290160188819997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26853676699526773459213331 40280515049290160188819997)
      ·
        refine ⟨15105193143483810070807499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40280515049290160188819997 15105193143483810070807499)
        ·
          refine ⟨22657789715225715106211249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15105193143483810070807499 22657789715225715106211249)
          ·
            refine ⟨16993342286419286329658437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22657789715225715106211249 16993342286419286329658437)
            ·
              refine ⟨3186251678703616186810957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16993342286419286329658437 3186251678703616186810957)
              ·
                refine ⟨1194844379513856070054109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3186251678703616186810957 1194844379513856070054109)
                ·
                  refine ⟨448066642317696026270291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194844379513856070054109 448066642317696026270291)
                  ·
                    rfl

theorem cell21_1963365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_1963365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963365 prefixEnd_1963365 := by exact prefixLift 1963365
  have htrace : WordTrace (prefixWord ++ tailWord_1963365) baseStart_1963365 baseEnd_1963365 := by
    simpa [prefixWord, tailWord_1963365, baseEnd_1963365] using wordTrace_append hprefix tailTrace_1963365
  have hstable : (prefixWord ++ tailWord_1963365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963365).length < 2 ^ (prefixWord ++ tailWord_1963365).sum := by decide
  have hdescent : baseEnd_1963365 < baseStart_1963365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963376 : List Nat := [2, 1, 1, 1, 4, 2, 10]
def baseStart_1963376 : Nat := 118140960795 + 1963376 * 2 ^ 59
def prefixEnd_1963376 : Nat := 4983230072969 + 3 ^ 40 * 1963376 * 2
def baseEnd_1963376 : Nat := 49785461407506939065215

theorem tailTrace_1963376 : CollatzResearch.WordTrace tailWord_1963376 prefixEnd_1963376 49785461407506939065215 := by
  unfold tailWord_1963376
  simp only [CollatzResearch.WordTrace]
  refine ⟨35805102867515772384942991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47740137156687696513257321 35805102867515772384942991)
  ·
    refine ⟨53707654301273658577414487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35805102867515772384942991 53707654301273658577414487)
    ·
      refine ⟨80561481451910487866121731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53707654301273658577414487 80561481451910487866121731)
      ·
        refine ⟨120842222177865731799182597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80561481451910487866121731 120842222177865731799182597)
        ·
          refine ⟨22657916658349824712346737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120842222177865731799182597 22657916658349824712346737)
          ·
            refine ⟨16993437493762368534260053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22657916658349824712346737 16993437493762368534260053)
            ·
              refine ⟨49785461407506939065215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16993437493762368534260053 49785461407506939065215)
              ·
                rfl

theorem cell21_1963376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 10].length) (baseStart_1963376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963376 prefixEnd_1963376 := by exact prefixLift 1963376
  have htrace : WordTrace (prefixWord ++ tailWord_1963376) baseStart_1963376 baseEnd_1963376 := by
    simpa [prefixWord, tailWord_1963376, baseEnd_1963376] using wordTrace_append hprefix tailTrace_1963376
  have hstable : (prefixWord ++ tailWord_1963376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963376).length < 2 ^ (prefixWord ++ tailWord_1963376).sum := by decide
  have hdescent : baseEnd_1963376 < baseStart_1963376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963396 : List Nat := [2, 3, 2, 1, 1, 4, 3, 1, 4]
def baseStart_1963396 : Nat := 118140960795 + 1963396 * 2 ^ 59
def prefixEnd_1963396 : Nat := 4983230072969 + 3 ^ 40 * 1963396 * 2
def baseEnd_1963396 : Nat := 448073716940046861253561

theorem tailTrace_1963396 : CollatzResearch.WordTrace tailWord_1963396 prefixEnd_1963396 448073716940046861253561 := by
  unfold tailWord_1963396
  simp only [CollatzResearch.WordTrace]
  refine ⟨35805467597479544092807021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47740623463306058790409361 35805467597479544092807021)
  ·
    refine ⟨13427050349054829034802633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35805467597479544092807021 13427050349054829034802633)
    ·
      refine ⟨10070287761791121776101975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13427050349054829034802633 10070287761791121776101975)
      ·
        refine ⟨15105431642686682664152963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10070287761791121776101975 15105431642686682664152963)
        ·
          refine ⟨22658147464030023996229445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15105431642686682664152963 22658147464030023996229445)
          ·
            refine ⟨4248402649505629499293021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22658147464030023996229445 4248402649505629499293021)
            ·
              refine ⟨1593150993564611062234883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4248402649505629499293021 1593150993564611062234883)
              ·
                refine ⟨2389726490346916593352325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1593150993564611062234883 2389726490346916593352325)
                ·
                  refine ⟨448073716940046861253561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2389726490346916593352325 448073716940046861253561)
                  ·
                    rfl

theorem cell21_1963396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_1963396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963396 prefixEnd_1963396 := by exact prefixLift 1963396
  have htrace : WordTrace (prefixWord ++ tailWord_1963396) baseStart_1963396 baseEnd_1963396 := by
    simpa [prefixWord, tailWord_1963396, baseEnd_1963396] using wordTrace_append hprefix tailTrace_1963396
  have hstable : (prefixWord ++ tailWord_1963396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963396).length < 2 ^ (prefixWord ++ tailWord_1963396).sum := by decide
  have hdescent : baseEnd_1963396 < baseStart_1963396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963497 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 10]
def baseStart_1963497 : Nat := 118140960795 + 1963497 * 2 ^ 59
def prefixEnd_1963497 : Nat := 4983230072969 + 3 ^ 40 * 1963497 * 2
def baseEnd_1963497 : Nat := 448096766516093130070021

theorem tailTrace_1963497 : CollatzResearch.WordTrace tailWord_1963497 prefixEnd_1963497 448096766516093130070021 := by
  unfold tailWord_1963497
  simp only [CollatzResearch.WordTrace]
  refine ⟨71614618967593182435040745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47743079311728788290027163 71614618967593182435040745)
  ·
    refine ⟨53710964225694886826280559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71614618967593182435040745 53710964225694886826280559)
    ·
      refine ⟨80566446338542330239420839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53710964225694886826280559 80566446338542330239420839)
      ·
        refine ⟨120849669507813495359131259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80566446338542330239420839 120849669507813495359131259)
        ·
          refine ⟨181274504261720243038696889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120849669507813495359131259 181274504261720243038696889)
          ·
            refine ⟨135955878196290182279022667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181274504261720243038696889 135955878196290182279022667)
            ·
              refine ⟨203933817294435273418534001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135955878196290182279022667 203933817294435273418534001)
              ·
                refine ⟨152950362970826455063900501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203933817294435273418534001 152950362970826455063900501)
                ·
                  refine ⟨448096766516093130070021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 152950362970826455063900501 448096766516093130070021)
                  ·
                    rfl

theorem cell21_1963497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_1963497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963497 prefixEnd_1963497 := by exact prefixLift 1963497
  have htrace : WordTrace (prefixWord ++ tailWord_1963497) baseStart_1963497 baseEnd_1963497 := by
    simpa [prefixWord, tailWord_1963497, baseEnd_1963497] using wordTrace_append hprefix tailTrace_1963497
  have hstable : (prefixWord ++ tailWord_1963497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963497).length < 2 ^ (prefixWord ++ tailWord_1963497).sum := by decide
  have hdescent : baseEnd_1963497 < baseStart_1963497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963514 : List Nat := [3, 1, 1, 1, 1, 2, 3, 5, 4]
def baseStart_1963514 : Nat := 118140960795 + 1963514 * 2 ^ 59
def prefixEnd_1963514 : Nat := 4983230072969 + 3 ^ 40 * 1963514 * 2
def baseEnd_1963514 : Nat := 448100646147704878286653

theorem tailTrace_1963514 : CollatzResearch.WordTrace tailWord_1963514 prefixEnd_1963514 448100646147704878286653 := by
  unfold tailWord_1963514
  simp only [CollatzResearch.WordTrace]
  refine ⟨17903809752132898584602399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47743492672354396225606397 17903809752132898584602399)
  ·
    refine ⟨26855714628199347876903599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17903809752132898584602399 26855714628199347876903599)
    ·
      refine ⟨40283571942299021815355399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26855714628199347876903599 40283571942299021815355399)
      ·
        refine ⟨60425357913448532723033099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40283571942299021815355399 60425357913448532723033099)
        ·
          refine ⟨90638036870172799084549649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60425357913448532723033099 90638036870172799084549649)
          ·
            refine ⟨67978527652629599313412237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90638036870172799084549649 67978527652629599313412237)
            ·
              refine ⟨25491947869736099742529589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67978527652629599313412237 25491947869736099742529589)
              ·
                refine ⟨2389870112787759350862149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25491947869736099742529589 2389870112787759350862149)
                ·
                  refine ⟨448100646147704878286653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2389870112787759350862149 448100646147704878286653)
                  ·
                    rfl

theorem cell21_1963514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_1963514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963514 prefixEnd_1963514 := by exact prefixLift 1963514
  have htrace : WordTrace (prefixWord ++ tailWord_1963514) baseStart_1963514 baseEnd_1963514 := by
    simpa [prefixWord, tailWord_1963514, baseEnd_1963514] using wordTrace_append hprefix tailTrace_1963514
  have hstable : (prefixWord ++ tailWord_1963514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963514).length < 2 ^ (prefixWord ++ tailWord_1963514).sum := by decide
  have hdescent : baseEnd_1963514 < baseStart_1963514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963528 : List Nat := [2, 1, 3, 2, 1, 1, 2, 9]
def baseStart_1963528 : Nat := 118140960795 + 1963528 * 2 ^ 59
def prefixEnd_1963528 : Nat := 4983230072969 + 3 ^ 40 * 1963528 * 2
def baseEnd_1963528 : Nat := 149367947046147988351097

theorem tailTrace_1963528 : CollatzResearch.WordTrace tailWord_1963528 prefixEnd_1963528 149367947046147988351097 := by
  unfold tailWord_1963528
  simp only [CollatzResearch.WordTrace]
  refine ⟨35807874815240437364709619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47743833086987249819612825 35807874815240437364709619)
  ·
    refine ⟨53711812222860656047064429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35807874815240437364709619 53711812222860656047064429)
    ·
      refine ⟨20141929583572746017649161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53711812222860656047064429 20141929583572746017649161)
      ·
        refine ⟨15106447187679559513236871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20141929583572746017649161 15106447187679559513236871)
        ·
          refine ⟨22659670781519339269855307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15106447187679559513236871 22659670781519339269855307)
          ·
            refine ⟨33989506172279008904782961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22659670781519339269855307 33989506172279008904782961)
            ·
              refine ⟨25492129629209256678587221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33989506172279008904782961 25492129629209256678587221)
              ·
                refine ⟨149367947046147988351097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25492129629209256678587221 149367947046147988351097)
                ·
                  rfl

theorem cell21_1963528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 9].length) (baseStart_1963528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963528 prefixEnd_1963528 := by exact prefixLift 1963528
  have htrace : WordTrace (prefixWord ++ tailWord_1963528) baseStart_1963528 baseEnd_1963528 := by
    simpa [prefixWord, tailWord_1963528, baseEnd_1963528] using wordTrace_append hprefix tailTrace_1963528
  have hstable : (prefixWord ++ tailWord_1963528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963528).length < 2 ^ (prefixWord ++ tailWord_1963528).sum := by decide
  have hdescent : baseEnd_1963528 < baseStart_1963528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963534 : List Nat := [4, 1, 1, 2, 4, 1, 2, 3, 3]
def baseStart_1963534 : Nat := 118140960795 + 1963534 * 2 ^ 59
def prefixEnd_1963534 : Nat := 4983230072969 + 3 ^ 40 * 1963534 * 2
def baseEnd_1963534 : Nat := 448105210420189287953279

theorem tailTrace_1963534 : CollatzResearch.WordTrace tailWord_1963534 prefixEnd_1963534 448105210420189287953279 := by
  unfold tailWord_1963534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8951996058557392219267207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47743978978972758502758437 8951996058557392219267207)
  ·
    refine ⟨13427994087836088328900811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8951996058557392219267207 13427994087836088328900811)
    ·
      refine ⟨20141991131754132493351217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13427994087836088328900811 20141991131754132493351217)
      ·
        refine ⟨15106493348815599370013413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20141991131754132493351217 15106493348815599370013413)
        ·
          refine ⟨2832467502902924881877515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15106493348815599370013413 2832467502902924881877515)
          ·
            refine ⟨4248701254354387322816273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2832467502902924881877515 4248701254354387322816273)
            ·
              refine ⟨3186525940765790492112205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4248701254354387322816273 3186525940765790492112205)
              ·
                refine ⟨1194947227787171434542077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3186525940765790492112205 1194947227787171434542077)
                ·
                  refine ⟨448105210420189287953279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194947227787171434542077 448105210420189287953279)
                  ·
                    rfl

theorem cell21_1963534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_1963534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963534 prefixEnd_1963534 := by exact prefixLift 1963534
  have htrace : WordTrace (prefixWord ++ tailWord_1963534) baseStart_1963534 baseEnd_1963534 := by
    simpa [prefixWord, tailWord_1963534, baseEnd_1963534] using wordTrace_append hprefix tailTrace_1963534
  have hstable : (prefixWord ++ tailWord_1963534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963534).length < 2 ^ (prefixWord ++ tailWord_1963534).sum := by decide
  have hdescent : baseEnd_1963534 < baseStart_1963534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963621 : List Nat := [1, 3, 1, 3, 3, 2, 2, 6]
def baseStart_1963621 : Nat := 118140960795 + 1963621 * 2 ^ 59
def prefixEnd_1963621 : Nat := 4983230072969 + 3 ^ 40 * 1963621 * 2
def baseEnd_1963621 : Nat := 149375021668498823334367

theorem tailTrace_1963621 : CollatzResearch.WordTrace tailWord_1963621 prefixEnd_1963621 149375021668498823334367 := by
  unfold tailWord_1963621
  simp only [CollatzResearch.WordTrace]
  refine ⟨71619141619143951612554717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47746094412762634408369811 71619141619143951612554717)
  ·
    refine ⟨26857178107178981854708019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71619141619143951612554717 26857178107178981854708019)
    ·
      refine ⟨40285767160768472782062029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26857178107178981854708019 40285767160768472782062029)
      ·
        refine ⟨15107162685288177293273261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40285767160768472782062029 15107162685288177293273261)
        ·
          refine ⟨5665186006983066484977473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15107162685288177293273261 5665186006983066484977473)
          ·
            refine ⟨4248889505237299863733105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5665186006983066484977473 4248889505237299863733105)
            ·
              refine ⟨3186667128927974897799829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4248889505237299863733105 3186667128927974897799829)
              ·
                refine ⟨149375021668498823334367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3186667128927974897799829 149375021668498823334367)
                ·
                  rfl

theorem cell21_1963621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 6].length) (baseStart_1963621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963621 prefixEnd_1963621 := by exact prefixLift 1963621
  have htrace : WordTrace (prefixWord ++ tailWord_1963621) baseStart_1963621 baseEnd_1963621 := by
    simpa [prefixWord, tailWord_1963621, baseEnd_1963621] using wordTrace_append hprefix tailTrace_1963621
  have hstable : (prefixWord ++ tailWord_1963621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963621).length < 2 ^ (prefixWord ++ tailWord_1963621).sum := by decide
  have hdescent : baseEnd_1963621 < baseStart_1963621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963624 : List Nat := [2, 1, 4, 3, 1, 1, 4, 1, 4]
def baseStart_1963624 : Nat := 118140960795 + 1963624 * 2 ^ 59
def prefixEnd_1963624 : Nat := 4983230072969 + 3 ^ 40 * 1963624 * 2
def baseEnd_1963624 : Nat := 448125749646369131453095

theorem tailTrace_1963624 : CollatzResearch.WordTrace tailWord_1963624 prefixEnd_1963624 448125749646369131453095 := by
  unfold tailWord_1963624
  simp only [CollatzResearch.WordTrace]
  refine ⟨35809625519066541562456963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47746167358755388749942617 35809625519066541562456963)
  ·
    refine ⟨53714438278599812343685445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35809625519066541562456963 53714438278599812343685445)
    ·
      refine ⟨10071457177237464814441021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53714438278599812343685445 10071457177237464814441021)
      ·
        refine ⟨3776796441464049305415383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10071457177237464814441021 3776796441464049305415383)
        ·
          refine ⟨5665194662196073958123075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3776796441464049305415383 5665194662196073958123075)
          ·
            refine ⟨8497791993294110937184613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5665194662196073958123075 8497791993294110937184613)
            ·
              refine ⟨1593335998742645800722115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8497791993294110937184613 1593335998742645800722115)
              ·
                refine ⟨2390003998113968701083173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1593335998742645800722115 2390003998113968701083173)
                ·
                  refine ⟨448125749646369131453095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2390003998113968701083173 448125749646369131453095)
                  ·
                    rfl

theorem cell21_1963624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 4].length) (baseStart_1963624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963624 prefixEnd_1963624 := by exact prefixLift 1963624
  have htrace : WordTrace (prefixWord ++ tailWord_1963624) baseStart_1963624 baseEnd_1963624 := by
    simpa [prefixWord, tailWord_1963624, baseEnd_1963624] using wordTrace_append hprefix tailTrace_1963624
  have hstable : (prefixWord ++ tailWord_1963624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963624).length < 2 ^ (prefixWord ++ tailWord_1963624).sum := by decide
  have hdescent : baseEnd_1963624 < baseStart_1963624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963734 : List Nat := [5, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_1963734 : Nat := 118140960795 + 1963734 * 2 ^ 59
def prefixEnd_1963734 : Nat := 4983230072969 + 3 ^ 40 * 1963734 * 2
def baseEnd_1963734 : Nat := 448150853145033384619537

theorem tailTrace_1963734 : CollatzResearch.WordTrace tailWord_1963734 prefixEnd_1963734 448150853145033384619537 := by
  unfold tailWord_1963734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4476453941733410744463641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47748842045156381274278837 4476453941733410744463641)
  ·
    refine ⟨3357340456300058058347731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4476453941733410744463641 3357340456300058058347731)
    ·
      refine ⟨5036010684450087087521597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3357340456300058058347731 5036010684450087087521597)
      ·
        refine ⟨1888504006668782657820599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5036010684450087087521597 1888504006668782657820599)
        ·
          refine ⟨2832756010003173986730899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1888504006668782657820599 2832756010003173986730899)
          ·
            refine ⟨4249134015004760980096349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2832756010003173986730899 4249134015004760980096349)
            ·
              refine ⟨1593425255626785367536131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4249134015004760980096349 1593425255626785367536131)
              ·
                refine ⟨2390137883440178051304197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1593425255626785367536131 2390137883440178051304197)
                ·
                  refine ⟨448150853145033384619537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2390137883440178051304197 448150853145033384619537)
                  ·
                    rfl

theorem cell21_1963734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_1963734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963734 prefixEnd_1963734 := by exact prefixLift 1963734
  have htrace : WordTrace (prefixWord ++ tailWord_1963734) baseStart_1963734 baseEnd_1963734 := by
    simpa [prefixWord, tailWord_1963734, baseEnd_1963734] using wordTrace_append hprefix tailTrace_1963734
  have hstable : (prefixWord ++ tailWord_1963734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963734).length < 2 ^ (prefixWord ++ tailWord_1963734).sum := by decide
  have hdescent : baseEnd_1963734 < baseStart_1963734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963787 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 5]
def baseStart_1963787 : Nat := 118140960795 + 1963787 * 2 ^ 59
def prefixEnd_1963787 : Nat := 4983230072969 + 3 ^ 40 * 1963787 * 2
def baseEnd_1963787 : Nat := 448162948467117070236095

theorem tailTrace_1963787 : CollatzResearch.WordTrace tailWord_1963787 prefixEnd_1963787 448162948467117070236095 := by
  unfold tailWord_1963787
  simp only [CollatzResearch.WordTrace]
  refine ⟨71625196136542561963097615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47750130757695041308731743 71625196136542561963097615)
  ·
    refine ⟨107437794204813842944646423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71625196136542561963097615 107437794204813842944646423)
    ·
      refine ⟨161156691307220764416969635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107437794204813842944646423 161156691307220764416969635)
      ·
        refine ⟨241735036960831146625454453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161156691307220764416969635 241735036960831146625454453)
        ·
          refine ⟨22662659715077919996136355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241735036960831146625454453 22662659715077919996136355)
          ·
            refine ⟨33993989572616879994204533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22662659715077919996136355 33993989572616879994204533)
            ·
              refine ⟨3186936522432832499456675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33993989572616879994204533 3186936522432832499456675)
              ·
                refine ⟨4780404783649248749185013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186936522432832499456675 4780404783649248749185013)
                ·
                  refine ⟨448162948467117070236095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4780404783649248749185013 448162948467117070236095)
                  ·
                    rfl

theorem cell21_1963787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 5].length) (baseStart_1963787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963787 prefixEnd_1963787 := by exact prefixLift 1963787
  have htrace : WordTrace (prefixWord ++ tailWord_1963787) baseStart_1963787 baseEnd_1963787 := by
    simpa [prefixWord, tailWord_1963787, baseEnd_1963787] using wordTrace_append hprefix tailTrace_1963787
  have hstable : (prefixWord ++ tailWord_1963787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963787).length < 2 ^ (prefixWord ++ tailWord_1963787).sum := by decide
  have hdescent : baseEnd_1963787 < baseStart_1963787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
