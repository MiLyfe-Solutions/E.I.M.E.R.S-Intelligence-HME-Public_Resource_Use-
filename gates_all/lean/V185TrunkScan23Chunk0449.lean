import V185TrunkScan23Chunk0448

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2655645 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 1, 6, 2]
def baseStart_2655645 : Nat := 118140960795 + 2655645 * 2 ^ 59
def prefixEnd_2655645 : Nat := 4983230072969 + 3 ^ 40 * 2655645 * 2
def baseEnd_2655645 : Nat := 1363622332709367510424417

theorem tailTrace_2655645 : CollatzResearch.WordTrace tailWord_2655645 prefixEnd_2655645 1363622332709367510424417 := by
  unfold tailWord_2655645
  simp only [CollatzResearch.WordTrace]
  refine ⟨96859330464059187902304389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64572886976039458601536259 96859330464059187902304389)
  ·
    refine ⟨18161124462011097731682073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96859330464059187902304389 18161124462011097731682073)
    ·
      refine ⟨13620843346508323298761555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18161124462011097731682073 13620843346508323298761555)
      ·
        refine ⟨20431265019762484948142333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13620843346508323298761555 20431265019762484948142333)
        ·
          refine ⟨7661724382410931855553375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20431265019762484948142333 7661724382410931855553375)
          ·
            refine ⟨11492586573616397783330063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7661724382410931855553375 11492586573616397783330063)
            ·
              refine ⟨17238879860424596674995095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11492586573616397783330063 17238879860424596674995095)
              ·
                refine ⟨25858319790636895012492643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17238879860424596674995095 25858319790636895012492643)
                ·
                  refine ⟨38787479685955342518738965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25858319790636895012492643 38787479685955342518738965)
                  ·
                    refine ⟨1818163110279156680565889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38787479685955342518738965 1818163110279156680565889)
                    ·
                      refine ⟨1363622332709367510424417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1818163110279156680565889 1363622332709367510424417)
                      ·
                        rfl

theorem cell23_2655645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_2655645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655645 prefixEnd_2655645 := by exact prefixLift 2655645
  have htrace : WordTrace (prefixWord ++ tailWord_2655645) baseStart_2655645 baseEnd_2655645 := by
    simpa [prefixWord, tailWord_2655645, baseEnd_2655645] using wordTrace_append hprefix tailTrace_2655645
  have hstable : (prefixWord ++ tailWord_2655645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655645).length < 2 ^ (prefixWord ++ tailWord_2655645).sum := by decide
  have hdescent : baseEnd_2655645 < baseStart_2655645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655648 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 3]
def baseStart_2655648 : Nat := 118140960795 + 2655648 * 2 ^ 59
def prefixEnd_2655648 : Nat := 4983230072969 + 3 ^ 40 * 2655648 * 2
def baseEnd_2655648 : Nat := 1363623873151330998686903

theorem tailTrace_2655648 : CollatzResearch.WordTrace tailWord_2655648 prefixEnd_2655648 1363623873151330998686903 := by
  unfold tailWord_2655648
  simp only [CollatzResearch.WordTrace]
  refine ⟨48429719941524159707331799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64572959922032212943109065 48429719941524159707331799)
  ·
    refine ⟨72644579912286239560997699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48429719941524159707331799 72644579912286239560997699)
    ·
      refine ⟨108966869868429359341496549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72644579912286239560997699 108966869868429359341496549)
      ·
        refine ⟨20431288100330504876530603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108966869868429359341496549 20431288100330504876530603)
        ·
          refine ⟨30646932150495757314795905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20431288100330504876530603 30646932150495757314795905)
          ·
            refine ⟨22985199112871817986096929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30646932150495757314795905 22985199112871817986096929)
            ·
              refine ⟨17238899334653863489572697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22985199112871817986096929 17238899334653863489572697)
              ·
                refine ⟨12929174500990397617179523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17238899334653863489572697 12929174500990397617179523)
                ·
                  refine ⟨19393761751485596425769285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12929174500990397617179523 19393761751485596425769285)
                  ·
                    refine ⟨3636330328403549329831741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19393761751485596425769285 3636330328403549329831741)
                    ·
                      refine ⟨1363623873151330998686903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3636330328403549329831741 1363623873151330998686903)
                      ·
                        rfl

theorem cell23_2655648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_2655648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655648 prefixEnd_2655648 := by exact prefixLift 2655648
  have htrace : WordTrace (prefixWord ++ tailWord_2655648) baseStart_2655648 baseEnd_2655648 := by
    simpa [prefixWord, tailWord_2655648, baseEnd_2655648] using wordTrace_append hprefix tailTrace_2655648
  have hstable : (prefixWord ++ tailWord_2655648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655648).length < 2 ^ (prefixWord ++ tailWord_2655648).sum := by decide
  have hdescent : baseEnd_2655648 < baseStart_2655648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655655 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 3, 4]
def baseStart_2655655 : Nat := 118140960795 + 2655655 * 2 ^ 59
def prefixEnd_2655655 : Nat := 4983230072969 + 3 ^ 40 * 2655655 * 2
def baseEnd_2655655 : Nat := 454542489171970823766457

theorem tailTrace_2655655 : CollatzResearch.WordTrace tailWord_2655655 prefixEnd_2655655 454542489171970823766457 := by
  unfold tailWord_2655655
  simp only [CollatzResearch.WordTrace]
  refine ⟨96859695194022959610168419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64573130129348639740112279 96859695194022959610168419)
  ·
    refine ⟨145289542791034439415252629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96859695194022959610168419 145289542791034439415252629)
    ·
      refine ⟨6810447318329739347589967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 145289542791034439415252629 6810447318329739347589967)
      ·
        refine ⟨10215670977494609021384951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6810447318329739347589967 10215670977494609021384951)
        ·
          refine ⟨15323506466241913532077427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10215670977494609021384951 15323506466241913532077427)
          ·
            refine ⟨22985259699362870298116141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15323506466241913532077427 22985259699362870298116141)
            ·
              refine ⟨8619472387261076361793553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22985259699362870298116141 8619472387261076361793553)
              ·
                refine ⟨6464604290445807271345165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8619472387261076361793553 6464604290445807271345165)
                ·
                  refine ⟨2424226608917177726754437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6464604290445807271345165 2424226608917177726754437)
                  ·
                    refine ⟨454542489171970823766457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2424226608917177726754437 454542489171970823766457)
                    ·
                      rfl

theorem cell23_2655655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_2655655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655655 prefixEnd_2655655 := by exact prefixLift 2655655
  have htrace : WordTrace (prefixWord ++ tailWord_2655655) baseStart_2655655 baseEnd_2655655 := by
    simpa [prefixWord, tailWord_2655655, baseEnd_2655655] using wordTrace_append hprefix tailTrace_2655655
  have hstable : (prefixWord ++ tailWord_2655655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655655).length < 2 ^ (prefixWord ++ tailWord_2655655).sum := by decide
  have hdescent : baseEnd_2655655 < baseStart_2655655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655695 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 3, 1, 3]
def baseStart_2655695 : Nat := 118140960795 + 2655695 * 2 ^ 59
def prefixEnd_2655695 : Nat := 4983230072969 + 3 ^ 40 * 2655695 * 2
def baseEnd_2655695 : Nat := 1363648006742092314799187

theorem tailTrace_2655695 : CollatzResearch.WordTrace tailWord_2655695 prefixEnd_2655695 1363648006742092314799187 := by
  unfold tailWord_2655695
  simp only [CollatzResearch.WordTrace]
  refine ⟨96861154113878046441624539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64574102742585364294416359 96861154113878046441624539)
  ·
    refine ⟨145291731170817069662436809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96861154113878046441624539 145291731170817069662436809)
    ·
      refine ⟨108968798378112802246827607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145291731170817069662436809 108968798378112802246827607)
      ·
        refine ⟨163453197567169203370241411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108968798378112802246827607 163453197567169203370241411)
        ·
          refine ⟨245179796350753805055362117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163453197567169203370241411 245179796350753805055362117)
          ·
            refine ⟨45971211815766338447880397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245179796350753805055362117 45971211815766338447880397)
            ·
              refine ⟨17239204430912376917955149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45971211815766338447880397 17239204430912376917955149)
              ·
                refine ⟨6464701661592141344233181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17239204430912376917955149 6464701661592141344233181)
                ·
                  refine ⟨2424263123097053004087443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6464701661592141344233181 2424263123097053004087443)
                  ·
                    refine ⟨3636394684645579506131165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2424263123097053004087443 3636394684645579506131165)
                    ·
                      refine ⟨1363648006742092314799187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3636394684645579506131165 1363648006742092314799187)
                      ·
                        rfl

theorem cell23_2655695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 1, 3].length) (baseStart_2655695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655695 prefixEnd_2655695 := by exact prefixLift 2655695
  have htrace : WordTrace (prefixWord ++ tailWord_2655695) baseStart_2655695 baseEnd_2655695 := by
    simpa [prefixWord, tailWord_2655695, baseEnd_2655695] using wordTrace_append hprefix tailTrace_2655695
  have hstable : (prefixWord ++ tailWord_2655695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655695).length < 2 ^ (prefixWord ++ tailWord_2655695).sum := by decide
  have hdescent : baseEnd_2655695 < baseStart_2655695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655705 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 1, 5, 2]
def baseStart_2655705 : Nat := 118140960795 + 2655705 * 2 ^ 59
def prefixEnd_2655705 : Nat := 4983230072969 + 3 ^ 40 * 2655705 * 2
def baseEnd_2655705 : Nat := 1363653141548637275674141

theorem tailTrace_2655705 : CollatzResearch.WordTrace tailWord_2655705 prefixEnd_2655705 1363653141548637275674141 := by
  unfold tailWord_2655705
  simp only [CollatzResearch.WordTrace]
  refine ⟨96861518843841818149488569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64574345895894545432992379 96861518843841818149488569)
  ·
    refine ⟨72646139132881363612116427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96861518843841818149488569 72646139132881363612116427)
    ·
      refine ⟨108969208699322045418174641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72646139132881363612116427 108969208699322045418174641)
      ·
        refine ⟨81726906524491534063630981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108969208699322045418174641 81726906524491534063630981)
        ·
          refine ⟨15323794973342162636930809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81726906524491534063630981 15323794973342162636930809)
          ·
            refine ⟨11492846230006621977698107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15323794973342162636930809 11492846230006621977698107)
            ·
              refine ⟨17239269345009932966547161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11492846230006621977698107 17239269345009932966547161)
              ·
                refine ⟨12929452008757449724910371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17239269345009932966547161 12929452008757449724910371)
                ·
                  refine ⟨19394178013136174587365557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12929452008757449724910371 19394178013136174587365557)
                  ·
                    refine ⟨1818204188731516367565521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19394178013136174587365557 1818204188731516367565521)
                    ·
                      refine ⟨1363653141548637275674141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1818204188731516367565521 1363653141548637275674141)
                      ·
                        rfl

theorem cell23_2655705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 5, 2].length) (baseStart_2655705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655705 prefixEnd_2655705 := by exact prefixLift 2655705
  have htrace : WordTrace (prefixWord ++ tailWord_2655705) baseStart_2655705 baseEnd_2655705 := by
    simpa [prefixWord, tailWord_2655705, baseEnd_2655705] using wordTrace_append hprefix tailTrace_2655705
  have hstable : (prefixWord ++ tailWord_2655705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655705).length < 2 ^ (prefixWord ++ tailWord_2655705).sum := by decide
  have hdescent : baseEnd_2655705 < baseStart_2655705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655715 : List Nat := [1, 1, 1, 6, 2, 1, 1, 4, 1, 5]
def baseStart_2655715 : Nat := 118140960795 + 2655715 * 2 ^ 59
def prefixEnd_2655715 : Nat := 4983230072969 + 3 ^ 40 * 2655715 * 2
def baseEnd_2655715 : Nat := 454552758785060745516365

theorem tailTrace_2655715 : CollatzResearch.WordTrace tailWord_2655715 prefixEnd_2655715 454552758785060745516365 := by
  unfold tailWord_2655715
  simp only [CollatzResearch.WordTrace]
  refine ⟨96861883573805589857352599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64574589049203726571568399 96861883573805589857352599)
  ·
    refine ⟨145292825360708384786028899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96861883573805589857352599 145292825360708384786028899)
    ·
      refine ⟨217939238041062577179043349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145292825360708384786028899 217939238041062577179043349)
      ·
        refine ⟨10215901783174808305267657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 217939238041062577179043349 10215901783174808305267657)
        ·
          refine ⟨7661926337381106228950743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10215901783174808305267657 7661926337381106228950743)
          ·
            refine ⟨11492889506071659343426115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7661926337381106228950743 11492889506071659343426115)
            ·
              refine ⟨17239334259107489015139173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11492889506071659343426115 17239334259107489015139173)
              ·
                refine ⟨3232375173582654190338595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17239334259107489015139173 3232375173582654190338595)
                ·
                  refine ⟨4848562760373981285507893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3232375173582654190338595 4848562760373981285507893)
                  ·
                    refine ⟨454552758785060745516365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4848562760373981285507893 454552758785060745516365)
                    ·
                      rfl

theorem cell23_2655715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 5].length) (baseStart_2655715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655715 prefixEnd_2655715 := by exact prefixLift 2655715
  have htrace : WordTrace (prefixWord ++ tailWord_2655715) baseStart_2655715 baseEnd_2655715 := by
    simpa [prefixWord, tailWord_2655715, baseEnd_2655715] using wordTrace_append hprefix tailTrace_2655715
  have hstable : (prefixWord ++ tailWord_2655715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655715).length < 2 ^ (prefixWord ++ tailWord_2655715).sum := by decide
  have hdescent : baseEnd_2655715 < baseStart_2655715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655729 : List Nat := [1, 2, 2, 2, 3, 2, 3, 3, 1, 1, 3]
def baseStart_2655729 : Nat := 118140960795 + 2655729 * 2 ^ 59
def prefixEnd_2655729 : Nat := 4983230072969 + 3 ^ 40 * 2655729 * 2
def baseEnd_2655729 : Nat := 1363665465084345181774031

theorem tailTrace_2655729 : CollatzResearch.WordTrace tailWord_2655729 prefixEnd_2655729 1363665465084345181774031 := by
  unfold tailWord_2655729
  simp only [CollatzResearch.WordTrace]
  refine ⟨96862394195754870248362241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64574929463836580165574827 96862394195754870248362241)
  ·
    refine ⟨72646795646816152686271681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96862394195754870248362241 72646795646816152686271681)
    ·
      refine ⟨54485096735112114514703761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72646795646816152686271681 54485096735112114514703761)
      ·
        refine ⟨40863822551334085886027821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54485096735112114514703761 40863822551334085886027821)
        ·
          refine ⟨15323933456750282207260433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40863822551334085886027821 15323933456750282207260433)
          ·
            refine ⟨11492950092562711655445325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15323933456750282207260433 11492950092562711655445325)
            ·
              refine ⟨4309856284711016870791997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11492950092562711655445325 4309856284711016870791997)
              ·
                refine ⟨1616196106766631326546999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4309856284711016870791997 1616196106766631326546999)
                ·
                  refine ⟨2424294160149946989820499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616196106766631326546999 2424294160149946989820499)
                  ·
                    refine ⟨3636441240224920484730749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2424294160149946989820499 3636441240224920484730749)
                    ·
                      refine ⟨1363665465084345181774031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3636441240224920484730749 1363665465084345181774031)
                      ·
                        rfl

theorem cell23_2655729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_2655729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655729 prefixEnd_2655729 := by exact prefixLift 2655729
  have htrace : WordTrace (prefixWord ++ tailWord_2655729) baseStart_2655729 baseEnd_2655729 := by
    simpa [prefixWord, tailWord_2655729, baseEnd_2655729] using wordTrace_append hprefix tailTrace_2655729
  have hstable : (prefixWord ++ tailWord_2655729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655729).length < 2 ^ (prefixWord ++ tailWord_2655729).sum := by decide
  have hdescent : baseEnd_2655729 < baseStart_2655729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655746 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_2655746 : Nat := 118140960795 + 2655746 * 2 ^ 59
def prefixEnd_2655746 : Nat := 4983230072969 + 3 ^ 40 * 2655746 * 2
def baseEnd_2655746 : Nat := 1363674194255471615261453

theorem tailTrace_2655746 : CollatzResearch.WordTrace tailWord_2655746 prefixEnd_2655746 1363674194255471615261453 := by
  unfold tailWord_2655746
  simp only [CollatzResearch.WordTrace]
  refine ⟨24215753559173320537932773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64575342824462188101154061 24215753559173320537932773)
  ·
    refine ⟨4540453792344997600862395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24215753559173320537932773 4540453792344997600862395)
    ·
      refine ⟨6810680688517496401293593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4540453792344997600862395 6810680688517496401293593)
      ·
        refine ⟨5108010516388122300970195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6810680688517496401293593 5108010516388122300970195)
        ·
          refine ⟨7662015774582183451455293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5108010516388122300970195 7662015774582183451455293)
          ·
            refine ⟨2873255915468318794295735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7662015774582183451455293 2873255915468318794295735)
            ·
              refine ⟨4309883873202478191443603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2873255915468318794295735 4309883873202478191443603)
              ·
                refine ⟨6464825809803717287165405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4309883873202478191443603 6464825809803717287165405)
                ·
                  refine ⟨2424309678676393982687027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6464825809803717287165405 2424309678676393982687027)
                  ·
                    refine ⟨3636464518014590974030541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2424309678676393982687027 3636464518014590974030541)
                    ·
                      refine ⟨1363674194255471615261453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3636464518014590974030541 1363674194255471615261453)
                      ·
                        rfl

theorem cell23_2655746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_2655746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655746 prefixEnd_2655746 := by exact prefixLift 2655746
  have htrace : WordTrace (prefixWord ++ tailWord_2655746) baseStart_2655746 baseEnd_2655746 := by
    simpa [prefixWord, tailWord_2655746, baseEnd_2655746] using wordTrace_append hprefix tailTrace_2655746
  have hstable : (prefixWord ++ tailWord_2655746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655746).length < 2 ^ (prefixWord ++ tailWord_2655746).sum := by decide
  have hdescent : baseEnd_2655746 < baseStart_2655746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655786 : List Nat := [3, 1, 4, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_2655786 : Nat := 118140960795 + 2655786 * 2 ^ 59
def prefixEnd_2655786 : Nat := 4983230072969 + 3 ^ 40 * 2655786 * 2
def baseEnd_2655786 : Nat := 1363694733481651458761269

theorem tailTrace_2655786 : CollatzResearch.WordTrace tailWord_2655786 prefixEnd_2655786 1363694733481651458761269 := by
  unfold tailWord_2655786
  simp only [CollatzResearch.WordTrace]
  refine ⟨24216118289137092245796803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64576315437698912655458141 24216118289137092245796803)
  ·
    refine ⟨36324177433705638368695205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24216118289137092245796803 36324177433705638368695205)
    ·
      refine ⟨6810783268819807194130351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36324177433705638368695205 6810783268819807194130351)
      ·
        refine ⟨10216174903229710791195527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6810783268819807194130351 10216174903229710791195527)
        ·
          refine ⟨15324262354844566186793291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10216174903229710791195527 15324262354844566186793291)
          ·
            refine ⟨22986393532266849280189937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15324262354844566186793291 22986393532266849280189937)
            ·
              refine ⟨17239795149200136960142453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22986393532266849280189937 17239795149200136960142453)
              ·
                refine ⟨1616230795237512840013355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17239795149200136960142453 1616230795237512840013355)
                ·
                  refine ⟨2424346192856269260020033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616230795237512840013355 2424346192856269260020033)
                  ·
                    refine ⟨1818259644642201945015025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2424346192856269260020033 1818259644642201945015025)
                    ·
                      refine ⟨1363694733481651458761269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1818259644642201945015025 1363694733481651458761269)
                      ·
                        rfl

theorem cell23_2655786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_2655786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655786 prefixEnd_2655786 := by exact prefixLift 2655786
  have htrace : WordTrace (prefixWord ++ tailWord_2655786) baseStart_2655786 baseEnd_2655786 := by
    simpa [prefixWord, tailWord_2655786, baseEnd_2655786] using wordTrace_append hprefix tailTrace_2655786
  have hstable : (prefixWord ++ tailWord_2655786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655786).length < 2 ^ (prefixWord ++ tailWord_2655786).sum := by decide
  have hdescent : baseEnd_2655786 < baseStart_2655786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655853 : List Nat := [1, 5, 1, 1, 5, 1, 1, 2, 2, 1, 3]
def baseStart_2655853 : Nat := 118140960795 + 2655853 * 2 ^ 59
def prefixEnd_2655853 : Nat := 4983230072969 + 3 ^ 40 * 2655853 * 2
def baseEnd_2655853 : Nat := 1363729136685502696623461

theorem tailTrace_2655853 : CollatzResearch.WordTrace tailWord_2655853 prefixEnd_2655853 1363729136685502696623461 := by
  unfold tailWord_2655853
  simp only [CollatzResearch.WordTrace]
  refine ⟨96866916847305639425876213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64577944564870426283917475 96866916847305639425876213)
  ·
    refine ⟨9081273454434903696175895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96866916847305639425876213 9081273454434903696175895)
    ·
      refine ⟨13621910181652355544263843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9081273454434903696175895 13621910181652355544263843)
      ·
        refine ⟨20432865272478533316395765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13621910181652355544263843 20432865272478533316395765)
        ·
          refine ⟨1915581119294862498412103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20432865272478533316395765 1915581119294862498412103)
          ·
            refine ⟨2873371678942293747618155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1915581119294862498412103 2873371678942293747618155)
            ·
              refine ⟨4310057518413440621427233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2873371678942293747618155 4310057518413440621427233)
              ·
                refine ⟨3232543138810080466070425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4310057518413440621427233 3232543138810080466070425)
                ·
                  refine ⟨2424407354107560349552819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3232543138810080466070425 2424407354107560349552819)
                  ·
                    refine ⟨3636611031161340524329229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2424407354107560349552819 3636611031161340524329229)
                    ·
                      refine ⟨1363729136685502696623461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3636611031161340524329229 1363729136685502696623461)
                      ·
                        rfl

theorem cell23_2655853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_2655853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655853 prefixEnd_2655853 := by exact prefixLift 2655853
  have htrace : WordTrace (prefixWord ++ tailWord_2655853) baseStart_2655853 baseEnd_2655853 := by
    simpa [prefixWord, tailWord_2655853, baseEnd_2655853] using wordTrace_append hprefix tailTrace_2655853
  have hstable : (prefixWord ++ tailWord_2655853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655853).length < 2 ^ (prefixWord ++ tailWord_2655853).sum := by decide
  have hdescent : baseEnd_2655853 < baseStart_2655853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655865 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 7]
def baseStart_2655865 : Nat := 118140960795 + 2655865 * 2 ^ 59
def prefixEnd_2655865 : Nat := 4983230072969 + 3 ^ 40 * 2655865 * 2
def baseEnd_2655865 : Nat := 151526144272595183297045

theorem tailTrace_2655865 : CollatzResearch.WordTrace tailWord_2655865 prefixEnd_2655865 151526144272595183297045 := by
  unfold tailWord_2655865
  simp only [CollatzResearch.WordTrace]
  refine ⟨96867354523262165475313049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64578236348841443650208699 96867354523262165475313049)
  ·
    refine ⟨72650515892446624106484787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96867354523262165475313049 72650515892446624106484787)
    ·
      refine ⟨108975773838669936159727181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72650515892446624106484787 108975773838669936159727181)
      ·
        refine ⟨40865915189501226059897693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108975773838669936159727181 40865915189501226059897693)
        ·
          refine ⟨15324718196062959772461635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40865915189501226059897693 15324718196062959772461635)
          ·
            refine ⟨22987077294094439658692453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15324718196062959772461635 22987077294094439658692453)
            ·
              refine ⟨4310076992642707436004835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22987077294094439658692453 4310076992642707436004835)
              ·
                refine ⟨6465115488964061154007253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4310076992642707436004835 6465115488964061154007253)
                ·
                  refine ⟨151526144272595183297045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6465115488964061154007253 151526144272595183297045)
                  ·
                    rfl

theorem cell23_2655865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 7].length) (baseStart_2655865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655865 prefixEnd_2655865 := by exact prefixLift 2655865
  have htrace : WordTrace (prefixWord ++ tailWord_2655865) baseStart_2655865 baseEnd_2655865 := by
    simpa [prefixWord, tailWord_2655865, baseEnd_2655865] using wordTrace_append hprefix tailTrace_2655865
  have hstable : (prefixWord ++ tailWord_2655865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655865).length < 2 ^ (prefixWord ++ tailWord_2655865).sum := by decide
  have hdescent : baseEnd_2655865 < baseStart_2655865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655876 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 1, 4, 2]
def baseStart_2655876 : Nat := 118140960795 + 2655876 * 2 ^ 59
def prefixEnd_2655876 : Nat := 4983230072969 + 3 ^ 40 * 2655876 * 2
def baseEnd_2655876 : Nat := 1363740946740556106635855

theorem tailTrace_2655876 : CollatzResearch.WordTrace tailWord_2655876 prefixEnd_2655876 1363740946740556106635855 := by
  unfold tailWord_2655876
  simp only [CollatzResearch.WordTrace]
  refine ⟨48433877863111157176981741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64578503817481542902642321 48433877863111157176981741)
  ·
    refine ⟨18162704198666683941368153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48433877863111157176981741 18162704198666683941368153)
    ·
      refine ⟨13622028149000012956026115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18162704198666683941368153 13622028149000012956026115)
      ·
        refine ⟨20433042223500019434039173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13622028149000012956026115 20433042223500019434039173)
        ·
          refine ⟨3831195416906253643882345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20433042223500019434039173 3831195416906253643882345)
          ·
            refine ⟨2873396562679690232911759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3831195416906253643882345 2873396562679690232911759)
            ·
              refine ⟨4310094844019535349367639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2873396562679690232911759 4310094844019535349367639)
              ·
                refine ⟨6465142266029303024051459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4310094844019535349367639 6465142266029303024051459)
                ·
                  refine ⟨9697713399043954536077189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6465142266029303024051459 9697713399043954536077189)
                  ·
                    refine ⟨1818321262320741475514473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9697713399043954536077189 1818321262320741475514473)
                    ·
                      refine ⟨1363740946740556106635855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1818321262320741475514473 1363740946740556106635855)
                      ·
                        rfl

theorem cell23_2655876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_2655876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655876 prefixEnd_2655876 := by exact prefixLift 2655876
  have htrace : WordTrace (prefixWord ++ tailWord_2655876) baseStart_2655876 baseEnd_2655876 := by
    simpa [prefixWord, tailWord_2655876, baseEnd_2655876] using wordTrace_append hprefix tailTrace_2655876
  have hstable : (prefixWord ++ tailWord_2655876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655876).length < 2 ^ (prefixWord ++ tailWord_2655876).sum := by decide
  have hdescent : baseEnd_2655876 < baseStart_2655876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655895 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 1, 7]
def baseStart_2655895 : Nat := 118140960795 + 2655895 * 2 ^ 59
def prefixEnd_2655895 : Nat := 4983230072969 + 3 ^ 40 * 2655895 * 2
def baseEnd_2655895 : Nat := 454583567624330510766089

theorem tailTrace_2655895 : CollatzResearch.WordTrace tailWord_2655895 prefixEnd_2655895 454583567624330510766089 := by
  unfold tailWord_2655895
  simp only [CollatzResearch.WordTrace]
  refine ⟨96868448713153480598905139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64578965808768987065936759 96868448713153480598905139)
  ·
    refine ⟨145302673069730220898357709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96868448713153480598905139 145302673069730220898357709)
    ·
      refine ⟨54488502401148832836884141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145302673069730220898357709 54488502401148832836884141)
      ·
        refine ⟨20433188400430812313831553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54488502401148832836884141 20433188400430812313831553)
        ·
          refine ⟨15324891300323109235373665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20433188400430812313831553 15324891300323109235373665)
          ·
            refine ⟨11493668475242331926530249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15324891300323109235373665 11493668475242331926530249)
            ·
              refine ⟨8620251356431748944897687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11493668475242331926530249 8620251356431748944897687)
              ·
                refine ⟨12930377034647623417346531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8620251356431748944897687 12930377034647623417346531)
                ·
                  refine ⟨19395565551971435126019797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12930377034647623417346531 19395565551971435126019797)
                  ·
                    refine ⟨454583567624330510766089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19395565551971435126019797 454583567624330510766089)
                    ·
                      rfl

theorem cell23_2655895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_2655895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655895 prefixEnd_2655895 := by exact prefixLift 2655895
  have htrace : WordTrace (prefixWord ++ tailWord_2655895) baseStart_2655895 baseEnd_2655895 := by
    simpa [prefixWord, tailWord_2655895, baseEnd_2655895] using wordTrace_append hprefix tailTrace_2655895
  have hstable : (prefixWord ++ tailWord_2655895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655895).length < 2 ^ (prefixWord ++ tailWord_2655895).sum := by decide
  have hdescent : baseEnd_2655895 < baseStart_2655895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655959 : List Nat := [1, 1, 3, 2, 1, 3, 2, 5, 1, 4]
def baseStart_2655959 : Nat := 118140960795 + 2655959 * 2 ^ 59
def prefixEnd_2655959 : Nat := 4983230072969 + 3 ^ 40 * 2655959 * 2
def baseEnd_2655959 : Nat := 454594521878293093965991

theorem tailTrace_2655959 : CollatzResearch.WordTrace tailWord_2655959 prefixEnd_2655959 454594521878293093965991 := by
  unfold tailWord_2655959
  simp only [CollatzResearch.WordTrace]
  refine ⟨96870782984921619529234931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64580521989947746352823287 96870782984921619529234931)
  ·
    refine ⟨145306174477382429293852397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96870782984921619529234931 145306174477382429293852397)
    ·
      refine ⟨54489815429018410985194649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145306174477382429293852397 54489815429018410985194649)
      ·
        refine ⟨40867361571763808238895987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54489815429018410985194649 40867361571763808238895987)
        ·
          refine ⟨61301042357645712358343981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40867361571763808238895987 61301042357645712358343981)
          ·
            refine ⟨22987890884117142134378993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61301042357645712358343981 22987890884117142134378993)
            ·
              refine ⟨17240918163087856600784245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22987890884117142134378993 17240918163087856600784245)
              ·
                refine ⟨1616336077789486556323523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17240918163087856600784245 1616336077789486556323523)
                ·
                  refine ⟨2424504116684229834485285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616336077789486556323523 2424504116684229834485285)
                  ·
                    refine ⟨454594521878293093965991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2424504116684229834485285 454594521878293093965991)
                    ·
                      rfl

theorem cell23_2655959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 1, 4].length) (baseStart_2655959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655959 prefixEnd_2655959 := by exact prefixLift 2655959
  have htrace : WordTrace (prefixWord ++ tailWord_2655959) baseStart_2655959 baseEnd_2655959 := by
    simpa [prefixWord, tailWord_2655959, baseEnd_2655959] using wordTrace_append hprefix tailTrace_2655959
  have hstable : (prefixWord ++ tailWord_2655959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655959).length < 2 ^ (prefixWord ++ tailWord_2655959).sum := by decide
  have hdescent : baseEnd_2655959 < baseStart_2655959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655972 : List Nat := [2, 3, 1, 1, 1, 3, 4, 2, 6]
def baseStart_2655972 : Nat := 118140960795 + 2655972 * 2 ^ 59
def prefixEnd_2655972 : Nat := 4983230072969 + 3 ^ 40 * 2655972 * 2
def baseEnd_2655972 : Nat := 151532248987043081226157

theorem tailTrace_2655972 : CollatzResearch.WordTrace tailWord_2655972 prefixEnd_2655972 151532248987043081226157 := by
  unfold tailWord_2655972
  simp only [CollatzResearch.WordTrace]
  refine ⟨48435628566937261374729085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64580838089249681832972113 48435628566937261374729085)
  ·
    refine ⟨18163360712601473015523407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48435628566937261374729085 18163360712601473015523407)
    ·
      refine ⟨27245041068902209523285111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18163360712601473015523407 27245041068902209523285111)
      ·
        refine ⟨40867561603353314284927667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27245041068902209523285111 40867561603353314284927667)
        ·
          refine ⟨61301342405029971427391501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40867561603353314284927667 61301342405029971427391501)
          ·
            refine ⟨22988003401886239285271813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61301342405029971427391501 22988003401886239285271813)
            ·
              refine ⟨4310250637853669865988465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22988003401886239285271813 4310250637853669865988465)
              ·
                refine ⟨3232687978390252399491349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4310250637853669865988465 3232687978390252399491349)
                ·
                  refine ⟨151532248987043081226157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3232687978390252399491349 151532248987043081226157)
                  ·
                    rfl

theorem cell23_2655972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_2655972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655972 prefixEnd_2655972 := by exact prefixLift 2655972
  have htrace : WordTrace (prefixWord ++ tailWord_2655972) baseStart_2655972 baseEnd_2655972 := by
    simpa [prefixWord, tailWord_2655972, baseEnd_2655972] using wordTrace_append hprefix tailTrace_2655972
  have hstable : (prefixWord ++ tailWord_2655972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655972).length < 2 ^ (prefixWord ++ tailWord_2655972).sum := by decide
  have hdescent : baseEnd_2655972 < baseStart_2655972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655976 : List Nat := [2, 1, 4, 1, 3, 2, 1, 4, 1, 4]
def baseStart_2655976 : Nat := 118140960795 + 2655976 * 2 ^ 59
def prefixEnd_2655976 : Nat := 4983230072969 + 3 ^ 40 * 2655976 * 2
def baseEnd_2655976 : Nat := 454597431602001905128465

theorem tailTrace_2655976 : CollatzResearch.WordTrace tailWord_2655976 prefixEnd_2655976 454597431602001905128465 := by
  unfold tailWord_2655976
  simp only [CollatzResearch.WordTrace]
  refine ⟨48435701512930015716301891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64580935350573354288402521 48435701512930015716301891)
  ·
    refine ⟨72653552269395023574452837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48435701512930015716301891 72653552269395023574452837)
    ·
      refine ⟨13622541050511566920209907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72653552269395023574452837 13622541050511566920209907)
      ·
        refine ⟨20433811575767350380314861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13622541050511566920209907 20433811575767350380314861)
        ·
          refine ⟨7662679340912756392618073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20433811575767350380314861 7662679340912756392618073)
          ·
            refine ⟨5747009505684567294463555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7662679340912756392618073 5747009505684567294463555)
            ·
              refine ⟨8620514258526850941695333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5747009505684567294463555 8620514258526850941695333)
              ·
                refine ⟨1616346423473784551567875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8620514258526850941695333 1616346423473784551567875)
                ·
                  refine ⟨2424519635210676827351813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616346423473784551567875 2424519635210676827351813)
                  ·
                    refine ⟨454597431602001905128465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2424519635210676827351813 454597431602001905128465)
                    ·
                      rfl

theorem cell23_2655976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_2655976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2655976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2655976 prefixEnd_2655976 := by exact prefixLift 2655976
  have htrace : WordTrace (prefixWord ++ tailWord_2655976) baseStart_2655976 baseEnd_2655976 := by
    simpa [prefixWord, tailWord_2655976, baseEnd_2655976] using wordTrace_append hprefix tailTrace_2655976
  have hstable : (prefixWord ++ tailWord_2655976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655976).length < 2 ^ (prefixWord ++ tailWord_2655976).sum := by decide
  have hdescent : baseEnd_2655976 < baseStart_2655976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656015 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 3, 6]
def baseStart_2656015 : Nat := 118140960795 + 2656015 * 2 ^ 59
def prefixEnd_2656015 : Nat := 4983230072969 + 3 ^ 40 * 2656015 * 2
def baseEnd_2656015 : Nat := 454604106850510354265905

theorem tailTrace_2656015 : CollatzResearch.WordTrace tailWord_2656015 prefixEnd_2656015 454604106850510354265905 := by
  unfold tailWord_2656015
  simp only [CollatzResearch.WordTrace]
  refine ⟨96872825472718741093273499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64581883648479160728848999 96872825472718741093273499)
  ·
    refine ⟨145309238209078111639910249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96872825472718741093273499 145309238209078111639910249)
    ·
      refine ⟨108981928656808583729932687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145309238209078111639910249 108981928656808583729932687)
      ·
        refine ⟨163472892985212875594899031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108981928656808583729932687 163472892985212875594899031)
        ·
          refine ⟨245209339477819313392348547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163472892985212875594899031 245209339477819313392348547)
          ·
            refine ⟨367814009216728970088522821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245209339477819313392348547 367814009216728970088522821)
            ·
              refine ⟨68965126728136681891598029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 367814009216728970088522821 68965126728136681891598029)
              ·
                refine ⟨25861922523051255709349261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68965126728136681891598029 25861922523051255709349261)
                ·
                  refine ⟨9698220946144220891005973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25861922523051255709349261 9698220946144220891005973)
                  ·
                    refine ⟨454604106850510354265905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9698220946144220891005973 454604106850510354265905)
                    ·
                      rfl

theorem cell23_2656015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 6].length) (baseStart_2656015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656015 prefixEnd_2656015 := by exact prefixLift 2656015
  have htrace : WordTrace (prefixWord ++ tailWord_2656015) baseStart_2656015 baseEnd_2656015 := by
    simpa [prefixWord, tailWord_2656015, baseEnd_2656015] using wordTrace_append hprefix tailTrace_2656015
  have hstable : (prefixWord ++ tailWord_2656015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656015).length < 2 ^ (prefixWord ++ tailWord_2656015).sum := by decide
  have hdescent : baseEnd_2656015 < baseStart_2656015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656049 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 1, 6]
def baseStart_2656049 : Nat := 118140960795 + 2656049 * 2 ^ 59
def prefixEnd_2656049 : Nat := 4983230072969 + 3 ^ 40 * 2656049 * 2
def baseEnd_2656049 : Nat := 454609926297927976590853

theorem tailTrace_2656049 : CollatzResearch.WordTrace tailWord_2656049 prefixEnd_2656049 454609926297927976590853 := by
  unfold tailWord_2656049
  simp only [CollatzResearch.WordTrace]
  refine ⟨96874065554595564900011201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64582710369730376600007467 96874065554595564900011201)
  ·
    refine ⟨72655549165946673675008401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96874065554595564900011201 72655549165946673675008401)
    ·
      refine ⟨54491661874460005256256301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72655549165946673675008401 54491661874460005256256301)
      ·
        refine ⟨20434373202922501971096113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54491661874460005256256301 20434373202922501971096113)
        ·
          refine ⟨15325779902191876478322085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20434373202922501971096113 15325779902191876478322085)
          ·
            refine ⟨2873583731660976839685391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15325779902191876478322085 2873583731660976839685391)
            ·
              refine ⟨4310375597491465259528087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2873583731660976839685391 4310375597491465259528087)
              ·
                refine ⟨6465563396237197889292131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4310375597491465259528087 6465563396237197889292131)
                ·
                  refine ⟨9698345094355796833938197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6465563396237197889292131 9698345094355796833938197)
                  ·
                    refine ⟨454609926297927976590853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9698345094355796833938197 454609926297927976590853)
                    ·
                      rfl

theorem cell23_2656049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_2656049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656049 prefixEnd_2656049 := by exact prefixLift 2656049
  have htrace : WordTrace (prefixWord ++ tailWord_2656049) baseStart_2656049 baseEnd_2656049 := by
    simpa [prefixWord, tailWord_2656049, baseEnd_2656049] using wordTrace_append hprefix tailTrace_2656049
  have hstable : (prefixWord ++ tailWord_2656049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656049).length < 2 ^ (prefixWord ++ tailWord_2656049).sum := by decide
  have hdescent : baseEnd_2656049 < baseStart_2656049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656056 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 3, 2, 2]
def baseStart_2656056 : Nat := 118140960795 + 2656056 * 2 ^ 59
def prefixEnd_2656056 : Nat := 4983230072969 + 3 ^ 40 * 2656056 * 2
def baseEnd_2656056 : Nat := 1363833373258365402385027

theorem tailTrace_2656056 : CollatzResearch.WordTrace tailWord_2656056 prefixEnd_2656056 1363833373258365402385027 := by
  unfold tailWord_2656056
  simp only [CollatzResearch.WordTrace]
  refine ⟨48437160432785102547758011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64582880577046803397010681 48437160432785102547758011)
  ·
    refine ⟨72655740649177653821637017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48437160432785102547758011 72655740649177653821637017)
    ·
      refine ⟨54491805486883240366227763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72655740649177653821637017 54491805486883240366227763)
      ·
        refine ⟨81737708230324860549341645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54491805486883240366227763 81737708230324860549341645)
        ·
          refine ⟨30651640586371822706003117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81737708230324860549341645 30651640586371822706003117)
          ·
            refine ⟨11494365219889433514751169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30651640586371822706003117 11494365219889433514751169)
            ·
              refine ⟨8620773914917075136063377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11494365219889433514751169 8620773914917075136063377)
              ·
                refine ⟨6465580436187806352047533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8620773914917075136063377 6465580436187806352047533)
                ·
                  refine ⟨2424592663570427382017825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6465580436187806352047533 2424592663570427382017825)
                  ·
                    refine ⟨1818444497677820536513369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2424592663570427382017825 1818444497677820536513369)
                    ·
                      refine ⟨1363833373258365402385027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1818444497677820536513369 1363833373258365402385027)
                      ·
                        rfl

theorem cell23_2656056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 3, 2, 2].length) (baseStart_2656056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656056 prefixEnd_2656056 := by exact prefixLift 2656056
  have htrace : WordTrace (prefixWord ++ tailWord_2656056) baseStart_2656056 baseEnd_2656056 := by
    simpa [prefixWord, tailWord_2656056, baseEnd_2656056] using wordTrace_append hprefix tailTrace_2656056
  have hstable : (prefixWord ++ tailWord_2656056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656056).length < 2 ^ (prefixWord ++ tailWord_2656056).sum := by decide
  have hdescent : baseEnd_2656056 < baseStart_2656056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656089 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 4, 1, 3]
def baseStart_2656089 : Nat := 118140960795 + 2656089 * 2 ^ 59
def prefixEnd_2656089 : Nat := 4983230072969 + 3 ^ 40 * 2656089 * 2
def baseEnd_2656089 : Nat := 1363850318119963773272375

theorem tailTrace_2656089 : CollatzResearch.WordTrace tailWord_2656089 prefixEnd_2656089 1363850318119963773272375 := by
  unfold tailWord_2656089
  simp only [CollatzResearch.WordTrace]
  refine ⟨96875524474450651731467321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64583682982967101154311547 96875524474450651731467321)
  ·
    refine ⟨72656643355837988798600491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96875524474450651731467321 72656643355837988798600491)
    ·
      refine ⟨108984965033756983197900737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72656643355837988798600491 108984965033756983197900737)
      ·
        refine ⟨81738723775317737398425553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108984965033756983197900737 81738723775317737398425553)
        ·
          refine ⟨61304042831488303048819165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81738723775317737398425553 61304042831488303048819165)
          ·
            refine ⟨22989016061808113643307187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61304042831488303048819165 22989016061808113643307187)
            ·
              refine ⟨34483524092712170464960781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22989016061808113643307187 34483524092712170464960781)
              ·
                refine ⟨12931321534767063924360293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34483524092712170464960781 12931321534767063924360293)
                ·
                  refine ⟨2424622787768824485817555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12931321534767063924360293 2424622787768824485817555)
                  ·
                    refine ⟨3636934181653236728726333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2424622787768824485817555 3636934181653236728726333)
                    ·
                      refine ⟨1363850318119963773272375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3636934181653236728726333 1363850318119963773272375)
                      ·
                        rfl

theorem cell23_2656089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 1, 3].length) (baseStart_2656089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656089 prefixEnd_2656089 := by exact prefixLift 2656089
  have htrace : WordTrace (prefixWord ++ tailWord_2656089) baseStart_2656089 baseEnd_2656089 := by
    simpa [prefixWord, tailWord_2656089, baseEnd_2656089] using wordTrace_append hprefix tailTrace_2656089
  have hstable : (prefixWord ++ tailWord_2656089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656089).length < 2 ^ (prefixWord ++ tailWord_2656089).sum := by decide
  have hdescent : baseEnd_2656089 < baseStart_2656089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656090 : List Nat := [3, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2]
def baseStart_2656090 : Nat := 118140960795 + 2656090 * 2 ^ 59
def prefixEnd_2656090 : Nat := 4983230072969 + 3 ^ 40 * 2656090 * 2
def baseEnd_2656090 : Nat := 1363850831600618269359871

theorem tailTrace_2656090 : CollatzResearch.WordTrace tailWord_2656090 prefixEnd_2656090 1363850831600618269359871 := by
  unfold tailWord_2656090
  simp only [CollatzResearch.WordTrace]
  refine ⟨24218890236861757225563431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64583707298298019268169149 24218890236861757225563431)
  ·
    refine ⟨36328335355292635838345147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24218890236861757225563431 36328335355292635838345147)
    ·
      refine ⟨54492503032938953757517721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36328335355292635838345147 54492503032938953757517721)
      ·
        refine ⟨40869377274704215318138291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54492503032938953757517721 40869377274704215318138291)
        ·
          refine ⟨61304065912056322977207437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40869377274704215318138291 61304065912056322977207437)
          ·
            refine ⟨22989024717021121116452789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61304065912056322977207437 22989024717021121116452789)
            ·
              refine ⟨2155221067220730104667449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22989024717021121116452789 2155221067220730104667449)
              ·
                refine ⟨1616415800415547578500587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2155221067220730104667449 1616415800415547578500587)
                ·
                  refine ⟨2424623700623321367750881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616415800415547578500587 2424623700623321367750881)
                  ·
                    refine ⟨1818467775467491025813161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2424623700623321367750881 1818467775467491025813161)
                    ·
                      refine ⟨1363850831600618269359871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1818467775467491025813161 1363850831600618269359871)
                      ·
                        rfl

theorem cell23_2656090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_2656090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656090 prefixEnd_2656090 := by exact prefixLift 2656090
  have htrace : WordTrace (prefixWord ++ tailWord_2656090) baseStart_2656090 baseEnd_2656090 := by
    simpa [prefixWord, tailWord_2656090, baseEnd_2656090] using wordTrace_append hprefix tailTrace_2656090
  have hstable : (prefixWord ++ tailWord_2656090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656090).length < 2 ^ (prefixWord ++ tailWord_2656090).sum := by decide
  have hdescent : baseEnd_2656090 < baseStart_2656090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656100 : List Nat := [2, 3, 1, 1, 6, 1, 2, 1, 2, 4]
def baseStart_2656100 : Nat := 118140960795 + 2656100 * 2 ^ 59
def prefixEnd_2656100 : Nat := 4983230072969 + 3 ^ 40 * 2656100 * 2
def baseEnd_2656100 : Nat := 454618655469054410078275

theorem tailTrace_2656100 : CollatzResearch.WordTrace tailWord_2656100 prefixEnd_2656100 454618655469054410078275 := by
  unfold tailWord_2656100
  simp only [CollatzResearch.WordTrace]
  refine ⟨48437962838705400305058877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64583950451607200406745169 48437962838705400305058877)
  ·
    refine ⟨18164236064514525114397079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48437962838705400305058877 18164236064514525114397079)
    ·
      refine ⟨27246354096771787671595619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18164236064514525114397079 27246354096771787671595619)
      ·
        refine ⟨40869531145157681507393429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27246354096771787671595619 40869531145157681507393429)
        ·
          refine ⟨1915759272429266320659067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40869531145157681507393429 1915759272429266320659067)
          ·
            refine ⟨2873638908643899480988601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1915759272429266320659067 2873638908643899480988601)
            ·
              refine ⟨2155229181482924610741451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2873638908643899480988601 2155229181482924610741451)
              ·
                refine ⟨3232843772224386916112177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2155229181482924610741451 3232843772224386916112177)
                ·
                  refine ⟨2424632829168290187084133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3232843772224386916112177 2424632829168290187084133)
                  ·
                    refine ⟨454618655469054410078275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2424632829168290187084133 454618655469054410078275)
                    ·
                      rfl

theorem cell23_2656100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_2656100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656100 prefixEnd_2656100 := by exact prefixLift 2656100
  have htrace : WordTrace (prefixWord ++ tailWord_2656100) baseStart_2656100 baseEnd_2656100 := by
    simpa [prefixWord, tailWord_2656100, baseEnd_2656100] using wordTrace_append hprefix tailTrace_2656100
  have hstable : (prefixWord ++ tailWord_2656100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656100).length < 2 ^ (prefixWord ++ tailWord_2656100).sum := by decide
  have hdescent : baseEnd_2656100 < baseStart_2656100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656133 : List Nat := [1, 3, 1, 1, 3, 2, 5, 1, 1, 3, 2]
def baseStart_2656133 : Nat := 118140960795 + 2656133 * 2 ^ 59
def prefixEnd_2656133 : Nat := 4983230072969 + 3 ^ 40 * 2656133 * 2
def baseEnd_2656133 : Nat := 1363872911268761601122173

theorem tailTrace_2656133 : CollatzResearch.WordTrace tailWord_2656133 prefixEnd_2656133 1363872911268761601122173 := by
  unfold tailWord_2656133
  simp only [CollatzResearch.WordTrace]
  refine ⟨96877129286291247246069053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64584752857527498164046035 96877129286291247246069053)
  ·
    refine ⟨36328923482359217717275895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96877129286291247246069053 36328923482359217717275895)
    ·
      refine ⟨54493385223538826575913843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36328923482359217717275895 54493385223538826575913843)
      ·
        refine ⟨81740077835308239863870765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54493385223538826575913843 81740077835308239863870765)
        ·
          refine ⟨30652529188240589948951537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81740077835308239863870765 30652529188240589948951537)
          ·
            refine ⟨22989396891180442461713653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30652529188240589948951537 22989396891180442461713653)
            ·
              refine ⟨2155255958548166480785655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22989396891180442461713653 2155255958548166480785655)
              ·
                refine ⟨3232883937822249721178483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2155255958548166480785655 3232883937822249721178483)
                ·
                  refine ⟨4849325906733374581767725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3232883937822249721178483 4849325906733374581767725)
                  ·
                    refine ⟨1818497215025015468162897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4849325906733374581767725 1818497215025015468162897)
                    ·
                      refine ⟨1363872911268761601122173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1818497215025015468162897 1363872911268761601122173)
                      ·
                        rfl

theorem cell23_2656133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 1, 3, 2].length) (baseStart_2656133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656133 prefixEnd_2656133 := by exact prefixLift 2656133
  have htrace : WordTrace (prefixWord ++ tailWord_2656133) baseStart_2656133 baseEnd_2656133 := by
    simpa [prefixWord, tailWord_2656133, baseEnd_2656133] using wordTrace_append hprefix tailTrace_2656133
  have hstable : (prefixWord ++ tailWord_2656133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656133).length < 2 ^ (prefixWord ++ tailWord_2656133).sum := by decide
  have hdescent : baseEnd_2656133 < baseStart_2656133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656214 : List Nat := [5, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_2656214 : Nat := 118140960795 + 2656214 * 2 ^ 59
def prefixEnd_2656214 : Nat := 4983230072969 + 3 ^ 40 * 2656214 * 2
def baseEnd_2656214 : Nat := 1363914503201775784209301

theorem tailTrace_2656214 : CollatzResearch.WordTrace tailWord_2656214 prefixEnd_2656214 1363914503201775784209301 := by
  unfold tailWord_2656214
  simp only [CollatzResearch.WordTrace]
  refine ⟨6055005224937362379985481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64586722399331865386511797 6055005224937362379985481)
  ·
    refine ⟨4541253918703021784989111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6055005224937362379985481 4541253918703021784989111)
    ·
      refine ⟨6811880878054532677483667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4541253918703021784989111 6811880878054532677483667)
      ·
        refine ⟨10217821317081799016225501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6811880878054532677483667 10217821317081799016225501)
        ·
          refine ⟨3831682993905674631084563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10217821317081799016225501 3831682993905674631084563)
          ·
            refine ⟨5747524490858511946626845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3831682993905674631084563 5747524490858511946626845)
            ·
              refine ⟨2155321684071941979985067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5747524490858511946626845 2155321684071941979985067)
              ·
                refine ⟨3232982526107912969977601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2155321684071941979985067 3232982526107912969977601)
                ·
                  refine ⟨2424736894580934727483201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3232982526107912969977601 2424736894580934727483201)
                  ·
                    refine ⟨1818552670935701045612401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2424736894580934727483201 1818552670935701045612401)
                    ·
                      refine ⟨1363914503201775784209301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1818552670935701045612401 1363914503201775784209301)
                      ·
                        rfl

theorem cell23_2656214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_2656214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656214 prefixEnd_2656214 := by exact prefixLift 2656214
  have htrace : WordTrace (prefixWord ++ tailWord_2656214) baseStart_2656214 baseEnd_2656214 := by
    simpa [prefixWord, tailWord_2656214, baseEnd_2656214] using wordTrace_append hprefix tailTrace_2656214
  have hstable : (prefixWord ++ tailWord_2656214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656214).length < 2 ^ (prefixWord ++ tailWord_2656214).sum := by decide
  have hdescent : baseEnd_2656214 < baseStart_2656214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656237 : List Nat := [1, 5, 1, 4, 2, 1, 1, 3, 5]
def baseStart_2656237 : Nat := 118140960795 + 2656237 * 2 ^ 59
def prefixEnd_2656237 : Nat := 4983230072969 + 3 ^ 40 * 2656237 * 2
def baseEnd_2656237 : Nat := 151547368139647688246855

theorem tailTrace_2656237 : CollatzResearch.WordTrace tailWord_2656237 prefixEnd_2656237 151547368139647688246855 := by
  unfold tailWord_2656237
  simp only [CollatzResearch.WordTrace]
  refine ⟨96880922477914473007854965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64587281651942982005236643 96880922477914473007854965)
  ·
    refine ⟨9082586482304481844486403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96880922477914473007854965 9082586482304481844486403)
    ·
      refine ⟨13623879723456722766729605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9082586482304481844486403 13623879723456722766729605)
      ·
        refine ⟨2554477448148135518761801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13623879723456722766729605 2554477448148135518761801)
        ·
          refine ⟨1915858086111101639071351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2554477448148135518761801 1915858086111101639071351)
          ·
            refine ⟨2873787129166652458607027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1915858086111101639071351 2873787129166652458607027)
            ·
              refine ⟨4310680693749978687910541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2873787129166652458607027 4310680693749978687910541)
              ·
                refine ⟨1616505260156242007966453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4310680693749978687910541 1616505260156242007966453)
                ·
                  refine ⟨151547368139647688246855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1616505260156242007966453 151547368139647688246855)
                  ·
                    rfl

theorem cell23_2656237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_2656237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656237 prefixEnd_2656237 := by exact prefixLift 2656237
  have htrace : WordTrace (prefixWord ++ tailWord_2656237) baseStart_2656237 baseEnd_2656237 := by
    simpa [prefixWord, tailWord_2656237, baseEnd_2656237] using wordTrace_append hprefix tailTrace_2656237
  have hstable : (prefixWord ++ tailWord_2656237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656237).length < 2 ^ (prefixWord ++ tailWord_2656237).sum := by decide
  have hdescent : baseEnd_2656237 < baseStart_2656237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656239 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 3]
def baseStart_2656239 : Nat := 118140960795 + 2656239 * 2 ^ 59
def prefixEnd_2656239 : Nat := 4983230072969 + 3 ^ 40 * 2656239 * 2
def baseEnd_2656239 : Nat := 1363927340218138186396685

theorem tailTrace_2656239 : CollatzResearch.WordTrace tailWord_2656239 prefixEnd_2656239 1363927340218138186396685 := by
  unfold tailWord_2656239
  simp only [CollatzResearch.WordTrace]
  refine ⟨96880995423907227349427771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64587330282604818232951847 96880995423907227349427771)
  ·
    refine ⟨145321493135860841024141657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96880995423907227349427771 145321493135860841024141657)
    ·
      refine ⟨108991119851895630768106243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145321493135860841024141657 108991119851895630768106243)
      ·
        refine ⟨163486679777843446152159365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108991119851895630768106243 163486679777843446152159365)
        ·
          refine ⟨30653752458345646153529881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163486679777843446152159365 30653752458345646153529881)
          ·
            refine ⟨22990314343759234615147411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30653752458345646153529881 22990314343759234615147411)
            ·
              refine ⟨34485471515638851922721117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22990314343759234615147411 34485471515638851922721117)
              ·
                refine ⟨12932051818364569471020419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34485471515638851922721117 12932051818364569471020419)
                ·
                  refine ⟨19398077727546854206530629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12932051818364569471020419 19398077727546854206530629)
                  ·
                    refine ⟨3637139573915035163724493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19398077727546854206530629 3637139573915035163724493)
                    ·
                      refine ⟨1363927340218138186396685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3637139573915035163724493 1363927340218138186396685)
                      ·
                        rfl

theorem cell23_2656239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 3].length) (baseStart_2656239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656239 prefixEnd_2656239 := by exact prefixLift 2656239
  have htrace : WordTrace (prefixWord ++ tailWord_2656239) baseStart_2656239 baseEnd_2656239 := by
    simpa [prefixWord, tailWord_2656239, baseEnd_2656239] using wordTrace_append hprefix tailTrace_2656239
  have hstable : (prefixWord ++ tailWord_2656239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656239).length < 2 ^ (prefixWord ++ tailWord_2656239).sum := by decide
  have hdescent : baseEnd_2656239 < baseStart_2656239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656263 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 3, 4]
def baseStart_2656263 : Nat := 118140960795 + 2656263 * 2 ^ 59
def prefixEnd_2656263 : Nat := 4983230072969 + 3 ^ 40 * 2656263 * 2
def baseEnd_2656263 : Nat := 454646554584615364165525

theorem tailTrace_2656263 : CollatzResearch.WordTrace tailWord_2656263 prefixEnd_2656263 454646554584615364165525 := by
  unfold tailWord_2656263
  simp only [CollatzResearch.WordTrace]
  refine ⟨96881870775820279448301443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64587913850546852965534295 96881870775820279448301443)
  ·
    refine ⟨145322806163730419172452165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96881870775820279448301443 145322806163730419172452165)
    ·
      refine ⟨27248026155699453594834781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145322806163730419172452165 27248026155699453594834781)
      ·
        refine ⟨10218009808387295098063043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27248026155699453594834781 10218009808387295098063043)
        ·
          refine ⟨15327014712580942647094565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10218009808387295098063043 15327014712580942647094565)
          ·
            refine ⟨2873815258608926746330231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15327014712580942647094565 2873815258608926746330231)
            ·
              refine ⟨4310722887913390119495347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2873815258608926746330231 4310722887913390119495347)
              ·
                refine ⟨6466084331870085179243021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4310722887913390119495347 6466084331870085179243021)
                ·
                  refine ⟨2424781624451281942216133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6466084331870085179243021 2424781624451281942216133)
                  ·
                    refine ⟨454646554584615364165525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2424781624451281942216133 454646554584615364165525)
                    ·
                      rfl

theorem cell23_2656263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_2656263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656263 prefixEnd_2656263 := by exact prefixLift 2656263
  have htrace : WordTrace (prefixWord ++ tailWord_2656263) baseStart_2656263 baseEnd_2656263 := by
    simpa [prefixWord, tailWord_2656263, baseEnd_2656263] using wordTrace_append hprefix tailTrace_2656263
  have hstable : (prefixWord ++ tailWord_2656263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656263).length < 2 ^ (prefixWord ++ tailWord_2656263).sum := by decide
  have hdescent : baseEnd_2656263 < baseStart_2656263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656320 : List Nat := [2, 1, 1, 2, 2, 5, 1, 4, 1, 1, 3]
def baseStart_2656320 : Nat := 118140960795 + 2656320 * 2 ^ 59
def prefixEnd_2656320 : Nat := 4983230072969 + 3 ^ 40 * 2656320 * 2
def baseEnd_2656320 : Nat := 1363968932151152369483813

theorem tailTrace_2656320 : CollatzResearch.WordTrace tailWord_2656320 prefixEnd_2656320 1363968932151152369483813 := by
  unfold tailWord_2656320
  simp only [CollatzResearch.WordTrace]
  refine ⟨48441974868306889091563207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64589299824409185455417609 48441974868306889091563207)
  ·
    refine ⟨72662962302460333637344811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48441974868306889091563207 72662962302460333637344811)
    ·
      refine ⟨108994443453690500456017217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72662962302460333637344811 108994443453690500456017217)
      ·
        refine ⟨81745832590267875342012913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108994443453690500456017217 81745832590267875342012913)
        ·
          refine ⟨61309374442700906506509685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81745832590267875342012913 61309374442700906506509685)
          ·
            refine ⟨5747753854003209984985283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61309374442700906506509685 5747753854003209984985283)
            ·
              refine ⟨8621630781004814977477925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5747753854003209984985283 8621630781004814977477925)
              ·
                refine ⟨1616555771438402808277111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8621630781004814977477925 1616555771438402808277111)
                ·
                  refine ⟨2424833657157604212415667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616555771438402808277111 2424833657157604212415667)
                  ·
                    refine ⟨3637250485736406318623501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2424833657157604212415667 3637250485736406318623501)
                    ·
                      refine ⟨1363968932151152369483813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3637250485736406318623501 1363968932151152369483813)
                      ·
                        rfl

theorem cell23_2656320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 1, 1, 3].length) (baseStart_2656320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656320 prefixEnd_2656320 := by exact prefixLift 2656320
  have htrace : WordTrace (prefixWord ++ tailWord_2656320) baseStart_2656320 baseEnd_2656320 := by
    simpa [prefixWord, tailWord_2656320, baseEnd_2656320] using wordTrace_append hprefix tailTrace_2656320
  have hstable : (prefixWord ++ tailWord_2656320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656320).length < 2 ^ (prefixWord ++ tailWord_2656320).sum := by decide
  have hdescent : baseEnd_2656320 < baseStart_2656320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656329 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 3, 1, 5]
def baseStart_2656329 : Nat := 118140960795 + 2656329 * 2 ^ 59
def prefixEnd_2656329 : Nat := 4983230072969 + 3 ^ 40 * 2656329 * 2
def baseEnd_2656329 : Nat := 1363973553477042834271271

theorem tailTrace_2656329 : CollatzResearch.WordTrace tailWord_2656329 prefixEnd_2656329 1363973553477042834271271 := by
  unfold tailWord_2656329
  simp only [CollatzResearch.WordTrace]
  refine ⟨96884277993581172720204041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64589518662387448480136027 96884277993581172720204041)
  ·
    refine ⟨72663208495185879540153031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96884277993581172720204041 72663208495185879540153031)
    ·
      refine ⟨108994812742778819310229547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72663208495185879540153031 108994812742778819310229547)
      ·
        refine ⟨163492219114168228965344321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108994812742778819310229547 163492219114168228965344321)
        ·
          refine ⟨122619164335626171724008241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163492219114168228965344321 122619164335626171724008241)
          ·
            refine ⟨91964373251719628793006181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122619164335626171724008241 91964373251719628793006181)
            ·
              refine ⟨17243319984697430398688659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91964373251719628793006181 17243319984697430398688659)
              ·
                refine ⟨25864979977046145598032989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17243319984697430398688659 25864979977046145598032989)
                ·
                  refine ⟨9699367491392304599262371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25864979977046145598032989 9699367491392304599262371)
                  ·
                    refine ⟨14549051237088456898893557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9699367491392304599262371 14549051237088456898893557)
                    ·
                      refine ⟨1363973553477042834271271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14549051237088456898893557 1363973553477042834271271)
                      ·
                        rfl

theorem cell23_2656329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_2656329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656329 prefixEnd_2656329 := by exact prefixLift 2656329
  have htrace : WordTrace (prefixWord ++ tailWord_2656329) baseStart_2656329 baseEnd_2656329 := by
    simpa [prefixWord, tailWord_2656329, baseEnd_2656329] using wordTrace_append hprefix tailTrace_2656329
  have hstable : (prefixWord ++ tailWord_2656329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656329).length < 2 ^ (prefixWord ++ tailWord_2656329).sum := by decide
  have hdescent : baseEnd_2656329 < baseStart_2656329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656343 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 5, 2, 2]
def baseStart_2656343 : Nat := 118140960795 + 2656343 * 2 ^ 59
def prefixEnd_2656343 : Nat := 4983230072969 + 3 ^ 40 * 2656343 * 2
def baseEnd_2656343 : Nat := 1363980742206205779496207

theorem tailTrace_2656343 : CollatzResearch.WordTrace tailWord_2656343 prefixEnd_2656343 1363980742206205779496207 := by
  unfold tailWord_2656343
  simp only [CollatzResearch.WordTrace]
  refine ⟨96884788615530453111213683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64589859077020302074142455 96884788615530453111213683)
  ·
    refine ⟨145327182923295679666820525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96884788615530453111213683 145327182923295679666820525)
    ·
      refine ⟨54497693596235879875057697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145327182923295679666820525 54497693596235879875057697)
      ·
        refine ⟨40873270197176909906293273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54497693596235879875057697 40873270197176909906293273)
        ·
          refine ⟨30654952647882682429719955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40873270197176909906293273 30654952647882682429719955)
          ·
            refine ⟨45982428971824023644579933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30654952647882682429719955 45982428971824023644579933)
            ·
              refine ⟨17243410864434008866717475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45982428971824023644579933 17243410864434008866717475)
              ·
                refine ⟨25865116296651013300076213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17243410864434008866717475 25865116296651013300076213)
                ·
                  refine ⟨2424854652811032496882145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25865116296651013300076213 2424854652811032496882145)
                  ·
                    refine ⟨1818640989608274372661609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2424854652811032496882145 1818640989608274372661609)
                    ·
                      refine ⟨1363980742206205779496207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1818640989608274372661609 1363980742206205779496207)
                      ·
                        rfl

theorem cell23_2656343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_2656343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656343 prefixEnd_2656343 := by exact prefixLift 2656343
  have htrace : WordTrace (prefixWord ++ tailWord_2656343) baseStart_2656343 baseEnd_2656343 := by
    simpa [prefixWord, tailWord_2656343, baseEnd_2656343] using wordTrace_append hprefix tailTrace_2656343
  have hstable : (prefixWord ++ tailWord_2656343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656343).length < 2 ^ (prefixWord ++ tailWord_2656343).sum := by decide
  have hdescent : baseEnd_2656343 < baseStart_2656343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656346 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3]
def baseStart_2656346 : Nat := 118140960795 + 2656346 * 2 ^ 59
def prefixEnd_2656346 : Nat := 4983230072969 + 3 ^ 40 * 2656346 * 2
def baseEnd_2656346 : Nat := 1363982282648169267758693

theorem tailTrace_2656346 : CollatzResearch.WordTrace tailWord_2656346 prefixEnd_2656346 1363982282648169267758693 := by
  unfold tailWord_2656346
  simp only [CollatzResearch.WordTrace]
  refine ⟨24221224508629896155893223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64589932023013056415715261 24221224508629896155893223)
  ·
    refine ⟨36331836762944844233839835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24221224508629896155893223 36331836762944844233839835)
    ·
      refine ⟨54497755144417266350759753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36331836762944844233839835 54497755144417266350759753)
      ·
        refine ⟨40873316358312949763069815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54497755144417266350759753 40873316358312949763069815)
        ·
          refine ⟨61309974537469424644604723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40873316358312949763069815 61309974537469424644604723)
          ·
            refine ⟨91964961806204136966907085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61309974537469424644604723 91964961806204136966907085)
            ·
              refine ⟨34486860677326551362590157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91964961806204136966907085 34486860677326551362590157)
              ·
                refine ⟨12932572753997456760971309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34486860677326551362590157 12932572753997456760971309)
                ·
                  refine ⟨4849714782749046285364241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12932572753997456760971309 4849714782749046285364241)
                  ·
                    refine ⟨3637286087061784714023181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4849714782749046285364241 3637286087061784714023181)
                    ·
                      refine ⟨1363982282648169267758693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3637286087061784714023181 1363982282648169267758693)
                      ·
                        rfl

theorem cell23_2656346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_2656346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656346 prefixEnd_2656346 := by exact prefixLift 2656346
  have htrace : WordTrace (prefixWord ++ tailWord_2656346) baseStart_2656346 baseEnd_2656346 := by
    simpa [prefixWord, tailWord_2656346, baseEnd_2656346] using wordTrace_append hprefix tailTrace_2656346
  have hstable : (prefixWord ++ tailWord_2656346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656346).length < 2 ^ (prefixWord ++ tailWord_2656346).sum := by decide
  have hdescent : baseEnd_2656346 < baseStart_2656346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656354 : List Nat := [3, 3, 2, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_2656354 : Nat := 118140960795 + 2656354 * 2 ^ 59
def prefixEnd_2656354 : Nat := 4983230072969 + 3 ^ 40 * 2656354 * 2
def baseEnd_2656354 : Nat := 1363986390493405236458657

theorem tailTrace_2656354 : CollatzResearch.WordTrace tailWord_2656354 prefixEnd_2656354 1363986390493405236458657 := by
  unfold tailWord_2656354
  simp only [CollatzResearch.WordTrace]
  refine ⟨24221297454622650497466029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64590126545660401326576077 24221297454622650497466029)
  ·
    refine ⟨9082986545483493936549761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24221297454622650497466029 9082986545483493936549761)
    ·
      refine ⟨6812239909112620452412321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9082986545483493936549761 6812239909112620452412321)
      ·
        refine ⟨5109179931834465339309241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6812239909112620452412321 5109179931834465339309241)
        ·
          refine ⟨3831884948875849004481931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5109179931834465339309241 3831884948875849004481931)
          ·
            refine ⟨5747827423313773506722897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3831884948875849004481931 5747827423313773506722897)
            ·
              refine ⟨4310870567485330130042173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5747827423313773506722897 4310870567485330130042173)
              ·
                refine ⟨1616576462806998798765815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4310870567485330130042173 1616576462806998798765815)
                ·
                  refine ⟨2424864694210498198148723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616576462806998798765815 2424864694210498198148723)
                  ·
                    refine ⟨3637297041315747297223085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2424864694210498198148723 3637297041315747297223085)
                    ·
                      refine ⟨1363986390493405236458657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3637297041315747297223085 1363986390493405236458657)
                      ·
                        rfl

theorem cell23_2656354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_2656354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656354 prefixEnd_2656354 := by exact prefixLift 2656354
  have htrace : WordTrace (prefixWord ++ tailWord_2656354) baseStart_2656354 baseEnd_2656354 := by
    simpa [prefixWord, tailWord_2656354, baseEnd_2656354] using wordTrace_append hprefix tailTrace_2656354
  have hstable : (prefixWord ++ tailWord_2656354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656354).length < 2 ^ (prefixWord ++ tailWord_2656354).sum := by decide
  have hdescent : baseEnd_2656354 < baseStart_2656354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656356 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_2656356 : Nat := 118140960795 + 2656356 * 2 ^ 59
def prefixEnd_2656356 : Nat := 4983230072969 + 3 ^ 40 * 2656356 * 2
def baseEnd_2656356 : Nat := 1363987417454714228633647

theorem tailTrace_2656356 : CollatzResearch.WordTrace tailWord_2656356 prefixEnd_2656356 1363987417454714228633647 := by
  unfold tailWord_2656356
  simp only [CollatzResearch.WordTrace]
  refine ⟨48442631382241678165718461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64590175176322237554291281 48442631382241678165718461)
  ·
    refine ⟨18165986768340629312144423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48442631382241678165718461 18165986768340629312144423)
    ·
      refine ⟨27248980152510943968216635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18165986768340629312144423 27248980152510943968216635)
      ·
        refine ⟨40873470228766415952324953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27248980152510943968216635 40873470228766415952324953)
        ·
          refine ⟨30655102671574811964243715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40873470228766415952324953 30655102671574811964243715)
          ·
            refine ⟨45982654007362217946365573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30655102671574811964243715 45982654007362217946365573)
            ·
              refine ⟨8621747626380415864943545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45982654007362217946365573 8621747626380415864943545)
              ·
                refine ⟨6466310719785311898707659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8621747626380415864943545 6466310719785311898707659)
                ·
                  refine ⟨9699466079677967848061489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6466310719785311898707659 9699466079677967848061489)
                  ·
                    refine ⟨7274599559758475886046117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9699466079677967848061489 7274599559758475886046117)
                    ·
                      refine ⟨1363987417454714228633647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7274599559758475886046117 1363987417454714228633647)
                      ·
                        rfl

theorem cell23_2656356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_2656356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656356 prefixEnd_2656356 := by exact prefixLift 2656356
  have htrace : WordTrace (prefixWord ++ tailWord_2656356) baseStart_2656356 baseEnd_2656356 := by
    simpa [prefixWord, tailWord_2656356, baseEnd_2656356] using wordTrace_append hprefix tailTrace_2656356
  have hstable : (prefixWord ++ tailWord_2656356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656356).length < 2 ^ (prefixWord ++ tailWord_2656356).sum := by decide
  have hdescent : baseEnd_2656356 < baseStart_2656356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656370 : List Nat := [3, 2, 1, 2, 2, 4, 1, 2, 2, 4]
def baseStart_2656370 : Nat := 118140960795 + 2656370 * 2 ^ 59
def prefixEnd_2656370 : Nat := 4983230072969 + 3 ^ 40 * 2656370 * 2
def baseEnd_2656370 : Nat := 454664868727959057952861

theorem tailTrace_2656370 : CollatzResearch.WordTrace tailWord_2656370 prefixEnd_2656370 454664868727959057952861 := by
  unfold tailWord_2656370
  simp only [CollatzResearch.WordTrace]
  refine ⟨24221443346608159180611641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64590515590955091148297709 24221443346608159180611641)
  ·
    refine ⟨18166082509956119385458731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24221443346608159180611641 18166082509956119385458731)
    ·
      refine ⟨27249123764934179078188097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18166082509956119385458731 27249123764934179078188097)
      ·
        refine ⟨20436842823700634308641073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27249123764934179078188097 20436842823700634308641073)
        ·
          refine ⟨15327632117775475731480805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20436842823700634308641073 15327632117775475731480805)
          ·
            refine ⟨2873931022082901699652651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15327632117775475731480805 2873931022082901699652651)
            ·
              refine ⟨4310896533124352549478977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2873931022082901699652651 4310896533124352549478977)
              ·
                refine ⟨3233172399843264412109233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4310896533124352549478977 3233172399843264412109233)
                ·
                  refine ⟨2424879299882448309081925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3233172399843264412109233 2424879299882448309081925)
                  ·
                    refine ⟨454664868727959057952861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2424879299882448309081925 454664868727959057952861)
                    ·
                      rfl

theorem cell23_2656370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_2656370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656370 prefixEnd_2656370 := by exact prefixLift 2656370
  have htrace : WordTrace (prefixWord ++ tailWord_2656370) baseStart_2656370 baseEnd_2656370 := by
    simpa [prefixWord, tailWord_2656370, baseEnd_2656370] using wordTrace_append hprefix tailTrace_2656370
  have hstable : (prefixWord ++ tailWord_2656370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656370).length < 2 ^ (prefixWord ++ tailWord_2656370).sum := by decide
  have hdescent : baseEnd_2656370 < baseStart_2656370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656377 : List Nat := [1, 2, 1, 3, 4, 1, 2, 4, 1, 2, 2]
def baseStart_2656377 : Nat := 118140960795 + 2656377 * 2 ^ 59
def prefixEnd_2656377 : Nat := 4983230072969 + 3 ^ 40 * 2656377 * 2
def baseEnd_2656377 : Nat := 1363998200548458646471051

theorem tailTrace_2656377 : CollatzResearch.WordTrace tailWord_2656377 prefixEnd_2656377 1363998200548458646471051 := by
  unfold tailWord_2656377
  simp only [CollatzResearch.WordTrace]
  refine ⟨96886028697407276917951385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64590685798271517945300923 96886028697407276917951385)
  ·
    refine ⟨72664521523055457688463539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96886028697407276917951385 72664521523055457688463539)
    ·
      refine ⟨108996782284583186532695309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72664521523055457688463539 108996782284583186532695309)
      ·
        refine ⟨40873793356718694949760741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108996782284583186532695309 40873793356718694949760741)
        ·
          refine ⟨7663836254384755303080139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40873793356718694949760741 7663836254384755303080139)
          ·
            refine ⟨11495754381577132954620209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7663836254384755303080139 11495754381577132954620209)
            ·
              refine ⟨8621815786182849715965157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11495754381577132954620209 8621815786182849715965157)
              ·
                refine ⟨1616590459909284321743467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8621815786182849715965157 1616590459909284321743467)
                ·
                  refine ⟨2424885689863926482615201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616590459909284321743467 2424885689863926482615201)
                  ·
                    refine ⟨1818664267397944861961401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2424885689863926482615201 1818664267397944861961401)
                    ·
                      refine ⟨1363998200548458646471051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1818664267397944861961401 1363998200548458646471051)
                      ·
                        rfl

theorem cell23_2656377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_2656377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656377 prefixEnd_2656377 := by exact prefixLift 2656377
  have htrace : WordTrace (prefixWord ++ tailWord_2656377) baseStart_2656377 baseEnd_2656377 := by
    simpa [prefixWord, tailWord_2656377, baseEnd_2656377] using wordTrace_append hprefix tailTrace_2656377
  have hstable : (prefixWord ++ tailWord_2656377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656377).length < 2 ^ (prefixWord ++ tailWord_2656377).sum := by decide
  have hdescent : baseEnd_2656377 < baseStart_2656377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656409 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 1, 8]
def baseStart_2656409 : Nat := 118140960795 + 2656409 * 2 ^ 59
def prefixEnd_2656409 : Nat := 4983230072969 + 3 ^ 40 * 2656409 * 2
def baseEnd_2656409 : Nat := 454671543976467507090301

theorem tailTrace_2656409 : CollatzResearch.WordTrace tailWord_2656409 prefixEnd_2656409 454671543976467507090301 := by
  unfold tailWord_2656409
  simp only [CollatzResearch.WordTrace]
  refine ⟨96887195833291346383116281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64591463888860897588744187 96887195833291346383116281)
  ·
    refine ⟨72665396874968509787337211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96887195833291346383116281 72665396874968509787337211)
    ·
      refine ⟨108998095312452764681005817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72665396874968509787337211 108998095312452764681005817)
      ·
        refine ⟨81748571484339573510754363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108998095312452764681005817 81748571484339573510754363)
        ·
          refine ⟨122622857226509360266131545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81748571484339573510754363 122622857226509360266131545)
          ·
            refine ⟨91967142919882020199598659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122622857226509360266131545 91967142919882020199598659)
            ·
              refine ⟨137950714379823030299397989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91967142919882020199598659 137950714379823030299397989)
              ·
                refine ⟨25865758946216818181137123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137950714379823030299397989 25865758946216818181137123)
                ·
                  refine ⟨38798638419325227271705685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25865758946216818181137123 38798638419325227271705685)
                  ·
                    refine ⟨454671543976467507090301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38798638419325227271705685 454671543976467507090301)
                    ·
                      rfl

theorem cell23_2656409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 8].length) (baseStart_2656409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656409 prefixEnd_2656409 := by exact prefixLift 2656409
  have htrace : WordTrace (prefixWord ++ tailWord_2656409) baseStart_2656409 baseEnd_2656409 := by
    simpa [prefixWord, tailWord_2656409, baseEnd_2656409] using wordTrace_append hprefix tailTrace_2656409
  have hstable : (prefixWord ++ tailWord_2656409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656409).length < 2 ^ (prefixWord ++ tailWord_2656409).sum := by decide
  have hdescent : baseEnd_2656409 < baseStart_2656409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656444 : List Nat := [2, 2, 2, 3, 3, 2, 2, 1, 2, 1, 3]
def baseStart_2656444 : Nat := 118140960795 + 2656444 * 2 ^ 59
def prefixEnd_2656444 : Nat := 4983230072969 + 3 ^ 40 * 2656444 * 2
def baseEnd_2656444 : Nat := 1364032603752309884333243

theorem tailTrace_2656444 : CollatzResearch.WordTrace tailWord_2656444 prefixEnd_2656444 1364032603752309884333243 := by
  unfold tailWord_2656444
  simp only [CollatzResearch.WordTrace]
  refine ⟨48444236194082273680320193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64592314925443031573760257 48444236194082273680320193)
  ·
    refine ⟨36333177145561705260240145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48444236194082273680320193 36333177145561705260240145)
    ·
      refine ⟨27249882859171278945180109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36333177145561705260240145 27249882859171278945180109)
      ·
        refine ⟨10218706072189229604442541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27249882859171278945180109 10218706072189229604442541)
        ·
          refine ⟨3832014777070961101665953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10218706072189229604442541 3832014777070961101665953)
          ·
            refine ⟨2874011082803220826249465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3832014777070961101665953 2874011082803220826249465)
            ·
              refine ⟨2155508312102415619687099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2874011082803220826249465 2155508312102415619687099)
              ·
                refine ⟨3233262468153623429530649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2155508312102415619687099 3233262468153623429530649)
                ·
                  refine ⟨2424946851115217572147987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3233262468153623429530649 2424946851115217572147987)
                  ·
                    refine ⟨3637420276672826358221981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2424946851115217572147987 3637420276672826358221981)
                    ·
                      refine ⟨1364032603752309884333243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3637420276672826358221981 1364032603752309884333243)
                      ·
                        rfl

theorem cell23_2656444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_2656444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656444 prefixEnd_2656444 := by exact prefixLift 2656444
  have htrace : WordTrace (prefixWord ++ tailWord_2656444) baseStart_2656444 baseEnd_2656444 := by
    simpa [prefixWord, tailWord_2656444, baseEnd_2656444] using wordTrace_append hprefix tailTrace_2656444
  have hstable : (prefixWord ++ tailWord_2656444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656444).length < 2 ^ (prefixWord ++ tailWord_2656444).sum := by decide
  have hdescent : baseEnd_2656444 < baseStart_2656444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656470 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2656470 : Nat := 118140960795 + 2656470 * 2 ^ 59
def prefixEnd_2656470 : Nat := 4983230072969 + 3 ^ 40 * 2656470 * 2
def baseEnd_2656470 : Nat := 1364045954249326782608123

theorem tailTrace_2656470 : CollatzResearch.WordTrace tailWord_2656470 prefixEnd_2656470 1364045954249326782608123 := by
  unfold tailWord_2656470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6055588792879397112567929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64592947124046902534057909 6055588792879397112567929)
  ·
    refine ⟨4541691594659547834425947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6055588792879397112567929 4541691594659547834425947)
    ·
      refine ⟨6812537391989321751638921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4541691594659547834425947 6812537391989321751638921)
      ·
        refine ⟨5109403043991991313729191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6812537391989321751638921 5109403043991991313729191)
        ·
          refine ⟨7664104565987986970593787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5109403043991991313729191 7664104565987986970593787)
          ·
            refine ⟨11496156848981980455890681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7664104565987986970593787 11496156848981980455890681)
            ·
              refine ⟨8622117636736485341918011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11496156848981980455890681 8622117636736485341918011)
              ·
                refine ⟨12933176455104728012877017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8622117636736485341918011 12933176455104728012877017)
                ·
                  refine ⟨9699882341328546009657763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12933176455104728012877017 9699882341328546009657763)
                  ·
                    refine ⟨14549823511992819014486645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9699882341328546009657763 14549823511992819014486645)
                    ·
                      refine ⟨1364045954249326782608123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14549823511992819014486645 1364045954249326782608123)
                      ·
                        rfl

theorem cell23_2656470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2656470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656470 prefixEnd_2656470 := by exact prefixLift 2656470
  have htrace : WordTrace (prefixWord ++ tailWord_2656470) baseStart_2656470 baseEnd_2656470 := by
    simpa [prefixWord, tailWord_2656470, baseEnd_2656470] using wordTrace_append hprefix tailTrace_2656470
  have hstable : (prefixWord ++ tailWord_2656470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656470).length < 2 ^ (prefixWord ++ tailWord_2656470).sum := by decide
  have hdescent : baseEnd_2656470 < baseStart_2656470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656510 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_2656510 : Nat := 118140960795 + 2656510 * 2 ^ 59
def prefixEnd_2656510 : Nat := 4983230072969 + 3 ^ 40 * 2656510 * 2
def baseEnd_2656510 : Nat := 1364066493475506626107939

theorem tailTrace_2656510 : CollatzResearch.WordTrace tailWord_2656510 prefixEnd_2656510 1364066493475506626107939 := by
  unfold tailWord_2656510
  simp only [CollatzResearch.WordTrace]
  refine ⟨12111359950740680079067873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64593919737283627088361989 12111359950740680079067873)
  ·
    refine ⟨9083519963055510059300905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12111359950740680079067873 9083519963055510059300905)
    ·
      refine ⟨6812639972291632544475679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9083519963055510059300905 6812639972291632544475679)
      ·
        refine ⟨10218959958437448816713519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6812639972291632544475679 10218959958437448816713519)
        ·
          refine ⟨15328439937656173225070279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10218959958437448816713519 15328439937656173225070279)
          ·
            refine ⟨22992659906484259837605419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15328439937656173225070279 22992659906484259837605419)
            ·
              refine ⟨34488989859726389756408129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22992659906484259837605419 34488989859726389756408129)
              ·
                refine ⟨25866742394794792317306097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34488989859726389756408129 25866742394794792317306097)
                ·
                  refine ⟨19400056796096094237979573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25866742394794792317306097 19400056796096094237979573)
                  ·
                    refine ⟨1818755324634008834810585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19400056796096094237979573 1818755324634008834810585)
                    ·
                      refine ⟨1364066493475506626107939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1818755324634008834810585 1364066493475506626107939)
                      ·
                        rfl

theorem cell23_2656510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_2656510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656510 prefixEnd_2656510 := by exact prefixLift 2656510
  have htrace : WordTrace (prefixWord ++ tailWord_2656510) baseStart_2656510 baseEnd_2656510 := by
    simpa [prefixWord, tailWord_2656510, baseEnd_2656510] using wordTrace_append hprefix tailTrace_2656510
  have hstable : (prefixWord ++ tailWord_2656510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656510).length < 2 ^ (prefixWord ++ tailWord_2656510).sum := by decide
  have hdescent : baseEnd_2656510 < baseStart_2656510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656520 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 2, 5]
def baseStart_2656520 : Nat := 118140960795 + 2656520 * 2 ^ 59
def prefixEnd_2656520 : Nat := 4983230072969 + 3 ^ 40 * 2656520 * 2
def baseEnd_2656520 : Nat := 454690542760683862327631

theorem tailTrace_2656520 : CollatzResearch.WordTrace tailWord_2656520 prefixEnd_2656520 454690542760683862327631 := by
  unfold tailWord_2656520
  simp only [CollatzResearch.WordTrace]
  refine ⟨48445622167944606170203507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64594162890592808226938009 48445622167944606170203507)
  ·
    refine ⟨72668433251916909255305261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48445622167944606170203507 72668433251916909255305261)
    ·
      refine ⟨27250662469468840970739473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72668433251916909255305261 27250662469468840970739473)
      ·
        refine ⟨20437996852101630728054605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27250662469468840970739473 20437996852101630728054605)
        ·
          refine ⟨7664248819538111523020477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20437996852101630728054605 7664248819538111523020477)
          ·
            refine ⟨2874093307326791821132679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7664248819538111523020477 2874093307326791821132679)
            ·
              refine ⟨4311139960990187731699019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2874093307326791821132679 4311139960990187731699019)
              ·
                refine ⟨6466709941485281597548529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4311139960990187731699019 6466709941485281597548529)
                ·
                  refine ⟨4850032456113961198161397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6466709941485281597548529 4850032456113961198161397)
                  ·
                    refine ⟨454690542760683862327631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4850032456113961198161397 454690542760683862327631)
                    ·
                      rfl

theorem cell23_2656520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_2656520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656520 prefixEnd_2656520 := by exact prefixLift 2656520
  have htrace : WordTrace (prefixWord ++ tailWord_2656520) baseStart_2656520 baseEnd_2656520 := by
    simpa [prefixWord, tailWord_2656520, baseEnd_2656520] using wordTrace_append hprefix tailTrace_2656520
  have hstable : (prefixWord ++ tailWord_2656520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656520).length < 2 ^ (prefixWord ++ tailWord_2656520).sum := by decide
  have hdescent : baseEnd_2656520 < baseStart_2656520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656523 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 1, 6, 2]
def baseStart_2656523 : Nat := 118140960795 + 2656523 * 2 ^ 59
def prefixEnd_2656523 : Nat := 4983230072969 + 3 ^ 40 * 2656523 * 2
def baseEnd_2656523 : Nat := 1364073168724015075245379

theorem tailTrace_2656523 : CollatzResearch.WordTrace tailWord_2656523 prefixEnd_2656523 1364073168724015075245379 := by
  unfold tailWord_2656523
  simp only [CollatzResearch.WordTrace]
  refine ⟨96891353754878343852766223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64594235836585562568510815 96891353754878343852766223)
  ·
    refine ⟨145337030632317515779149335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96891353754878343852766223 145337030632317515779149335)
    ·
      refine ⟨218005545948476273668724003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145337030632317515779149335 218005545948476273668724003)
      ·
        refine ⟨327008318922714410503086005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218005545948476273668724003 327008318922714410503086005)
        ·
          refine ⟨30657029899004475984664313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 327008318922714410503086005 30657029899004475984664313)
          ·
            refine ⟨22992772424253356988498235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30657029899004475984664313 22992772424253356988498235)
            ·
              refine ⟨34489158636380035482747353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22992772424253356988498235 34489158636380035482747353)
              ·
                refine ⟨25866868977285026612060515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34489158636380035482747353 25866868977285026612060515)
                ·
                  refine ⟨38800303465927539918090773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25866868977285026612060515 38800303465927539918090773)
                  ·
                    refine ⟨1818764224965353433660505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38800303465927539918090773 1818764224965353433660505)
                    ·
                      refine ⟨1364073168724015075245379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1818764224965353433660505 1364073168724015075245379)
                      ·
                        rfl

theorem cell23_2656523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 6, 2].length) (baseStart_2656523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656523 prefixEnd_2656523 := by exact prefixLift 2656523
  have htrace : WordTrace (prefixWord ++ tailWord_2656523) baseStart_2656523 baseEnd_2656523 := by
    simpa [prefixWord, tailWord_2656523, baseEnd_2656523] using wordTrace_append hprefix tailTrace_2656523
  have hstable : (prefixWord ++ tailWord_2656523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656523).length < 2 ^ (prefixWord ++ tailWord_2656523).sum := by decide
  have hdescent : baseEnd_2656523 < baseStart_2656523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656536 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 1, 3, 6]
def baseStart_2656536 : Nat := 118140960795 + 2656536 * 2 ^ 59
def prefixEnd_2656536 : Nat := 4983230072969 + 3 ^ 40 * 2656536 * 2
def baseEnd_2656536 : Nat := 1364079843972523524382819

theorem tailTrace_2656536 : CollatzResearch.WordTrace tailWord_2656536 prefixEnd_2656536 1364079843972523524382819 := by
  unfold tailWord_2656536
  simp only [CollatzResearch.WordTrace]
  refine ⟨48445913951915623536494731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64594551935887498048659641 48445913951915623536494731)
  ·
    refine ⟨72668870927873435304742097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48445913951915623536494731 72668870927873435304742097)
    ·
      refine ⟨54501653195905076478556573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72668870927873435304742097 54501653195905076478556573)
      ·
        refine ⟨20438119948464403679458715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54501653195905076478556573 20438119948464403679458715)
        ·
          refine ⟨30657179922696605519188073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20438119948464403679458715 30657179922696605519188073)
          ·
            refine ⟨22992884942022454139391055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30657179922696605519188073 22992884942022454139391055)
            ·
              refine ⟨34489327413033681209086583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22992884942022454139391055 34489327413033681209086583)
              ·
                refine ⟨51733991119550521813629875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34489327413033681209086583 51733991119550521813629875)
                ·
                  refine ⟨77600986679325782720444813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51733991119550521813629875 77600986679325782720444813)
                  ·
                    refine ⟨29100370004747168520166805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77600986679325782720444813 29100370004747168520166805)
                    ·
                      refine ⟨1364079843972523524382819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29100370004747168520166805 1364079843972523524382819)
                      ·
                        rfl

theorem cell23_2656536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_2656536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656536 prefixEnd_2656536 := by exact prefixLift 2656536
  have htrace : WordTrace (prefixWord ++ tailWord_2656536) baseStart_2656536 baseEnd_2656536 := by
    simpa [prefixWord, tailWord_2656536, baseEnd_2656536] using wordTrace_append hprefix tailTrace_2656536
  have hstable : (prefixWord ++ tailWord_2656536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656536).length < 2 ^ (prefixWord ++ tailWord_2656536).sum := by decide
  have hdescent : baseEnd_2656536 < baseStart_2656536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656607 : List Nat := [1, 1, 2, 3, 1, 2, 2, 6, 1, 1, 3]
def baseStart_2656607 : Nat := 118140960795 + 2656607 * 2 ^ 59
def prefixEnd_2656607 : Nat := 4983230072969 + 3 ^ 40 * 2656607 * 2
def baseEnd_2656607 : Nat := 1364116301098992746594993

theorem tailTrace_2656607 : CollatzResearch.WordTrace tailWord_2656607 prefixEnd_2656607 1364116301098992746594993 := by
  unfold tailWord_2656607
  simp only [CollatzResearch.WordTrace]
  refine ⟨96894417486574026198824075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64596278324382684132549383 96894417486574026198824075)
  ·
    refine ⟨145341626229861039298236113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96894417486574026198824075 145341626229861039298236113)
    ·
      refine ⟨109006219672395779473677085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145341626229861039298236113 109006219672395779473677085)
      ·
        refine ⟨40877332377148417302628907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109006219672395779473677085 40877332377148417302628907)
        ·
          refine ⟨61315998565722625953943361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40877332377148417302628907 61315998565722625953943361)
          ·
            refine ⟨45986998924291969465457521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61315998565722625953943361 45986998924291969465457521)
            ·
              refine ⟨34490249193218977099093141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45986998924291969465457521 34490249193218977099093141)
              ·
                refine ⟨1616730430932139551519991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34490249193218977099093141 1616730430932139551519991)
                ·
                  refine ⟨2425095646398209327279987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616730430932139551519991 2425095646398209327279987)
                  ·
                    refine ⟨3637643469597313990919981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2425095646398209327279987 3637643469597313990919981)
                    ·
                      refine ⟨1364116301098992746594993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3637643469597313990919981 1364116301098992746594993)
                      ·
                        rfl

theorem cell23_2656607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_2656607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656607 prefixEnd_2656607 := by exact prefixLift 2656607
  have htrace : WordTrace (prefixWord ++ tailWord_2656607) baseStart_2656607 baseEnd_2656607 := by
    simpa [prefixWord, tailWord_2656607, baseEnd_2656607] using wordTrace_append hprefix tailTrace_2656607
  have hstable : (prefixWord ++ tailWord_2656607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656607).length < 2 ^ (prefixWord ++ tailWord_2656607).sum := by decide
  have hdescent : baseEnd_2656607 < baseStart_2656607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656623 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 6, 4]
def baseStart_2656623 : Nat := 118140960795 + 2656623 * 2 ^ 59
def prefixEnd_2656623 : Nat := 4983230072969 + 3 ^ 40 * 2656623 * 2
def baseEnd_2656623 : Nat := 454708172263154894664973

theorem tailTrace_2656623 : CollatzResearch.WordTrace tailWord_2656623 prefixEnd_2656623 454708172263154894664973 := by
  unfold tailWord_2656623
  simp only [CollatzResearch.WordTrace]
  refine ⟨96895001054516060931406523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64596667369677373954271015 96895001054516060931406523)
  ·
    refine ⟨145342501581774091397109785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96895001054516060931406523 145342501581774091397109785)
    ·
      refine ⟨109006876186330568547832339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145342501581774091397109785 109006876186330568547832339)
      ·
        refine ⟨163510314279495852821748509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109006876186330568547832339 163510314279495852821748509)
        ·
          refine ⟨61316367854810944808155691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163510314279495852821748509 61316367854810944808155691)
          ·
            refine ⟨91974551782216417212233537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61316367854810944808155691 91974551782216417212233537)
            ·
              refine ⟨68980913836662312909175153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91974551782216417212233537 68980913836662312909175153)
              ·
                refine ⟨51735685377496734681881365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68980913836662312909175153 51735685377496734681881365)
                ·
                  refine ⟨2425110252070159438213189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51735685377496734681881365 2425110252070159438213189)
                  ·
                    refine ⟨454708172263154894664973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2425110252070159438213189 454708172263154894664973)
                    ·
                      rfl

theorem cell23_2656623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 4].length) (baseStart_2656623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656623 prefixEnd_2656623 := by exact prefixLift 2656623
  have htrace : WordTrace (prefixWord ++ tailWord_2656623) baseStart_2656623 baseEnd_2656623 := by
    simpa [prefixWord, tailWord_2656623, baseEnd_2656623] using wordTrace_append hprefix tailTrace_2656623
  have hstable : (prefixWord ++ tailWord_2656623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656623).length < 2 ^ (prefixWord ++ tailWord_2656623).sum := by decide
  have hdescent : baseEnd_2656623 < baseStart_2656623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656647 : List Nat := [1, 1, 4, 2, 2, 1, 5, 1, 1, 1, 4]
def baseStart_2656647 : Nat := 118140960795 + 2656647 * 2 ^ 59
def prefixEnd_2656647 : Nat := 4983230072969 + 3 ^ 40 * 2656647 * 2
def baseEnd_2656647 : Nat := 1364136840325172590094809

theorem tailTrace_2656647 : CollatzResearch.WordTrace tailWord_2656647 prefixEnd_2656647 1364136840325172590094809 := by
  unfold tailWord_2656647
  simp only [CollatzResearch.WordTrace]
  refine ⟨96895876406429113030280195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64597250937619408686853463 96895876406429113030280195)
  ·
    refine ⟨145343814609643669545420293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96895876406429113030280195 145343814609643669545420293)
    ·
      refine ⟨27251965239308188039766305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145343814609643669545420293 27251965239308188039766305)
      ·
        refine ⟨20438973929481141029824729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27251965239308188039766305 20438973929481141029824729)
        ·
          refine ⟨15329230447110855772368547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20438973929481141029824729 15329230447110855772368547)
          ·
            refine ⟨22993845670666283658552821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15329230447110855772368547 22993845670666283658552821)
            ·
              refine ⟨2155673031624964092989327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22993845670666283658552821 2155673031624964092989327)
              ·
                refine ⟨3233509547437446139483991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2155673031624964092989327 3233509547437446139483991)
                ·
                  refine ⟨4850264321156169209225987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3233509547437446139483991 4850264321156169209225987)
                  ·
                    refine ⟨7275396481734253813838981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4850264321156169209225987 7275396481734253813838981)
                    ·
                      refine ⟨1364136840325172590094809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7275396481734253813838981 1364136840325172590094809)
                      ·
                        rfl

theorem cell23_2656647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_2656647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656647 prefixEnd_2656647 := by exact prefixLift 2656647
  have htrace : WordTrace (prefixWord ++ tailWord_2656647) baseStart_2656647 baseEnd_2656647 := by
    simpa [prefixWord, tailWord_2656647, baseEnd_2656647] using wordTrace_append hprefix tailTrace_2656647
  have hstable : (prefixWord ++ tailWord_2656647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656647).length < 2 ^ (prefixWord ++ tailWord_2656647).sum := by decide
  have hdescent : baseEnd_2656647 < baseStart_2656647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656713 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 2, 6]
def baseStart_2656713 : Nat := 118140960795 + 2656713 * 2 ^ 59
def prefixEnd_2656713 : Nat := 4983230072969 + 3 ^ 40 * 2656713 * 2
def baseEnd_2656713 : Nat := 454723576682789777289835

theorem tailTrace_2656713 : CollatzResearch.WordTrace tailWord_2656713 prefixEnd_2656713 454723576682789777289835 := by
  unfold tailWord_2656713
  simp only [CollatzResearch.WordTrace]
  refine ⟨96898283624190006302182793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64598855749460004201455195 96898283624190006302182793)
  ·
    refine ⟨72673712718142504726637095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96898283624190006302182793 72673712718142504726637095)
    ·
      refine ⟨109010569077213757089955643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72673712718142504726637095 109010569077213757089955643)
      ·
        refine ⟨163515853615820635634933465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109010569077213757089955643 163515853615820635634933465)
        ·
          refine ⟨122636890211865476726200099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163515853615820635634933465 122636890211865476726200099)
          ·
            refine ⟨183955335317798215089300149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122636890211865476726200099 183955335317798215089300149)
            ·
              refine ⟨17245812686043582664621889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 183955335317798215089300149 17245812686043582664621889)
              ·
                refine ⟨12934359514532686998466417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17245812686043582664621889 12934359514532686998466417)
                ·
                  refine ⟨9700769635899515248849813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12934359514532686998466417 9700769635899515248849813)
                  ·
                    refine ⟨454723576682789777289835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9700769635899515248849813 454723576682789777289835)
                    ·
                      rfl

theorem cell23_2656713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 6].length) (baseStart_2656713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656713 prefixEnd_2656713 := by exact prefixLift 2656713
  have htrace : WordTrace (prefixWord ++ tailWord_2656713) baseStart_2656713 baseEnd_2656713 := by
    simpa [prefixWord, tailWord_2656713, baseEnd_2656713] using wordTrace_append hprefix tailTrace_2656713
  have hstable : (prefixWord ++ tailWord_2656713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656713).length < 2 ^ (prefixWord ++ tailWord_2656713).sum := by decide
  have hdescent : baseEnd_2656713 < baseStart_2656713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656741 : List Nat := [1, 3, 1, 5, 2, 1, 2, 2, 1, 3, 2]
def baseStart_2656741 : Nat := 118140960795 + 2656741 * 2 ^ 59
def prefixEnd_2656741 : Nat := 4983230072969 + 3 ^ 40 * 2656741 * 2
def baseEnd_2656741 : Nat := 1364185107506695222319377

theorem tailTrace_2656741 : CollatzResearch.WordTrace tailWord_2656741 prefixEnd_2656741 1364185107506695222319377 := by
  unfold tailWord_2656741
  simp only [CollatzResearch.WordTrace]
  refine ⟨96899304868088567084202077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64599536578725711389468051 96899304868088567084202077)
  ·
    refine ⟨36337239325533212656575779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96899304868088567084202077 36337239325533212656575779)
    ·
      refine ⟨54505858988299818984863669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36337239325533212656575779 54505858988299818984863669)
      ·
        refine ⟨5109924280153108029830969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54505858988299818984863669 5109924280153108029830969)
        ·
          refine ⟨3832443210114831022373227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5109924280153108029830969 3832443210114831022373227)
          ·
            refine ⟨5748664815172246533559841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832443210114831022373227 5748664815172246533559841)
            ·
              refine ⟨4311498611379184900169881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5748664815172246533559841 4311498611379184900169881)
              ·
                refine ⟨3233623958534388675127411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4311498611379184900169881 3233623958534388675127411)
                ·
                  refine ⟨4850435937801583012691117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3233623958534388675127411 4850435937801583012691117)
                  ·
                    refine ⟨1818913476675593629759169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4850435937801583012691117 1818913476675593629759169)
                    ·
                      refine ⟨1364185107506695222319377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1818913476675593629759169 1364185107506695222319377)
                      ·
                        rfl

theorem cell23_2656741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_2656741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656741 prefixEnd_2656741 := by exact prefixLift 2656741
  have htrace : WordTrace (prefixWord ++ tailWord_2656741) baseStart_2656741 baseEnd_2656741 := by
    simpa [prefixWord, tailWord_2656741, baseEnd_2656741] using wordTrace_append hprefix tailTrace_2656741
  have hstable : (prefixWord ++ tailWord_2656741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656741).length < 2 ^ (prefixWord ++ tailWord_2656741).sum := by decide
  have hdescent : baseEnd_2656741 < baseStart_2656741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656783 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 7]
def baseStart_2656783 : Nat := 118140960795 + 2656783 * 2 ^ 59
def prefixEnd_2656783 : Nat := 4983230072969 + 3 ^ 40 * 2656783 * 2
def baseEnd_2656783 : Nat := 1364206673694184057994183

theorem tailTrace_2656783 : CollatzResearch.WordTrace tailWord_2656783 prefixEnd_2656783 1364206673694184057994183 := by
  unfold tailWord_2656783
  simp only [CollatzResearch.WordTrace]
  refine ⟨96900836733936408257231003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64600557822624272171487335 96900836733936408257231003)
  ·
    refine ⟨145351255100904612385846505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96900836733936408257231003 145351255100904612385846505)
    ·
      refine ⟨109013441325678459289384879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145351255100904612385846505 109013441325678459289384879)
      ·
        refine ⟨163520161988517688934077319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109013441325678459289384879 163520161988517688934077319)
        ·
          refine ⟨245280242982776533401115979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163520161988517688934077319 245280242982776533401115979)
          ·
            refine ⟨367920364474164800101673969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245280242982776533401115979 367920364474164800101673969)
            ·
              refine ⟨275940273355623600076255477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367920364474164800101673969 275940273355623600076255477)
              ·
                refine ⟨25869400627089712507148951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 275940273355623600076255477 25869400627089712507148951)
                ·
                  refine ⟨38804100940634568760723427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25869400627089712507148951 38804100940634568760723427)
                  ·
                    refine ⟨58206151410951853141085141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38804100940634568760723427 58206151410951853141085141)
                    ·
                      refine ⟨1364206673694184057994183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58206151410951853141085141 1364206673694184057994183)
                      ·
                        rfl

theorem cell23_2656783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_2656783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656783 prefixEnd_2656783 := by exact prefixLift 2656783
  have htrace : WordTrace (prefixWord ++ tailWord_2656783) baseStart_2656783 baseEnd_2656783 := by
    simpa [prefixWord, tailWord_2656783, baseEnd_2656783] using wordTrace_append hprefix tailTrace_2656783
  have hstable : (prefixWord ++ tailWord_2656783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656783).length < 2 ^ (prefixWord ++ tailWord_2656783).sum := by decide
  have hdescent : baseEnd_2656783 < baseStart_2656783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656788 : List Nat := [2, 4, 3, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_2656788 : Nat := 118140960795 + 2656788 * 2 ^ 59
def prefixEnd_2656788 : Nat := 4983230072969 + 3 ^ 40 * 2656788 * 2
def baseEnd_2656788 : Nat := 1364209241097456538431661

theorem tailTrace_2656788 : CollatzResearch.WordTrace tailWord_2656788 prefixEnd_2656788 1364209241097456538431661 := by
  unfold tailWord_2656788
  simp only [CollatzResearch.WordTrace]
  refine ⟨48450509549459147055581509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64600679399278862740775345 48450509549459147055581509)
  ·
    refine ⟨9084470540523590072921533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48450509549459147055581509 9084470540523590072921533)
    ·
      refine ⟨3406676452696346277345575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9084470540523590072921533 3406676452696346277345575)
      ·
        refine ⟨5110014679044519416018363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3406676452696346277345575 5110014679044519416018363)
        ·
          refine ⟨7665022018566779124027545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5110014679044519416018363 7665022018566779124027545)
          ·
            refine ⟨5748766513925084343020659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7665022018566779124027545 5748766513925084343020659)
            ·
              refine ⟨8623149770887626514530989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5748766513925084343020659 8623149770887626514530989)
              ·
                refine ⟨3233681164082859942949121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8623149770887626514530989 3233681164082859942949121)
                ·
                  refine ⟨2425260873062144957211841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3233681164082859942949121 2425260873062144957211841)
                  ·
                    refine ⟨1818945654796608717908881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2425260873062144957211841 1818945654796608717908881)
                    ·
                      refine ⟨1364209241097456538431661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1818945654796608717908881 1364209241097456538431661)
                      ·
                        rfl

theorem cell23_2656788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_2656788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656788 prefixEnd_2656788 := by exact prefixLift 2656788
  have htrace : WordTrace (prefixWord ++ tailWord_2656788) baseStart_2656788 baseEnd_2656788 := by
    simpa [prefixWord, tailWord_2656788, baseEnd_2656788] using wordTrace_append hprefix tailTrace_2656788
  have hstable : (prefixWord ++ tailWord_2656788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656788).length < 2 ^ (prefixWord ++ tailWord_2656788).sum := by decide
  have hdescent : baseEnd_2656788 < baseStart_2656788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656914 : List Nat := [3, 2, 3, 1, 2, 1, 1, 4, 1, 5]
def baseStart_2656914 : Nat := 118140960795 + 2656914 * 2 ^ 59
def prefixEnd_2656914 : Nat := 4983230072969 + 3 ^ 40 * 2656914 * 2
def baseEnd_2656914 : Nat := 454757979886641015152027

theorem tailTrace_2656914 : CollatzResearch.WordTrace tailWord_2656914 prefixEnd_2656914 454757979886641015152027 := by
  unfold tailWord_2656914
  simp only [CollatzResearch.WordTrace]
  refine ⟨24226403674115454407562449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64603743130974545086833197 24226403674115454407562449)
  ·
    refine ⟨18169802755586590805671837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24226403674115454407562449 18169802755586590805671837)
    ·
      refine ⟨6813676033344971552126939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18169802755586590805671837 6813676033344971552126939)
      ·
        refine ⟨10220514050017457328190409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6813676033344971552126939 10220514050017457328190409)
        ·
          refine ⟨7665385537513092996142807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10220514050017457328190409 7665385537513092996142807)
          ·
            refine ⟨11498078306269639494214211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7665385537513092996142807 11498078306269639494214211)
            ·
              refine ⟨17247117459404459241321317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11498078306269639494214211 17247117459404459241321317)
              ·
                refine ⟨3233834523638336107747747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17247117459404459241321317 3233834523638336107747747)
                ·
                  refine ⟨4850751785457504161621621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3233834523638336107747747 4850751785457504161621621)
                  ·
                    refine ⟨454757979886641015152027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4850751785457504161621621 454757979886641015152027)
                    ·
                      rfl

theorem cell23_2656914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_2656914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656914 prefixEnd_2656914 := by exact prefixLift 2656914
  have htrace : WordTrace (prefixWord ++ tailWord_2656914) baseStart_2656914 baseEnd_2656914 := by
    simpa [prefixWord, tailWord_2656914, baseEnd_2656914] using wordTrace_append hprefix tailTrace_2656914
  have hstable : (prefixWord ++ tailWord_2656914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656914).length < 2 ^ (prefixWord ++ tailWord_2656914).sum := by decide
  have hdescent : baseEnd_2656914 < baseStart_2656914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656945 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 3, 1, 3]
def baseStart_2656945 : Nat := 118140960795 + 2656945 * 2 ^ 59
def prefixEnd_2656945 : Nat := 4983230072969 + 3 ^ 40 * 2656945 * 2
def baseEnd_2656945 : Nat := 1364289857560212424168439

theorem tailTrace_2656945 : CollatzResearch.WordTrace tailWord_2656945 prefixEnd_2656945 1364289857560212424168439 := by
  unfold tailWord_2656945
  simp only [CollatzResearch.WordTrace]
  refine ⟨96906745359349509924628289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64604496906233006616418859 96906745359349509924628289)
  ·
    refine ⟨72680059019512132443471217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96906745359349509924628289 72680059019512132443471217)
    ·
      refine ⟨54510044264634099332603413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72680059019512132443471217 54510044264634099332603413)
      ·
        refine ⟨2555158324904723406215785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54510044264634099332603413 2555158324904723406215785)
        ·
          refine ⟨1916368743678542554661839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2555158324904723406215785 1916368743678542554661839)
          ·
            refine ⟨2874553115517813831992759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1916368743678542554661839 2874553115517813831992759)
            ·
              refine ⟨4311829673276720747989139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2874553115517813831992759 4311829673276720747989139)
              ·
                refine ⟨6467744509915081121983709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4311829673276720747989139 6467744509915081121983709)
                ·
                  refine ⟨2425404191218155420743891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6467744509915081121983709 2425404191218155420743891)
                  ·
                    refine ⟨3638106286827233131115837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2425404191218155420743891 3638106286827233131115837)
                    ·
                      refine ⟨1364289857560212424168439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3638106286827233131115837 1364289857560212424168439)
                      ·
                        rfl

theorem cell23_2656945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_2656945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656945 prefixEnd_2656945 := by exact prefixLift 2656945
  have htrace : WordTrace (prefixWord ++ tailWord_2656945) baseStart_2656945 baseEnd_2656945 := by
    simpa [prefixWord, tailWord_2656945, baseEnd_2656945] using wordTrace_append hprefix tailTrace_2656945
  have hstable : (prefixWord ++ tailWord_2656945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656945).length < 2 ^ (prefixWord ++ tailWord_2656945).sum := by decide
  have hdescent : baseEnd_2656945 < baseStart_2656945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656957 : List Nat := [1, 4, 1, 2, 1, 4, 2, 8]
def baseStart_2656957 : Nat := 118140960795 + 2656957 * 2 ^ 59
def prefixEnd_2656957 : Nat := 4983230072969 + 3 ^ 40 * 2656957 * 2
def baseEnd_2656957 : Nat := 50529482197335791748829

theorem tailTrace_2656957 : CollatzResearch.WordTrace tailWord_2656957 prefixEnd_2656957 50529482197335791748829 := by
  unfold tailWord_2656957
  simp only [CollatzResearch.WordTrace]
  refine ⟨96907183035306035974065125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64604788690204023982710083 96907183035306035974065125)
  ·
    refine ⟨18170096819119881745137211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96907183035306035974065125 18170096819119881745137211)
    ·
      refine ⟨27255145228679822617705817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18170096819119881745137211 27255145228679822617705817)
      ·
        refine ⟨20441358921509866963279363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27255145228679822617705817 20441358921509866963279363)
        ·
          refine ⟨30662038382264800444919045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20441358921509866963279363 30662038382264800444919045)
          ·
            refine ⟨5749132196674650083422321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30662038382264800444919045 5749132196674650083422321)
            ·
              refine ⟨4311849147505987562566741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5749132196674650083422321 4311849147505987562566741)
              ·
                refine ⟨50529482197335791748829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4311849147505987562566741 50529482197335791748829)
                ·
                  rfl

theorem cell23_2656957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 8].length) (baseStart_2656957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656957 prefixEnd_2656957 := by exact prefixLift 2656957
  have htrace : WordTrace (prefixWord ++ tailWord_2656957) baseStart_2656957 baseEnd_2656957 := by
    simpa [prefixWord, tailWord_2656957, baseEnd_2656957] using wordTrace_append hprefix tailTrace_2656957
  have hstable : (prefixWord ++ tailWord_2656957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656957).length < 2 ^ (prefixWord ++ tailWord_2656957).sum := by decide
  have hdescent : baseEnd_2656957 < baseStart_2656957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656981 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2656981 : Nat := 118140960795 + 2656981 * 2 ^ 59
def prefixEnd_2656981 : Nat := 4983230072969 + 3 ^ 40 * 2656981 * 2
def baseEnd_2656981 : Nat := 1364308342863774283318273

theorem tailTrace_2656981 : CollatzResearch.WordTrace tailWord_2656981 prefixEnd_2656981 1364308342863774283318273 := by
  unfold tailWord_2656981
  simp only [CollatzResearch.WordTrace]
  refine ⟨96908058387219088072938797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64605372258146058715292531 96908058387219088072938797)
  ·
    refine ⟨36340521895207158027352049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96908058387219088072938797 36340521895207158027352049)
    ·
      refine ⟨27255391421405368520514037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36340521895207158027352049 27255391421405368520514037)
      ·
        refine ⟨2555192945756753298798191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27255391421405368520514037 2555192945756753298798191)
        ·
          refine ⟨3832789418635129948197287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2555192945756753298798191 3832789418635129948197287)
          ·
            refine ⟨5749184127952694922295931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832789418635129948197287 5749184127952694922295931)
            ·
              refine ⟨8623776191929042383443897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5749184127952694922295931 8623776191929042383443897)
              ·
                refine ⟨6467832143946781787582923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8623776191929042383443897 6467832143946781787582923)
                ·
                  refine ⟨9701748215920172681374385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6467832143946781787582923 9701748215920172681374385)
                  ·
                    refine ⟨7276311161940129511030789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9701748215920172681374385 7276311161940129511030789)
                    ·
                      refine ⟨1364308342863774283318273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7276311161940129511030789 1364308342863774283318273)
                      ·
                        rfl

theorem cell23_2656981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2656981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656981 prefixEnd_2656981 := by exact prefixLift 2656981
  have htrace : WordTrace (prefixWord ++ tailWord_2656981) baseStart_2656981 baseEnd_2656981 := by
    simpa [prefixWord, tailWord_2656981, baseEnd_2656981] using wordTrace_append hprefix tailTrace_2656981
  have hstable : (prefixWord ++ tailWord_2656981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656981).length < 2 ^ (prefixWord ++ tailWord_2656981).sum := by decide
  have hdescent : baseEnd_2656981 < baseStart_2656981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656984 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 1, 3, 3]
def baseStart_2656984 : Nat := 118140960795 + 2656984 * 2 ^ 59
def prefixEnd_2656984 : Nat := 4983230072969 + 3 ^ 40 * 2656984 * 2
def baseEnd_2656984 : Nat := 1364309883305737771580759

theorem tailTrace_2656984 : CollatzResearch.WordTrace tailWord_2656984 prefixEnd_2656984 1364309883305737771580759 := by
  unfold tailWord_2656984
  simp only [CollatzResearch.WordTrace]
  refine ⟨48454083903104109792649003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64605445204138813056865337 48454083903104109792649003)
  ·
    refine ⟨72681125854656164688973505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48454083903104109792649003 72681125854656164688973505)
    ·
      refine ⟨54510844390992123516730129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72681125854656164688973505 54510844390992123516730129)
      ·
        refine ⟨40883133293244092637547597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54510844390992123516730129 40883133293244092637547597)
        ·
          refine ⟨15331174984966534739080349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40883133293244092637547597 15331174984966534739080349)
          ·
            refine ⟨5749190619362450527155131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15331174984966534739080349 5749190619362450527155131)
            ·
              refine ⟨8623785929043675790732697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5749190619362450527155131 8623785929043675790732697)
              ·
                refine ⟨6467839446782756843049523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8623785929043675790732697 6467839446782756843049523)
                ·
                  refine ⟨9701759170174135264574285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6467839446782756843049523 9701759170174135264574285)
                  ·
                    refine ⟨3638159688815300724215357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9701759170174135264574285 3638159688815300724215357)
                    ·
                      refine ⟨1364309883305737771580759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3638159688815300724215357 1364309883305737771580759)
                      ·
                        rfl

theorem cell23_2656984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_2656984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2656984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2656984 prefixEnd_2656984 := by exact prefixLift 2656984
  have htrace : WordTrace (prefixWord ++ tailWord_2656984) baseStart_2656984 baseEnd_2656984 := by
    simpa [prefixWord, tailWord_2656984, baseEnd_2656984] using wordTrace_append hprefix tailTrace_2656984
  have hstable : (prefixWord ++ tailWord_2656984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656984).length < 2 ^ (prefixWord ++ tailWord_2656984).sum := by decide
  have hdescent : baseEnd_2656984 < baseStart_2656984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657007 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 4]
def baseStart_2657007 : Nat := 118140960795 + 2657007 * 2 ^ 59
def prefixEnd_2657007 : Nat := 4983230072969 + 3 ^ 40 * 2657007 * 2
def baseEnd_2657007 : Nat := 1364321693360791181593153

theorem tailTrace_2657007 : CollatzResearch.WordTrace tailWord_2657007 prefixEnd_2657007 1364321693360791181593153 := by
  unfold tailWord_2657007
  simp only [CollatzResearch.WordTrace]
  refine ⟨96909006685124894513385275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64606004456749929675590183 96909006685124894513385275)
  ·
    refine ⟨145363510027687341770077913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96909006685124894513385275 145363510027687341770077913)
    ·
      refine ⟨109022632520765506327558435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145363510027687341770077913 109022632520765506327558435)
      ·
        refine ⟨163533948781148259491337653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109022632520765506327558435 163533948781148259491337653)
        ·
          refine ⟨15331307698232649327312905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163533948781148259491337653 15331307698232649327312905)
          ·
            refine ⟨11498480773674486995484679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15331307698232649327312905 11498480773674486995484679)
            ·
              refine ⟨17247721160511730493227019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11498480773674486995484679 17247721160511730493227019)
              ·
                refine ⟨25871581740767595739840529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17247721160511730493227019 25871581740767595739840529)
                ·
                  refine ⟨19403686305575696804880397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25871581740767595739840529 19403686305575696804880397)
                  ·
                    refine ⟨7276382364590886301830149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19403686305575696804880397 7276382364590886301830149)
                    ·
                      refine ⟨1364321693360791181593153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7276382364590886301830149 1364321693360791181593153)
                      ·
                        rfl

theorem cell23_2657007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_2657007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657007 prefixEnd_2657007 := by exact prefixLift 2657007
  have htrace : WordTrace (prefixWord ++ tailWord_2657007) baseStart_2657007 baseEnd_2657007 := by
    simpa [prefixWord, tailWord_2657007, baseEnd_2657007] using wordTrace_append hprefix tailTrace_2657007
  have hstable : (prefixWord ++ tailWord_2657007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657007).length < 2 ^ (prefixWord ++ tailWord_2657007).sum := by decide
  have hdescent : baseEnd_2657007 < baseStart_2657007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657027 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 3]
def baseStart_2657027 : Nat := 118140960795 + 2657027 * 2 ^ 59
def prefixEnd_2657027 : Nat := 4983230072969 + 3 ^ 40 * 2657027 * 2
def baseEnd_2657027 : Nat := 1364331962973881103343061

theorem tailTrace_2657027 : CollatzResearch.WordTrace tailWord_2657027 prefixEnd_2657027 1364331962973881103343061 := by
  unfold tailWord_2657027
  simp only [CollatzResearch.WordTrace]
  refine ⟨96909736145052437929113335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64606490763368291952742223 96909736145052437929113335)
  ·
    refine ⟨145364604217578656893670003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96909736145052437929113335 145364604217578656893670003)
    ·
      refine ⟨218046906326367985340505005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145364604217578656893670003 218046906326367985340505005)
      ·
        refine ⟨81767589872387994502689377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218046906326367985340505005 81767589872387994502689377)
        ·
          refine ⟨61325692404290995877017033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81767589872387994502689377 61325692404290995877017033)
          ·
            refine ⟨45994269303218246907762775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61325692404290995877017033 45994269303218246907762775)
            ·
              refine ⟨68991403954827370361644163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45994269303218246907762775 68991403954827370361644163)
              ·
                refine ⟨103487105932241055542466245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68991403954827370361644163 103487105932241055542466245)
                ·
                  refine ⟨19403832362295197914212421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103487105932241055542466245 19403832362295197914212421)
                  ·
                    refine ⟨3638218567930349608914829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19403832362295197914212421 3638218567930349608914829)
                    ·
                      refine ⟨1364331962973881103343061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3638218567930349608914829 1364331962973881103343061)
                      ·
                        rfl

theorem cell23_2657027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_2657027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657027 prefixEnd_2657027 := by exact prefixLift 2657027
  have htrace : WordTrace (prefixWord ++ tailWord_2657027) baseStart_2657027 baseEnd_2657027 := by
    simpa [prefixWord, tailWord_2657027, baseEnd_2657027] using wordTrace_append hprefix tailTrace_2657027
  have hstable : (prefixWord ++ tailWord_2657027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657027).length < 2 ^ (prefixWord ++ tailWord_2657027).sum := by decide
  have hdescent : baseEnd_2657027 < baseStart_2657027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657058 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 4, 2, 2]
def baseStart_2657058 : Nat := 118140960795 + 2657058 * 2 ^ 59
def prefixEnd_2657058 : Nat := 4983230072969 + 3 ^ 40 * 2657058 * 2
def baseEnd_2657058 : Nat := 1364347880874170482055419

theorem tailTrace_2657058 : CollatzResearch.WordTrace tailWord_2657058 prefixEnd_2657058 1364347880874170482055419 := by
  unfold tailWord_2657058
  simp only [CollatzResearch.WordTrace]
  refine ⟨24227716701985032555872957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64607244538626753482327885 24227716701985032555872957)
  ·
    refine ⟨9085393763244387208452359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24227716701985032555872957 9085393763244387208452359)
    ·
      refine ⟨13628090644866580812678539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9085393763244387208452359 13628090644866580812678539)
      ·
        refine ⟨20442135967299871219017809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13628090644866580812678539 20442135967299871219017809)
        ·
          refine ⟨15331601975474903414263357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20442135967299871219017809 15331601975474903414263357)
          ·
            refine ⟨5749350740803088780348759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15331601975474903414263357 5749350740803088780348759)
            ·
              refine ⟨8624026111204633170523139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5749350740803088780348759 8624026111204633170523139)
              ·
                refine ⟨12936039166806949755784709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8624026111204633170523139 12936039166806949755784709)
                ·
                  refine ⟨2425507343776303079209633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12936039166806949755784709 2425507343776303079209633)
                  ·
                    refine ⟨1819130507832227309407225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2425507343776303079209633 1819130507832227309407225)
                    ·
                      refine ⟨1364347880874170482055419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819130507832227309407225 1364347880874170482055419)
                      ·
                        rfl

theorem cell23_2657058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_2657058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657058 prefixEnd_2657058 := by exact prefixLift 2657058
  have htrace : WordTrace (prefixWord ++ tailWord_2657058) baseStart_2657058 baseEnd_2657058 := by
    simpa [prefixWord, tailWord_2657058, baseEnd_2657058] using wordTrace_append hprefix tailTrace_2657058
  have hstable : (prefixWord ++ tailWord_2657058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657058).length < 2 ^ (prefixWord ++ tailWord_2657058).sum := by decide
  have hdescent : baseEnd_2657058 < baseStart_2657058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657064 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 7]
def baseStart_2657064 : Nat := 118140960795 + 2657064 * 2 ^ 59
def prefixEnd_2657064 : Nat := 4983230072969 + 3 ^ 40 * 2657064 * 2
def baseEnd_2657064 : Nat := 151594551306455273175599

theorem tailTrace_2657064 : CollatzResearch.WordTrace tailWord_2657064 prefixEnd_2657064 151594551306455273175599 := by
  unfold tailWord_2657064
  simp only [CollatzResearch.WordTrace]
  refine ⟨48455542822959196624105123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64607390430612262165473497 48455542822959196624105123)
  ·
    refine ⟨72683314234438794936157685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48455542822959196624105123 72683314234438794936157685)
    ·
      refine ⟨6814060709478637025264783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72683314234438794936157685 6814060709478637025264783)
      ·
        refine ⟨10221091064217955537897175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6814060709478637025264783 10221091064217955537897175)
        ·
          refine ⟨15331636596326933306845763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10221091064217955537897175 15331636596326933306845763)
          ·
            refine ⟨22997454894490399960268645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15331636596326933306845763 22997454894490399960268645)
            ·
              refine ⟨4312022792716949992550371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22997454894490399960268645 4312022792716949992550371)
              ·
                refine ⟨6468034189075424988825557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4312022792716949992550371 6468034189075424988825557)
                ·
                  refine ⟨151594551306455273175599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6468034189075424988825557 151594551306455273175599)
                  ·
                    rfl

theorem cell23_2657064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 7].length) (baseStart_2657064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657064 prefixEnd_2657064 := by exact prefixLift 2657064
  have htrace : WordTrace (prefixWord ++ tailWord_2657064) baseStart_2657064 baseEnd_2657064 := by
    simpa [prefixWord, tailWord_2657064, baseEnd_2657064] using wordTrace_append hprefix tailTrace_2657064
  have hstable : (prefixWord ++ tailWord_2657064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657064).length < 2 ^ (prefixWord ++ tailWord_2657064).sum := by decide
  have hdescent : baseEnd_2657064 < baseStart_2657064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657074 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3]
def baseStart_2657074 : Nat := 118140960795 + 2657074 * 2 ^ 59
def prefixEnd_2657074 : Nat := 4983230072969 + 3 ^ 40 * 2657074 * 2
def baseEnd_2657074 : Nat := 1364356096564642419455345

theorem tailTrace_2657074 : CollatzResearch.WordTrace tailWord_2657074 prefixEnd_2657074 1364356096564642419455345 := by
  unfold tailWord_2657074
  simp only [CollatzResearch.WordTrace]
  refine ⟨24227862593970541239018569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64607633583921443304049517 24227862593970541239018569)
  ·
    refine ⟨18170896945477905929263927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24227862593970541239018569 18170896945477905929263927)
    ·
      refine ⟨27256345418216858893895891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18170896945477905929263927 27256345418216858893895891)
      ·
        refine ⟨40884518127325288340843837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27256345418216858893895891 40884518127325288340843837)
        ·
          refine ⟨15331694297746983127816439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40884518127325288340843837 15331694297746983127816439)
          ·
            refine ⟨22997541446620474691724659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15331694297746983127816439 22997541446620474691724659)
            ·
              refine ⟨34496312169930712037586989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22997541446620474691724659 34496312169930712037586989)
              ·
                refine ⟨12936117063724017014095121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34496312169930712037586989 12936117063724017014095121)
                ·
                  refine ⟨9702087797793012760571341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12936117063724017014095121 9702087797793012760571341)
                  ·
                    refine ⟨3638282924172379785214253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9702087797793012760571341 3638282924172379785214253)
                    ·
                      refine ⟨1364356096564642419455345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3638282924172379785214253 1364356096564642419455345)
                      ·
                        rfl

theorem cell23_2657074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_2657074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657074 prefixEnd_2657074 := by exact prefixLift 2657074
  have htrace : WordTrace (prefixWord ++ tailWord_2657074) baseStart_2657074 baseEnd_2657074 := by
    simpa [prefixWord, tailWord_2657074, baseEnd_2657074] using wordTrace_append hprefix tailTrace_2657074
  have hstable : (prefixWord ++ tailWord_2657074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657074).length < 2 ^ (prefixWord ++ tailWord_2657074).sum := by decide
  have hdescent : baseEnd_2657074 < baseStart_2657074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657075 : List Nat := [1, 1, 1, 2, 6, 2, 3, 1, 2, 2, 2]
def baseStart_2657075 : Nat := 118140960795 + 2657075 * 2 ^ 59
def prefixEnd_2657075 : Nat := 4983230072969 + 3 ^ 40 * 2657075 * 2
def baseEnd_2657075 : Nat := 1364356610045296915542841

theorem tailTrace_2657075 : CollatzResearch.WordTrace tailWord_2657075 prefixEnd_2657075 1364356610045296915542841 := by
  unfold tailWord_2657075
  simp only [CollatzResearch.WordTrace]
  refine ⟨96911486848878542126860679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64607657899252361417907119 96911486848878542126860679)
  ·
    refine ⟨145367230273317813190291019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96911486848878542126860679 145367230273317813190291019)
    ·
      refine ⟨218050845409976719785436529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145367230273317813190291019 218050845409976719785436529)
      ·
        refine ⟨163538134057482539839077397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218050845409976719785436529 163538134057482539839077397)
        ·
          refine ⟨7665850033944494054956753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 163538134057482539839077397 7665850033944494054956753)
          ·
            refine ⟨5749387525458370541217565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7665850033944494054956753 5749387525458370541217565)
            ·
              refine ⟨2156020322046888952956587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5749387525458370541217565 2156020322046888952956587)
              ·
                refine ⟨3234030483070333429434881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2156020322046888952956587 3234030483070333429434881)
                ·
                  refine ⟨2425522862302750072076161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3234030483070333429434881 2425522862302750072076161)
                  ·
                    refine ⟨1819142146727062554057121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2425522862302750072076161 1819142146727062554057121)
                    ·
                      refine ⟨1364356610045296915542841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819142146727062554057121 1364356610045296915542841)
                      ·
                        rfl

theorem cell23_2657075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 2, 2, 2].length) (baseStart_2657075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657075 prefixEnd_2657075 := by exact prefixLift 2657075
  have htrace : WordTrace (prefixWord ++ tailWord_2657075) baseStart_2657075 baseEnd_2657075 := by
    simpa [prefixWord, tailWord_2657075, baseEnd_2657075] using wordTrace_append hprefix tailTrace_2657075
  have hstable : (prefixWord ++ tailWord_2657075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657075).length < 2 ^ (prefixWord ++ tailWord_2657075).sum := by decide
  have hdescent : baseEnd_2657075 < baseStart_2657075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657114 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4]
def baseStart_2657114 : Nat := 118140960795 + 2657114 * 2 ^ 59
def prefixEnd_2657114 : Nat := 4983230072969 + 3 ^ 40 * 2657114 * 2
def baseEnd_2657114 : Nat := 1364376635790822262955161

theorem tailTrace_2657114 : CollatzResearch.WordTrace tailWord_2657114 prefixEnd_2657114 1364376635790822262955161 := by
  unfold tailWord_2657114
  simp only [CollatzResearch.WordTrace]
  refine ⟨24228227323934312946882599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64608606197158167858353597 24228227323934312946882599)
  ·
    refine ⟨36342340985901469420323899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24228227323934312946882599 36342340985901469420323899)
    ·
      refine ⟨54513511478852204130485849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36342340985901469420323899 54513511478852204130485849)
      ·
        refine ⟨40885133609139153097864387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54513511478852204130485849 40885133609139153097864387)
        ·
          refine ⟨61327700413708729646796581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40885133609139153097864387 61327700413708729646796581)
          ·
            refine ⟨11498943827570386808774359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61327700413708729646796581 11498943827570386808774359)
            ·
              refine ⟨17248415741355580213161539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11498943827570386808774359 17248415741355580213161539)
              ·
                refine ⟨25872623612033370319742309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17248415741355580213161539 25872623612033370319742309)
                ·
                  refine ⟨4851116927256256934951683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25872623612033370319742309 4851116927256256934951683)
                  ·
                    refine ⟨7276675390884385402427525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4851116927256256934951683 7276675390884385402427525)
                    ·
                      refine ⟨1364376635790822262955161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7276675390884385402427525 1364376635790822262955161)
                      ·
                        rfl

theorem cell23_2657114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_2657114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657114 prefixEnd_2657114 := by exact prefixLift 2657114
  have htrace : WordTrace (prefixWord ++ tailWord_2657114) baseStart_2657114 baseEnd_2657114 := by
    simpa [prefixWord, tailWord_2657114, baseEnd_2657114] using wordTrace_append hprefix tailTrace_2657114
  have hstable : (prefixWord ++ tailWord_2657114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657114).length < 2 ^ (prefixWord ++ tailWord_2657114).sum := by decide
  have hdescent : baseEnd_2657114 < baseStart_2657114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657184 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 3, 5]
def baseStart_2657184 : Nat := 118140960795 + 2657184 * 2 ^ 59
def prefixEnd_2657184 : Nat := 4983230072969 + 3 ^ 40 * 2657184 * 2
def baseEnd_2657184 : Nat := 454804193145545663026613

theorem tailTrace_2657184 : CollatzResearch.WordTrace tailWord_2657184 prefixEnd_2657184 454804193145545663026613 := by
  unfold tailWord_2657184
  simp only [CollatzResearch.WordTrace]
  refine ⟨48457731202741826871289303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64610308270322435828385737 48457731202741826871289303)
  ·
    refine ⟨72686596804112740306933955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48457731202741826871289303 72686596804112740306933955)
    ·
      refine ⟨109029895206169110460400933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72686596804112740306933955 109029895206169110460400933)
      ·
        refine ⟨20443105351156708211325175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109029895206169110460400933 20443105351156708211325175)
        ·
          refine ⟨30664658026735062316987763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20443105351156708211325175 30664658026735062316987763)
          ·
            refine ⟨45996987040102593475481645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30664658026735062316987763 45996987040102593475481645)
            ·
              refine ⟨17248870140038472553305617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45996987040102593475481645 17248870140038472553305617)
              ·
                refine ⟨12936652605028854414979213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17248870140038472553305617 12936652605028854414979213)
                ·
                  refine ⟨4851244726885820405617205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12936652605028854414979213 4851244726885820405617205)
                  ·
                    refine ⟨454804193145545663026613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4851244726885820405617205 454804193145545663026613)
                    ·
                      rfl

theorem cell23_2657184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 3, 5].length) (baseStart_2657184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657184 prefixEnd_2657184 := by exact prefixLift 2657184
  have htrace : WordTrace (prefixWord ++ tailWord_2657184) baseStart_2657184 baseEnd_2657184 := by
    simpa [prefixWord, tailWord_2657184, baseEnd_2657184] using wordTrace_append hprefix tailTrace_2657184
  have hstable : (prefixWord ++ tailWord_2657184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657184).length < 2 ^ (prefixWord ++ tailWord_2657184).sum := by decide
  have hdescent : baseEnd_2657184 < baseStart_2657184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657208 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 2, 3, 2]
def baseStart_2657208 : Nat := 118140960795 + 2657208 * 2 ^ 59
def prefixEnd_2657208 : Nat := 4983230072969 + 3 ^ 40 * 2657208 * 2
def baseEnd_2657208 : Nat := 1364424902972344895179729

theorem tailTrace_2657208 : CollatzResearch.WordTrace tailWord_2657208 prefixEnd_2657208 1364424902972344895179729 := by
  unfold tailWord_2657208
  simp only [CollatzResearch.WordTrace]
  refine ⟨48458168878698352920726139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64610891838264470560968185 48458168878698352920726139)
  ·
    refine ⟨72687253318047529381089209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48458168878698352920726139 72687253318047529381089209)
    ·
      refine ⟨54515439988535647035816907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72687253318047529381089209 54515439988535647035816907)
      ·
        refine ⟨81773159982803470553725361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54515439988535647035816907 81773159982803470553725361)
        ·
          refine ⟨61329869987102602915294021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81773159982803470553725361 61329869987102602915294021)
          ·
            refine ⟨11499350622581738046617629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61329869987102602915294021 11499350622581738046617629)
            ·
              refine ⟨4312256483468151767481611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11499350622581738046617629 4312256483468151767481611)
              ·
                refine ⟨6468384725202227651222417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4312256483468151767481611 6468384725202227651222417)
                ·
                  refine ⟨4851288543901670738416813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6468384725202227651222417 4851288543901670738416813)
                  ·
                    refine ⟨1819233203963126526906305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4851288543901670738416813 1819233203963126526906305)
                    ·
                      refine ⟨1364424902972344895179729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819233203963126526906305 1364424902972344895179729)
                      ·
                        rfl

theorem cell23_2657208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 2, 3, 2].length) (baseStart_2657208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657208 prefixEnd_2657208 := by exact prefixLift 2657208
  have htrace : WordTrace (prefixWord ++ tailWord_2657208) baseStart_2657208 baseEnd_2657208 := by
    simpa [prefixWord, tailWord_2657208, baseEnd_2657208] using wordTrace_append hprefix tailTrace_2657208
  have hstable : (prefixWord ++ tailWord_2657208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657208).length < 2 ^ (prefixWord ++ tailWord_2657208).sum := by decide
  have hdescent : baseEnd_2657208 < baseStart_2657208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657222 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_2657222 : Nat := 118140960795 + 2657222 * 2 ^ 59
def prefixEnd_2657222 : Nat := 4983230072969 + 3 ^ 40 * 2657222 * 2
def baseEnd_2657222 : Nat := 151603565744611982267185

theorem tailTrace_2657222 : CollatzResearch.WordTrace tailWord_2657222 prefixEnd_2657222 151603565744611982267185 := by
  unfold tailWord_2657222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3028651511854562069764435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64611232252897324154974613 3028651511854562069764435)
  ·
    refine ⟨4542977267781843104646653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3028651511854562069764435 4542977267781843104646653)
    ·
      refine ⟨1703616475418191164242495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4542977267781843104646653 1703616475418191164242495)
      ·
        refine ⟨2555424713127286746363743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1703616475418191164242495 2555424713127286746363743)
        ·
          refine ⟨3833137069690930119545615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2555424713127286746363743 3833137069690930119545615)
          ·
            refine ⟨5749705604536395179318423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3833137069690930119545615 5749705604536395179318423)
            ·
              refine ⟨8624558406804592768977635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5749705604536395179318423 8624558406804592768977635)
              ·
                refine ⟨12936837610206889153466453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8624558406804592768977635 12936837610206889153466453)
                ·
                  refine ⟨151603565744611982267185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12936837610206889153466453 151603565744611982267185)
                  ·
                    rfl

theorem cell23_2657222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_2657222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657222 prefixEnd_2657222 := by exact prefixLift 2657222
  have htrace : WordTrace (prefixWord ++ tailWord_2657222) baseStart_2657222 baseEnd_2657222 := by
    simpa [prefixWord, tailWord_2657222, baseEnd_2657222] using wordTrace_append hprefix tailTrace_2657222
  have hstable : (prefixWord ++ tailWord_2657222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657222).length < 2 ^ (prefixWord ++ tailWord_2657222).sum := by decide
  have hdescent : baseEnd_2657222 < baseStart_2657222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657231 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 4, 4]
def baseStart_2657231 : Nat := 118140960795 + 2657231 * 2 ^ 59
def prefixEnd_2657231 : Nat := 4983230072969 + 3 ^ 40 * 2657231 * 2
def baseEnd_2657231 : Nat := 454812237675799435064041

theorem tailTrace_2657231 : CollatzResearch.WordTrace tailWord_2657231 prefixEnd_2657231 454812237675799435064041 := by
  unfold tailWord_2657231
  simp only [CollatzResearch.WordTrace]
  refine ⟨96917176636313380769539547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64611451090875587179693031 96917176636313380769539547)
  ·
    refine ⟨145375764954470071154309321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96917176636313380769539547 145375764954470071154309321)
    ·
      refine ⟨109031823715852553365731991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145375764954470071154309321 109031823715852553365731991)
      ·
        refine ⟨163547735573778830048597987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109031823715852553365731991 163547735573778830048597987)
        ·
          refine ⟨245321603360668245072896981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163547735573778830048597987 245321603360668245072896981)
          ·
            refine ⟨5749725078765661993896023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 245321603360668245072896981 5749725078765661993896023)
            ·
              refine ⟨8624587618148492990844035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5749725078765661993896023 8624587618148492990844035)
              ·
                refine ⟨12936881427222739486266053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8624587618148492990844035 12936881427222739486266053)
                ·
                  refine ⟨2425665267604263653674885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12936881427222739486266053 2425665267604263653674885)
                  ·
                    refine ⟨454812237675799435064041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2425665267604263653674885 454812237675799435064041)
                    ·
                      rfl

theorem cell23_2657231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 4].length) (baseStart_2657231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657231 prefixEnd_2657231 := by exact prefixLift 2657231
  have htrace : WordTrace (prefixWord ++ tailWord_2657231) baseStart_2657231 baseEnd_2657231 := by
    simpa [prefixWord, tailWord_2657231, baseEnd_2657231] using wordTrace_append hprefix tailTrace_2657231
  have hstable : (prefixWord ++ tailWord_2657231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657231).length < 2 ^ (prefixWord ++ tailWord_2657231).sum := by decide
  have hdescent : baseEnd_2657231 < baseStart_2657231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657241 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 1, 1, 5]
def baseStart_2657241 : Nat := 118140960795 + 2657241 * 2 ^ 59
def prefixEnd_2657241 : Nat := 4983230072969 + 3 ^ 40 * 2657241 * 2
def baseEnd_2657241 : Nat := 1364441847833943266067077

theorem tailTrace_2657241 : CollatzResearch.WordTrace tailWord_2657241 prefixEnd_2657241 1364441847833943266067077 := by
  unfold tailWord_2657241
  simp only [CollatzResearch.WordTrace]
  refine ⟨96917541366277152477403577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64611694244184768318269051 96917541366277152477403577)
  ·
    refine ⟨72688156024707864358052683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96917541366277152477403577 72688156024707864358052683)
    ·
      refine ⟨109032234037061796537079025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72688156024707864358052683 109032234037061796537079025)
      ·
        refine ⟨81774175527796347402809269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109032234037061796537079025 81774175527796347402809269)
        ·
          refine ⟨7666328955730907569013369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81774175527796347402809269 7666328955730907569013369)
          ·
            refine ⟨5749746716798180676760027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7666328955730907569013369 5749746716798180676760027)
            ·
              refine ⟨8624620075197271015140041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5749746716798180676760027 8624620075197271015140041)
              ·
                refine ⟨6468465056397953261355031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8624620075197271015140041 6468465056397953261355031)
                ·
                  refine ⟨9702697584596929892032547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6468465056397953261355031 9702697584596929892032547)
                  ·
                    refine ⟨14554046376895394838048821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9702697584596929892032547 14554046376895394838048821)
                    ·
                      refine ⟨1364441847833943266067077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14554046376895394838048821 1364441847833943266067077)
                      ·
                        rfl

theorem cell23_2657241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_2657241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657241 prefixEnd_2657241 := by exact prefixLift 2657241
  have htrace : WordTrace (prefixWord ++ tailWord_2657241) baseStart_2657241 baseEnd_2657241 := by
    simpa [prefixWord, tailWord_2657241, baseEnd_2657241] using wordTrace_append hprefix tailTrace_2657241
  have hstable : (prefixWord ++ tailWord_2657241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657241).length < 2 ^ (prefixWord ++ tailWord_2657241).sum := by decide
  have hdescent : baseEnd_2657241 < baseStart_2657241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657255 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 3, 2, 2]
def baseStart_2657255 : Nat := 118140960795 + 2657255 * 2 ^ 59
def prefixEnd_2657255 : Nat := 4983230072969 + 3 ^ 40 * 2657255 * 2
def baseEnd_2657255 : Nat := 1364449036563106211292013

theorem tailTrace_2657255 : CollatzResearch.WordTrace tailWord_2657255 prefixEnd_2657255 1364449036563106211292013 := by
  unfold tailWord_2657255
  simp only [CollatzResearch.WordTrace]
  refine ⟨96918051988226432868413219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64612034658817621912275479 96918051988226432868413219)
  ·
    refine ⟨145377077982339649302619829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96918051988226432868413219 145377077982339649302619829)
    ·
      refine ⟨13629101060844342122120609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145377077982339649302619829 13629101060844342122120609)
      ·
        refine ⟨10221825795633256591590457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13629101060844342122120609 10221825795633256591590457)
        ·
          refine ⟨7666369346724942443692843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10221825795633256591590457 7666369346724942443692843)
          ·
            refine ⟨11499554020087413665539265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7666369346724942443692843 11499554020087413665539265)
            ·
              refine ⟨8624665515065560249154449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11499554020087413665539265 8624665515065560249154449)
              ·
                refine ⟨6468499136299170186865837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8624665515065560249154449 6468499136299170186865837)
                ·
                  refine ⟨2425687176112188820074689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6468499136299170186865837 2425687176112188820074689)
                  ·
                    refine ⟨1819265382084141615056017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2425687176112188820074689 1819265382084141615056017)
                    ·
                      refine ⟨1364449036563106211292013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819265382084141615056017 1364449036563106211292013)
                      ·
                        rfl

theorem cell23_2657255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_2657255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657255 prefixEnd_2657255 := by exact prefixLift 2657255
  have htrace : WordTrace (prefixWord ++ tailWord_2657255) baseStart_2657255 baseEnd_2657255 := by
    simpa [prefixWord, tailWord_2657255, baseEnd_2657255] using wordTrace_append hprefix tailTrace_2657255
  have hstable : (prefixWord ++ tailWord_2657255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657255).length < 2 ^ (prefixWord ++ tailWord_2657255).sum := by decide
  have hdescent : baseEnd_2657255 < baseStart_2657255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657258 : List Nat := [3, 1, 3, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_2657258 : Nat := 118140960795 + 2657258 * 2 ^ 59
def prefixEnd_2657258 : Nat := 4983230072969 + 3 ^ 40 * 2657258 * 2
def baseEnd_2657258 : Nat := 1364450577005069699554499

theorem tailTrace_2657258 : CollatzResearch.WordTrace tailWord_2657258 prefixEnd_2657258 1364450577005069699554499 := by
  unfold tailWord_2657258
  simp only [CollatzResearch.WordTrace]
  refine ⟨24229540351803891095193107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64612107604810376253848285 24229540351803891095193107)
  ·
    refine ⟨36344310527705836642789661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24229540351803891095193107 36344310527705836642789661)
    ·
      refine ⟨13629116447889688741046123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36344310527705836642789661 13629116447889688741046123)
      ·
        refine ⟨20443674671834533111569185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13629116447889688741046123 20443674671834533111569185)
        ·
          refine ⟨15332756003875899833676889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20443674671834533111569185 15332756003875899833676889)
          ·
            refine ⟨11499567002906924875257667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15332756003875899833676889 11499567002906924875257667)
            ·
              refine ⟨17249350504360387312886501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11499567002906924875257667 17249350504360387312886501)
              ·
                refine ⟨3234253219567572621166219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17249350504360387312886501 3234253219567572621166219)
                ·
                  refine ⟨4851379829351358931749329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3234253219567572621166219 4851379829351358931749329)
                  ·
                    refine ⟨3638534872013519198811997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4851379829351358931749329 3638534872013519198811997)
                    ·
                      refine ⟨1364450577005069699554499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3638534872013519198811997 1364450577005069699554499)
                      ·
                        rfl

theorem cell23_2657258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_2657258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657258 prefixEnd_2657258 := by exact prefixLift 2657258
  have htrace : WordTrace (prefixWord ++ tailWord_2657258) baseStart_2657258 baseEnd_2657258 := by
    simpa [prefixWord, tailWord_2657258, baseEnd_2657258] using wordTrace_append hprefix tailTrace_2657258
  have hstable : (prefixWord ++ tailWord_2657258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657258).length < 2 ^ (prefixWord ++ tailWord_2657258).sum := by decide
  have hdescent : baseEnd_2657258 < baseStart_2657258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657266 : List Nat := [3, 2, 1, 5, 2, 1, 1, 3, 1, 1, 3]
def baseStart_2657266 : Nat := 118140960795 + 2657266 * 2 ^ 59
def prefixEnd_2657266 : Nat := 4983230072969 + 3 ^ 40 * 2657266 * 2
def baseEnd_2657266 : Nat := 1364454684850305668254463

theorem tailTrace_2657266 : CollatzResearch.WordTrace tailWord_2657266 prefixEnd_2657266 1364454684850305668254463 := by
  unfold tailWord_2657266
  simp only [CollatzResearch.WordTrace]
  refine ⟨24229613297796645436765913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64612302127457721164709101 24229613297796645436765913)
  ·
    refine ⟨18172209973347484077574435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24229613297796645436765913 18172209973347484077574435)
    ·
      refine ⟨27258314960021226116361653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18172209973347484077574435 27258314960021226116361653)
      ·
        refine ⟨2555467027501989948408905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27258314960021226116361653 2555467027501989948408905)
        ·
          refine ⟨1916600270626492461306679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2555467027501989948408905 1916600270626492461306679)
          ·
            refine ⟨2874900405939738691960019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1916600270626492461306679 2874900405939738691960019)
            ·
              refine ⟨4312350608909608037940029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2874900405939738691960019 4312350608909608037940029)
              ·
                refine ⟨1617131478341103014227511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4312350608909608037940029 1617131478341103014227511)
                ·
                  refine ⟨2425697217511654521341267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617131478341103014227511 2425697217511654521341267)
                  ·
                    refine ⟨3638545826267481782011901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2425697217511654521341267 3638545826267481782011901)
                    ·
                      refine ⟨1364454684850305668254463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3638545826267481782011901 1364454684850305668254463)
                      ·
                        rfl

theorem cell23_2657266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_2657266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657266 prefixEnd_2657266 := by exact prefixLift 2657266
  have htrace : WordTrace (prefixWord ++ tailWord_2657266) baseStart_2657266 baseEnd_2657266 := by
    simpa [prefixWord, tailWord_2657266, baseEnd_2657266] using wordTrace_append hprefix tailTrace_2657266
  have hstable : (prefixWord ++ tailWord_2657266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657266).length < 2 ^ (prefixWord ++ tailWord_2657266).sum := by decide
  have hdescent : baseEnd_2657266 < baseStart_2657266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657278 : List Nat := [4, 2, 2, 2, 2, 2, 9]
def baseStart_2657278 : Nat := 118140960795 + 2657278 * 2 ^ 59
def prefixEnd_2657278 : Nat := 4983230072969 + 3 ^ 40 * 2657278 * 2
def baseEnd_2657278 : Nat := 16845195637261229892647

theorem tailTrace_2657278 : CollatzResearch.WordTrace tailWord_2657278 prefixEnd_2657278 16845195637261229892647 := by
  unfold tailWord_2657278
  simp only [CollatzResearch.WordTrace]
  refine ⟨12114861358392888474562561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64612593911428738531000325 12114861358392888474562561)
  ·
    refine ⟨9086146018794666355921921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12114861358392888474562561 9086146018794666355921921)
    ·
      refine ⟨6814609514095999766941441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9086146018794666355921921 6814609514095999766941441)
      ·
        refine ⟨5110957135571999825206081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6814609514095999766941441 5110957135571999825206081)
        ·
          refine ⟨3833217851678999868904561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5110957135571999825206081 3833217851678999868904561)
          ·
            refine ⟨2874913388759249901678421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3833217851678999868904561 2874913388759249901678421)
            ·
              refine ⟨16845195637261229892647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2874913388759249901678421 16845195637261229892647)
              ·
                rfl

theorem cell23_2657278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 9].length) (baseStart_2657278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657278 prefixEnd_2657278 := by exact prefixLift 2657278
  have htrace : WordTrace (prefixWord ++ tailWord_2657278) baseStart_2657278 baseEnd_2657278 := by
    simpa [prefixWord, tailWord_2657278, baseEnd_2657278] using wordTrace_append hprefix tailTrace_2657278
  have hstable : (prefixWord ++ tailWord_2657278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657278).length < 2 ^ (prefixWord ++ tailWord_2657278).sum := by decide
  have hdescent : baseEnd_2657278 < baseStart_2657278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657288 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 4, 1, 3]
def baseStart_2657288 : Nat := 118140960795 + 2657288 * 2 ^ 59
def prefixEnd_2657288 : Nat := 4983230072969 + 3 ^ 40 * 2657288 * 2
def baseEnd_2657288 : Nat := 1364465981424704582179361

theorem tailTrace_2657288 : CollatzResearch.WordTrace tailWord_2657288 prefixEnd_2657288 1364465981424704582179361 := by
  unfold tailWord_2657288
  simp only [CollatzResearch.WordTrace]
  refine ⟨48459627798553439752182259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64612837064737919669576345 48459627798553439752182259)
  ·
    refine ⟨72689441697830159628273389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48459627798553439752182259 72689441697830159628273389)
    ·
      refine ⟨27258540636686309860602521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72689441697830159628273389 27258540636686309860602521)
      ·
        refine ⟨20443905477514732395451891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27258540636686309860602521 20443905477514732395451891)
        ·
          refine ⟨30665858216272098593177837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20443905477514732395451891 30665858216272098593177837)
          ·
            refine ⟨11499696831102036972441689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30665858216272098593177837 11499696831102036972441689)
            ·
              refine ⟨8624772623326527729331267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11499696831102036972441689 8624772623326527729331267)
              ·
                refine ⟨12937158934989791593996901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8624772623326527729331267 12937158934989791593996901)
                ·
                  refine ⟨2425717300310585923874419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12937158934989791593996901 2425717300310585923874419)
                  ·
                    refine ⟨3638575950465878885811629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2425717300310585923874419 3638575950465878885811629)
                    ·
                      refine ⟨1364465981424704582179361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3638575950465878885811629 1364465981424704582179361)
                      ·
                        rfl

theorem cell23_2657288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_2657288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657288 prefixEnd_2657288 := by exact prefixLift 2657288
  have htrace : WordTrace (prefixWord ++ tailWord_2657288) baseStart_2657288 baseEnd_2657288 := by
    simpa [prefixWord, tailWord_2657288, baseEnd_2657288] using wordTrace_append hprefix tailTrace_2657288
  have hstable : (prefixWord ++ tailWord_2657288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657288).length < 2 ^ (prefixWord ++ tailWord_2657288).sum := by decide
  have hdescent : baseEnd_2657288 < baseStart_2657288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657305 : List Nat := [1, 2, 1, 2, 1, 1, 8, 1, 2, 1, 3]
def baseStart_2657305 : Nat := 118140960795 + 2657305 * 2 ^ 59
def prefixEnd_2657305 : Nat := 4983230072969 + 3 ^ 40 * 2657305 * 2
def baseEnd_2657305 : Nat := 1364474710595831015666783

theorem tailTrace_2657305 : CollatzResearch.WordTrace tailWord_2657305 prefixEnd_2657305 1364474710595831015666783 := by
  unfold tailWord_2657305
  simp only [CollatzResearch.WordTrace]
  refine ⟨96919875638045291407733369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64613250425363527605155579 96919875638045291407733369)
  ·
    refine ⟨72689906728533968555800027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96919875638045291407733369 72689906728533968555800027)
    ·
      refine ⟨109034860092800952833700041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72689906728533968555800027 109034860092800952833700041)
      ·
        refine ⟨81776145069600714625275031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109034860092800952833700041 81776145069600714625275031)
        ·
          refine ⟨122664217604401071937912547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81776145069600714625275031 122664217604401071937912547)
          ·
            refine ⟨183996326406601607906868821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122664217604401071937912547 183996326406601607906868821)
            ·
              refine ⟨2156206950077362592658619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 183996326406601607906868821 2156206950077362592658619)
              ·
                refine ⟨3234310425116043888987929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2156206950077362592658619 3234310425116043888987929)
                ·
                  refine ⟨2425732818837032916740947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3234310425116043888987929 2425732818837032916740947)
                  ·
                    refine ⟨3638599228255549375111421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2425732818837032916740947 3638599228255549375111421)
                    ·
                      refine ⟨1364474710595831015666783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3638599228255549375111421 1364474710595831015666783)
                      ·
                        rfl

theorem cell23_2657305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 2, 1, 3].length) (baseStart_2657305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657305 prefixEnd_2657305 := by exact prefixLift 2657305
  have htrace : WordTrace (prefixWord ++ tailWord_2657305) baseStart_2657305 baseEnd_2657305 := by
    simpa [prefixWord, tailWord_2657305, baseEnd_2657305] using wordTrace_append hprefix tailTrace_2657305
  have hstable : (prefixWord ++ tailWord_2657305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657305).length < 2 ^ (prefixWord ++ tailWord_2657305).sum := by decide
  have hdescent : baseEnd_2657305 < baseStart_2657305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657315 : List Nat := [1, 1, 1, 4, 3, 2, 3, 2, 1, 3, 2]
def baseStart_2657315 : Nat := 118140960795 + 2657315 * 2 ^ 59
def prefixEnd_2657315 : Nat := 4983230072969 + 3 ^ 40 * 2657315 * 2
def baseEnd_2657315 : Nat := 1364479845402375976541737

theorem tailTrace_2657315 : CollatzResearch.WordTrace tailWord_2657315 prefixEnd_2657315 1364479845402375976541737 := by
  unfold tailWord_2657315
  simp only [CollatzResearch.WordTrace]
  refine ⟨96920240368009063115597399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64613493578672708743731599 96920240368009063115597399)
  ·
    refine ⟨145380360552013594673396099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96920240368009063115597399 145380360552013594673396099)
    ·
      refine ⟨218070540828020392010094149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145380360552013594673396099 218070540828020392010094149)
      ·
        refine ⟨40888226405253823501892653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218070540828020392010094149 40888226405253823501892653)
        ·
          refine ⟨15333084901970183813209745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40888226405253823501892653 15333084901970183813209745)
          ·
            refine ⟨11499813676477637859907309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15333084901970183813209745 11499813676477637859907309)
            ·
              refine ⟨4312430128679114197465241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11499813676477637859907309 4312430128679114197465241)
              ·
                refine ⟨3234322596509335648098931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4312430128679114197465241 3234322596509335648098931)
                ·
                  refine ⟨4851483894764003472148397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3234322596509335648098931 4851483894764003472148397)
                  ·
                    refine ⟨1819306460536501302055649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4851483894764003472148397 1819306460536501302055649)
                    ·
                      refine ⟨1364479845402375976541737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819306460536501302055649 1364479845402375976541737)
                      ·
                        rfl

theorem cell23_2657315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_2657315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657315 prefixEnd_2657315 := by exact prefixLift 2657315
  have htrace : WordTrace (prefixWord ++ tailWord_2657315) baseStart_2657315 baseEnd_2657315 := by
    simpa [prefixWord, tailWord_2657315, baseEnd_2657315] using wordTrace_append hprefix tailTrace_2657315
  have hstable : (prefixWord ++ tailWord_2657315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657315).length < 2 ^ (prefixWord ++ tailWord_2657315).sum := by decide
  have hdescent : baseEnd_2657315 < baseStart_2657315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657328 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 1, 4, 2]
def baseStart_2657328 : Nat := 118140960795 + 2657328 * 2 ^ 59
def prefixEnd_2657328 : Nat := 4983230072969 + 3 ^ 40 * 2657328 * 2
def baseEnd_2657328 : Nat := 1364486520650884425679177

theorem tailTrace_2657328 : CollatzResearch.WordTrace tailWord_2657328 prefixEnd_2657328 1364486520650884425679177 := by
  unfold tailWord_2657328
  simp only [CollatzResearch.WordTrace]
  refine ⟨48460357258480983167910319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64613809677974644223880425 48460357258480983167910319)
  ·
    refine ⟨72690535887721474751865479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48460357258480983167910319 72690535887721474751865479)
    ·
      refine ⟨109035803831582212127798219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72690535887721474751865479 109035803831582212127798219)
      ·
        refine ⟨163553705747373318191697329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109035803831582212127798219 163553705747373318191697329)
        ·
          refine ⟨122665279310529988643772997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163553705747373318191697329 122665279310529988643772997)
          ·
            refine ⟨22999739870724372870707437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122665279310529988643772997 22999739870724372870707437)
            ·
              refine ⟨8624902451521639826515289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22999739870724372870707437 8624902451521639826515289)
              ·
                refine ⟨6468676838641229869886467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8624902451521639826515289 6468676838641229869886467)
                ·
                  refine ⟨9703015257961844804829701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6468676838641229869886467 9703015257961844804829701)
                  ·
                    refine ⟨1819315360867845900905569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9703015257961844804829701 1819315360867845900905569)
                    ·
                      refine ⟨1364486520650884425679177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819315360867845900905569 1364486520650884425679177)
                      ·
                        rfl

theorem cell23_2657328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 1, 4, 2].length) (baseStart_2657328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657328 prefixEnd_2657328 := by exact prefixLift 2657328
  have htrace : WordTrace (prefixWord ++ tailWord_2657328) baseStart_2657328 baseEnd_2657328 := by
    simpa [prefixWord, tailWord_2657328, baseEnd_2657328] using wordTrace_append hprefix tailTrace_2657328
  have hstable : (prefixWord ++ tailWord_2657328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657328).length < 2 ^ (prefixWord ++ tailWord_2657328).sum := by decide
  have hdescent : baseEnd_2657328 < baseStart_2657328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657361 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 1, 5, 3]
def baseStart_2657361 : Nat := 118140960795 + 2657361 * 2 ^ 59
def prefixEnd_2657361 : Nat := 4983230072969 + 3 ^ 40 * 2657361 * 2
def baseEnd_2657361 : Nat := 1364503465512482796566525

theorem tailTrace_2657361 : CollatzResearch.WordTrace tailWord_2657361 prefixEnd_2657361 1364503465512482796566525 := by
  unfold tailWord_2657361
  simp only [CollatzResearch.WordTrace]
  refine ⟨96921918125842412971771937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64614612083894941981181291 96921918125842412971771937)
  ·
    refine ⟨72691438594381809728828953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96921918125842412971771937 72691438594381809728828953)
    ·
      refine ⟨54518578945786357296621715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72691438594381809728828953 54518578945786357296621715)
      ·
        refine ⟨81777868418679535944932573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54518578945786357296621715 81777868418679535944932573)
        ·
          refine ⟨30666700657004825979349715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81777868418679535944932573 30666700657004825979349715)
          ·
            refine ⟨46000050985507238969024573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30666700657004825979349715 46000050985507238969024573)
            ·
              refine ⟨17250019119565214613384215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46000050985507238969024573 17250019119565214613384215)
              ·
                refine ⟨25875028679347821920076323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17250019119565214613384215 25875028679347821920076323)
                ·
                  refine ⟨38812543019021732880114485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25875028679347821920076323 38812543019021732880114485)
                  ·
                    refine ⟨3638675908033287457510733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38812543019021732880114485 3638675908033287457510733)
                    ·
                      refine ⟨1364503465512482796566525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3638675908033287457510733 1364503465512482796566525)
                      ·
                        rfl

theorem cell23_2657361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_2657361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657361 prefixEnd_2657361 := by exact prefixLift 2657361
  have htrace : WordTrace (prefixWord ++ tailWord_2657361) baseStart_2657361 baseEnd_2657361 := by
    simpa [prefixWord, tailWord_2657361, baseEnd_2657361] using wordTrace_append hprefix tailTrace_2657361
  have hstable : (prefixWord ++ tailWord_2657361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657361).length < 2 ^ (prefixWord ++ tailWord_2657361).sum := by decide
  have hdescent : baseEnd_2657361 < baseStart_2657361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657362 : List Nat := [3, 2, 2, 1, 3, 1, 2, 3, 2, 2, 2]
def baseStart_2657362 : Nat := 118140960795 + 2657362 * 2 ^ 59
def prefixEnd_2657362 : Nat := 4983230072969 + 3 ^ 40 * 2657362 * 2
def baseEnd_2657362 : Nat := 1364503978993137292654021

theorem tailTrace_2657362 : CollatzResearch.WordTrace tailWord_2657362 prefixEnd_2657362 1364503978993137292654021 := by
  unfold tailWord_2657362
  simp only [CollatzResearch.WordTrace]
  refine ⟨24230488649709697535639585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64614636399225860095038893 24230488649709697535639585)
  ·
    refine ⟨18172866487282273151729689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24230488649709697535639585 18172866487282273151729689)
    ·
      refine ⟨13629649865461704863797267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18172866487282273151729689 13629649865461704863797267)
      ·
        refine ⟨20444474798192557295695901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13629649865461704863797267 20444474798192557295695901)
        ·
          refine ⟨7666678049322208985885963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20444474798192557295695901 7666678049322208985885963)
          ·
            refine ⟨11500017073983313478828945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7666678049322208985885963 11500017073983313478828945)
            ·
              refine ⟨8625012805487485109121709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11500017073983313478828945 8625012805487485109121709)
              ·
                refine ⟨3234379802057806915920641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8625012805487485109121709 3234379802057806915920641)
                ·
                  refine ⟨2425784851543355186940481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3234379802057806915920641 2425784851543355186940481)
                  ·
                    refine ⟨1819338638657516390205361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2425784851543355186940481 1819338638657516390205361)
                    ·
                      refine ⟨1364503978993137292654021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819338638657516390205361 1364503978993137292654021)
                      ·
                        rfl

theorem cell23_2657362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_2657362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657362 prefixEnd_2657362 := by exact prefixLift 2657362
  have htrace : WordTrace (prefixWord ++ tailWord_2657362) baseStart_2657362 baseEnd_2657362 := by
    simpa [prefixWord, tailWord_2657362, baseEnd_2657362] using wordTrace_append hprefix tailTrace_2657362
  have hstable : (prefixWord ++ tailWord_2657362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657362).length < 2 ^ (prefixWord ++ tailWord_2657362).sum := by decide
  have hdescent : baseEnd_2657362 < baseStart_2657362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657381 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 1, 7]
def baseStart_2657381 : Nat := 118140960795 + 2657381 * 2 ^ 59
def prefixEnd_2657381 : Nat := 4983230072969 + 3 ^ 40 * 2657381 * 2
def baseEnd_2657381 : Nat := 454837911708524239438811

theorem tailTrace_2657381 : CollatzResearch.WordTrace tailWord_2657381 prefixEnd_2657381 454837911708524239438811 := by
  unfold tailWord_2657381
  simp only [CollatzResearch.WordTrace]
  refine ⟨96922647585769956387499997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64615098390513304258333331 96922647585769956387499997)
  ·
    refine ⟨36345992844663733645312499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96922647585769956387499997 36345992844663733645312499)
    ·
      refine ⟨54518989266995600467968749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36345992844663733645312499 54518989266995600467968749)
      ·
        refine ⟨20444620975123350175488281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54518989266995600467968749 20444620975123350175488281)
        ·
          refine ⟨15333465731342512631616211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20444620975123350175488281 15333465731342512631616211)
          ·
            refine ⟨23000198597013768947424317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15333465731342512631616211 23000198597013768947424317)
            ·
              refine ⟨8625074473880163355284119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23000198597013768947424317 8625074473880163355284119)
              ·
                refine ⟨12937611710820245032926179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8625074473880163355284119 12937611710820245032926179)
                ·
                  refine ⟨19406417566230367549389269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12937611710820245032926179 19406417566230367549389269)
                  ·
                    refine ⟨454837911708524239438811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19406417566230367549389269 454837911708524239438811)
                    ·
                      rfl

theorem cell23_2657381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_2657381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657381 prefixEnd_2657381 := by exact prefixLift 2657381
  have htrace : WordTrace (prefixWord ++ tailWord_2657381) baseStart_2657381 baseEnd_2657381 := by
    simpa [prefixWord, tailWord_2657381, baseEnd_2657381] using wordTrace_append hprefix tailTrace_2657381
  have hstable : (prefixWord ++ tailWord_2657381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657381).length < 2 ^ (prefixWord ++ tailWord_2657381).sum := by decide
  have hdescent : baseEnd_2657381 < baseStart_2657381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657398 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_2657398 : Nat := 118140960795 + 2657398 * 2 ^ 59
def prefixEnd_2657398 : Nat := 4983230072969 + 3 ^ 40 * 2657398 * 2
def baseEnd_2657398 : Nat := 454840821432233050601285

theorem tailTrace_2657398 : CollatzResearch.WordTrace tailWord_2657398 prefixEnd_2657398 454840821432233050601285 := by
  unfold tailWord_2657398
  simp only [CollatzResearch.WordTrace]
  refine ⟨6057704226669273018179303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64615511751138912193912565 6057704226669273018179303)
  ·
    refine ⟨9086556340003909527268955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6057704226669273018179303 9086556340003909527268955)
    ·
      refine ⟨13629834510005864290903433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9086556340003909527268955 13629834510005864290903433)
      ·
        refine ⟨10222375882504398218177575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13629834510005864290903433 10222375882504398218177575)
        ·
          refine ⟨15333563823756597327266363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10222375882504398218177575 15333563823756597327266363)
          ·
            refine ⟨23000345735634895990899545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15333563823756597327266363 23000345735634895990899545)
            ·
              refine ⟨17250259301726171993174659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23000345735634895990899545 17250259301726171993174659)
              ·
                refine ⟨25875388952589257989761989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17250259301726171993174659 25875388952589257989761989)
                ·
                  refine ⟨4851635428610485873080373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25875388952589257989761989 4851635428610485873080373)
                  ·
                    refine ⟨454840821432233050601285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4851635428610485873080373 454840821432233050601285)
                    ·
                      rfl

theorem cell23_2657398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_2657398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657398 prefixEnd_2657398 := by exact prefixLift 2657398
  have htrace : WordTrace (prefixWord ++ tailWord_2657398) baseStart_2657398 baseEnd_2657398 := by
    simpa [prefixWord, tailWord_2657398, baseEnd_2657398] using wordTrace_append hprefix tailTrace_2657398
  have hstable : (prefixWord ++ tailWord_2657398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657398).length < 2 ^ (prefixWord ++ tailWord_2657398).sum := by decide
  have hdescent : baseEnd_2657398 < baseStart_2657398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657441 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 10]
def baseStart_2657441 : Nat := 118140960795 + 2657441 * 2 ^ 59
def prefixEnd_2657441 : Nat := 4983230072969 + 3 ^ 40 * 2657441 * 2
def baseEnd_2657441 : Nat := 151616060440538053729573

theorem tailTrace_2657441 : CollatzResearch.WordTrace tailWord_2657441 prefixEnd_2657441 151616060440538053729573 := by
  unfold tailWord_2657441
  simp only [CollatzResearch.WordTrace]
  refine ⟨96924835965552586634684177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64616557310368391089789451 96924835965552586634684177)
  ·
    refine ⟨72693626974164439976013133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96924835965552586634684177 72693626974164439976013133)
    ·
      refine ⟨27260110115311664991004925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72693626974164439976013133 27260110115311664991004925)
      ·
        refine ⟨10222541293241874371626847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27260110115311664991004925 10222541293241874371626847)
        ·
          refine ⟨15333811939862811557440271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10222541293241874371626847 15333811939862811557440271)
          ·
            refine ⟨23000717909794217336160407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15333811939862811557440271 23000717909794217336160407)
            ·
              refine ⟨34501076864691326004240611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23000717909794217336160407 34501076864691326004240611)
              ·
                refine ⟨51751615297036989006360917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34501076864691326004240611 51751615297036989006360917)
                ·
                  refine ⟨151616060440538053729573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 51751615297036989006360917 151616060440538053729573)
                  ·
                    rfl

theorem cell23_2657441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 10].length) (baseStart_2657441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657441 prefixEnd_2657441 := by exact prefixLift 2657441
  have htrace : WordTrace (prefixWord ++ tailWord_2657441) baseStart_2657441 baseEnd_2657441 := by
    simpa [prefixWord, tailWord_2657441, baseEnd_2657441] using wordTrace_append hprefix tailTrace_2657441
  have hstable : (prefixWord ++ tailWord_2657441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657441).length < 2 ^ (prefixWord ++ tailWord_2657441).sum := by decide
  have hdescent : baseEnd_2657441 < baseStart_2657441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657491 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 4]
def baseStart_2657491 : Nat := 118140960795 + 2657491 * 2 ^ 59
def prefixEnd_2657491 : Nat := 4983230072969 + 3 ^ 40 * 2657491 * 2
def baseEnd_2657491 : Nat := 1364570217997567287940927

theorem tailTrace_2657491 : CollatzResearch.WordTrace tailWord_2657491 prefixEnd_2657491 1364570217997567287940927 := by
  unfold tailWord_2657491
  simp only [CollatzResearch.WordTrace]
  refine ⟨96926659615371445174004327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64617773076914296782669551 96926659615371445174004327)
  ·
    refine ⟨145389989423057167761006491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96926659615371445174004327 145389989423057167761006491)
    ·
      refine ⟨218084984134585751641509737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145389989423057167761006491 218084984134585751641509737)
      ·
        refine ⟨163563738100939313731132303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218084984134585751641509737 163563738100939313731132303)
        ·
          refine ⟨245345607151408970596698455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163563738100939313731132303 245345607151408970596698455)
          ·
            refine ⟨368018410727113455895047683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245345607151408970596698455 368018410727113455895047683)
            ·
              refine ⟨552027616090670183842571525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368018410727113455895047683 552027616090670183842571525)
              ·
                refine ⟨103505178017000659470482161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 552027616090670183842571525 103505178017000659470482161)
                ·
                  refine ⟨77628883512750494602861621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103505178017000659470482161 77628883512750494602861621)
                  ·
                    refine ⟨7277707829320358869018277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77628883512750494602861621 7277707829320358869018277)
                    ·
                      refine ⟨1364570217997567287940927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7277707829320358869018277 1364570217997567287940927)
                      ·
                        rfl

theorem cell23_2657491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_2657491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657491 prefixEnd_2657491 := by exact prefixLift 2657491
  have htrace : WordTrace (prefixWord ++ tailWord_2657491) baseStart_2657491 baseEnd_2657491 := by
    simpa [prefixWord, tailWord_2657491, baseEnd_2657491] using wordTrace_append hprefix tailTrace_2657491
  have hstable : (prefixWord ++ tailWord_2657491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657491).length < 2 ^ (prefixWord ++ tailWord_2657491).sum := by decide
  have hdescent : baseEnd_2657491 < baseStart_2657491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657495 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 2, 3, 2]
def baseStart_2657495 : Nat := 118140960795 + 2657495 * 2 ^ 59
def prefixEnd_2657495 : Nat := 4983230072969 + 3 ^ 40 * 2657495 * 2
def baseEnd_2657495 : Nat := 1364572271920185272290909

theorem tailTrace_2657495 : CollatzResearch.WordTrace tailWord_2657495 prefixEnd_2657495 1364572271920185272290909 := by
  unfold tailWord_2657495
  simp only [CollatzResearch.WordTrace]
  refine ⟨96926805507356953857149939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64617870338237969238099959 96926805507356953857149939)
  ·
    refine ⟨145390208261035430785724909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96926805507356953857149939 145390208261035430785724909)
    ·
      refine ⟨54521328097888286544646841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145390208261035430785724909 54521328097888286544646841)
      ·
        refine ⟨40890996073416214908485131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54521328097888286544646841 40890996073416214908485131)
        ·
          refine ⟨61336494110124322362727697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40890996073416214908485131 61336494110124322362727697)
          ·
            refine ⟨46002370582593241772045773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61336494110124322362727697 46002370582593241772045773)
            ·
              refine ⟨17250888968472465664517165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46002370582593241772045773 17250888968472465664517165)
              ·
                refine ⟨6469083363177174624193937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17250888968472465664517165 6469083363177174624193937)
                ·
                  refine ⟨4851812522382880968145453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6469083363177174624193937 4851812522382880968145453)
                  ·
                    refine ⟨1819429695893580363054545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4851812522382880968145453 1819429695893580363054545)
                    ·
                      refine ⟨1364572271920185272290909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819429695893580363054545 1364572271920185272290909)
                      ·
                        rfl

theorem cell23_2657495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_2657495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657495 prefixEnd_2657495 := by exact prefixLift 2657495
  have htrace : WordTrace (prefixWord ++ tailWord_2657495) baseStart_2657495 baseEnd_2657495 := by
    simpa [prefixWord, tailWord_2657495, baseEnd_2657495] using wordTrace_append hprefix tailTrace_2657495
  have hstable : (prefixWord ++ tailWord_2657495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657495).length < 2 ^ (prefixWord ++ tailWord_2657495).sum := by decide
  have hdescent : baseEnd_2657495 < baseStart_2657495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657519 : List Nat := [1, 1, 2, 1, 7, 1, 1, 4, 1, 1, 3]
def baseStart_2657519 : Nat := 118140960795 + 2657519 * 2 ^ 59
def prefixEnd_2657519 : Nat := 4983230072969 + 3 ^ 40 * 2657519 * 2
def baseEnd_2657519 : Nat := 1364584595455893178390799

theorem tailTrace_2657519 : CollatzResearch.WordTrace tailWord_2657519 prefixEnd_2657519 1364584595455893178390799 := by
  unfold tailWord_2657519
  simp only [CollatzResearch.WordTrace]
  refine ⟨96927680859270005956023611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64618453906180003970682407 96927680859270005956023611)
  ·
    refine ⟨145391521288905008934035417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96927680859270005956023611 145391521288905008934035417)
    ·
      refine ⟨109043640966678756700526563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145391521288905008934035417 109043640966678756700526563)
      ·
        refine ⟨163565461450018135050789845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109043640966678756700526563 163565461450018135050789845)
        ·
          refine ⟨3833565502734800040252887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 163565461450018135050789845 3833565502734800040252887)
          ·
            refine ⟨5750348254102200060379331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3833565502734800040252887 5750348254102200060379331)
            ·
              refine ⟨8625522381153300090568997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5750348254102200060379331 8625522381153300090568997)
              ·
                refine ⟨1617285446466243766981687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8625522381153300090568997 1617285446466243766981687)
                ·
                  refine ⟨2425928169699365650472531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617285446466243766981687 2425928169699365650472531)
                  ·
                    refine ⟨3638892254549048475708797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2425928169699365650472531 3638892254549048475708797)
                    ·
                      refine ⟨1364584595455893178390799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3638892254549048475708797 1364584595455893178390799)
                      ·
                        rfl

theorem cell23_2657519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 1, 1, 3].length) (baseStart_2657519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657519 prefixEnd_2657519 := by exact prefixLift 2657519
  have htrace : WordTrace (prefixWord ++ tailWord_2657519) baseStart_2657519 baseEnd_2657519 := by
    simpa [prefixWord, tailWord_2657519, baseEnd_2657519] using wordTrace_append hprefix tailTrace_2657519
  have hstable : (prefixWord ++ tailWord_2657519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657519).length < 2 ^ (prefixWord ++ tailWord_2657519).sum := by decide
  have hdescent : baseEnd_2657519 < baseStart_2657519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657535 : List Nat := [1, 1, 2, 2, 1, 5, 2, 3, 2, 4]
def baseStart_2657535 : Nat := 118140960795 + 2657535 * 2 ^ 59
def prefixEnd_2657535 : Nat := 4983230072969 + 3 ^ 40 * 2657535 * 2
def baseEnd_2657535 : Nat := 454864270382121705263575

theorem tailTrace_2657535 : CollatzResearch.WordTrace tailWord_2657535 prefixEnd_2657535 454864270382121705263575 := by
  unfold tailWord_2657535
  simp only [CollatzResearch.WordTrace]
  refine ⟨96928264427212040688606059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64618842951474693792404039 96928264427212040688606059)
  ·
    refine ⟨145392396640818061032909089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96928264427212040688606059 145392396640818061032909089)
    ·
      refine ⟨109044297480613545774681817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145392396640818061032909089 109044297480613545774681817)
      ·
        refine ⟨81783223110460159331011363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109044297480613545774681817 81783223110460159331011363)
        ·
          refine ⟨122674834665690238996517045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81783223110460159331011363 122674834665690238996517045)
          ·
            refine ⟨11500765749908459905923473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122674834665690238996517045 11500765749908459905923473)
            ·
              refine ⟨8625574312431344929442605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11500765749908459905923473 8625574312431344929442605)
              ·
                refine ⟨3234590367161754348540977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8625574312431344929442605 3234590367161754348540977)
                ·
                  refine ⟨2425942775371315761405733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3234590367161754348540977 2425942775371315761405733)
                  ·
                    refine ⟨454864270382121705263575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2425942775371315761405733 454864270382121705263575)
                    ·
                      rfl

theorem cell23_2657535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 4].length) (baseStart_2657535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657535 prefixEnd_2657535 := by exact prefixLift 2657535
  have htrace : WordTrace (prefixWord ++ tailWord_2657535) baseStart_2657535 baseEnd_2657535 := by
    simpa [prefixWord, tailWord_2657535, baseEnd_2657535] using wordTrace_append hprefix tailTrace_2657535
  have hstable : (prefixWord ++ tailWord_2657535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657535).length < 2 ^ (prefixWord ++ tailWord_2657535).sum := by decide
  have hdescent : baseEnd_2657535 < baseStart_2657535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657545 : List Nat := [1, 2, 1, 1, 3, 3, 2, 4, 1, 2, 3]
def baseStart_2657545 : Nat := 118140960795 + 2657545 * 2 ^ 59
def prefixEnd_2657545 : Nat := 4983230072969 + 3 ^ 40 * 2657545 * 2
def baseEnd_2657545 : Nat := 1364597945952910076665679

theorem tailTrace_2657545 : CollatzResearch.WordTrace tailWord_2657545 prefixEnd_2657545 1364597945952910076665679 := by
  unfold tailWord_2657545
  simp only [CollatzResearch.WordTrace]
  refine ⟨96928629157175812396470089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64619086104783874930980059 96928629157175812396470089)
  ·
    refine ⟨72696471867881859297352567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96928629157175812396470089 72696471867881859297352567)
    ·
      refine ⟨109044707801822788946028851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72696471867881859297352567 109044707801822788946028851)
      ·
        refine ⟨163567061702734183419043277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109044707801822788946028851 163567061702734183419043277)
        ·
          refine ⟨61337648138525318782141229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163567061702734183419043277 61337648138525318782141229)
          ·
            refine ⟨23001618051946994543302961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61337648138525318782141229 23001618051946994543302961)
            ·
              refine ⟨17251213538960245907477221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23001618051946994543302961 17251213538960245907477221)
              ·
                refine ⟨3234602538555046107651979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17251213538960245907477221 3234602538555046107651979)
                ·
                  refine ⟨4851903807832569161477969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3234602538555046107651979 4851903807832569161477969)
                  ·
                    refine ⟨3638927855874426871108477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4851903807832569161477969 3638927855874426871108477)
                    ·
                      refine ⟨1364597945952910076665679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3638927855874426871108477 1364597945952910076665679)
                      ·
                        rfl

theorem cell23_2657545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 2, 3].length) (baseStart_2657545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657545 prefixEnd_2657545 := by exact prefixLift 2657545
  have htrace : WordTrace (prefixWord ++ tailWord_2657545) baseStart_2657545 baseEnd_2657545 := by
    simpa [prefixWord, tailWord_2657545, baseEnd_2657545] using wordTrace_append hprefix tailTrace_2657545
  have hstable : (prefixWord ++ tailWord_2657545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657545).length < 2 ^ (prefixWord ++ tailWord_2657545).sum := by decide
  have hdescent : baseEnd_2657545 < baseStart_2657545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657562 : List Nat := [3, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3]
def baseStart_2657562 : Nat := 118140960795 + 2657562 * 2 ^ 59
def prefixEnd_2657562 : Nat := 4983230072969 + 3 ^ 40 * 2657562 * 2
def baseEnd_2657562 : Nat := 1364606675124036510153101

theorem tailTrace_2657562 : CollatzResearch.WordTrace tailWord_2657562 prefixEnd_2657562 1364606675124036510153101 := by
  unfold tailWord_2657562
  simp only [CollatzResearch.WordTrace]
  refine ⟨24232312299528556074959735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64619499465409482866559293 24232312299528556074959735)
  ·
    refine ⟨36348468449292834112439603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24232312299528556074959735 36348468449292834112439603)
    ·
      refine ⟨54522702673939251168659405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36348468449292834112439603 54522702673939251168659405)
      ·
        refine ⟨20446013502727219188247277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54522702673939251168659405 20446013502727219188247277)
        ·
          refine ⟨7667255063522707195592729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20446013502727219188247277 7667255063522707195592729)
          ·
            refine ⟨5750441297642030396694547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7667255063522707195592729 5750441297642030396694547)
            ·
              refine ⟨8625661946463045595041821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5750441297642030396694547 8625661946463045595041821)
              ·
                refine ⟨3234623229923642098140683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8625661946463045595041821 3234623229923642098140683)
                ·
                  refine ⟨4851934844885463147211025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3234623229923642098140683 4851934844885463147211025)
                  ·
                    refine ⟨3638951133664097360408269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4851934844885463147211025 3638951133664097360408269)
                    ·
                      refine ⟨1364606675124036510153101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3638951133664097360408269 1364606675124036510153101)
                      ·
                        rfl

theorem cell23_2657562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_2657562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657562 prefixEnd_2657562 := by exact prefixLift 2657562
  have htrace : WordTrace (prefixWord ++ tailWord_2657562) baseStart_2657562 baseEnd_2657562 := by
    simpa [prefixWord, tailWord_2657562, baseEnd_2657562] using wordTrace_append hprefix tailTrace_2657562
  have hstable : (prefixWord ++ tailWord_2657562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657562).length < 2 ^ (prefixWord ++ tailWord_2657562).sum := by decide
  have hdescent : baseEnd_2657562 < baseStart_2657562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657576 : List Nat := [2, 1, 5, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_2657576 : Nat := 118140960795 + 2657576 * 2 ^ 59
def prefixEnd_2657576 : Nat := 4983230072969 + 3 ^ 40 * 2657576 * 2
def baseEnd_2657576 : Nat := 1364613863853199455378037

theorem tailTrace_2657576 : CollatzResearch.WordTrace tailWord_2657576 prefixEnd_2657576 1364613863853199455378037 := by
  unfold tailWord_2657576
  simp only [CollatzResearch.WordTrace]
  refine ⟨48464879910031752345424291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64619839880042336460565721 48464879910031752345424291)
  ·
    refine ⟨72697319865047628518136437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48464879910031752345424291 72697319865047628518136437)
    ·
      refine ⟨6815373737348215173575291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72697319865047628518136437 6815373737348215173575291)
      ·
        refine ⟨10223060606022322760362937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6815373737348215173575291 10223060606022322760362937)
        ·
          refine ⟨7667295454516742070272203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10223060606022322760362937 7667295454516742070272203)
          ·
            refine ⟨11500943181775113105408305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7667295454516742070272203 11500943181775113105408305)
            ·
              refine ⟨8625707386331334829056229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11500943181775113105408305 8625707386331334829056229)
              ·
                refine ⟨1617320134937125280448043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8625707386331334829056229 1617320134937125280448043)
                ·
                  refine ⟨2425980202405687920672065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617320134937125280448043 2425980202405687920672065)
                  ·
                    refine ⟨1819485151804265940504049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2425980202405687920672065 1819485151804265940504049)
                    ·
                      refine ⟨1364613863853199455378037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819485151804265940504049 1364613863853199455378037)
                      ·
                        rfl

theorem cell23_2657576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_2657576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657576 prefixEnd_2657576 := by exact prefixLift 2657576
  have htrace : WordTrace (prefixWord ++ tailWord_2657576) baseStart_2657576 baseEnd_2657576 := by
    simpa [prefixWord, tailWord_2657576, baseEnd_2657576] using wordTrace_append hprefix tailTrace_2657576
  have hstable : (prefixWord ++ tailWord_2657576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657576).length < 2 ^ (prefixWord ++ tailWord_2657576).sum := by decide
  have hdescent : baseEnd_2657576 < baseStart_2657576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657653 : List Nat := [1, 3, 4, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_2657653 : Nat := 118140960795 + 2657653 * 2 ^ 59
def prefixEnd_2657653 : Nat := 4983230072969 + 3 ^ 40 * 2657653 * 2
def baseEnd_2657653 : Nat := 1364653401863595654115183

theorem tailTrace_2657653 : CollatzResearch.WordTrace tailWord_2657653 prefixEnd_2657653 1364653401863595654115183 := by
  unfold tailWord_2657653
  simp only [CollatzResearch.WordTrace]
  refine ⟨96932568240784546841401613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64621712160523031227601075 96932568240784546841401613)
  ·
    refine ⟨36349713090294205065525605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96932568240784546841401613 36349713090294205065525605)
    ·
      refine ⟨6815571204430163449786051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36349713090294205065525605 6815571204430163449786051)
      ·
        refine ⟨10223356806645245174679077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6815571204430163449786051 10223356806645245174679077)
        ·
          refine ⟨1916879401245983470252327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10223356806645245174679077 1916879401245983470252327)
          ·
            refine ⟨2875319101868975205378491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1916879401245983470252327 2875319101868975205378491)
            ·
              refine ⟨4312978652803462808067737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2875319101868975205378491 4312978652803462808067737)
              ·
                refine ⟨3234733989602597106050803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4312978652803462808067737 3234733989602597106050803)
                ·
                  refine ⟨4852100984403895659076205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3234733989602597106050803 4852100984403895659076205)
                  ·
                    refine ⟨1819537869151460872153577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4852100984403895659076205 1819537869151460872153577)
                    ·
                      refine ⟨1364653401863595654115183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819537869151460872153577 1364653401863595654115183)
                      ·
                        rfl

theorem cell23_2657653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_2657653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657653 prefixEnd_2657653 := by exact prefixLift 2657653
  have htrace : WordTrace (prefixWord ++ tailWord_2657653) baseStart_2657653 baseEnd_2657653 := by
    simpa [prefixWord, tailWord_2657653, baseEnd_2657653] using wordTrace_append hprefix tailTrace_2657653
  have hstable : (prefixWord ++ tailWord_2657653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657653).length < 2 ^ (prefixWord ++ tailWord_2657653).sum := by decide
  have hdescent : baseEnd_2657653 < baseStart_2657653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657666 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_2657666 : Nat := 118140960795 + 2657666 * 2 ^ 59
def prefixEnd_2657666 : Nat := 4983230072969 + 3 ^ 40 * 2657666 * 2
def baseEnd_2657666 : Nat := 1364660077112104103252623

theorem tailTrace_2657666 : CollatzResearch.WordTrace tailWord_2657666 prefixEnd_2657666 1364660077112104103252623 := by
  unfold tailWord_2657666
  simp only [CollatzResearch.WordTrace]
  refine ⟨24233260597434362515406213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64622028259824966707749901 24233260597434362515406213)
  ·
    refine ⟨4543736362018942971638665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24233260597434362515406213 4543736362018942971638665)
    ·
      refine ⟨3407802271514207228728999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4543736362018942971638665 3407802271514207228728999)
      ·
        refine ⟨5111703407271310843093499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3407802271514207228728999 5111703407271310843093499)
        ·
          refine ⟨7667555110906966264640249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5111703407271310843093499 7667555110906966264640249)
          ·
            refine ⟨5750666333180224698480187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7667555110906966264640249 5750666333180224698480187)
            ·
              refine ⟨8625999499770337047720281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5750666333180224698480187 8625999499770337047720281)
              ·
                refine ⟨6469499624827752785790211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8625999499770337047720281 6469499624827752785790211)
                ·
                  refine ⟨9704249437241629178685317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6469499624827752785790211 9704249437241629178685317)
                  ·
                    refine ⟨1819546769482805471003497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9704249437241629178685317 1819546769482805471003497)
                    ·
                      refine ⟨1364660077112104103252623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819546769482805471003497 1364660077112104103252623)
                      ·
                        rfl

theorem cell23_2657666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_2657666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657666 prefixEnd_2657666 := by exact prefixLift 2657666
  have htrace : WordTrace (prefixWord ++ tailWord_2657666) baseStart_2657666 baseEnd_2657666 := by
    simpa [prefixWord, tailWord_2657666, baseEnd_2657666] using wordTrace_append hprefix tailTrace_2657666
  have hstable : (prefixWord ++ tailWord_2657666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657666).length < 2 ^ (prefixWord ++ tailWord_2657666).sum := by decide
  have hdescent : baseEnd_2657666 < baseStart_2657666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657685 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 2, 5]
def baseStart_2657685 : Nat := 118140960795 + 2657685 * 2 ^ 59
def prefixEnd_2657685 : Nat := 4983230072969 + 3 ^ 40 * 2657685 * 2
def baseEnd_2657685 : Nat := 454889944414846509638345

theorem tailTrace_2657685 : CollatzResearch.WordTrace tailWord_2657685 prefixEnd_2657685 454889944414846509638345 := by
  unfold tailWord_2657685
  simp only [CollatzResearch.WordTrace]
  refine ⟨96933735376668616306566509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64622490251112410871044339 96933735376668616306566509)
  ·
    refine ⟨36350150766250731114962441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96933735376668616306566509 36350150766250731114962441)
    ·
      refine ⟨27262613074688048336221831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36350150766250731114962441 27262613074688048336221831)
      ·
        refine ⟨40893919612032072504332747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27262613074688048336221831 40893919612032072504332747)
        ·
          refine ⟨61340879418048108756499121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40893919612032072504332747 61340879418048108756499121)
          ·
            refine ⟨46005659563536081567374341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61340879418048108756499121 46005659563536081567374341)
            ·
              refine ⟨8626061168163015293882689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46005659563536081567374341 8626061168163015293882689)
              ·
                refine ⟨6469545876122261470412017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8626061168163015293882689 6469545876122261470412017)
                ·
                  refine ⟨4852159407091696102809013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6469545876122261470412017 4852159407091696102809013)
                  ·
                    refine ⟨454889944414846509638345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4852159407091696102809013 454889944414846509638345)
                    ·
                      rfl

theorem cell23_2657685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_2657685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657685 prefixEnd_2657685 := by exact prefixLift 2657685
  have htrace : WordTrace (prefixWord ++ tailWord_2657685) baseStart_2657685 baseEnd_2657685 := by
    simpa [prefixWord, tailWord_2657685, baseEnd_2657685] using wordTrace_append hprefix tailTrace_2657685
  have hstable : (prefixWord ++ tailWord_2657685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657685).length < 2 ^ (prefixWord ++ tailWord_2657685).sum := by decide
  have hdescent : baseEnd_2657685 < baseStart_2657685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657689 : List Nat := [1, 2, 1, 2, 1, 7, 2, 2, 5]
def baseStart_2657689 : Nat := 118140960795 + 2657689 * 2 ^ 59
def prefixEnd_2657689 : Nat := 4983230072969 + 3 ^ 40 * 2657689 * 2
def baseEnd_2657689 : Nat := 151630209685239723696113

theorem tailTrace_2657689 : CollatzResearch.WordTrace tailWord_2657689 prefixEnd_2657689 151630209685239723696113 := by
  unfold tailWord_2657689
  simp only [CollatzResearch.WordTrace]
  refine ⟨96933881268654124989712121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64622587512436083326474747 96933881268654124989712121)
  ·
    refine ⟨72700410951490593742284091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96933881268654124989712121 72700410951490593742284091)
    ·
      refine ⟨109050616427235890613426137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72700410951490593742284091 109050616427235890613426137)
      ·
        refine ⟨81787962320426917960069603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109050616427235890613426137 81787962320426917960069603)
        ·
          refine ⟨122681943480640376940104405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81787962320426917960069603 122681943480640376940104405)
          ·
            refine ⟨2875358050327508834533697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 122681943480640376940104405 2875358050327508834533697)
            ·
              refine ⟨2156518537745631625900273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2875358050327508834533697 2156518537745631625900273)
              ·
                refine ⟨1617388903309223719425205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2156518537745631625900273 1617388903309223719425205)
                ·
                  refine ⟨151630209685239723696113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1617388903309223719425205 151630209685239723696113)
                  ·
                    rfl

theorem cell23_2657689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 5].length) (baseStart_2657689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657689 prefixEnd_2657689 := by exact prefixLift 2657689
  have htrace : WordTrace (prefixWord ++ tailWord_2657689) baseStart_2657689 baseEnd_2657689 := by
    simpa [prefixWord, tailWord_2657689, baseEnd_2657689] using wordTrace_append hprefix tailTrace_2657689
  have hstable : (prefixWord ++ tailWord_2657689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657689).length < 2 ^ (prefixWord ++ tailWord_2657689).sum := by decide
  have hdescent : baseEnd_2657689 < baseStart_2657689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657695 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 5]
def baseStart_2657695 : Nat := 118140960795 + 2657695 * 2 ^ 59
def prefixEnd_2657695 : Nat := 4983230072969 + 3 ^ 40 * 2657695 * 2
def baseEnd_2657695 : Nat := 1364674968051084489789989

theorem tailTrace_2657695 : CollatzResearch.WordTrace tailWord_2657695 prefixEnd_2657695 1364674968051084489789989 := by
  unfold tailWord_2657695
  simp only [CollatzResearch.WordTrace]
  refine ⟨96934100106632388014430539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64622733404421592009620359 96934100106632388014430539)
  ·
    refine ⟨145401150159948582021645809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96934100106632388014430539 145401150159948582021645809)
    ·
      refine ⟨109050862619961436516234357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145401150159948582021645809 109050862619961436516234357)
      ·
        refine ⟨10223518370621384673396971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109050862619961436516234357 10223518370621384673396971)
        ·
          refine ⟨15335277555932077010095457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10223518370621384673396971 15335277555932077010095457)
          ·
            refine ⟨11501458166949057757571593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15335277555932077010095457 11501458166949057757571593)
            ·
              refine ⟨8626093625211793318178695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11501458166949057757571593 8626093625211793318178695)
              ·
                refine ⟨12939140437817689977268043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8626093625211793318178695 12939140437817689977268043)
                ·
                  refine ⟨19408710656726534965902065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12939140437817689977268043 19408710656726534965902065)
                  ·
                    refine ⟨14556532992544901224426549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19408710656726534965902065 14556532992544901224426549)
                    ·
                      refine ⟨1364674968051084489789989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14556532992544901224426549 1364674968051084489789989)
                      ·
                        rfl

theorem cell23_2657695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_2657695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657695 prefixEnd_2657695 := by exact prefixLift 2657695
  have htrace : WordTrace (prefixWord ++ tailWord_2657695) baseStart_2657695 baseEnd_2657695 := by
    simpa [prefixWord, tailWord_2657695, baseEnd_2657695] using wordTrace_append hprefix tailTrace_2657695
  have hstable : (prefixWord ++ tailWord_2657695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657695).length < 2 ^ (prefixWord ++ tailWord_2657695).sum := by decide
  have hdescent : baseEnd_2657695 < baseStart_2657695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657742 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3]
def baseStart_2657742 : Nat := 118140960795 + 2657742 * 2 ^ 59
def prefixEnd_2657742 : Nat := 4983230072969 + 3 ^ 40 * 2657742 * 2
def baseEnd_2657742 : Nat := 1364699101641845805902273

theorem tailTrace_2657742 : CollatzResearch.WordTrace tailWord_2657742 prefixEnd_2657742 1364699101641845805902273 := by
  unfold tailWord_2657742
  simp only [CollatzResearch.WordTrace]
  refine ⟨12116976792182764380173935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64623876224974743360927653 12116976792182764380173935)
  ·
    refine ⟨18175465188274146570260903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12116976792182764380173935 18175465188274146570260903)
    ·
      refine ⟨27263197782411219855391355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18175465188274146570260903 27263197782411219855391355)
      ·
        refine ⟨40894796673616829783087033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27263197782411219855391355 40894796673616829783087033)
        ·
          refine ⟨30671097505212622337315275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40894796673616829783087033 30671097505212622337315275)
          ·
            refine ⟨46006646257818933505972913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30671097505212622337315275 46006646257818933505972913)
            ·
              refine ⟨34504984693364200129479685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46006646257818933505972913 34504984693364200129479685)
              ·
                refine ⟨6469684630005787524277441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34504984693364200129479685 6469684630005787524277441)
                ·
                  refine ⟨4852263472504340643208081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6469684630005787524277441 4852263472504340643208081)
                  ·
                    refine ⟨3639197604378255482406061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4852263472504340643208081 3639197604378255482406061)
                    ·
                      refine ⟨1364699101641845805902273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3639197604378255482406061 1364699101641845805902273)
                      ·
                        rfl

theorem cell23_2657742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_2657742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657742 prefixEnd_2657742 := by exact prefixLift 2657742
  have htrace : WordTrace (prefixWord ++ tailWord_2657742) baseStart_2657742 baseEnd_2657742 := by
    simpa [prefixWord, tailWord_2657742, baseEnd_2657742] using wordTrace_append hprefix tailTrace_2657742
  have hstable : (prefixWord ++ tailWord_2657742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657742).length < 2 ^ (prefixWord ++ tailWord_2657742).sum := by decide
  have hdescent : baseEnd_2657742 < baseStart_2657742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657749 : List Nat := [1, 3, 2, 3, 1, 1, 1, 6, 1, 4]
def baseStart_2657749 : Nat := 118140960795 + 2657749 * 2 ^ 59
def prefixEnd_2657749 : Nat := 4983230072969 + 3 ^ 40 * 2657749 * 2
def baseEnd_2657749 : Nat := 454900898668809092838247

theorem tailTrace_2657749 : CollatzResearch.WordTrace tailWord_2657749 prefixEnd_2657749 454900898668809092838247 := by
  unfold tailWord_2657749
  simp only [CollatzResearch.WordTrace]
  refine ⟨96936069648436755236896301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64624046432291170157930867 96936069648436755236896301)
  ·
    refine ⟨36351026118163783213836113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96936069648436755236896301 36351026118163783213836113)
    ·
      refine ⟨27263269588622837410377085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36351026118163783213836113 27263269588622837410377085)
      ·
        refine ⟨10223726095733564028891407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27263269588622837410377085 10223726095733564028891407)
        ·
          refine ⟨15335589143600346043337111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10223726095733564028891407 15335589143600346043337111)
          ·
            refine ⟨23003383715400519065005667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15335589143600346043337111 23003383715400519065005667)
            ·
              refine ⟨34505075573100778597508501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23003383715400519065005667 34505075573100778597508501)
              ·
                refine ⟨1617425417489098996758211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34505075573100778597508501 1617425417489098996758211)
                ·
                  refine ⟨2426138126233648495137317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617425417489098996758211 2426138126233648495137317)
                  ·
                    refine ⟨454900898668809092838247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2426138126233648495137317 454900898668809092838247)
                    ·
                      rfl

theorem cell23_2657749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_2657749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657749 prefixEnd_2657749 := by exact prefixLift 2657749
  have htrace : WordTrace (prefixWord ++ tailWord_2657749) baseStart_2657749 baseEnd_2657749 := by
    simpa [prefixWord, tailWord_2657749, baseEnd_2657749] using wordTrace_append hprefix tailTrace_2657749
  have hstable : (prefixWord ++ tailWord_2657749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657749).length < 2 ^ (prefixWord ++ tailWord_2657749).sum := by decide
  have hdescent : baseEnd_2657749 < baseStart_2657749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657772 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 3]
def baseStart_2657772 : Nat := 118140960795 + 2657772 * 2 ^ 59
def prefixEnd_2657772 : Nat := 4983230072969 + 3 ^ 40 * 2657772 * 2
def baseEnd_2657772 : Nat := 1364714506061480688527135

theorem tailTrace_2657772 : CollatzResearch.WordTrace tailWord_2657772 prefixEnd_2657772 1364714506061480688527135 := by
  unfold tailWord_2657772
  simp only [CollatzResearch.WordTrace]
  refine ⟨48468454263676715082491785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64624605684902286776655713 48468454263676715082491785)
  ·
    refine ⟨36351340697757536311868839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48468454263676715082491785 36351340697757536311868839)
    ·
      refine ⟨54527011046636304467803259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36351340697757536311868839 54527011046636304467803259)
      ·
        refine ⟨81790516569954456701704889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54527011046636304467803259 81790516569954456701704889)
        ·
          refine ⟨61342887427465842526278667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81790516569954456701704889 61342887427465842526278667)
          ·
            refine ⟨92014331141198763789418001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61342887427465842526278667 92014331141198763789418001)
            ·
              refine ⟨69010748355899072842063501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92014331141198763789418001 69010748355899072842063501)
              ·
                refine ⟨25879030633462152315773813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69010748355899072842063501 25879030633462152315773813)
                ·
                  refine ⟨2426159121887076779603795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25879030633462152315773813 2426159121887076779603795)
                  ·
                    refine ⟨3639238682830615169405693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2426159121887076779603795 3639238682830615169405693)
                    ·
                      refine ⟨1364714506061480688527135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3639238682830615169405693 1364714506061480688527135)
                      ·
                        rfl

theorem cell23_2657772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 3].length) (baseStart_2657772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657772 prefixEnd_2657772 := by exact prefixLift 2657772
  have htrace : WordTrace (prefixWord ++ tailWord_2657772) baseStart_2657772 baseEnd_2657772 := by
    simpa [prefixWord, tailWord_2657772, baseEnd_2657772] using wordTrace_append hprefix tailTrace_2657772
  have hstable : (prefixWord ++ tailWord_2657772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657772).length < 2 ^ (prefixWord ++ tailWord_2657772).sum := by decide
  have hdescent : baseEnd_2657772 < baseStart_2657772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657775 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 3, 5]
def baseStart_2657775 : Nat := 118140960795 + 2657775 * 2 ^ 59
def prefixEnd_2657775 : Nat := 4983230072969 + 3 ^ 40 * 2657775 * 2
def baseEnd_2657775 : Nat := 454905348834481392263207

theorem tailTrace_2657775 : CollatzResearch.WordTrace tailWord_2657775 prefixEnd_2657775 454905348834481392263207 := by
  unfold tailWord_2657775
  simp only [CollatzResearch.WordTrace]
  refine ⟨96937017946342561677342779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64624678630895041118228519 96937017946342561677342779)
  ·
    refine ⟨145405526919513842516014169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96937017946342561677342779 145405526919513842516014169)
    ·
      refine ⟨109054145189635381887010627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145405526919513842516014169 109054145189635381887010627)
      ·
        refine ⟨163581217784453072830515941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109054145189635381887010627 163581217784453072830515941)
        ·
          refine ⟨30671478334584951155721739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163581217784453072830515941 30671478334584951155721739)
          ·
            refine ⟨46007217501877426733582609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30671478334584951155721739 46007217501877426733582609)
            ·
              refine ⟨34505413126408070050186957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46007217501877426733582609 34505413126408070050186957)
              ·
                refine ⟨12939529922403026268820109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34505413126408070050186957 12939529922403026268820109)
                ·
                  refine ⟨4852323720901134850807541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12939529922403026268820109 4852323720901134850807541)
                  ·
                    refine ⟨454905348834481392263207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4852323720901134850807541 454905348834481392263207)
                    ·
                      rfl

theorem cell23_2657775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 5].length) (baseStart_2657775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657775 prefixEnd_2657775 := by exact prefixLift 2657775
  have htrace : WordTrace (prefixWord ++ tailWord_2657775) baseStart_2657775 baseEnd_2657775 := by
    simpa [prefixWord, tailWord_2657775, baseEnd_2657775] using wordTrace_append hprefix tailTrace_2657775
  have hstable : (prefixWord ++ tailWord_2657775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657775).length < 2 ^ (prefixWord ++ tailWord_2657775).sum := by decide
  have hdescent : baseEnd_2657775 < baseStart_2657775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657799 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 4, 3, 2]
def baseStart_2657799 : Nat := 118140960795 + 2657799 * 2 ^ 59
def prefixEnd_2657799 : Nat := 4983230072969 + 3 ^ 40 * 2657799 * 2
def baseEnd_2657799 : Nat := 1364728370039152082889511

theorem tailTrace_2657799 : CollatzResearch.WordTrace tailWord_2657799 prefixEnd_2657799 1364728370039152082889511 := by
  unfold tailWord_2657799
  simp only [CollatzResearch.WordTrace]
  refine ⟨96937893298255613776216451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64625262198837075850810967 96937893298255613776216451)
  ·
    refine ⟨145406839947383420664324677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96937893298255613776216451 145406839947383420664324677)
    ·
      refine ⟨27263782490134391374560877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145406839947383420664324677 27263782490134391374560877)
      ·
        refine ⟨10223918433800396765460329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27263782490134391374560877 10223918433800396765460329)
        ·
          refine ⟨7667938825350297574095247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10223918433800396765460329 7667938825350297574095247)
          ·
            refine ⟨11501908238025446361142871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7667938825350297574095247 11501908238025446361142871)
            ·
              refine ⟨17252862357038169541714307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11501908238025446361142871 17252862357038169541714307)
              ·
                refine ⟨25879293535557254312571461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17252862357038169541714307 25879293535557254312571461)
                ·
                  refine ⟨4852367537916985183607149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25879293535557254312571461 4852367537916985183607149)
                  ·
                    refine ⟨1819637826718869443852681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4852367537916985183607149 1819637826718869443852681)
                    ·
                      refine ⟨1364728370039152082889511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819637826718869443852681 1364728370039152082889511)
                      ·
                        rfl

theorem cell23_2657799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_2657799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657799 prefixEnd_2657799 := by exact prefixLift 2657799
  have htrace : WordTrace (prefixWord ++ tailWord_2657799) baseStart_2657799 baseEnd_2657799 := by
    simpa [prefixWord, tailWord_2657799, baseEnd_2657799] using wordTrace_append hprefix tailTrace_2657799
  have hstable : (prefixWord ++ tailWord_2657799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657799).length < 2 ^ (prefixWord ++ tailWord_2657799).sum := by decide
  have hdescent : baseEnd_2657799 < baseStart_2657799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657829 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 5, 2, 2]
def baseStart_2657829 : Nat := 118140960795 + 2657829 * 2 ^ 59
def prefixEnd_2657829 : Nat := 4983230072969 + 3 ^ 40 * 2657829 * 2
def baseEnd_2657829 : Nat := 1364743774458786965514373

theorem tailTrace_2657829 : CollatzResearch.WordTrace tailWord_2657829 prefixEnd_2657829 1364743774458786965514373 := by
  unfold tailWord_2657829
  simp only [CollatzResearch.WordTrace]
  refine ⟨96938987488146928899808541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64625991658764619266539027 96938987488146928899808541)
  ·
    refine ⟨36352120308055098337428203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96938987488146928899808541 36352120308055098337428203)
    ·
      refine ⟨54528180462082647506142305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36352120308055098337428203 54528180462082647506142305)
      ·
        refine ⟨40896135346561985629606729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54528180462082647506142305 40896135346561985629606729)
        ·
          refine ⟨30672101509921489222205047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40896135346561985629606729 30672101509921489222205047)
          ·
            refine ⟨46008152264882233833307571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30672101509921489222205047 46008152264882233833307571)
            ·
              refine ⟨69012228397323350749961357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46008152264882233833307571 69012228397323350749961357)
              ·
                refine ⟨25879585648996256531235509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69012228397323350749961357 25879585648996256531235509)
                ·
                  refine ⟨2426211154593399049803329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25879585648996256531235509 2426211154593399049803329)
                  ·
                    refine ⟨1819658365945049287352497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2426211154593399049803329 1819658365945049287352497)
                    ·
                      refine ⟨1364743774458786965514373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819658365945049287352497 1364743774458786965514373)
                      ·
                        rfl

theorem cell23_2657829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_2657829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657829 prefixEnd_2657829 := by exact prefixLift 2657829
  have htrace : WordTrace (prefixWord ++ tailWord_2657829) baseStart_2657829 baseEnd_2657829 := by
    simpa [prefixWord, tailWord_2657829, baseEnd_2657829] using wordTrace_append hprefix tailTrace_2657829
  have hstable : (prefixWord ++ tailWord_2657829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657829).length < 2 ^ (prefixWord ++ tailWord_2657829).sum := by decide
  have hdescent : baseEnd_2657829 < baseStart_2657829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657849 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 1, 1, 5]
def baseStart_2657849 : Nat := 118140960795 + 2657849 * 2 ^ 59
def prefixEnd_2657849 : Nat := 4983230072969 + 3 ^ 40 * 2657849 * 2
def baseEnd_2657849 : Nat := 1364754044071876887264281

theorem tailTrace_2657849 : CollatzResearch.WordTrace tailWord_2657849 prefixEnd_2657849 1364754044071876887264281 := by
  unfold tailWord_2657849
  simp only [CollatzResearch.WordTrace]
  refine ⟨96939716948074472315536601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64626477965382981543691067 96939716948074472315536601)
  ·
    refine ⟨72704787711055854236652451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96939716948074472315536601 72704787711055854236652451)
    ·
      refine ⟨109057181566583781354978677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72704787711055854236652451 109057181566583781354978677)
      ·
        refine ⟨10224110771867229502029251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109057181566583781354978677 10224110771867229502029251)
        ·
          refine ⟨15336166157800844253043877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10224110771867229502029251 15336166157800844253043877)
          ·
            refine ⟨2875531154587658297445727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15336166157800844253043877 2875531154587658297445727)
            ·
              refine ⟨4313296731881487446168591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2875531154587658297445727 4313296731881487446168591)
              ·
                refine ⟨6469945097822231169252887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4313296731881487446168591 6469945097822231169252887)
                ·
                  refine ⟨9704917646733346753879331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6469945097822231169252887 9704917646733346753879331)
                  ·
                    refine ⟨14557376470100020130818997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9704917646733346753879331 14557376470100020130818997)
                    ·
                      refine ⟨1364754044071876887264281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14557376470100020130818997 1364754044071876887264281)
                      ·
                        rfl

theorem cell23_2657849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_2657849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657849 prefixEnd_2657849 := by exact prefixLift 2657849
  have htrace : WordTrace (prefixWord ++ tailWord_2657849) baseStart_2657849 baseEnd_2657849 := by
    simpa [prefixWord, tailWord_2657849, baseEnd_2657849] using wordTrace_append hprefix tailTrace_2657849
  have hstable : (prefixWord ++ tailWord_2657849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657849).length < 2 ^ (prefixWord ++ tailWord_2657849).sum := by decide
  have hdescent : baseEnd_2657849 < baseStart_2657849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657852 : List Nat := [2, 2, 2, 2, 5, 10]
def baseStart_2657852 : Nat := 118140960795 + 2657852 * 2 ^ 59
def prefixEnd_2657852 : Nat := 4983230072969 + 3 ^ 40 * 2657852 * 2
def baseEnd_2657852 : Nat := 5616278125571359570069

theorem tailTrace_2657852 : CollatzResearch.WordTrace tailWord_2657852 prefixEnd_2657852 5616278125571359570069 := by
  unfold tailWord_2657852
  simp only [CollatzResearch.WordTrace]
  refine ⟨48469913183531801913947905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64626550911375735885263873 48469913183531801913947905)
  ·
    refine ⟨36352434887648851435460929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48469913183531801913947905 36352434887648851435460929)
    ·
      refine ⟨27264326165736638576595697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36352434887648851435460929 27264326165736638576595697)
      ·
        refine ⟨20448244624302478932446773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27264326165736638576595697 20448244624302478932446773)
        ·
          refine ⟨1917022933528357399916885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20448244624302478932446773 1917022933528357399916885)
          ·
            refine ⟨5616278125571359570069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1917022933528357399916885 5616278125571359570069)
            ·
              rfl

theorem cell23_2657852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 10].length) (baseStart_2657852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657852 prefixEnd_2657852 := by exact prefixLift 2657852
  have htrace : WordTrace (prefixWord ++ tailWord_2657852) baseStart_2657852 baseEnd_2657852 := by
    simpa [prefixWord, tailWord_2657852, baseEnd_2657852] using wordTrace_append hprefix tailTrace_2657852
  have hstable : (prefixWord ++ tailWord_2657852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657852).length < 2 ^ (prefixWord ++ tailWord_2657852).sum := by decide
  have hdescent : baseEnd_2657852 < baseStart_2657852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657875 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 5]
def baseStart_2657875 : Nat := 118140960795 + 2657875 * 2 ^ 59
def prefixEnd_2657875 : Nat := 4983230072969 + 3 ^ 40 * 2657875 * 2
def baseEnd_2657875 : Nat := 1364767394568893785539161

theorem tailTrace_2657875 : CollatzResearch.WordTrace tailWord_2657875 prefixEnd_2657875 1364767394568893785539161 := by
  unfold tailWord_2657875
  simp only [CollatzResearch.WordTrace]
  refine ⟨96940665245980278755983079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64627110163986852503988719 96940665245980278755983079)
  ·
    refine ⟨145410997868970418133974619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96940665245980278755983079 145410997868970418133974619)
    ·
      refine ⟨218116496803455627200961929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145410997868970418133974619 218116496803455627200961929)
      ·
        refine ⟨163587372602591720400721447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218116496803455627200961929 163587372602591720400721447)
        ·
          refine ⟨245381058903887580601082171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163587372602591720400721447 245381058903887580601082171)
          ·
            refine ⟨368071588355831370901623257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245381058903887580601082171 368071588355831370901623257)
            ·
              refine ⟨276053691266873528176217443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368071588355831370901623257 276053691266873528176217443)
              ·
                refine ⟨414080536900310292264326165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276053691266873528176217443 414080536900310292264326165)
                ·
                  refine ⟨19410025167202044949890289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 414080536900310292264326165 19410025167202044949890289)
                  ·
                    refine ⟨14557518875401533712417717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19410025167202044949890289 14557518875401533712417717)
                    ·
                      refine ⟨1364767394568893785539161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14557518875401533712417717 1364767394568893785539161)
                      ·
                        rfl

theorem cell23_2657875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_2657875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657875 prefixEnd_2657875 := by exact prefixLift 2657875
  have htrace : WordTrace (prefixWord ++ tailWord_2657875) baseStart_2657875 baseEnd_2657875 := by
    simpa [prefixWord, tailWord_2657875, baseEnd_2657875] using wordTrace_append hprefix tailTrace_2657875
  have hstable : (prefixWord ++ tailWord_2657875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657875).length < 2 ^ (prefixWord ++ tailWord_2657875).sum := by decide
  have hdescent : baseEnd_2657875 < baseStart_2657875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657879 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 3]
def baseStart_2657879 : Nat := 118140960795 + 2657879 * 2 ^ 59
def prefixEnd_2657879 : Nat := 4983230072969 + 3 ^ 40 * 2657879 * 2
def baseEnd_2657879 : Nat := 1364769448491511769889143

theorem tailTrace_2657879 : CollatzResearch.WordTrace tailWord_2657879 prefixEnd_2657879 1364769448491511769889143 := by
  unfold tailWord_2657879
  simp only [CollatzResearch.WordTrace]
  refine ⟨96940811137965787439128691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64627207425310524959419127 96940811137965787439128691)
  ·
    refine ⟨145411216706948681158693037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96940811137965787439128691 145411216706948681158693037)
    ·
      refine ⟨54529206265105755434509889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145411216706948681158693037 54529206265105755434509889)
      ·
        refine ⟨40896904698829316575882417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54529206265105755434509889 40896904698829316575882417)
        ·
          refine ⟨30672678524121987431911813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40896904698829316575882417 30672678524121987431911813)
          ·
            refine ⟨5751127223272872643483465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30672678524121987431911813 5751127223272872643483465)
            ·
              refine ⟨4313345417454654482612599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5751127223272872643483465 4313345417454654482612599)
              ·
                refine ⟨6470018126181981723918899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4313345417454654482612599 6470018126181981723918899)
                ·
                  refine ⟨9705027189272972585878349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6470018126181981723918899 9705027189272972585878349)
                  ·
                    refine ⟨3639385195977364719704381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9705027189272972585878349 3639385195977364719704381)
                    ·
                      refine ⟨1364769448491511769889143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3639385195977364719704381 1364769448491511769889143)
                      ·
                        rfl

theorem cell23_2657879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_2657879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657879 prefixEnd_2657879 := by exact prefixLift 2657879
  have htrace : WordTrace (prefixWord ++ tailWord_2657879) baseStart_2657879 baseEnd_2657879 := by
    simpa [prefixWord, tailWord_2657879, baseEnd_2657879] using wordTrace_append hprefix tailTrace_2657879
  have hstable : (prefixWord ++ tailWord_2657879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657879).length < 2 ^ (prefixWord ++ tailWord_2657879).sum := by decide
  have hdescent : baseEnd_2657879 < baseStart_2657879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657889 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 3, 3, 2]
def baseStart_2657889 : Nat := 118140960795 + 2657889 * 2 ^ 59
def prefixEnd_2657889 : Nat := 4983230072969 + 3 ^ 40 * 2657889 * 2
def baseEnd_2657889 : Nat := 1364774583298056730764097

theorem tailTrace_2657889 : CollatzResearch.WordTrace tailWord_2657889 prefixEnd_2657889 1364774583298056730764097 := by
  unfold tailWord_2657889
  simp only [CollatzResearch.WordTrace]
  refine ⟨96941175867929559146992721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64627450578619706097995147 96941175867929559146992721)
  ·
    refine ⟨72705881900947169360244541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96941175867929559146992721 72705881900947169360244541)
    ·
      refine ⟨27264705712855188510091703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72705881900947169360244541 27264705712855188510091703)
      ·
        refine ⟨40897058569282782765137555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27264705712855188510091703 40897058569282782765137555)
        ·
          refine ⟨61345587853924174147706333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40897058569282782765137555 61345587853924174147706333)
          ·
            refine ⟨23004595445221565305389875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61345587853924174147706333 23004595445221565305389875)
            ·
              refine ⟨34506893167832347958084813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23004595445221565305389875 34506893167832347958084813)
              ·
                refine ⟨12940084937937130484281805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34506893167832347958084813 12940084937937130484281805)
                ·
                  refine ⟨4852531851726423931605677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12940084937937130484281805 4852531851726423931605677)
                  ·
                    refine ⟨1819699444397408974352129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4852531851726423931605677 1819699444397408974352129)
                    ·
                      refine ⟨1364774583298056730764097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819699444397408974352129 1364774583298056730764097)
                      ·
                        rfl

theorem cell23_2657889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_2657889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657889 prefixEnd_2657889 := by exact prefixLift 2657889
  have htrace : WordTrace (prefixWord ++ tailWord_2657889) baseStart_2657889 baseEnd_2657889 := by
    simpa [prefixWord, tailWord_2657889, baseEnd_2657889] using wordTrace_append hprefix tailTrace_2657889
  have hstable : (prefixWord ++ tailWord_2657889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657889).length < 2 ^ (prefixWord ++ tailWord_2657889).sum := by decide
  have hdescent : baseEnd_2657889 < baseStart_2657889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657932 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 2, 2, 4]
def baseStart_2657932 : Nat := 118140960795 + 2657932 * 2 ^ 59
def prefixEnd_2657932 : Nat := 4983230072969 + 3 ^ 40 * 2657932 * 2
def baseEnd_2657932 : Nat := 1364796662966200062526399

theorem tailTrace_2657932 : CollatzResearch.WordTrace tailWord_2657932 prefixEnd_2657932 1364796662966200062526399 := by
  unfold tailWord_2657932
  simp only [CollatzResearch.WordTrace]
  refine ⟨48471372103386888745404025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64628496137849184993872033 48471372103386888745404025)
  ·
    refine ⟨36353529077540166559053019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48471372103386888745404025 36353529077540166559053019)
    ·
      refine ⟨54530293616310249838579529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36353529077540166559053019 54530293616310249838579529)
      ·
        refine ⟨40897720212232687378934647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54530293616310249838579529 40897720212232687378934647)
        ·
          refine ⟨61346580318349031068401971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40897720212232687378934647 61346580318349031068401971)
          ·
            refine ⟨92019870477523546602602957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61346580318349031068401971 92019870477523546602602957)
            ·
              refine ⟨34507451429071329975976109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92019870477523546602602957 34507451429071329975976109)
              ·
                refine ⟨12940294285901748740991041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34507451429071329975976109 12940294285901748740991041)
                ·
                  refine ⟨9705220714426311555743281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12940294285901748740991041 9705220714426311555743281)
                  ·
                    refine ⟨7278915535819733666807461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9705220714426311555743281 7278915535819733666807461)
                    ·
                      refine ⟨1364796662966200062526399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7278915535819733666807461 1364796662966200062526399)
                      ·
                        rfl

theorem cell23_2657932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_2657932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657932 prefixEnd_2657932 := by exact prefixLift 2657932
  have htrace : WordTrace (prefixWord ++ tailWord_2657932) baseStart_2657932 baseEnd_2657932 := by
    simpa [prefixWord, tailWord_2657932, baseEnd_2657932] using wordTrace_append hprefix tailTrace_2657932
  have hstable : (prefixWord ++ tailWord_2657932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657932).length < 2 ^ (prefixWord ++ tailWord_2657932).sum := by decide
  have hdescent : baseEnd_2657932 < baseStart_2657932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657936 : List Nat := [2, 1, 1, 1, 1, 1, 3, 7, 2, 2, 2]
def baseStart_2657936 : Nat := 118140960795 + 2657936 * 2 ^ 59
def prefixEnd_2657936 : Nat := 4983230072969 + 3 ^ 40 * 2657936 * 2
def baseEnd_2657936 : Nat := 1364798716888818046876381

theorem tailTrace_2657936 : CollatzResearch.WordTrace tailWord_2657936 prefixEnd_2657936 1364798716888818046876381 := by
  unfold tailWord_2657936
  simp only [CollatzResearch.WordTrace]
  refine ⟨48471445049379643086976831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64628593399172857449302441 48471445049379643086976831)
  ·
    refine ⟨72707167574069464630465247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48471445049379643086976831 72707167574069464630465247)
    ·
      refine ⟨109060751361104196945697871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72707167574069464630465247 109060751361104196945697871)
      ·
        refine ⟨163591127041656295418546807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109060751361104196945697871 163591127041656295418546807)
        ·
          refine ⟨245386690562484443127820211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163591127041656295418546807 245386690562484443127820211)
          ·
            refine ⟨368080035843726664691730317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245386690562484443127820211 368080035843726664691730317)
            ·
              refine ⟨138030013441397499259398869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 368080035843726664691730317 138030013441397499259398869)
              ·
                refine ⟨3235078440032753888892161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 138030013441397499259398869 3235078440032753888892161)
                ·
                  refine ⟨2426308830024565416669121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3235078440032753888892161 2426308830024565416669121)
                  ·
                    refine ⟨1819731622518424062501841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2426308830024565416669121 1819731622518424062501841)
                    ·
                      refine ⟨1364798716888818046876381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819731622518424062501841 1364798716888818046876381)
                      ·
                        rfl

theorem cell23_2657936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 2, 2, 2].length) (baseStart_2657936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657936 prefixEnd_2657936 := by exact prefixLift 2657936
  have htrace : WordTrace (prefixWord ++ tailWord_2657936) baseStart_2657936 baseEnd_2657936 := by
    simpa [prefixWord, tailWord_2657936, baseEnd_2657936] using wordTrace_append hprefix tailTrace_2657936
  have hstable : (prefixWord ++ tailWord_2657936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657936).length < 2 ^ (prefixWord ++ tailWord_2657936).sum := by decide
  have hdescent : baseEnd_2657936 < baseStart_2657936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657940 : List Nat := [2, 4, 2, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_2657940 : Nat := 118140960795 + 2657940 * 2 ^ 59
def prefixEnd_2657940 : Nat := 4983230072969 + 3 ^ 40 * 2657940 * 2
def baseEnd_2657940 : Nat := 1364800770811436031226363

theorem tailTrace_2657940 : CollatzResearch.WordTrace tailWord_2657940 prefixEnd_2657940 1364800770811436031226363 := by
  unfold tailWord_2657940
  simp only [CollatzResearch.WordTrace]
  refine ⟨48471517995372397428549637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64628690660496529904732849 48471517995372397428549637)
  ·
    refine ⟨9088409624132324517853057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48471517995372397428549637 9088409624132324517853057)
    ·
      refine ⟨6816307218099243388389793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9088409624132324517853057 6816307218099243388389793)
      ·
        refine ⟨5112230413574432541292345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6816307218099243388389793 5112230413574432541292345)
        ·
          refine ⟨3834172810180824405969259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5112230413574432541292345 3834172810180824405969259)
          ·
            refine ⟨5751259215271236608953889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3834172810180824405969259 5751259215271236608953889)
            ·
              refine ⟨4313444411453427456715417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5751259215271236608953889 4313444411453427456715417)
              ·
                refine ⟨3235083308590070592536563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4313444411453427456715417 3235083308590070592536563)
                ·
                  refine ⟨4852624962885105888804845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3235083308590070592536563 4852624962885105888804845)
                  ·
                    refine ⟨1819734361081914708301817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4852624962885105888804845 1819734361081914708301817)
                    ·
                      refine ⟨1364800770811436031226363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819734361081914708301817 1364800770811436031226363)
                      ·
                        rfl

theorem cell23_2657940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_2657940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2657940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2657940 prefixEnd_2657940 := by exact prefixLift 2657940
  have htrace : WordTrace (prefixWord ++ tailWord_2657940) baseStart_2657940 baseEnd_2657940 := by
    simpa [prefixWord, tailWord_2657940, baseEnd_2657940] using wordTrace_append hprefix tailTrace_2657940
  have hstable : (prefixWord ++ tailWord_2657940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657940).length < 2 ^ (prefixWord ++ tailWord_2657940).sum := by decide
  have hdescent : baseEnd_2657940 < baseStart_2657940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658009 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 2, 1, 4]
def baseStart_2658009 : Nat := 118140960795 + 2658009 * 2 ^ 59
def prefixEnd_2658009 : Nat := 4983230072969 + 3 ^ 40 * 2658009 * 2
def baseEnd_2658009 : Nat := 1364836200976596261263545

theorem tailTrace_2658009 : CollatzResearch.WordTrace tailWord_2658009 prefixEnd_2658009 1364836200976596261263545 := by
  unfold tailWord_2658009
  simp only [CollatzResearch.WordTrace]
  refine ⟨96945552627494819641361081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64630368418329879760907387 96945552627494819641361081)
  ·
    refine ⟨72709164470621114731020811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96945552627494819641361081 72709164470621114731020811)
    ·
      refine ⟨109063746705931672096531217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72709164470621114731020811 109063746705931672096531217)
      ·
        refine ⟨81797810029448754072398413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109063746705931672096531217 81797810029448754072398413)
        ·
          refine ⟨30674178761043282777149405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81797810029448754072398413 30674178761043282777149405)
          ·
            refine ⟨11502817035391231041431027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30674178761043282777149405 11502817035391231041431027)
            ·
              refine ⟨17254225553086846562146541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11502817035391231041431027 17254225553086846562146541)
              ·
                refine ⟨6470334582407567460804953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17254225553086846562146541 6470334582407567460804953)
                ·
                  refine ⟨4852750936805675595603715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6470334582407567460804953 4852750936805675595603715)
                  ·
                    refine ⟨7279126405208513393405573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4852750936805675595603715 7279126405208513393405573)
                    ·
                      refine ⟨1364836200976596261263545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7279126405208513393405573 1364836200976596261263545)
                      ·
                        rfl

theorem cell23_2658009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_2658009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658009 prefixEnd_2658009 := by exact prefixLift 2658009
  have htrace : WordTrace (prefixWord ++ tailWord_2658009) baseStart_2658009 baseEnd_2658009 := by
    simpa [prefixWord, tailWord_2658009, baseEnd_2658009] using wordTrace_append hprefix tailTrace_2658009
  have hstable : (prefixWord ++ tailWord_2658009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658009).length < 2 ^ (prefixWord ++ tailWord_2658009).sum := by decide
  have hdescent : baseEnd_2658009 < baseStart_2658009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658049 : List Nat := [1, 2, 4, 1, 1, 1, 4, 3, 6]
def baseStart_2658049 : Nat := 118140960795 + 2658049 * 2 ^ 59
def prefixEnd_2658049 : Nat := 4983230072969 + 3 ^ 40 * 2658049 * 2
def baseEnd_2658049 : Nat := 151650748911419567195929

theorem tailTrace_2658049 : CollatzResearch.WordTrace tailWord_2658049 prefixEnd_2658049 151650748911419567195929 := by
  unfold tailWord_2658049
  simp only [CollatzResearch.WordTrace]
  refine ⟨96947011547349906472817201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64631341031566604315211467 96947011547349906472817201)
  ·
    refine ⟨72710258660512429854612901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96947011547349906472817201 72710258660512429854612901)
    ·
      refine ⟨13633173498846080597739919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72710258660512429854612901 13633173498846080597739919)
      ·
        refine ⟨20449760248269120896609879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13633173498846080597739919 20449760248269120896609879)
        ·
          refine ⟨30674640372403681344914819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20449760248269120896609879 30674640372403681344914819)
          ·
            refine ⟨46011960558605522017372229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30674640372403681344914819 46011960558605522017372229)
            ·
              refine ⟨8627242604738535378257293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46011960558605522017372229 8627242604738535378257293)
              ·
                refine ⟨3235215976776950766846485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8627242604738535378257293 3235215976776950766846485)
                ·
                  refine ⟨151650748911419567195929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3235215976776950766846485 151650748911419567195929)
                  ·
                    rfl

theorem cell23_2658049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 6].length) (baseStart_2658049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658049 prefixEnd_2658049 := by exact prefixLift 2658049
  have htrace : WordTrace (prefixWord ++ tailWord_2658049) baseStart_2658049 baseEnd_2658049 := by
    simpa [prefixWord, tailWord_2658049, baseEnd_2658049] using wordTrace_append hprefix tailTrace_2658049
  have hstable : (prefixWord ++ tailWord_2658049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658049).length < 2 ^ (prefixWord ++ tailWord_2658049).sum := by decide
  have hdescent : baseEnd_2658049 < baseStart_2658049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658076 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_2658076 : Nat := 118140960795 + 2658076 * 2 ^ 59
def prefixEnd_2658076 : Nat := 4983230072969 + 3 ^ 40 * 2658076 * 2
def baseEnd_2658076 : Nat := 1364870604180447499125737

theorem tailTrace_2658076 : CollatzResearch.WordTrace tailWord_2658076 prefixEnd_2658076 1364870604180447499125737 := by
  unfold tailWord_2658076
  simp only [CollatzResearch.WordTrace]
  refine ⟨48473998159126045042025041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64631997545501393389366721 48473998159126045042025041)
  ·
    refine ⟨36355498619344533781518781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48473998159126045042025041 36355498619344533781518781)
    ·
      refine ⟨13633311982254200168069543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36355498619344533781518781 13633311982254200168069543)
      ·
        refine ⟨20449967973381300252104315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13633311982254200168069543 20449967973381300252104315)
        ·
          refine ⟨30674951960071950378156473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20449967973381300252104315 30674951960071950378156473)
          ·
            refine ⟨23006213970053962783617355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30674951960071950378156473 23006213970053962783617355)
            ·
              refine ⟨34509320955080944175426033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23006213970053962783617355 34509320955080944175426033)
              ·
                refine ⟨25881990716310708131569525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34509320955080944175426033 25881990716310708131569525)
                ·
                  refine ⟨2426436629654128887334643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25881990716310708131569525 2426436629654128887334643)
                  ·
                    refine ⟨3639654944481193331001965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2426436629654128887334643 3639654944481193331001965)
                    ·
                      refine ⟨1364870604180447499125737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3639654944481193331001965 1364870604180447499125737)
                      ·
                        rfl

theorem cell23_2658076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_2658076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658076 prefixEnd_2658076 := by exact prefixLift 2658076
  have htrace : WordTrace (prefixWord ++ tailWord_2658076) baseStart_2658076 baseEnd_2658076 := by
    simpa [prefixWord, tailWord_2658076, baseEnd_2658076] using wordTrace_append hprefix tailTrace_2658076
  have hstable : (prefixWord ++ tailWord_2658076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658076).length < 2 ^ (prefixWord ++ tailWord_2658076).sum := by decide
  have hdescent : baseEnd_2658076 < baseStart_2658076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658146 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2658146 : Nat := 118140960795 + 2658146 * 2 ^ 59
def prefixEnd_2658146 : Nat := 4983230072969 + 3 ^ 40 * 2658146 * 2
def baseEnd_2658146 : Nat := 1364906547826262225250415

theorem tailTrace_2658146 : CollatzResearch.WordTrace tailWord_2658146 prefixEnd_2658146 1364906547826262225250415 := by
  unfold tailWord_2658146
  simp only [CollatzResearch.WordTrace]
  refine ⟨24237637356999623009774573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64633699618665661359398861 24237637356999623009774573)
  ·
    refine ⟨9089114008874858628665465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24237637356999623009774573 9089114008874858628665465)
    ·
      refine ⟨6816835506656143971499099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9089114008874858628665465 6816835506656143971499099)
      ·
        refine ⟨10225253259984215957248649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6816835506656143971499099 10225253259984215957248649)
        ·
          refine ⟨7668939944988161967936487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10225253259984215957248649 7668939944988161967936487)
          ·
            refine ⟨11503409917482242951904731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7668939944988161967936487 11503409917482242951904731)
            ·
              refine ⟨17255114876223364427857097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11503409917482242951904731 17255114876223364427857097)
              ·
                refine ⟨12941336157167523320892823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17255114876223364427857097 12941336157167523320892823)
                ·
                  refine ⟨19412004235751284981339235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12941336157167523320892823 19412004235751284981339235)
                  ·
                    refine ⟨29118006353626927472008853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19412004235751284981339235 29118006353626927472008853)
                    ·
                      refine ⟨1364906547826262225250415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29118006353626927472008853 1364906547826262225250415)
                      ·
                        rfl

theorem cell23_2658146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2658146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658146 prefixEnd_2658146 := by exact prefixLift 2658146
  have htrace : WordTrace (prefixWord ++ tailWord_2658146) baseStart_2658146 baseEnd_2658146 := by
    simpa [prefixWord, tailWord_2658146, baseEnd_2658146] using wordTrace_append hprefix tailTrace_2658146
  have hstable : (prefixWord ++ tailWord_2658146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658146).length < 2 ^ (prefixWord ++ tailWord_2658146).sum := by decide
  have hdescent : baseEnd_2658146 < baseStart_2658146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658183 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 3]
def baseStart_2658183 : Nat := 118140960795 + 2658183 * 2 ^ 59
def prefixEnd_2658183 : Nat := 4983230072969 + 3 ^ 40 * 2658183 * 2
def baseEnd_2658183 : Nat := 1364925546610478580487745

theorem tailTrace_2658183 : CollatzResearch.WordTrace tailWord_2658183 prefixEnd_2658183 1364925546610478580487745 := by
  unfold tailWord_2658183
  simp only [CollatzResearch.WordTrace]
  refine ⟨96951898928864447358195203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64634599285909631572130135 96951898928864447358195203)
  ·
    refine ⟨145427848393296671037292805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96951898928864447358195203 145427848393296671037292805)
    ·
      refine ⟨27267721573743125819492401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145427848393296671037292805 27267721573743125819492401)
      ·
        refine ⟨20450791180307344364619301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27267721573743125819492401 20450791180307344364619301)
        ·
          refine ⟨3834523346307627068366119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20450791180307344364619301 3834523346307627068366119)
          ·
            refine ⟨5751785019461440602549179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3834523346307627068366119 5751785019461440602549179)
            ·
              refine ⟨8627677529192160903823769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5751785019461440602549179 8627677529192160903823769)
              ·
                refine ⟨6470758146894120677867827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8627677529192160903823769 6470758146894120677867827)
                ·
                  refine ⟨9706137220341181016801741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6470758146894120677867827 9706137220341181016801741)
                  ·
                    refine ⟨3639801457627942881300653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9706137220341181016801741 3639801457627942881300653)
                    ·
                      refine ⟨1364925546610478580487745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3639801457627942881300653 1364925546610478580487745)
                      ·
                        rfl

theorem cell23_2658183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_2658183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658183 prefixEnd_2658183 := by exact prefixLift 2658183
  have htrace : WordTrace (prefixWord ++ tailWord_2658183) baseStart_2658183 baseEnd_2658183 := by
    simpa [prefixWord, tailWord_2658183, baseEnd_2658183] using wordTrace_append hprefix tailTrace_2658183
  have hstable : (prefixWord ++ tailWord_2658183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658183).length < 2 ^ (prefixWord ++ tailWord_2658183).sum := by decide
  have hdescent : baseEnd_2658183 < baseStart_2658183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658193 : List Nat := [1, 2, 2, 1, 1, 1, 4, 5, 1, 3, 2]
def baseStart_2658193 : Nat := 118140960795 + 2658193 * 2 ^ 59
def prefixEnd_2658193 : Nat := 4983230072969 + 3 ^ 40 * 2658193 * 2
def baseEnd_2658193 : Nat := 1364930681417023541362699

theorem tailTrace_2658193 : CollatzResearch.WordTrace tailWord_2658193 prefixEnd_2658193 1364930681417023541362699 := by
  unfold tailWord_2658193
  simp only [CollatzResearch.WordTrace]
  refine ⟨96952263658828219066059233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64634842439218812710706155 96952263658828219066059233)
  ·
    refine ⟨72714197744121164299544425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96952263658828219066059233 72714197744121164299544425)
    ·
      refine ⟨54535648308090873224658319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72714197744121164299544425 54535648308090873224658319)
      ·
        refine ⟨81803472462136309836987479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54535648308090873224658319 81803472462136309836987479)
        ·
          refine ⟨122705208693204464755481219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81803472462136309836987479 122705208693204464755481219)
          ·
            refine ⟨184057813039806697133221829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122705208693204464755481219 184057813039806697133221829)
            ·
              refine ⟨34510839944963755712479093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184057813039806697133221829 34510839944963755712479093)
              ·
                refine ⟨3235391244840352098044915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34510839944963755712479093 3235391244840352098044915)
                ·
                  refine ⟨4853086867260528147067373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3235391244840352098044915 4853086867260528147067373)
                  ·
                    refine ⟨1819907575222698055150265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4853086867260528147067373 1819907575222698055150265)
                    ·
                      refine ⟨1364930681417023541362699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819907575222698055150265 1364930681417023541362699)
                      ·
                        rfl

theorem cell23_2658193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 3, 2].length) (baseStart_2658193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658193 prefixEnd_2658193 := by exact prefixLift 2658193
  have htrace : WordTrace (prefixWord ++ tailWord_2658193) baseStart_2658193 baseEnd_2658193 := by
    simpa [prefixWord, tailWord_2658193, baseEnd_2658193] using wordTrace_append hprefix tailTrace_2658193
  have hstable : (prefixWord ++ tailWord_2658193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658193).length < 2 ^ (prefixWord ++ tailWord_2658193).sum := by decide
  have hdescent : baseEnd_2658193 < baseStart_2658193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658223 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 1, 4, 2]
def baseStart_2658223 : Nat := 118140960795 + 2658223 * 2 ^ 59
def prefixEnd_2658223 : Nat := 4983230072969 + 3 ^ 40 * 2658223 * 2
def baseEnd_2658223 : Nat := 1364946085836658423987561

theorem tailTrace_2658223 : CollatzResearch.WordTrace tailWord_2658223 prefixEnd_2658223 1364946085836658423987561 := by
  unfold tailWord_2658223
  simp only [CollatzResearch.WordTrace]
  refine ⟨96953357848719534189651323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64635571899146356126434215 96953357848719534189651323)
  ·
    refine ⟨145430036773079301284476985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96953357848719534189651323 145430036773079301284476985)
    ·
      refine ⟨109072527579809475963357739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145430036773079301284476985 109072527579809475963357739)
      ·
        refine ⟨163608791369714213945036609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109072527579809475963357739 163608791369714213945036609)
        ·
          refine ⟨122706593527285660458777457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163608791369714213945036609 122706593527285660458777457)
          ·
            refine ⟨92029945145464245344083093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122706593527285660458777457 92029945145464245344083093)
            ·
              refine ⟨4313903678693636500503895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92029945145464245344083093 4313903678693636500503895)
              ·
                refine ⟨6470855518040454750755843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4313903678693636500503895 6470855518040454750755843)
                ·
                  refine ⟨9706283277060682126133765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6470855518040454750755843 9706283277060682126133765)
                  ·
                    refine ⟨1819928114448877898650081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9706283277060682126133765 1819928114448877898650081)
                    ·
                      refine ⟨1364946085836658423987561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819928114448877898650081 1364946085836658423987561)
                      ·
                        rfl

theorem cell23_2658223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 4, 2].length) (baseStart_2658223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658223 prefixEnd_2658223 := by exact prefixLift 2658223
  have htrace : WordTrace (prefixWord ++ tailWord_2658223) baseStart_2658223 baseEnd_2658223 := by
    simpa [prefixWord, tailWord_2658223, baseEnd_2658223] using wordTrace_append hprefix tailTrace_2658223
  have hstable : (prefixWord ++ tailWord_2658223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658223).length < 2 ^ (prefixWord ++ tailWord_2658223).sum := by decide
  have hdescent : baseEnd_2658223 < baseStart_2658223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658256 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 3]
def baseStart_2658256 : Nat := 118140960795 + 2658256 * 2 ^ 59
def prefixEnd_2658256 : Nat := 4983230072969 + 3 ^ 40 * 2658256 * 2
def baseEnd_2658256 : Nat := 1364963030698256794874909

theorem tailTrace_2658256 : CollatzResearch.WordTrace tailWord_2658256 prefixEnd_2658256 1364963030698256794874909 := by
  unfold tailWord_2658256
  simp only [CollatzResearch.WordTrace]
  refine ⟨48477280728799990412801311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64636374305066653883735081 48477280728799990412801311)
  ·
    refine ⟨72715921093199985619201967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48477280728799990412801311 72715921093199985619201967)
    ·
      refine ⟨109073881639799978428802951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72715921093199985619201967 109073881639799978428802951)
      ·
        refine ⟨163610822459699967643204427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109073881639799978428802951 163610822459699967643204427)
        ·
          refine ⟨245416233689549951464806641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163610822459699967643204427 245416233689549951464806641)
          ·
            refine ⟨184062175267162463598604981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245416233689549951464806641 184062175267162463598604981)
            ·
              refine ⟨17255828931296480962369217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184062175267162463598604981 17255828931296480962369217)
              ·
                refine ⟨12941871698472360721776913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17255828931296480962369217 12941871698472360721776913)
                ·
                  refine ⟨9706403773854270541332685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12941871698472360721776913 9706403773854270541332685)
                  ·
                    refine ⟨3639901415195351452999757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9706403773854270541332685 3639901415195351452999757)
                    ·
                      refine ⟨1364963030698256794874909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3639901415195351452999757 1364963030698256794874909)
                      ·
                        rfl

theorem cell23_2658256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 3].length) (baseStart_2658256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658256 prefixEnd_2658256 := by exact prefixLift 2658256
  have htrace : WordTrace (prefixWord ++ tailWord_2658256) baseStart_2658256 baseEnd_2658256 := by
    simpa [prefixWord, tailWord_2658256, baseEnd_2658256] using wordTrace_append hprefix tailTrace_2658256
  have hstable : (prefixWord ++ tailWord_2658256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658256).length < 2 ^ (prefixWord ++ tailWord_2658256).sum := by decide
  have hdescent : baseEnd_2658256 < baseStart_2658256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658274 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_2658274 : Nat := 118140960795 + 2658274 * 2 ^ 59
def prefixEnd_2658274 : Nat := 4983230072969 + 3 ^ 40 * 2658274 * 2
def baseEnd_2658274 : Nat := 1364972273350037724449827

theorem tailTrace_2658274 : CollatzResearch.WordTrace tailWord_2658274 prefixEnd_2658274 1364972273350037724449827 := by
  unfold tailWord_2658274
  simp only [CollatzResearch.WordTrace]
  refine ⟨24238804492883692474939469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64636811981023179933171917 24238804492883692474939469)
  ·
    refine ⟨9089551684831384678102301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24238804492883692474939469 9089551684831384678102301)
    ·
      refine ⟨3408581881811769254288363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9089551684831384678102301 3408581881811769254288363)
      ·
        refine ⟨5112872822717653881432545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3408581881811769254288363 5112872822717653881432545)
        ·
          refine ⟨3834654617038240411074409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5112872822717653881432545 3834654617038240411074409)
          ·
            refine ⟨2875990962778680308305807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3834654617038240411074409 2875990962778680308305807)
            ·
              refine ⟨4313986444168020462458711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2875990962778680308305807 4313986444168020462458711)
              ·
                refine ⟨6470979666252030693688067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4313986444168020462458711 6470979666252030693688067)
                ·
                  refine ⟨9706469499378046040532101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6470979666252030693688067 9706469499378046040532101)
                  ·
                    refine ⟨1819963031133383632599769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9706469499378046040532101 1819963031133383632599769)
                    ·
                      refine ⟨1364972273350037724449827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1819963031133383632599769 1364972273350037724449827)
                      ·
                        rfl

theorem cell23_2658274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_2658274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658274 prefixEnd_2658274 := by exact prefixLift 2658274
  have htrace : WordTrace (prefixWord ++ tailWord_2658274) baseStart_2658274 baseEnd_2658274 := by
    simpa [prefixWord, tailWord_2658274, baseEnd_2658274] using wordTrace_append hprefix tailTrace_2658274
  have hstable : (prefixWord ++ tailWord_2658274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658274).length < 2 ^ (prefixWord ++ tailWord_2658274).sum := by decide
  have hdescent : baseEnd_2658274 < baseStart_2658274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658296 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 1, 3, 4]
def baseStart_2658296 : Nat := 118140960795 + 2658296 * 2 ^ 59
def prefixEnd_2658296 : Nat := 4983230072969 + 3 ^ 40 * 2658296 * 2
def baseEnd_2658296 : Nat := 1364983569924436638374725

theorem tailTrace_2658296 : CollatzResearch.WordTrace tailWord_2658296 prefixEnd_2658296 1364983569924436638374725 := by
  unfold tailWord_2658296
  simp only [CollatzResearch.WordTrace]
  refine ⟨48478010188727533828529371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64637346918303378438039161 48478010188727533828529371)
  ·
    refine ⟨72717015283091300742794057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48478010188727533828529371 72717015283091300742794057)
    ·
      refine ⟨54537761462318475557095543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72717015283091300742794057 54537761462318475557095543)
      ·
        refine ⟨81806642193477713335643315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54537761462318475557095543 81806642193477713335643315)
        ·
          refine ⟨122709963290216570003464973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81806642193477713335643315 122709963290216570003464973)
          ·
            refine ⟨46016236233831213751299365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122709963290216570003464973 46016236233831213751299365)
            ·
              refine ⟨8628044293843352578368631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46016236233831213751299365 8628044293843352578368631)
              ·
                refine ⟨12942066440765028867552947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8628044293843352578368631 12942066440765028867552947)
                ·
                  refine ⟨19413099661147543301329421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12942066440765028867552947 19413099661147543301329421)
                  ·
                    refine ⟨7279912372930328737998533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19413099661147543301329421 7279912372930328737998533)
                    ·
                      refine ⟨1364983569924436638374725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7279912372930328737998533 1364983569924436638374725)
                      ·
                        rfl

theorem cell23_2658296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_2658296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658296 prefixEnd_2658296 := by exact prefixLift 2658296
  have htrace : WordTrace (prefixWord ++ tailWord_2658296) baseStart_2658296 baseEnd_2658296 := by
    simpa [prefixWord, tailWord_2658296, baseEnd_2658296] using wordTrace_append hprefix tailTrace_2658296
  have hstable : (prefixWord ++ tailWord_2658296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658296).length < 2 ^ (prefixWord ++ tailWord_2658296).sum := by decide
  have hdescent : baseEnd_2658296 < baseStart_2658296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658323 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 3, 4]
def baseStart_2658323 : Nat := 118140960795 + 2658323 * 2 ^ 59
def prefixEnd_2658323 : Nat := 4983230072969 + 3 ^ 40 * 2658323 * 2
def baseEnd_2658323 : Nat := 454999144634036010912367

theorem tailTrace_2658323 : CollatzResearch.WordTrace tailWord_2658323 prefixEnd_2658323 454999144634036010912367 := by
  unfold tailWord_2658323
  simp only [CollatzResearch.WordTrace]
  refine ⟨96957005148357251268291623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64638003432238167512194415 96957005148357251268291623)
  ·
    refine ⟨145435507722535876902437435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96957005148357251268291623 145435507722535876902437435)
    ·
      refine ⟨218153261583803815353656153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145435507722535876902437435 218153261583803815353656153)
      ·
        refine ⟨163614946187852861515242115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218153261583803815353656153 163614946187852861515242115)
        ·
          refine ⟨245422419281779292272863173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163614946187852861515242115 245422419281779292272863173)
          ·
            refine ⟨46016703615333617301161845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245422419281779292272863173 46016703615333617301161845)
            ·
              refine ⟨4314065963937526621983923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46016703615333617301161845 4314065963937526621983923)
              ·
                refine ⟨6471098945906289932975885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4314065963937526621983923 6471098945906289932975885)
                ·
                  refine ⟨2426662104714858724865957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6471098945906289932975885 2426662104714858724865957)
                  ·
                    refine ⟨454999144634036010912367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2426662104714858724865957 454999144634036010912367)
                    ·
                      rfl

theorem cell23_2658323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 4].length) (baseStart_2658323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658323 prefixEnd_2658323 := by exact prefixLift 2658323
  have htrace : WordTrace (prefixWord ++ tailWord_2658323) baseStart_2658323 baseEnd_2658323 := by
    simpa [prefixWord, tailWord_2658323, baseEnd_2658323] using wordTrace_append hprefix tailTrace_2658323
  have hstable : (prefixWord ++ tailWord_2658323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658323).length < 2 ^ (prefixWord ++ tailWord_2658323).sum := by decide
  have hdescent : baseEnd_2658323 < baseStart_2658323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658350 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_2658350 : Nat := 118140960795 + 2658350 * 2 ^ 59
def prefixEnd_2658350 : Nat := 4983230072969 + 3 ^ 40 * 2658350 * 2
def baseEnd_2658350 : Nat := 1365011297879779427099477

theorem tailTrace_2658350 : CollatzResearch.WordTrace tailWord_2658350 prefixEnd_2658350 1365011297879779427099477 := by
  unfold tailWord_2658350
  simp only [CollatzResearch.WordTrace]
  refine ⟨12119748739907429359940563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64638659946172956586349669 12119748739907429359940563)
  ·
    refine ⟨18179623109861144039910845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12119748739907429359940563 18179623109861144039910845)
    ·
      refine ⟨6817358666197929014966567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18179623109861144039910845 6817358666197929014966567)
      ·
        refine ⟨10226037999296893522449851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6817358666197929014966567 10226037999296893522449851)
        ·
          refine ⟨15339056998945340283674777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10226037999296893522449851 15339056998945340283674777)
          ·
            refine ⟨11504292749209005212756083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15339056998945340283674777 11504292749209005212756083)
            ·
              refine ⟨17256439123813507819134125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11504292749209005212756083 17256439123813507819134125)
              ·
                refine ⟨6471164671430065432175297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17256439123813507819134125 6471164671430065432175297)
                ·
                  refine ⟨4853373503572549074131473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6471164671430065432175297 4853373503572549074131473)
                  ·
                    refine ⟨3640030127679411805598605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4853373503572549074131473 3640030127679411805598605)
                    ·
                      refine ⟨1365011297879779427099477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3640030127679411805598605 1365011297879779427099477)
                      ·
                        rfl

theorem cell23_2658350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_2658350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658350 prefixEnd_2658350 := by exact prefixLift 2658350
  have htrace : WordTrace (prefixWord ++ tailWord_2658350) baseStart_2658350 baseEnd_2658350 := by
    simpa [prefixWord, tailWord_2658350, baseEnd_2658350] using wordTrace_append hprefix tailTrace_2658350
  have hstable : (prefixWord ++ tailWord_2658350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658350).length < 2 ^ (prefixWord ++ tailWord_2658350).sum := by decide
  have hdescent : baseEnd_2658350 < baseStart_2658350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658363 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 5, 1, 3]
def baseStart_2658363 : Nat := 118140960795 + 2658363 * 2 ^ 59
def prefixEnd_2658363 : Nat := 4983230072969 + 3 ^ 40 * 2658363 * 2
def baseEnd_2658363 : Nat := 1365017973128287876236917

theorem tailTrace_2658363 : CollatzResearch.WordTrace tailWord_2658363 prefixEnd_2658363 1365017973128287876236917 := by
  unfold tailWord_2658363
  simp only [CollatzResearch.WordTrace]
  refine ⟨96958464068212338099747743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64638976045474892066498495 96958464068212338099747743)
  ·
    refine ⟨145437696102318507149621615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96958464068212338099747743 145437696102318507149621615)
    ·
      refine ⟨218156544153477760724432423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145437696102318507149621615 218156544153477760724432423)
      ·
        refine ⟨327234816230216641086648635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218156544153477760724432423 327234816230216641086648635)
        ·
          refine ⟨490852224345324961629972953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327234816230216641086648635 490852224345324961629972953)
          ·
            refine ⟨368139168258993721222479715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 490852224345324961629972953 368139168258993721222479715)
            ·
              refine ⟨552208752388490581833719573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368139168258993721222479715 552208752388490581833719573)
              ·
                refine ⟨25884785268210496023455605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 552208752388490581833719573 25884785268210496023455605)
                ·
                  refine ⟨2426698618894734002198963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25884785268210496023455605 2426698618894734002198963)
                  ·
                    refine ⟨3640047928342101003298445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2426698618894734002198963 3640047928342101003298445)
                    ·
                      refine ⟨1365017973128287876236917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3640047928342101003298445 1365017973128287876236917)
                      ·
                        rfl

theorem cell23_2658363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 1, 3].length) (baseStart_2658363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658363 prefixEnd_2658363 := by exact prefixLift 2658363
  have htrace : WordTrace (prefixWord ++ tailWord_2658363) baseStart_2658363 baseEnd_2658363 := by
    simpa [prefixWord, tailWord_2658363, baseEnd_2658363] using wordTrace_append hprefix tailTrace_2658363
  have hstable : (prefixWord ++ tailWord_2658363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658363).length < 2 ^ (prefixWord ++ tailWord_2658363).sum := by decide
  have hdescent : baseEnd_2658363 < baseStart_2658363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658373 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 3, 5, 2]
def baseStart_2658373 : Nat := 118140960795 + 2658373 * 2 ^ 59
def prefixEnd_2658373 : Nat := 4983230072969 + 3 ^ 40 * 2658373 * 2
def baseEnd_2658373 : Nat := 1365023107934832837111871

theorem tailTrace_2658373 : CollatzResearch.WordTrace tailWord_2658373 prefixEnd_2658373 1365023107934832837111871 := by
  unfold tailWord_2658373
  simp only [CollatzResearch.WordTrace]
  refine ⟨96958828798176109807611773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64639219198784073205074515 96958828798176109807611773)
  ·
    refine ⟨36359560799316041177854415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96958828798176109807611773 36359560799316041177854415)
    ·
      refine ⟨54539341198974061766781623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36359560799316041177854415 54539341198974061766781623)
      ·
        refine ⟨81809011798461092650172435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54539341198974061766781623 81809011798461092650172435)
        ·
          refine ⟨122713517697691638975258653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81809011798461092650172435 122713517697691638975258653)
          ·
            refine ⟨46017569136634364615721995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122713517697691638975258653 46017569136634364615721995)
            ·
              refine ⟨69026353704951546923582993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46017569136634364615721995 69026353704951546923582993)
              ·
                refine ⟨51769765278713660192687245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69026353704951546923582993 51769765278713660192687245)
                ·
                  refine ⟨19413661979517622572257717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51769765278713660192687245 19413661979517622572257717)
                  ·
                    refine ⟨1820030810579777116149161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19413661979517622572257717 1820030810579777116149161)
                    ·
                      refine ⟨1365023107934832837111871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1820030810579777116149161 1365023107934832837111871)
                      ·
                        rfl

theorem cell23_2658373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 5, 2].length) (baseStart_2658373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658373 prefixEnd_2658373 := by exact prefixLift 2658373
  have htrace : WordTrace (prefixWord ++ tailWord_2658373) baseStart_2658373 baseEnd_2658373 := by
    simpa [prefixWord, tailWord_2658373, baseEnd_2658373] using wordTrace_append hprefix tailTrace_2658373
  have hstable : (prefixWord ++ tailWord_2658373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658373).length < 2 ^ (prefixWord ++ tailWord_2658373).sum := by decide
  have hdescent : baseEnd_2658373 < baseStart_2658373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658374 : List Nat := [6, 1, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_2658374 : Nat := 118140960795 + 2658374 * 2 ^ 59
def prefixEnd_2658374 : Nat := 4983230072969 + 3 ^ 40 * 2658374 * 2
def baseEnd_2658374 : Nat := 455007873805162444399789

theorem tailTrace_2658374 : CollatzResearch.WordTrace tailWord_2658374 prefixEnd_2658374 455007873805162444399789 := by
  unfold tailWord_2658374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3029964539724140218074943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64639243514114991318932117 3029964539724140218074943)
  ·
    refine ⟨4544946809586210327112415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3029964539724140218074943 4544946809586210327112415)
    ·
      refine ⟨6817420214379315490668623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4544946809586210327112415 6817420214379315490668623)
      ·
        refine ⟨10226130321568973236002935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6817420214379315490668623 10226130321568973236002935)
        ·
          refine ⟨15339195482353459854004403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10226130321568973236002935 15339195482353459854004403)
          ·
            refine ⟨23008793223530189781006605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15339195482353459854004403 23008793223530189781006605)
            ·
              refine ⟨8628297458823821167877477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23008793223530189781006605 8628297458823821167877477)
              ·
                refine ⟨1617805773529466468977027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8628297458823821167877477 1617805773529466468977027)
                ·
                  refine ⟨2426708660294199703465541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617805773529466468977027 2426708660294199703465541)
                  ·
                    refine ⟨455007873805162444399789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2426708660294199703465541 455007873805162444399789)
                    ·
                      rfl

theorem cell23_2658374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_2658374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658374 prefixEnd_2658374 := by exact prefixLift 2658374
  have htrace : WordTrace (prefixWord ++ tailWord_2658374) baseStart_2658374 baseEnd_2658374 := by
    simpa [prefixWord, tailWord_2658374, baseEnd_2658374] using wordTrace_append hprefix tailTrace_2658374
  have hstable : (prefixWord ++ tailWord_2658374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658374).length < 2 ^ (prefixWord ++ tailWord_2658374).sum := by decide
  have hdescent : baseEnd_2658374 < baseStart_2658374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658397 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2658397 : Nat := 118140960795 + 2658397 * 2 ^ 59
def prefixEnd_2658397 : Nat := 4983230072969 + 3 ^ 40 * 2658397 * 2
def baseEnd_2658397 : Nat := 1365035431470540743211761

theorem tailTrace_2658397 : CollatzResearch.WordTrace tailWord_2658397 prefixEnd_2658397 1365035431470540743211761 := by
  unfold tailWord_2658397
  simp only [CollatzResearch.WordTrace]
  refine ⟨96959704150089161906485445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64639802766726107937656963 96959704150089161906485445)
  ·
    refine ⟨18179944528141717857466021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96959704150089161906485445 18179944528141717857466021)
    ·
      refine ⟨3408739599026572098274879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18179944528141717857466021 3408739599026572098274879)
      ·
        refine ⟨5113109398539858147412319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3408739599026572098274879 5113109398539858147412319)
        ·
          refine ⟨7669664097809787221118479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5113109398539858147412319 7669664097809787221118479)
          ·
            refine ⟨11504496146714680831677719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7669664097809787221118479 11504496146714680831677719)
            ·
              refine ⟨17256744220072021247516579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11504496146714680831677719 17256744220072021247516579)
              ·
                refine ⟨25885116330108031871274869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17256744220072021247516579 25885116330108031871274869)
                ·
                  refine ⟨2426729655947627987932019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25885116330108031871274869 2426729655947627987932019)
                  ·
                    refine ⟨3640094483921441981898029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2426729655947627987932019 3640094483921441981898029)
                    ·
                      refine ⟨1365035431470540743211761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3640094483921441981898029 1365035431470540743211761)
                      ·
                        rfl

theorem cell23_2658397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2658397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658397 prefixEnd_2658397 := by exact prefixLift 2658397
  have htrace : WordTrace (prefixWord ++ tailWord_2658397) baseStart_2658397 baseEnd_2658397 := by
    simpa [prefixWord, tailWord_2658397, baseEnd_2658397] using wordTrace_append hprefix tailTrace_2658397
  have hstable : (prefixWord ++ tailWord_2658397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658397).length < 2 ^ (prefixWord ++ tailWord_2658397).sum := by decide
  have hdescent : baseEnd_2658397 < baseStart_2658397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658403 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 4]
def baseStart_2658403 : Nat := 118140960795 + 2658403 * 2 ^ 59
def prefixEnd_2658403 : Nat := 4983230072969 + 3 ^ 40 * 2658403 * 2
def baseEnd_2658403 : Nat := 1365038512354467719736733

theorem tailTrace_2658403 : CollatzResearch.WordTrace tailWord_2658403 prefixEnd_2658403 1365038512354467719736733 := by
  unfold tailWord_2658403
  simp only [CollatzResearch.WordTrace]
  refine ⟨96959922988067424931203863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64639948658711616620802575 96959922988067424931203863)
  ·
    refine ⟨145439884482101137396805795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96959922988067424931203863 145439884482101137396805795)
    ·
      refine ⟨218159826723151706095208693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145439884482101137396805795 218159826723151706095208693)
      ·
        refine ⟨20452483755295472446425815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 218159826723151706095208693 20452483755295472446425815)
        ·
          refine ⟨30678725632943208669638723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20452483755295472446425815 30678725632943208669638723)
          ·
            refine ⟨46018088449414813004458085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30678725632943208669638723 46018088449414813004458085)
            ·
              refine ⟨8628391584265277438335891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46018088449414813004458085 8628391584265277438335891)
              ·
                refine ⟨12942587376397916157503837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8628391584265277438335891 12942587376397916157503837)
                ·
                  refine ⟨4853470266149218559063939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12942587376397916157503837 4853470266149218559063939)
                  ·
                    refine ⟨7280205399223827838595909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4853470266149218559063939 7280205399223827838595909)
                    ·
                      refine ⟨1365038512354467719736733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7280205399223827838595909 1365038512354467719736733)
                      ·
                        rfl

theorem cell23_2658403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_2658403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658403 prefixEnd_2658403 := by exact prefixLift 2658403
  have htrace : WordTrace (prefixWord ++ tailWord_2658403) baseStart_2658403 baseEnd_2658403 := by
    simpa [prefixWord, tailWord_2658403, baseEnd_2658403] using wordTrace_append hprefix tailTrace_2658403
  have hstable : (prefixWord ++ tailWord_2658403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658403).length < 2 ^ (prefixWord ++ tailWord_2658403).sum := by decide
  have hdescent : baseEnd_2658403 < baseStart_2658403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658413 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_2658413 : Nat := 118140960795 + 2658413 * 2 ^ 59
def prefixEnd_2658413 : Nat := 4983230072969 + 3 ^ 40 * 2658413 * 2
def baseEnd_2658413 : Nat := 455014549053670893537229

theorem tailTrace_2658413 : CollatzResearch.WordTrace tailWord_2658413 prefixEnd_2658413 455014549053670893537229 := by
  unfold tailWord_2658413
  simp only [CollatzResearch.WordTrace]
  refine ⟨96960287718031196639067893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64640191812020797759378595 96960287718031196639067893)
  ·
    refine ⟨9090026973565424684912615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96960287718031196639067893 9090026973565424684912615)
    ·
      refine ⟨13635040460348137027368923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9090026973565424684912615 13635040460348137027368923)
      ·
        refine ⟨20452560690522205541053385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13635040460348137027368923 20452560690522205541053385)
        ·
          refine ⟨15339420517891654155790039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20452560690522205541053385 15339420517891654155790039)
          ·
            refine ⟨23009130776837481233685059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15339420517891654155790039 23009130776837481233685059)
            ·
              refine ⟨34513696165256221850527589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23009130776837481233685059 34513696165256221850527589)
              ·
                refine ⟨6471318030985541596973923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34513696165256221850527589 6471318030985541596973923)
                ·
                  refine ⟨9706977046478312395460885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6471318030985541596973923 9706977046478312395460885)
                  ·
                    refine ⟨455014549053670893537229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9706977046478312395460885 455014549053670893537229)
                    ·
                      rfl

theorem cell23_2658413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_2658413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658413 prefixEnd_2658413 := by exact prefixLift 2658413
  have htrace : WordTrace (prefixWord ++ tailWord_2658413) baseStart_2658413 baseEnd_2658413 := by
    simpa [prefixWord, tailWord_2658413, baseEnd_2658413] using wordTrace_append hprefix tailTrace_2658413
  have hstable : (prefixWord ++ tailWord_2658413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658413).length < 2 ^ (prefixWord ++ tailWord_2658413).sum := by decide
  have hdescent : baseEnd_2658413 < baseStart_2658413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658414 : List Nat := [4, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3]
def baseStart_2658414 : Nat := 118140960795 + 2658414 * 2 ^ 59
def prefixEnd_2658414 : Nat := 4983230072969 + 3 ^ 40 * 2658414 * 2
def baseEnd_2658414 : Nat := 1365044160641667176699183

theorem tailTrace_2658414 : CollatzResearch.WordTrace tailWord_2658414 prefixEnd_2658414 1365044160641667176699183 := by
  unfold tailWord_2658414
  simp only [CollatzResearch.WordTrace]
  refine ⟨12120040523878446726231787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64640216127351715873236197 12120040523878446726231787)
  ·
    refine ⟨18180060785817670089347681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12120040523878446726231787 18180060785817670089347681)
    ·
      refine ⟨13635045589363252567010761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18180060785817670089347681 13635045589363252567010761)
      ·
        refine ⟨10226284192022439425258071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13635045589363252567010761 10226284192022439425258071)
        ·
          refine ⟨15339426288033659137887107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10226284192022439425258071 15339426288033659137887107)
          ·
            refine ⟨23009139432050488706830661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15339426288033659137887107 23009139432050488706830661)
            ·
              refine ⟨4314213643509466632530749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23009139432050488706830661 4314213643509466632530749)
              ·
                refine ⟨1617830116316049987199031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4314213643509466632530749 1617830116316049987199031)
                ·
                  refine ⟨2426745174474074980798547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617830116316049987199031 2426745174474074980798547)
                  ·
                    refine ⟨3640117761711112471197821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2426745174474074980798547 3640117761711112471197821)
                    ·
                      refine ⟨1365044160641667176699183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3640117761711112471197821 1365044160641667176699183)
                      ·
                        rfl

theorem cell23_2658414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_2658414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658414 prefixEnd_2658414 := by exact prefixLift 2658414
  have htrace : WordTrace (prefixWord ++ tailWord_2658414) baseStart_2658414 baseEnd_2658414 := by
    simpa [prefixWord, tailWord_2658414, baseEnd_2658414] using wordTrace_append hprefix tailTrace_2658414
  have hstable : (prefixWord ++ tailWord_2658414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658414).length < 2 ^ (prefixWord ++ tailWord_2658414).sum := by decide
  have hdescent : baseEnd_2658414 < baseStart_2658414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658437 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 3, 2, 2]
def baseStart_2658437 : Nat := 118140960795 + 2658437 * 2 ^ 59
def prefixEnd_2658437 : Nat := 4983230072969 + 3 ^ 40 * 2658437 * 2
def baseEnd_2658437 : Nat := 1365055970696720586711577

theorem tailTrace_2658437 : CollatzResearch.WordTrace tailWord_2658437 prefixEnd_2658437 1365055970696720586711577 := by
  unfold tailWord_2658437
  simp only [CollatzResearch.WordTrace]
  refine ⟨96961163069944248737941565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64640775379962832491961043 96961163069944248737941565)
  ·
    refine ⟨36360436151229093276728087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96961163069944248737941565 36360436151229093276728087)
    ·
      refine ⟨54540654226843639915092131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36360436151229093276728087 54540654226843639915092131)
      ·
        refine ⟨81810981340265459872638197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54540654226843639915092131 81810981340265459872638197)
        ·
          refine ⟨7669779500649886863059831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81810981340265459872638197 7669779500649886863059831)
          ·
            refine ⟨11504669250974830294589747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7669779500649886863059831 11504669250974830294589747)
            ·
              refine ⟨17257003876462245441884621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11504669250974830294589747 17257003876462245441884621)
              ·
                refine ⟨6471376453673342040706733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17257003876462245441884621 6471376453673342040706733)
                ·
                  refine ⟨2426766170127503265265025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6471376453673342040706733 2426766170127503265265025)
                  ·
                    refine ⟨1820074627595627448948769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2426766170127503265265025 1820074627595627448948769)
                    ·
                      refine ⟨1365055970696720586711577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1820074627595627448948769 1365055970696720586711577)
                      ·
                        rfl

theorem cell23_2658437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 2, 2].length) (baseStart_2658437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658437 prefixEnd_2658437 := by exact prefixLift 2658437
  have htrace : WordTrace (prefixWord ++ tailWord_2658437) baseStart_2658437 baseEnd_2658437 := by
    simpa [prefixWord, tailWord_2658437, baseEnd_2658437] using wordTrace_append hprefix tailTrace_2658437
  have hstable : (prefixWord ++ tailWord_2658437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658437).length < 2 ^ (prefixWord ++ tailWord_2658437).sum := by decide
  have hdescent : baseEnd_2658437 < baseStart_2658437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658440 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2658440 : Nat := 118140960795 + 2658440 * 2 ^ 59
def prefixEnd_2658440 : Nat := 4983230072969 + 3 ^ 40 * 2658440 * 2
def baseEnd_2658440 : Nat := 1365057511138684074974063

theorem tailTrace_2658440 : CollatzResearch.WordTrace tailWord_2658440 prefixEnd_2658440 1365057511138684074974063 := by
  unfold tailWord_2658440
  simp only [CollatzResearch.WordTrace]
  refine ⟨48480636244466690125150387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64640848325955586833533849 48480636244466690125150387)
  ·
    refine ⟨72720954366700035187725581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48480636244466690125150387 72720954366700035187725581)
    ·
      refine ⟨27270357887512513195397093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72720954366700035187725581 27270357887512513195397093)
      ·
        refine ⟨5113192103908596224136955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27270357887512513195397093 5113192103908596224136955)
        ·
          refine ⟨7669788155862894336205433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5113192103908596224136955 7669788155862894336205433)
          ·
            refine ⟨5752341116897170752154075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7669788155862894336205433 5752341116897170752154075)
            ·
              refine ⟨8628511675345756128231113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5752341116897170752154075 8628511675345756128231113)
              ·
                refine ⟨6471383756509317096173335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8628511675345756128231113 6471383756509317096173335)
                ·
                  refine ⟨9707075634763975644260003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6471383756509317096173335 9707075634763975644260003)
                  ·
                    refine ⟨14560613452145963466390005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9707075634763975644260003 14560613452145963466390005)
                    ·
                      refine ⟨1365057511138684074974063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14560613452145963466390005 1365057511138684074974063)
                      ·
                        rfl

theorem cell23_2658440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2658440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658440 prefixEnd_2658440 := by exact prefixLift 2658440
  have htrace : WordTrace (prefixWord ++ tailWord_2658440) baseStart_2658440 baseEnd_2658440 := by
    simpa [prefixWord, tailWord_2658440, baseEnd_2658440] using wordTrace_append hprefix tailTrace_2658440
  have hstable : (prefixWord ++ tailWord_2658440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658440).length < 2 ^ (prefixWord ++ tailWord_2658440).sum := by decide
  have hdescent : baseEnd_2658440 < baseStart_2658440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658493 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_2658493 : Nat := 118140960795 + 2658493 * 2 ^ 59
def prefixEnd_2658493 : Nat := 4983230072969 + 3 ^ 40 * 2658493 * 2
def baseEnd_2658493 : Nat := 1365084725613372367611319

theorem tailTrace_2658493 : CollatzResearch.WordTrace tailWord_2658493 prefixEnd_2658493 1365084725613372367611319 := by
  unfold tailWord_2658493
  simp only [CollatzResearch.WordTrace]
  refine ⟨96963205557741370301980133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64642137038494246867986755 96963205557741370301980133)
  ·
    refine ⟨18180601042076506931621275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96963205557741370301980133 18180601042076506931621275)
    ·
      refine ⟨27270901563114760397431913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18180601042076506931621275 27270901563114760397431913)
      ·
        refine ⟨20453176172336070298073935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27270901563114760397431913 20453176172336070298073935)
        ·
          refine ⟨30679764258504105447110903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20453176172336070298073935 30679764258504105447110903)
          ·
            refine ⟨46019646387756158170666355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30679764258504105447110903 46019646387756158170666355)
            ·
              refine ⟨69029469581634237255999533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46019646387756158170666355 69029469581634237255999533)
              ·
                refine ⟨25886051093112838970999825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69029469581634237255999533 25886051093112838970999825)
                ·
                  refine ⟨19414538319834629228249869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25886051093112838970999825 19414538319834629228249869)
                  ·
                    refine ⟨7280451869937985960593701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19414538319834629228249869 7280451869937985960593701)
                    ·
                      refine ⟨1365084725613372367611319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7280451869937985960593701 1365084725613372367611319)
                      ·
                        rfl

theorem cell23_2658493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_2658493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658493 prefixEnd_2658493 := by exact prefixLift 2658493
  have htrace : WordTrace (prefixWord ++ tailWord_2658493) baseStart_2658493 baseEnd_2658493 := by
    simpa [prefixWord, tailWord_2658493, baseEnd_2658493] using wordTrace_append hprefix tailTrace_2658493
  have hstable : (prefixWord ++ tailWord_2658493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658493).length < 2 ^ (prefixWord ++ tailWord_2658493).sum := by decide
  have hdescent : baseEnd_2658493 < baseStart_2658493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658498 : List Nat := [3, 5, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_2658498 : Nat := 118140960795 + 2658498 * 2 ^ 59
def prefixEnd_2658498 : Nat := 4983230072969 + 3 ^ 40 * 2658498 * 2
def baseEnd_2658498 : Nat := 455029097672214949349599

theorem tailTrace_2658498 : CollatzResearch.WordTrace tailWord_2658498 prefixEnd_2658498 455029097672214949349599 := by
  unfold tailWord_2658498
  simp only [CollatzResearch.WordTrace]
  refine ⟨24240846980680814038978037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64642258615148837437274765 24240846980680814038978037)
  ·
    refine ⟨2272579404438826316154191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24240846980680814038978037 2272579404438826316154191)
    ·
      refine ⟨3408869106658239474231287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2272579404438826316154191 3408869106658239474231287)
      ·
        refine ⟨5113303659987359211346931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3408869106658239474231287 5113303659987359211346931)
        ·
          refine ⟨7669955489981038817020397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5113303659987359211346931 7669955489981038817020397)
          ·
            refine ⟨2876233308742889556382649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7669955489981038817020397 2876233308742889556382649)
            ·
              refine ⟨2157174981557167167286987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2876233308742889556382649 2157174981557167167286987)
              ·
                refine ⟨3235762472335750750930481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2157174981557167167286987 3235762472335750750930481)
                ·
                  refine ⟨2426821854251813063197861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3235762472335750750930481 2426821854251813063197861)
                  ·
                    refine ⟨455029097672214949349599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2426821854251813063197861 455029097672214949349599)
                    ·
                      rfl

theorem cell23_2658498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_2658498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658498 prefixEnd_2658498 := by exact prefixLift 2658498
  have htrace : WordTrace (prefixWord ++ tailWord_2658498) baseStart_2658498 baseEnd_2658498 := by
    simpa [prefixWord, tailWord_2658498, baseEnd_2658498] using wordTrace_append hprefix tailTrace_2658498
  have hstable : (prefixWord ++ tailWord_2658498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658498).length < 2 ^ (prefixWord ++ tailWord_2658498).sum := by decide
  have hdescent : baseEnd_2658498 < baseStart_2658498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658513 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 2, 1, 5]
def baseStart_2658513 : Nat := 118140960795 + 2658513 * 2 ^ 59
def prefixEnd_2658513 : Nat := 4983230072969 + 3 ^ 40 * 2658513 * 2
def baseEnd_2658513 : Nat := 1365094995226462289361227

theorem tailTrace_2658513 : CollatzResearch.WordTrace tailWord_2658513 prefixEnd_2658513 1365094995226462289361227 := by
  unfold tailWord_2658513
  simp only [CollatzResearch.WordTrace]
  refine ⟨96963935017668913717708193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64642623345112609145138795 96963935017668913717708193)
  ·
    refine ⟨72722951263251685288281145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96963935017668913717708193 72722951263251685288281145)
    ·
      refine ⟨54542213447438763966210859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72722951263251685288281145 54542213447438763966210859)
      ·
        refine ⟨81813320171158145949316289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54542213447438763966210859 81813320171158145949316289)
        ·
          refine ⟨61359990128368609461987217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81813320171158145949316289 61359990128368609461987217)
          ·
            refine ⟨46019992596276457096490413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61359990128368609461987217 46019992596276457096490413)
            ·
              refine ⟨17257497223603671411183905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46019992596276457096490413 17257497223603671411183905)
              ·
                refine ⟨12943122917702753558387929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17257497223603671411183905 12943122917702753558387929)
                ·
                  refine ⟨9707342188277065168790947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12943122917702753558387929 9707342188277065168790947)
                  ·
                    refine ⟨14561013282415597753186421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9707342188277065168790947 14561013282415597753186421)
                    ·
                      refine ⟨1365094995226462289361227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14561013282415597753186421 1365094995226462289361227)
                      ·
                        rfl

theorem cell23_2658513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_2658513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658513 prefixEnd_2658513 := by exact prefixLift 2658513
  have htrace : WordTrace (prefixWord ++ tailWord_2658513) baseStart_2658513 baseEnd_2658513 := by
    simpa [prefixWord, tailWord_2658513, baseEnd_2658513] using wordTrace_append hprefix tailTrace_2658513
  have hstable : (prefixWord ++ tailWord_2658513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658513).length < 2 ^ (prefixWord ++ tailWord_2658513).sum := by decide
  have hdescent : baseEnd_2658513 < baseStart_2658513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658514 : List Nat := [3, 2, 2, 2, 1, 2, 3, 2, 1, 3, 2]
def baseStart_2658514 : Nat := 118140960795 + 2658514 * 2 ^ 59
def prefixEnd_2658514 : Nat := 4983230072969 + 3 ^ 40 * 2658514 * 2
def baseEnd_2658514 : Nat := 1365095508707116785448723

theorem tailTrace_2658514 : CollatzResearch.WordTrace tailWord_2658514 prefixEnd_2658514 1365095508707116785448723 := by
  unfold tailWord_2658514
  simp only [CollatzResearch.WordTrace]
  refine ⟨24240992872666322722123649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64642647660443527258996397 24240992872666322722123649)
  ·
    refine ⟨18180744654499742041592737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24240992872666322722123649 18180744654499742041592737)
    ·
      refine ⟨13635558490874806531194553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18180744654499742041592737 13635558490874806531194553)
      ·
        refine ⟨10226668868156104898395915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13635558490874806531194553 10226668868156104898395915)
        ·
          refine ⟨15340003302234157347593873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10226668868156104898395915 15340003302234157347593873)
          ·
            refine ⟨11505002476675618010695405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15340003302234157347593873 11505002476675618010695405)
            ·
              refine ⟨4314375928753356754010777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11505002476675618010695405 4314375928753356754010777)
              ·
                refine ⟨3235781946565017565508083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4314375928753356754010777 3235781946565017565508083)
                ·
                  refine ⟨4853672919847526348262125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3235781946565017565508083 4853672919847526348262125)
                  ·
                    refine ⟨1820127344942822380598297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4853672919847526348262125 1820127344942822380598297)
                    ·
                      refine ⟨1365095508707116785448723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1820127344942822380598297 1365095508707116785448723)
                      ·
                        rfl

theorem cell23_2658514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_2658514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658514 prefixEnd_2658514 := by exact prefixLift 2658514
  have htrace : WordTrace (prefixWord ++ tailWord_2658514) baseStart_2658514 baseEnd_2658514 := by
    simpa [prefixWord, tailWord_2658514, baseEnd_2658514] using wordTrace_append hprefix tailTrace_2658514
  have hstable : (prefixWord ++ tailWord_2658514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658514).length < 2 ^ (prefixWord ++ tailWord_2658514).sum := by decide
  have hdescent : baseEnd_2658514 < baseStart_2658514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658563 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 1, 7]
def baseStart_2658563 : Nat := 118140960795 + 2658563 * 2 ^ 59
def prefixEnd_2658563 : Nat := 4983230072969 + 3 ^ 40 * 2658563 * 2
def baseEnd_2658563 : Nat := 455040223086395697911999

theorem tailTrace_2658563 : CollatzResearch.WordTrace tailWord_2658563 prefixEnd_2658563 455040223086395697911999 := by
  unfold tailWord_2658563
  simp only [CollatzResearch.WordTrace]
  refine ⟨96965758667487772257028343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64643839111658514838018895 96965758667487772257028343)
  ·
    refine ⟨145448638001231658385542515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96965758667487772257028343 145448638001231658385542515)
    ·
      refine ⟨218172957001847487578313773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145448638001231658385542515 218172957001847487578313773)
      ·
        refine ⟨81814858875692807841867665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218172957001847487578313773 81814858875692807841867665)
        ·
          refine ⟨61361144156769605881400749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81814858875692807841867665 61361144156769605881400749)
          ·
            refine ⟨23010429058788602205525281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61361144156769605881400749 23010429058788602205525281)
            ·
              refine ⟨17257821794091451654143961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23010429058788602205525281 17257821794091451654143961)
              ·
                refine ⟨12943366345568588740607971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17257821794091451654143961 12943366345568588740607971)
                ·
                  refine ⟨19415049518352883110911957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12943366345568588740607971 19415049518352883110911957)
                  ·
                    refine ⟨455040223086395697911999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19415049518352883110911957 455040223086395697911999)
                    ·
                      rfl

theorem cell23_2658563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 7].length) (baseStart_2658563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658563 prefixEnd_2658563 := by exact prefixLift 2658563
  have htrace : WordTrace (prefixWord ++ tailWord_2658563) baseStart_2658563 baseEnd_2658563 := by
    simpa [prefixWord, tailWord_2658563, baseEnd_2658563] using wordTrace_append hprefix tailTrace_2658563
  have hstable : (prefixWord ++ tailWord_2658563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658563).length < 2 ^ (prefixWord ++ tailWord_2658563).sum := by decide
  have hdescent : baseEnd_2658563 < baseStart_2658563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658567 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 7]
def baseStart_2658567 : Nat := 118140960795 + 2658567 * 2 ^ 59
def prefixEnd_2658567 : Nat := 4983230072969 + 3 ^ 40 * 2658567 * 2
def baseEnd_2658567 : Nat := 151680302575756119787331

theorem tailTrace_2658567 : CollatzResearch.WordTrace tailWord_2658567 prefixEnd_2658567 151680302575756119787331 := by
  unfold tailWord_2658567
  simp only [CollatzResearch.WordTrace]
  refine ⟨96965904559473280940173955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64643936372982187293449303 96965904559473280940173955)
  ·
    refine ⟨145448856839209921410260933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96965904559473280940173955 145448856839209921410260933)
    ·
      refine ⟨27271660657351860264423925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145448856839209921410260933 27271660657351860264423925)
      ·
        refine ⟨2556718186626736899789743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27271660657351860264423925 2556718186626736899789743)
        ·
          refine ⟨3835077279940105349684615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2556718186626736899789743 3835077279940105349684615)
          ·
            refine ⟨5752615919910158024526923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3835077279940105349684615 5752615919910158024526923)
            ·
              refine ⟨8628923879865237036790385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5752615919910158024526923 8628923879865237036790385)
              ·
                refine ⟨6471692909898927777592789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8628923879865237036790385 6471692909898927777592789)
                ·
                  refine ⟨151680302575756119787331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6471692909898927777592789 151680302575756119787331)
                  ·
                    rfl

theorem cell23_2658567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 7].length) (baseStart_2658567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658567 prefixEnd_2658567 := by exact prefixLift 2658567
  have htrace : WordTrace (prefixWord ++ tailWord_2658567) baseStart_2658567 baseEnd_2658567 := by
    simpa [prefixWord, tailWord_2658567, baseEnd_2658567] using wordTrace_append hprefix tailTrace_2658567
  have hstable : (prefixWord ++ tailWord_2658567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658567).length < 2 ^ (prefixWord ++ tailWord_2658567).sum := by decide
  have hdescent : baseEnd_2658567 < baseStart_2658567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658620 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 3, 4, 3]
def baseStart_2658620 : Nat := 118140960795 + 2658620 * 2 ^ 59
def prefixEnd_2658620 : Nat := 4983230072969 + 3 ^ 40 * 2658620 * 2
def baseEnd_2658620 : Nat := 1365149937656493370723235

theorem tailTrace_2658620 : CollatzResearch.WordTrace tailWord_2658620 prefixEnd_2658620 1365149937656493370723235 := by
  unfold tailWord_2658620
  simp only [CollatzResearch.WordTrace]
  refine ⟨48483918814140635495926657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64645225085520847327902209 48483918814140635495926657)
  ·
    refine ⟨36362939110605476621944993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48483918814140635495926657 36362939110605476621944993)
    ·
      refine ⟨27272204332954107466458745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36362939110605476621944993 27272204332954107466458745)
      ·
        refine ⟨20454153249715580599844059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27272204332954107466458745 20454153249715580599844059)
        ·
          refine ⟨30681229874573370899766089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20454153249715580599844059 30681229874573370899766089)
          ·
            refine ⟨23010922405930028174824567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30681229874573370899766089 23010922405930028174824567)
            ·
              refine ⟨34516383608895042262236851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23010922405930028174824567 34516383608895042262236851)
              ·
                refine ⟨51774575413342563393355277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34516383608895042262236851 51774575413342563393355277)
                ·
                  refine ⟨19415465780003461272508229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51774575413342563393355277 19415465780003461272508229)
                  ·
                    refine ⟨3640399833750648988595293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19415465780003461272508229 3640399833750648988595293)
                    ·
                      refine ⟨1365149937656493370723235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3640399833750648988595293 1365149937656493370723235)
                      ·
                        rfl

theorem cell23_2658620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_2658620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658620 prefixEnd_2658620 := by exact prefixLift 2658620
  have htrace : WordTrace (prefixWord ++ tailWord_2658620) baseStart_2658620 baseEnd_2658620 := by
    simpa [prefixWord, tailWord_2658620, baseEnd_2658620] using wordTrace_append hprefix tailTrace_2658620
  have hstable : (prefixWord ++ tailWord_2658620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658620).length < 2 ^ (prefixWord ++ tailWord_2658620).sum := by decide
  have hdescent : baseEnd_2658620 < baseStart_2658620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658643 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 8]
def baseStart_2658643 : Nat := 118140960795 + 2658643 * 2 ^ 59
def prefixEnd_2658643 : Nat := 4983230072969 + 3 ^ 40 * 2658643 * 2
def baseEnd_2658643 : Nat := 1365161747711546780735629

theorem tailTrace_2658643 : CollatzResearch.WordTrace tailWord_2658643 prefixEnd_2658643 1365161747711546780735629 := by
  unfold tailWord_2658643
  simp only [CollatzResearch.WordTrace]
  refine ⟨96968676507197945919940583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64645784338131963946627055 96968676507197945919940583)
  ·
    refine ⟨145453014760796918879910875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96968676507197945919940583 145453014760796918879910875)
    ·
      refine ⟨218179522141195378319866313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145453014760796918879910875 218179522141195378319866313)
      ·
        refine ⟨163634641605896533739899735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218179522141195378319866313 163634641605896533739899735)
        ·
          refine ⟨245451962408844800609849603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163634641605896533739899735 245451962408844800609849603)
          ·
            refine ⟨368177943613267200914774405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245451962408844800609849603 368177943613267200914774405)
            ·
              refine ⟨69033364427487600171520201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 368177943613267200914774405 69033364427487600171520201)
              ·
                refine ⟨51775023320615700128640151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69033364427487600171520201 51775023320615700128640151)
                ·
                  refine ⟨77662534980923550192960227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51775023320615700128640151 77662534980923550192960227)
                  ·
                    refine ⟨116493802471385325289440341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77662534980923550192960227 116493802471385325289440341)
                    ·
                      refine ⟨1365161747711546780735629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 116493802471385325289440341 1365161747711546780735629)
                      ·
                        rfl

theorem cell23_2658643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_2658643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658643 prefixEnd_2658643 := by exact prefixLift 2658643
  have htrace : WordTrace (prefixWord ++ tailWord_2658643) baseStart_2658643 baseEnd_2658643 := by
    simpa [prefixWord, tailWord_2658643, baseEnd_2658643] using wordTrace_append hprefix tailTrace_2658643
  have hstable : (prefixWord ++ tailWord_2658643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658643).length < 2 ^ (prefixWord ++ tailWord_2658643).sum := by decide
  have hdescent : baseEnd_2658643 < baseStart_2658643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658661 : List Nat := [1, 3, 1, 3, 1, 4, 3, 2, 1, 4]
def baseStart_2658661 : Nat := 118140960795 + 2658661 * 2 ^ 59
def prefixEnd_2658661 : Nat := 4983230072969 + 3 ^ 40 * 2658661 * 2
def baseEnd_2658661 : Nat := 455056996787775903436849

theorem tailTrace_2658661 : CollatzResearch.WordTrace tailWord_2658661 prefixEnd_2658661 455056996787775903436849 := by
  unfold tailWord_2658661
  simp only [CollatzResearch.WordTrace]
  refine ⟨96969333021132734994095837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64646222014088489996063891 96969333021132734994095837)
  ·
    refine ⟨36363499882924775622785939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96969333021132734994095837 36363499882924775622785939)
    ·
      refine ⟨54545249824387163434178909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36363499882924775622785939 54545249824387163434178909)
      ·
        refine ⟨20454468684145186287817091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54545249824387163434178909 20454468684145186287817091)
        ·
          refine ⟨30681703026217779431725637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20454468684145186287817091 30681703026217779431725637)
          ·
            refine ⟨5752819317415833643448557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30681703026217779431725637 5752819317415833643448557)
            ·
              refine ⟨2157307244030937616293209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5752819317415833643448557 2157307244030937616293209)
              ·
                refine ⟨1617980433023203212219907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2157307244030937616293209 1617980433023203212219907)
                ·
                  refine ⟨2426970649534804818329861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617980433023203212219907 2426970649534804818329861)
                  ·
                    refine ⟨455056996787775903436849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2426970649534804818329861 455056996787775903436849)
                    ·
                      rfl

theorem cell23_2658661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 1, 4].length) (baseStart_2658661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658661 prefixEnd_2658661 := by exact prefixLift 2658661
  have htrace : WordTrace (prefixWord ++ tailWord_2658661) baseStart_2658661 baseEnd_2658661 := by
    simpa [prefixWord, tailWord_2658661, baseEnd_2658661] using wordTrace_append hprefix tailTrace_2658661
  have hstable : (prefixWord ++ tailWord_2658661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658661).length < 2 ^ (prefixWord ++ tailWord_2658661).sum := by decide
  have hdescent : baseEnd_2658661 < baseStart_2658661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658674 : List Nat := [3, 2, 1, 2, 1, 5, 2, 1, 6]
def baseStart_2658674 : Nat := 118140960795 + 2658674 * 2 ^ 59
def prefixEnd_2658674 : Nat := 4983230072969 + 3 ^ 40 * 2658674 * 2
def baseEnd_2658674 : Nat := 151686407290204017716443

theorem tailTrace_2658674 : CollatzResearch.WordTrace tailWord_2658674 prefixEnd_2658674 151686407290204017716443 := by
  unfold tailWord_2658674
  simp only [CollatzResearch.WordTrace]
  refine ⟨24242451792521409553579769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64646538113390425476212717 24242451792521409553579769)
  ·
    refine ⟨18181838844391057165184827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24242451792521409553579769 18181838844391057165184827)
    ·
      refine ⟨27272758266586585747777241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18181838844391057165184827 27272758266586585747777241)
      ·
        refine ⟨20454568699939939310832931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27272758266586585747777241 20454568699939939310832931)
        ·
          refine ⟨30681853049909908966249397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20454568699939939310832931 30681853049909908966249397)
          ·
            refine ⟨2876423723429053965585881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30681853049909908966249397 2876423723429053965585881)
            ·
              refine ⟨2157317792571790474189411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2876423723429053965585881 2157317792571790474189411)
              ·
                refine ⟨3235976688857685711284117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2157317792571790474189411 3235976688857685711284117)
                ·
                  refine ⟨151686407290204017716443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3235976688857685711284117 151686407290204017716443)
                  ·
                    rfl

theorem cell23_2658674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_2658674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658674 prefixEnd_2658674 := by exact prefixLift 2658674
  have htrace : WordTrace (prefixWord ++ tailWord_2658674) baseStart_2658674 baseEnd_2658674 := by
    simpa [prefixWord, tailWord_2658674, baseEnd_2658674] using wordTrace_append hprefix tailTrace_2658674
  have hstable : (prefixWord ++ tailWord_2658674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658674).length < 2 ^ (prefixWord ++ tailWord_2658674).sum := by decide
  have hdescent : baseEnd_2658674 < baseStart_2658674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658700 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 3, 6]
def baseStart_2658700 : Nat := 118140960795 + 2658700 * 2 ^ 59
def prefixEnd_2658700 : Nat := 4983230072969 + 3 ^ 40 * 2658700 * 2
def baseEnd_2658700 : Nat := 455063672036284352574289

theorem tailTrace_2658700 : CollatzResearch.WordTrace tailWord_2658700 prefixEnd_2658700 455063672036284352574289 := by
  unfold tailWord_2658700
  simp only [CollatzResearch.WordTrace]
  refine ⟨48485377733995722327382777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64647170311994296436510369 48485377733995722327382777)
  ·
    refine ⟨36364033300496791745537083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48485377733995722327382777 36364033300496791745537083)
    ·
      refine ⟨54546049950745187618305625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36364033300496791745537083 54546049950745187618305625)
      ·
        refine ⟨40909537463058890713729219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54546049950745187618305625 40909537463058890713729219)
        ·
          refine ⟨61364306194588336070593829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40909537463058890713729219 61364306194588336070593829)
          ·
            refine ⟨11505807411485313013236343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61364306194588336070593829 11505807411485313013236343)
            ·
              refine ⟨17258711117227969519854515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11505807411485313013236343 17258711117227969519854515)
              ·
                refine ⟨25888066675841954279781773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17258711117227969519854515 25888066675841954279781773)
                ·
                  refine ⟨9708025003440732854918165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25888066675841954279781773 9708025003440732854918165)
                  ·
                    refine ⟨455063672036284352574289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9708025003440732854918165 455063672036284352574289)
                    ·
                      rfl

theorem cell23_2658700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_2658700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658700 prefixEnd_2658700 := by exact prefixLift 2658700
  have htrace : WordTrace (prefixWord ++ tailWord_2658700) baseStart_2658700 baseEnd_2658700 := by
    simpa [prefixWord, tailWord_2658700, baseEnd_2658700] using wordTrace_append hprefix tailTrace_2658700
  have hstable : (prefixWord ++ tailWord_2658700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658700).length < 2 ^ (prefixWord ++ tailWord_2658700).sum := by decide
  have hdescent : baseEnd_2658700 < baseStart_2658700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658737 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2658737 : Nat := 118140960795 + 2658737 * 2 ^ 59
def prefixEnd_2658737 : Nat := 4983230072969 + 3 ^ 40 * 2658737 * 2
def baseEnd_2658737 : Nat := 1365210014893069412960197

theorem tailTrace_2658737 : CollatzResearch.WordTrace tailWord_2658737 prefixEnd_2658737 1365210014893069412960197 := by
  unfold tailWord_2658737
  simp only [CollatzResearch.WordTrace]
  refine ⟨96972104968857399973862465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64648069979238266649241643 96972104968857399973862465)
  ·
    refine ⟨72729078726643049980396849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96972104968857399973862465 72729078726643049980396849)
    ·
      refine ⟨54546809044982287485297637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72729078726643049980396849 54546809044982287485297637)
      ·
        refine ⟨10227526695934178903493307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54546809044982287485297637 10227526695934178903493307)
        ·
          refine ⟨15341290043901268355239961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10227526695934178903493307 15341290043901268355239961)
          ·
            refine ⟨11505967532925951266429971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15341290043901268355239961 11505967532925951266429971)
            ·
              refine ⟨17258951299388926899644957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11505967532925951266429971 17258951299388926899644957)
              ·
                refine ⟨6472106737270847587366859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17258951299388926899644957 6472106737270847587366859)
                ·
                  refine ⟨9708160105906271381050289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6472106737270847587366859 9708160105906271381050289)
                  ·
                    refine ⟨7281120079429703535787717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9708160105906271381050289 7281120079429703535787717)
                    ·
                      refine ⟨1365210014893069412960197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7281120079429703535787717 1365210014893069412960197)
                      ·
                        rfl

theorem cell23_2658737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2658737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658737 prefixEnd_2658737 := by exact prefixLift 2658737
  have htrace : WordTrace (prefixWord ++ tailWord_2658737) baseStart_2658737 baseEnd_2658737 := by
    simpa [prefixWord, tailWord_2658737, baseEnd_2658737] using wordTrace_append hprefix tailTrace_2658737
  have hstable : (prefixWord ++ tailWord_2658737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658737).length < 2 ^ (prefixWord ++ tailWord_2658737).sum := by decide
  have hdescent : baseEnd_2658737 < baseStart_2658737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658801 : List Nat := [1, 2, 2, 2, 3, 1, 4, 2, 1, 3, 2]
def baseStart_2658801 : Nat := 118140960795 + 2658801 * 2 ^ 59
def prefixEnd_2658801 : Nat := 4983230072969 + 3 ^ 40 * 2658801 * 2
def baseEnd_2658801 : Nat := 1365242877654957162559903

theorem tailTrace_2658801 : CollatzResearch.WordTrace tailWord_2658801 prefixEnd_2658801 1365242877654957162559903 := by
  unfold tailWord_2658801
  simp only [CollatzResearch.WordTrace]
  refine ⟨96974439240625538904192257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64649626160417025936128171 96974439240625538904192257)
  ·
    refine ⟨72730829430469154178144193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96974439240625538904192257 72730829430469154178144193)
    ·
      refine ⟨54548122072851865633608145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72730829430469154178144193 54548122072851865633608145)
      ·
        refine ⟨40911091554638899225206109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54548122072851865633608145 40911091554638899225206109)
        ·
          refine ⟨15341659332989587209452291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40911091554638899225206109 15341659332989587209452291)
          ·
            refine ⟨23012488999484380814178437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15341659332989587209452291 23012488999484380814178437)
            ·
              refine ⟨4314841687403321402658457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23012488999484380814178437 4314841687403321402658457)
              ·
                refine ⟨3236131265552491051993843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4314841687403321402658457 3236131265552491051993843)
                ·
                  refine ⟨4854196898328736577990765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3236131265552491051993843 4854196898328736577990765)
                  ·
                    refine ⟨1820323836873276216746537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4854196898328736577990765 1820323836873276216746537)
                    ·
                      refine ⟨1365242877654957162559903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1820323836873276216746537 1365242877654957162559903)
                      ·
                        rfl

theorem cell23_2658801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_2658801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658801 prefixEnd_2658801 := by exact prefixLift 2658801
  have htrace : WordTrace (prefixWord ++ tailWord_2658801) baseStart_2658801 baseEnd_2658801 := by
    simpa [prefixWord, tailWord_2658801, baseEnd_2658801] using wordTrace_append hprefix tailTrace_2658801
  have hstable : (prefixWord ++ tailWord_2658801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658801).length < 2 ^ (prefixWord ++ tailWord_2658801).sum := by decide
  have hdescent : baseEnd_2658801 < baseStart_2658801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658817 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_2658817 : Nat := 118140960795 + 2658817 * 2 ^ 59
def prefixEnd_2658817 : Nat := 4983230072969 + 3 ^ 40 * 2658817 * 2
def baseEnd_2658817 : Nat := 1365251093345429099959829

theorem tailTrace_2658817 : CollatzResearch.WordTrace tailWord_2658817 prefixEnd_2658817 1365251093345429099959829 := by
  unfold tailWord_2658817
  simp only [CollatzResearch.WordTrace]
  refine ⟨96975022808567573636774705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64650015205711715757849803 96975022808567573636774705)
  ·
    refine ⟨72731267106425680227581029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96975022808567573636774705 72731267106425680227581029)
    ·
      refine ⟨13637112582454815042671443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72731267106425680227581029 13637112582454815042671443)
      ·
        refine ⟨20455668873682222564007165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13637112582454815042671443 20455668873682222564007165)
        ·
          refine ⟨7670875827630833461502687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20455668873682222564007165 7670875827630833461502687)
          ·
            refine ⟨11506313741446250192254031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7670875827630833461502687 11506313741446250192254031)
            ·
              refine ⟨17259470612169375288381047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11506313741446250192254031 17259470612169375288381047)
              ·
                refine ⟨25889205918254062932571571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17259470612169375288381047 25889205918254062932571571)
                ·
                  refine ⟨38833808877381094398857357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25889205918254062932571571 38833808877381094398857357)
                  ·
                    refine ⟨14562678329017910399571509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38833808877381094398857357 14562678329017910399571509)
                    ·
                      refine ⟨1365251093345429099959829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14562678329017910399571509 1365251093345429099959829)
                      ·
                        rfl

theorem cell23_2658817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_2658817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658817 prefixEnd_2658817 := by exact prefixLift 2658817
  have htrace : WordTrace (prefixWord ++ tailWord_2658817) baseStart_2658817 baseEnd_2658817 := by
    simpa [prefixWord, tailWord_2658817, baseEnd_2658817] using wordTrace_append hprefix tailTrace_2658817
  have hstable : (prefixWord ++ tailWord_2658817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658817).length < 2 ^ (prefixWord ++ tailWord_2658817).sum := by decide
  have hdescent : baseEnd_2658817 < baseStart_2658817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658847 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 3]
def baseStart_2658847 : Nat := 118140960795 + 2658847 * 2 ^ 59
def prefixEnd_2658847 : Nat := 4983230072969 + 3 ^ 40 * 2658847 * 2
def baseEnd_2658847 : Nat := 1365266497765063982584691

theorem tailTrace_2658847 : CollatzResearch.WordTrace tailWord_2658847 prefixEnd_2658847 1365266497765063982584691 := by
  unfold tailWord_2658847
  simp only [CollatzResearch.WordTrace]
  refine ⟨96976116998458888760366795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64650744665639259173577863 96976116998458888760366795)
  ·
    refine ⟨145464175497688333140550193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96976116998458888760366795 145464175497688333140550193)
    ·
      refine ⟨109098131623266249855412645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145464175497688333140550193 109098131623266249855412645)
      ·
        refine ⟨20455899679362421847889871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109098131623266249855412645 20455899679362421847889871)
        ·
          refine ⟨30683849519043632771834807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20455899679362421847889871 30683849519043632771834807)
          ·
            refine ⟨46025774278565449157752211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30683849519043632771834807 46025774278565449157752211)
            ·
              refine ⟨69038661417848173736628317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46025774278565449157752211 69038661417848173736628317)
              ·
                refine ⟨25889498031693065151235619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69038661417848173736628317 25889498031693065151235619)
                ·
                  refine ⟨38834247047539597726853429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25889498031693065151235619 38834247047539597726853429)
                  ·
                    refine ⟨3640710660706837286892509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38834247047539597726853429 3640710660706837286892509)
                    ·
                      refine ⟨1365266497765063982584691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3640710660706837286892509 1365266497765063982584691)
                      ·
                        rfl

theorem cell23_2658847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_2658847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658847 prefixEnd_2658847 := by exact prefixLift 2658847
  have htrace : WordTrace (prefixWord ++ tailWord_2658847) baseStart_2658847 baseEnd_2658847 := by
    simpa [prefixWord, tailWord_2658847, baseEnd_2658847] using wordTrace_append hprefix tailTrace_2658847
  have hstable : (prefixWord ++ tailWord_2658847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658847).length < 2 ^ (prefixWord ++ tailWord_2658847).sum := by decide
  have hdescent : baseEnd_2658847 < baseStart_2658847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658852 : List Nat := [2, 3, 1, 5, 2, 1, 1, 2, 1, 3, 2]
def baseStart_2658852 : Nat := 118140960795 + 2658852 * 2 ^ 59
def prefixEnd_2658852 : Nat := 4983230072969 + 3 ^ 40 * 2658852 * 2
def baseEnd_2658852 : Nat := 1365269065168336463022169

theorem tailTrace_2658852 : CollatzResearch.WordTrace tailWord_2658852 prefixEnd_2658852 1365269065168336463022169 := by
  unfold tailWord_2658852
  simp only [CollatzResearch.WordTrace]
  refine ⟨48488149681720387307149405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64650866242293849742865873 48488149681720387307149405)
  ·
    refine ⟨18183056130645145240181027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48488149681720387307149405 18183056130645145240181027)
    ·
      refine ⟨27274584195967717860271541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18183056130645145240181027 27274584195967717860271541)
      ·
        refine ⟨2556992268371973549400457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27274584195967717860271541 2556992268371973549400457)
        ·
          refine ⟨1917744201278980162050343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2556992268371973549400457 1917744201278980162050343)
          ·
            refine ⟨2876616301918470243075515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917744201278980162050343 2876616301918470243075515)
            ·
              refine ⟨4314924452877705364613273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2876616301918470243075515 4314924452877705364613273)
              ·
                refine ⟨3236193339658279023459955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4314924452877705364613273 3236193339658279023459955)
                ·
                  refine ⟨4854290009487418535189933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3236193339658279023459955 4854290009487418535189933)
                  ·
                    refine ⟨1820358753557781950696225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4854290009487418535189933 1820358753557781950696225)
                    ·
                      refine ⟨1365269065168336463022169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1820358753557781950696225 1365269065168336463022169)
                      ·
                        rfl

theorem cell23_2658852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_2658852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658852 prefixEnd_2658852 := by exact prefixLift 2658852
  have htrace : WordTrace (prefixWord ++ tailWord_2658852) baseStart_2658852 baseEnd_2658852 := by
    simpa [prefixWord, tailWord_2658852, baseEnd_2658852] using wordTrace_append hprefix tailTrace_2658852
  have hstable : (prefixWord ++ tailWord_2658852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658852).length < 2 ^ (prefixWord ++ tailWord_2658852).sum := by decide
  have hdescent : baseEnd_2658852 < baseStart_2658852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658904 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 1, 6, 2]
def baseStart_2658904 : Nat := 118140960795 + 2658904 * 2 ^ 59
def prefixEnd_2658904 : Nat := 4983230072969 + 3 ^ 40 * 2658904 * 2
def baseEnd_2658904 : Nat := 1365295766162370259571929

theorem tailTrace_2658904 : CollatzResearch.WordTrace tailWord_2658904 prefixEnd_2658904 1365295766162370259571929 := by
  unfold tailWord_2658904
  simp only [CollatzResearch.WordTrace]
  refine ⟨48489097979626193747595883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64652130639501591663461177 48489097979626193747595883)
  ·
    refine ⟨72733646969439290621393825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48489097979626193747595883 72733646969439290621393825)
    ·
      refine ⟨54550235227079467966045369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72733646969439290621393825 54550235227079467966045369)
      ·
        refine ⟨40912676420309600974534027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54550235227079467966045369 40912676420309600974534027)
        ·
          refine ⟨61369014630464401461801041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40912676420309600974534027 61369014630464401461801041)
          ·
            refine ⟨46026760972848301096350781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61369014630464401461801041 46026760972848301096350781)
            ·
              refine ⟨17260035364818112911131543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46026760972848301096350781 17260035364818112911131543)
              ·
                refine ⟨25890053047227169366697315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17260035364818112911131543 25890053047227169366697315)
                ·
                  refine ⟨38835079570840754050045973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25890053047227169366697315 38835079570840754050045973)
                  ·
                    refine ⟨1820394354883160346095905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38835079570840754050045973 1820394354883160346095905)
                    ·
                      refine ⟨1365295766162370259571929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1820394354883160346095905 1365295766162370259571929)
                      ·
                        rfl

theorem cell23_2658904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_2658904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658904 prefixEnd_2658904 := by exact prefixLift 2658904
  have htrace : WordTrace (prefixWord ++ tailWord_2658904) baseStart_2658904 baseEnd_2658904 := by
    simpa [prefixWord, tailWord_2658904, baseEnd_2658904] using wordTrace_append hprefix tailTrace_2658904
  have hstable : (prefixWord ++ tailWord_2658904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658904).length < 2 ^ (prefixWord ++ tailWord_2658904).sum := by decide
  have hdescent : baseEnd_2658904 < baseStart_2658904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658944 : List Nat := [2, 1, 1, 2, 1, 5, 3, 2, 6]
def baseStart_2658944 : Nat := 118140960795 + 2658944 * 2 ^ 59
def prefixEnd_2658944 : Nat := 4983230072969 + 3 ^ 40 * 2658944 * 2
def baseEnd_2658944 : Nat := 151701811709838900341305

theorem tailTrace_2658944 : CollatzResearch.WordTrace tailWord_2658944 prefixEnd_2658944 151701811709838900341305 := by
  unfold tailWord_2658944
  simp only [CollatzResearch.WordTrace]
  refine ⟨48489827439553737163323943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64653103252738316217765257 48489827439553737163323943)
  ·
    refine ⟨72734741159330605744985915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48489827439553737163323943 72734741159330605744985915)
    ·
      refine ⟨109102111738995908617478873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72734741159330605744985915 109102111738995908617478873)
      ·
        refine ⟨81826583804246931463109155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109102111738995908617478873 81826583804246931463109155)
        ·
          refine ⟨122739875706370397194663733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81826583804246931463109155 122739875706370397194663733)
          ·
            refine ⟨11506863347472224736999725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122739875706370397194663733 11506863347472224736999725)
            ·
              refine ⟨4315073755302084276374897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11506863347472224736999725 4315073755302084276374897)
              ·
                refine ⟨3236305316476563207281173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4315073755302084276374897 3236305316476563207281173)
                ·
                  refine ⟨151701811709838900341305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3236305316476563207281173 151701811709838900341305)
                  ·
                    rfl

theorem cell23_2658944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 6].length) (baseStart_2658944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658944 prefixEnd_2658944 := by exact prefixLift 2658944
  have htrace : WordTrace (prefixWord ++ tailWord_2658944) baseStart_2658944 baseEnd_2658944 := by
    simpa [prefixWord, tailWord_2658944, baseEnd_2658944] using wordTrace_append hprefix tailTrace_2658944
  have hstable : (prefixWord ++ tailWord_2658944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658944).length < 2 ^ (prefixWord ++ tailWord_2658944).sum := by decide
  have hdescent : baseEnd_2658944 < baseStart_2658944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658947 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 6]
def baseStart_2658947 : Nat := 118140960795 + 2658947 * 2 ^ 59
def prefixEnd_2658947 : Nat := 4983230072969 + 3 ^ 40 * 2658947 * 2
def baseEnd_2658947 : Nat := 1365317845830513591334231

theorem tailTrace_2658947 : CollatzResearch.WordTrace tailWord_2658947 prefixEnd_2658947 1365317845830513591334231 := by
  unfold tailWord_2658947
  simp only [CollatzResearch.WordTrace]
  refine ⟨96979764298096605839007095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64653176198731070559338063 96979764298096605839007095)
  ·
    refine ⟨145469646447144908758510643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96979764298096605839007095 145469646447144908758510643)
    ·
      refine ⟨218204469670717363137765965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145469646447144908758510643 218204469670717363137765965)
      ·
        refine ⟨81826676126519011176662237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218204469670717363137765965 81826676126519011176662237)
        ·
          refine ⟨30685003547444629191248339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81826676126519011176662237 30685003547444629191248339)
          ·
            refine ⟨46027505321166943786872509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30685003547444629191248339 46027505321166943786872509)
            ·
              refine ⟨17260314495437603920077191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46027505321166943786872509 17260314495437603920077191)
              ·
                refine ⟨25890471743156405880115787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17260314495437603920077191 25890471743156405880115787)
                ·
                  refine ⟨38835707614734608820173681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25890471743156405880115787 38835707614734608820173681)
                  ·
                    refine ⟨29126780711050956615130261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38835707614734608820173681 29126780711050956615130261)
                    ·
                      refine ⟨1365317845830513591334231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29126780711050956615130261 1365317845830513591334231)
                      ·
                        rfl

theorem cell23_2658947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_2658947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658947 prefixEnd_2658947 := by exact prefixLift 2658947
  have htrace : WordTrace (prefixWord ++ tailWord_2658947) baseStart_2658947 baseEnd_2658947 := by
    simpa [prefixWord, tailWord_2658947, baseEnd_2658947] using wordTrace_append hprefix tailTrace_2658947
  have hstable : (prefixWord ++ tailWord_2658947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658947).length < 2 ^ (prefixWord ++ tailWord_2658947).sum := by decide
  have hdescent : baseEnd_2658947 < baseStart_2658947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658948 : List Nat := [2, 3, 2, 1, 3, 1, 2, 4, 1, 4]
def baseStart_2658948 : Nat := 118140960795 + 2658948 * 2 ^ 59
def prefixEnd_2658948 : Nat := 4983230072969 + 3 ^ 40 * 2658948 * 2
def baseEnd_2658948 : Nat := 455106119770389362473909

theorem tailTrace_2658948 : CollatzResearch.WordTrace tailWord_2658948 prefixEnd_2658948 455106119770389362473909 := by
  unfold tailWord_2658948
  simp only [CollatzResearch.WordTrace]
  refine ⟨48489900385546491504896749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64653200514061988673195665 48489900385546491504896749)
  ·
    refine ⟨18183712644579934314336281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48489900385546491504896749 18183712644579934314336281)
    ·
      refine ⟨13637784483434950735752211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18183712644579934314336281 13637784483434950735752211)
      ·
        refine ⟨20456676725152426103628317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13637784483434950735752211 20456676725152426103628317)
        ·
          refine ⟨7671253771932159788860619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20456676725152426103628317 7671253771932159788860619)
          ·
            refine ⟨11506880657898239683290929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7671253771932159788860619 11506880657898239683290929)
            ·
              refine ⟨8630160493423679762468197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11506880657898239683290929 8630160493423679762468197)
              ·
                refine ⟨1618155092516939955462787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8630160493423679762468197 1618155092516939955462787)
                ·
                  refine ⟨2427232638775409933194181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1618155092516939955462787 2427232638775409933194181)
                  ·
                    refine ⟨455106119770389362473909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2427232638775409933194181 455106119770389362473909)
                    ·
                      rfl

theorem cell23_2658948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_2658948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658948 prefixEnd_2658948 := by exact prefixLift 2658948
  have htrace : WordTrace (prefixWord ++ tailWord_2658948) baseStart_2658948 baseEnd_2658948 := by
    simpa [prefixWord, tailWord_2658948, baseEnd_2658948] using wordTrace_append hprefix tailTrace_2658948
  have hstable : (prefixWord ++ tailWord_2658948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658948).length < 2 ^ (prefixWord ++ tailWord_2658948).sum := by decide
  have hdescent : baseEnd_2658948 < baseStart_2658948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658981 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 2, 3, 2]
def baseStart_2658981 : Nat := 118140960795 + 2658981 * 2 ^ 59
def prefixEnd_2658981 : Nat := 4983230072969 + 3 ^ 40 * 2658981 * 2
def baseEnd_2658981 : Nat := 1365335304172766458309075

theorem tailTrace_2658981 : CollatzResearch.WordTrace tailWord_2658981 prefixEnd_2658981 1365335304172766458309075 := by
  unfold tailWord_2658981
  simp only [CollatzResearch.WordTrace]
  refine ⟨96981004379973429645744797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64654002919982286430496531 96981004379973429645744797)
  ·
    refine ⟨36367876642490036117154299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96981004379973429645744797 36367876642490036117154299)
    ·
      refine ⟨54551814963735054175731449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36367876642490036117154299 54551814963735054175731449)
      ·
        refine ⟨40913861222801290631798587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54551814963735054175731449 40913861222801290631798587)
        ·
          refine ⟨61370791834201935947697881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40913861222801290631798587 61370791834201935947697881)
          ·
            refine ⟨46028093875651451960773411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61370791834201935947697881 46028093875651451960773411)
            ·
              refine ⟨69042140813477177941160117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46028093875651451960773411 69042140813477177941160117)
              ·
                refine ⟨6472700701263485431983761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69042140813477177941160117 6472700701263485431983761)
                ·
                  refine ⟨4854525525947614073987821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6472700701263485431983761 4854525525947614073987821)
                  ·
                    refine ⟨1820447072230355277745433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4854525525947614073987821 1820447072230355277745433)
                    ·
                      refine ⟨1365335304172766458309075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1820447072230355277745433 1365335304172766458309075)
                      ·
                        rfl

theorem cell23_2658981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_2658981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658981 prefixEnd_2658981 := by exact prefixLift 2658981
  have htrace : WordTrace (prefixWord ++ tailWord_2658981) baseStart_2658981 baseEnd_2658981 := by
    simpa [prefixWord, tailWord_2658981, baseEnd_2658981] using wordTrace_append hprefix tailTrace_2658981
  have hstable : (prefixWord ++ tailWord_2658981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658981).length < 2 ^ (prefixWord ++ tailWord_2658981).sum := by decide
  have hdescent : baseEnd_2658981 < baseStart_2658981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658994 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_2658994 : Nat := 118140960795 + 2658994 * 2 ^ 59
def prefixEnd_2658994 : Nat := 4983230072969 + 3 ^ 40 * 2658994 * 2
def baseEnd_2658994 : Nat := 1365341979421274907446515

theorem tailTrace_2658994 : CollatzResearch.WordTrace tailWord_2658994 prefixEnd_2658994 1365341979421274907446515 := by
  unfold tailWord_2658994
  simp only [CollatzResearch.WordTrace]
  refine ⟨24245369632231583216492009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64654319019284221910645357 24245369632231583216492009)
  ·
    refine ⟨18184027224173687412369007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24245369632231583216492009 18184027224173687412369007)
    ·
      refine ⟨27276040836260531118553511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18184027224173687412369007 27276040836260531118553511)
      ·
        refine ⟨40914061254390796677830267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27276040836260531118553511 40914061254390796677830267)
        ·
          refine ⟨61371091881586195016745401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40914061254390796677830267 61371091881586195016745401)
          ·
            refine ⟨46028318911189646262559051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61371091881586195016745401 46028318911189646262559051)
            ·
              refine ⟨69042478366784469393838577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46028318911189646262559051 69042478366784469393838577)
              ·
                refine ⟨51781858775088352045378933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69042478366784469393838577 51781858775088352045378933)
                ·
                  refine ⟨4854549260164533004254275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51781858775088352045378933 4854549260164533004254275)
                  ·
                    refine ⟨7281823890246799506381413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4854549260164533004254275 7281823890246799506381413)
                    ·
                      refine ⟨1365341979421274907446515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7281823890246799506381413 1365341979421274907446515)
                      ·
                        rfl

theorem cell23_2658994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_2658994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2658994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2658994 prefixEnd_2658994 := by exact prefixLift 2658994
  have htrace : WordTrace (prefixWord ++ tailWord_2658994) baseStart_2658994 baseEnd_2658994 := by
    simpa [prefixWord, tailWord_2658994, baseEnd_2658994] using wordTrace_append hprefix tailTrace_2658994
  have hstable : (prefixWord ++ tailWord_2658994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658994).length < 2 ^ (prefixWord ++ tailWord_2658994).sum := by decide
  have hdescent : baseEnd_2658994 < baseStart_2658994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659028 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2659028 : Nat := 118140960795 + 2659028 * 2 ^ 59
def prefixEnd_2659028 : Nat := 4983230072969 + 3 ^ 40 * 2659028 * 2
def baseEnd_2659028 : Nat := 1365359437763527774421359

theorem tailTrace_2659028 : CollatzResearch.WordTrace tailWord_2659028 prefixEnd_2659028 1365359437763527774421359 := by
  unfold tailWord_2659028
  simp only [CollatzResearch.WordTrace]
  refine ⟨48491359305401578336352869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64655145740535437781803825 48491359305401578336352869)
  ·
    refine ⟨9092129869762795938066163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48491359305401578336352869 9092129869762795938066163)
    ·
      refine ⟨13638194804644193907099245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9092129869762795938066163 13638194804644193907099245)
      ·
        refine ⟨5114323051741572715162217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13638194804644193907099245 5114323051741572715162217)
        ·
          refine ⟨3835742288806179536371663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5114323051741572715162217 3835742288806179536371663)
          ·
            refine ⟨5753613433209269304557495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3835742288806179536371663 5753613433209269304557495)
            ·
              refine ⟨8630420149813903956836243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5753613433209269304557495 8630420149813903956836243)
              ·
                refine ⟨12945630224720855935254365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8630420149813903956836243 12945630224720855935254365)
                ·
                  refine ⟨4854611334270320975720387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12945630224720855935254365 4854611334270320975720387)
                  ·
                    refine ⟨7281917001405481463580581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4854611334270320975720387 7281917001405481463580581)
                    ·
                      refine ⟨1365359437763527774421359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7281917001405481463580581 1365359437763527774421359)
                      ·
                        rfl

theorem cell23_2659028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2659028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659028 prefixEnd_2659028 := by exact prefixLift 2659028
  have htrace : WordTrace (prefixWord ++ tailWord_2659028) baseStart_2659028 baseEnd_2659028 := by
    simpa [prefixWord, tailWord_2659028, baseEnd_2659028] using wordTrace_append hprefix tailTrace_2659028
  have hstable : (prefixWord ++ tailWord_2659028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659028).length < 2 ^ (prefixWord ++ tailWord_2659028).sum := by decide
  have hdescent : baseEnd_2659028 < baseStart_2659028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659031 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 3]
def baseStart_2659031 : Nat := 118140960795 + 2659031 * 2 ^ 59
def prefixEnd_2659031 : Nat := 4983230072969 + 3 ^ 40 * 2659031 * 2
def baseEnd_2659031 : Nat := 1365360978205491262683845

theorem tailTrace_2659031 : CollatzResearch.WordTrace tailWord_2659031 prefixEnd_2659031 1365360978205491262683845 := by
  unfold tailWord_2659031
  simp only [CollatzResearch.WordTrace]
  refine ⟨96982828029792288185064947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64655218686528192123376631 96982828029792288185064947)
  ·
    refine ⟨145474242044688432277597421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96982828029792288185064947 145474242044688432277597421)
    ·
      refine ⟨54552840766758162104099033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145474242044688432277597421 54552840766758162104099033)
      ·
        refine ⟨40914630575068621578074275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54552840766758162104099033 40914630575068621578074275)
        ·
          refine ⟨61371945862602932367111413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40914630575068621578074275 61371945862602932367111413)
          ·
            refine ⟨5753619924619024909416695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61371945862602932367111413 5753619924619024909416695)
            ·
              refine ⟨8630429886928537364125043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5753619924619024909416695 8630429886928537364125043)
              ·
                refine ⟨12945644830392806046187565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8630429886928537364125043 12945644830392806046187565)
                ·
                  refine ⟨4854616811397302267320337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12945644830392806046187565 4854616811397302267320337)
                  ·
                    refine ⟨3640962608547976700490253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4854616811397302267320337 3640962608547976700490253)
                    ·
                      refine ⟨1365360978205491262683845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3640962608547976700490253 1365360978205491262683845)
                      ·
                        rfl

theorem cell23_2659031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_2659031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659031 prefixEnd_2659031 := by exact prefixLift 2659031
  have htrace : WordTrace (prefixWord ++ tailWord_2659031) baseStart_2659031 baseEnd_2659031 := by
    simpa [prefixWord, tailWord_2659031, baseEnd_2659031] using wordTrace_append hprefix tailTrace_2659031
  have hstable : (prefixWord ++ tailWord_2659031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659031).length < 2 ^ (prefixWord ++ tailWord_2659031).sum := by decide
  have hdescent : baseEnd_2659031 < baseStart_2659031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659041 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_2659041 : Nat := 118140960795 + 2659041 * 2 ^ 59
def prefixEnd_2659041 : Nat := 4983230072969 + 3 ^ 40 * 2659041 * 2
def baseEnd_2659041 : Nat := 1365366113012036223558799

theorem tailTrace_2659041 : CollatzResearch.WordTrace tailWord_2659041 prefixEnd_2659041 1365366113012036223558799 := by
  unfold tailWord_2659041
  simp only [CollatzResearch.WordTrace]
  refine ⟨96983192759756059892928977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64655461839837373261952651 96983192759756059892928977)
  ·
    refine ⟨72737394569817044919696733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96983192759756059892928977 72737394569817044919696733)
    ·
      refine ⟨27276522963681391844886275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72737394569817044919696733 27276522963681391844886275)
      ·
        refine ⟨40914784445522087767329413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27276522963681391844886275 40914784445522087767329413)
        ·
          refine ⟨7671522083535391456374265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40914784445522087767329413 7671522083535391456374265)
          ·
            refine ⟨5753641562651543592280699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7671522083535391456374265 5753641562651543592280699)
            ·
              refine ⟨8630462343977315388421049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5753641562651543592280699 8630462343977315388421049)
              ·
                refine ⟨6472846757982986541315787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8630462343977315388421049 6472846757982986541315787)
                ·
                  refine ⟨9709270136974479811973681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6472846757982986541315787 9709270136974479811973681)
                  ·
                    refine ⟨7281952602730859858980261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9709270136974479811973681 7281952602730859858980261)
                    ·
                      refine ⟨1365366113012036223558799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7281952602730859858980261 1365366113012036223558799)
                      ·
                        rfl

theorem cell23_2659041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_2659041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659041 prefixEnd_2659041 := by exact prefixLift 2659041
  have htrace : WordTrace (prefixWord ++ tailWord_2659041) baseStart_2659041 baseEnd_2659041 := by
    simpa [prefixWord, tailWord_2659041, baseEnd_2659041] using wordTrace_append hprefix tailTrace_2659041
  have hstable : (prefixWord ++ tailWord_2659041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659041).length < 2 ^ (prefixWord ++ tailWord_2659041).sum := by decide
  have hdescent : baseEnd_2659041 < baseStart_2659041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659048 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_2659048 : Nat := 118140960795 + 2659048 * 2 ^ 59
def prefixEnd_2659048 : Nat := 4983230072969 + 3 ^ 40 * 2659048 * 2
def baseEnd_2659048 : Nat := 1365369707376617696171267

theorem tailTrace_2659048 : CollatzResearch.WordTrace tailWord_2659048 prefixEnd_2659048 1365369707376617696171267 := by
  unfold tailWord_2659048
  simp only [CollatzResearch.WordTrace]
  refine ⟨48491724035365350044216899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64655632047153800058955865 48491724035365350044216899)
  ·
    refine ⟨72737586053048025066325349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48491724035365350044216899 72737586053048025066325349)
    ·
      refine ⟨13638297384946504699936003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72737586053048025066325349 13638297384946504699936003)
      ·
        refine ⟨20457446077419757049904005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13638297384946504699936003 20457446077419757049904005)
        ·
          refine ⟨3835771139516204446857001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20457446077419757049904005 3835771139516204446857001)
          ·
            refine ⟨2876828354637153335142751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3835771139516204446857001 2876828354637153335142751)
            ·
              refine ⟨4315242531955730002714127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2876828354637153335142751 4315242531955730002714127)
              ·
                refine ⟨6472863797933595004071191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4315242531955730002714127 6472863797933595004071191)
                ·
                  refine ⟨9709295696900392506106787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6472863797933595004071191 9709295696900392506106787)
                  ·
                    refine ⟨14563943545350588759160181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9709295696900392506106787 14563943545350588759160181)
                    ·
                      refine ⟨1365369707376617696171267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14563943545350588759160181 1365369707376617696171267)
                      ·
                        rfl

theorem cell23_2659048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_2659048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659048 prefixEnd_2659048 := by exact prefixLift 2659048
  have htrace : WordTrace (prefixWord ++ tailWord_2659048) baseStart_2659048 baseEnd_2659048 := by
    simpa [prefixWord, tailWord_2659048, baseEnd_2659048] using wordTrace_append hprefix tailTrace_2659048
  have hstable : (prefixWord ++ tailWord_2659048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659048).length < 2 ^ (prefixWord ++ tailWord_2659048).sum := by decide
  have hdescent : baseEnd_2659048 < baseStart_2659048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659062 : List Nat := [5, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2]
def baseStart_2659062 : Nat := 118140960795 + 2659062 * 2 ^ 59
def prefixEnd_2659062 : Nat := 4983230072969 + 3 ^ 40 * 2659062 * 2
def baseEnd_2659062 : Nat := 1365376896105780641396203

theorem tailTrace_2659062 : CollatzResearch.WordTrace tailWord_2659062 prefixEnd_2659062 1365376896105780641396203 := by
  unfold tailWord_2659062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6061497418292498779965215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64655972461786653652962293 6061497418292498779965215)
  ·
    refine ⟨9092246127438748169947823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6061497418292498779965215 9092246127438748169947823)
    ·
      refine ⟨13638369191158122254921735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9092246127438748169947823 13638369191158122254921735)
      ·
        refine ⟨20457553786737183382382603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13638369191158122254921735 20457553786737183382382603)
        ·
          refine ⟨30686330680105775073573905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20457553786737183382382603 30686330680105775073573905)
          ·
            refine ⟨23014748010079331305180429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30686330680105775073573905 23014748010079331305180429)
            ·
              refine ⟨8630530503779749239442661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23014748010079331305180429 8630530503779749239442661)
              ·
                refine ⟨1618224469458702982395499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8630530503779749239442661 1618224469458702982395499)
                ·
                  refine ⟨2427336704188054473593249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1618224469458702982395499 2427336704188054473593249)
                  ·
                    refine ⟨1820502528141040855194937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2427336704188054473593249 1820502528141040855194937)
                    ·
                      refine ⟨1365376896105780641396203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1820502528141040855194937 1365376896105780641396203)
                      ·
                        rfl

theorem cell23_2659062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_2659062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659062 prefixEnd_2659062 := by exact prefixLift 2659062
  have htrace : WordTrace (prefixWord ++ tailWord_2659062) baseStart_2659062 baseEnd_2659062 := by
    simpa [prefixWord, tailWord_2659062, baseEnd_2659062] using wordTrace_append hprefix tailTrace_2659062
  have hstable : (prefixWord ++ tailWord_2659062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659062).length < 2 ^ (prefixWord ++ tailWord_2659062).sum := by decide
  have hdescent : baseEnd_2659062 < baseStart_2659062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659084 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 4, 3, 4]
def baseStart_2659084 : Nat := 118140960795 + 2659084 * 2 ^ 59
def prefixEnd_2659084 : Nat := 4983230072969 + 3 ^ 40 * 2659084 * 2
def baseEnd_2659084 : Nat := 1365388192680179555321101

theorem tailTrace_2659084 : CollatzResearch.WordTrace tailWord_2659084 prefixEnd_2659084 1365388192680179555321101 := by
  unfold tailWord_2659084
  simp only [CollatzResearch.WordTrace]
  refine ⟨48492380549300139118372153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64656507399066852157829537 48492380549300139118372153)
  ·
    refine ⟨36369285411975104338779115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48492380549300139118372153 36369285411975104338779115)
    ·
      refine ⟨54553928117962656508168673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36369285411975104338779115 54553928117962656508168673)
      ·
        refine ⟨40915446088471992381126505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54553928117962656508168673 40915446088471992381126505)
        ·
          refine ⟨30686584566353994285844879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40915446088471992381126505 30686584566353994285844879)
          ·
            refine ⟨46029876849530991428767319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30686584566353994285844879 46029876849530991428767319)
            ·
              refine ⟨69044815274296487143150979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46029876849530991428767319 69044815274296487143150979)
              ·
                refine ⟨103567222911444730714726469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69044815274296487143150979 103567222911444730714726469)
                ·
                  refine ⟨19418854295895887009011213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103567222911444730714726469 19418854295895887009011213)
                  ·
                    refine ⟨7282070360960957628379205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19418854295895887009011213 7282070360960957628379205)
                    ·
                      refine ⟨1365388192680179555321101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7282070360960957628379205 1365388192680179555321101)
                      ·
                        rfl

theorem cell23_2659084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_2659084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659084 prefixEnd_2659084 := by exact prefixLift 2659084
  have htrace : WordTrace (prefixWord ++ tailWord_2659084) baseStart_2659084 baseEnd_2659084 := by
    simpa [prefixWord, tailWord_2659084, baseEnd_2659084] using wordTrace_append hprefix tailTrace_2659084
  have hstable : (prefixWord ++ tailWord_2659084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659084).length < 2 ^ (prefixWord ++ tailWord_2659084).sum := by decide
  have hdescent : baseEnd_2659084 < baseStart_2659084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659135 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 1, 4, 2]
def baseStart_2659135 : Nat := 118140960795 + 2659135 * 2 ^ 59
def prefixEnd_2659135 : Nat := 4983230072969 + 3 ^ 40 * 2659135 * 2
def baseEnd_2659135 : Nat := 1365414380193558855783367

theorem tailTrace_2659135 : CollatzResearch.WordTrace tailWord_2659135 prefixEnd_2659135 1365414380193558855783367 := by
  unfold tailWord_2659135
  simp only [CollatzResearch.WordTrace]
  refine ⟨96986621221415513946850859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64657747480943675964567239 96986621221415513946850859)
  ·
    refine ⟨145479931832123270920276289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96986621221415513946850859 145479931832123270920276289)
    ·
      refine ⟨109109948874092453190207217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145479931832123270920276289 109109948874092453190207217)
      ·
        refine ⟨81832461655569339892655413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109109948874092453190207217 81832461655569339892655413)
        ·
          refine ⟨7671793280209625614936445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81832461655569339892655413 7671793280209625614936445)
          ·
            refine ⟨2876922480078609605601167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7671793280209625614936445 2876922480078609605601167)
            ·
              refine ⟨4315383720117914408401751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2876922480078609605601167 4315383720117914408401751)
              ·
                refine ⟨6473075580176871612602627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4315383720117914408401751 6473075580176871612602627)
                ·
                  refine ⟨9709613370265307418903941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6473075580176871612602627 9709613370265307418903941)
                  ·
                    refine ⟨1820552506924745141044489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9709613370265307418903941 1820552506924745141044489)
                    ·
                      refine ⟨1365414380193558855783367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1820552506924745141044489 1365414380193558855783367)
                      ·
                        rfl

theorem cell23_2659135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 4, 2].length) (baseStart_2659135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659135 prefixEnd_2659135 := by exact prefixLift 2659135
  have htrace : WordTrace (prefixWord ++ tailWord_2659135) baseStart_2659135 baseEnd_2659135 := by
    simpa [prefixWord, tailWord_2659135, baseEnd_2659135] using wordTrace_append hprefix tailTrace_2659135
  have hstable : (prefixWord ++ tailWord_2659135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659135).length < 2 ^ (prefixWord ++ tailWord_2659135).sum := by decide
  have hdescent : baseEnd_2659135 < baseStart_2659135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659171 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 4, 5]
def baseStart_2659171 : Nat := 118140960795 + 2659171 * 2 ^ 59
def prefixEnd_2659171 : Nat := 4983230072969 + 3 ^ 40 * 2659171 * 2
def baseEnd_2659171 : Nat := 455144288499040238311067

theorem tailTrace_2659171 : CollatzResearch.WordTrace tailWord_2659171 prefixEnd_2659171 455144288499040238311067 := by
  unfold tailWord_2659171
  simp only [CollatzResearch.WordTrace]
  refine ⟨96987934249285092095161367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64658622832856728063440911 96987934249285092095161367)
  ·
    refine ⟨145481901373927638142742051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96987934249285092095161367 145481901373927638142742051)
    ·
      refine ⟨218222852060891457214113077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145481901373927638142742051 218222852060891457214113077)
      ·
        refine ⟨20458392380708574113823101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 218222852060891457214113077 20458392380708574113823101)
        ·
          refine ⟨7671897142765715292683663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20458392380708574113823101 7671897142765715292683663)
          ·
            refine ⟨11507845714148572939025495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7671897142765715292683663 11507845714148572939025495)
            ·
              refine ⟨17261768571222859408538243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11507845714148572939025495 17261768571222859408538243)
              ·
                refine ⟨25892652856834289112807365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17261768571222859408538243 25892652856834289112807365)
                ·
                  refine ⟨4854872410656429208651381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25892652856834289112807365 4854872410656429208651381)
                  ·
                    refine ⟨455144288499040238311067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4854872410656429208651381 455144288499040238311067)
                    ·
                      rfl

theorem cell23_2659171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 5].length) (baseStart_2659171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659171 prefixEnd_2659171 := by exact prefixLift 2659171
  have htrace : WordTrace (prefixWord ++ tailWord_2659171) baseStart_2659171 baseEnd_2659171 := by
    simpa [prefixWord, tailWord_2659171, baseEnd_2659171] using wordTrace_append hprefix tailTrace_2659171
  have hstable : (prefixWord ++ tailWord_2659171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659171).length < 2 ^ (prefixWord ++ tailWord_2659171).sum := by decide
  have hdescent : baseEnd_2659171 < baseStart_2659171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659175 : List Nat := [1, 1, 5, 1, 2, 3, 3, 2, 5]
def baseStart_2659175 : Nat := 118140960795 + 2659175 * 2 ^ 59
def prefixEnd_2659175 : Nat := 4983230072969 + 3 ^ 40 * 2659175 * 2
def baseEnd_2659175 : Nat := 151714991046637633253687

theorem tailTrace_2659175 : CollatzResearch.WordTrace tailWord_2659175 prefixEnd_2659175 151714991046637633253687 := by
  unfold tailWord_2659175
  simp only [CollatzResearch.WordTrace]
  refine ⟨96988080141270600778306979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64658720094180400518871319 96988080141270600778306979)
  ·
    refine ⟨145482120211905901167460469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96988080141270600778306979 145482120211905901167460469)
    ·
      refine ⟨13638948769866178234449419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145482120211905901167460469 13638948769866178234449419)
      ·
        refine ⟨20458423154799267351674129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13638948769866178234449419 20458423154799267351674129)
        ·
          refine ⟨15343817366099450513755597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20458423154799267351674129 15343817366099450513755597)
          ·
            refine ⟨5753931512287293942658349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15343817366099450513755597 5753931512287293942658349)
            ·
              refine ⟨2157724317107735228496881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5753931512287293942658349 2157724317107735228496881)
              ·
                refine ⟨1618293237830801421372661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2157724317107735228496881 1618293237830801421372661)
                ·
                  refine ⟨151714991046637633253687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1618293237830801421372661 151714991046637633253687)
                  ·
                    rfl

theorem cell23_2659175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 5].length) (baseStart_2659175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659175 prefixEnd_2659175 := by exact prefixLift 2659175
  have htrace : WordTrace (prefixWord ++ tailWord_2659175) baseStart_2659175 baseEnd_2659175 := by
    simpa [prefixWord, tailWord_2659175, baseEnd_2659175] using wordTrace_append hprefix tailTrace_2659175
  have hstable : (prefixWord ++ tailWord_2659175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659175).length < 2 ^ (prefixWord ++ tailWord_2659175).sum := by decide
  have hdescent : baseEnd_2659175 < baseStart_2659175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659208 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2659208 : Nat := 118140960795 + 2659208 * 2 ^ 59
def prefixEnd_2659208 : Nat := 4983230072969 + 3 ^ 40 * 2659208 * 2
def baseEnd_2659208 : Nat := 1365451864281337070170531

theorem tailTrace_2659208 : CollatzResearch.WordTrace tailWord_2659208 prefixEnd_2659208 1365451864281337070170531 := by
  unfold tailWord_2659208
  simp only [CollatzResearch.WordTrace]
  refine ⟨48494641875075523707129139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64659522500100698276172185 48494641875075523707129139)
  ·
    refine ⟨72741962812613285560693709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48494641875075523707129139 72741962812613285560693709)
    ·
      refine ⟨27278236054729982085260141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72741962812613285560693709 27278236054729982085260141)
      ·
        refine ⟨10229338520523743281972553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27278236054729982085260141 10229338520523743281972553)
        ·
          refine ⟨7672003890392807461479415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10229338520523743281972553 7672003890392807461479415)
          ·
            refine ⟨11508005835589211192219123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7672003890392807461479415 11508005835589211192219123)
            ·
              refine ⟨17262008753383816788328685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11508005835589211192219123 17262008753383816788328685)
              ·
                refine ⟨6473253282518931295623257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17262008753383816788328685 6473253282518931295623257)
                ·
                  refine ⟨4854939961889198471717443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6473253282518931295623257 4854939961889198471717443)
                  ·
                    refine ⟨7282409942833797707576165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4854939961889198471717443 7282409942833797707576165)
                    ·
                      refine ⟨1365451864281337070170531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7282409942833797707576165 1365451864281337070170531)
                      ·
                        rfl

theorem cell23_2659208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2659208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659208 prefixEnd_2659208 := by exact prefixLift 2659208
  have htrace : WordTrace (prefixWord ++ tailWord_2659208) baseStart_2659208 baseEnd_2659208 := by
    simpa [prefixWord, tailWord_2659208, baseEnd_2659208] using wordTrace_append hprefix tailTrace_2659208
  have hstable : (prefixWord ++ tailWord_2659208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659208).length < 2 ^ (prefixWord ++ tailWord_2659208).sum := by decide
  have hdescent : baseEnd_2659208 < baseStart_2659208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659211 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 3]
def baseStart_2659211 : Nat := 118140960795 + 2659211 * 2 ^ 59
def prefixEnd_2659211 : Nat := 4983230072969 + 3 ^ 40 * 2659211 * 2
def baseEnd_2659211 : Nat := 1365453404723300558433017

theorem tailTrace_2659211 : CollatzResearch.WordTrace tailWord_2659211 prefixEnd_2659211 1365453404723300558433017 := by
  unfold tailWord_2659211
  simp only [CollatzResearch.WordTrace]
  refine ⟨96989393169140178926617487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64659595446093452617744991 96989393169140178926617487)
  ·
    refine ⟨145484089753710268389926231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96989393169140178926617487 145484089753710268389926231)
    ·
      refine ⟨218226134630565402584889347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145484089753710268389926231 218226134630565402584889347)
      ·
        refine ⟨327339201945848103877334021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218226134630565402584889347 327339201945848103877334021)
        ·
          refine ⟨61376100364846519477000129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 327339201945848103877334021 61376100364846519477000129)
          ·
            refine ⟨46032075273634889607750097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61376100364846519477000129 46032075273634889607750097)
            ·
              refine ⟨34524056455226167205812573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46032075273634889607750097 34524056455226167205812573)
              ·
                refine ⟨12946521170709812702179715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34524056455226167205812573 12946521170709812702179715)
                ·
                  refine ⟨19419781756064719053269573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12946521170709812702179715 19419781756064719053269573)
                  ·
                    refine ⟨3641209079262134822488045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19419781756064719053269573 3641209079262134822488045)
                    ·
                      refine ⟨1365453404723300558433017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3641209079262134822488045 1365453404723300558433017)
                      ·
                        rfl

theorem cell23_2659211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 3].length) (baseStart_2659211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659211 prefixEnd_2659211 := by exact prefixLift 2659211
  have htrace : WordTrace (prefixWord ++ tailWord_2659211) baseStart_2659211 baseEnd_2659211 := by
    simpa [prefixWord, tailWord_2659211, baseEnd_2659211] using wordTrace_append hprefix tailTrace_2659211
  have hstable : (prefixWord ++ tailWord_2659211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659211).length < 2 ^ (prefixWord ++ tailWord_2659211).sum := by decide
  have hdescent : baseEnd_2659211 < baseStart_2659211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659222 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2659222 : Nat := 118140960795 + 2659222 * 2 ^ 59
def prefixEnd_2659222 : Nat := 4983230072969 + 3 ^ 40 * 2659222 * 2
def baseEnd_2659222 : Nat := 455153017670166671798489

theorem tailTrace_2659222 : CollatzResearch.WordTrace tailWord_2659222 prefixEnd_2659222 455153017670166671798489 := by
  unfold tailWord_2659222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6061862148256270487829245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64659862914733551870178613 6061862148256270487829245)
  ·
    refine ⟨2273198305596101432935967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6061862148256270487829245 2273198305596101432935967)
    ·
      refine ⟨3409797458394152149403951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2273198305596101432935967 3409797458394152149403951)
      ·
        refine ⟨5114696187591228224105927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3409797458394152149403951 5114696187591228224105927)
        ·
          refine ⟨7672044281386842336158891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5114696187591228224105927 7672044281386842336158891)
          ·
            refine ⟨11508066422080263504238337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7672044281386842336158891 11508066422080263504238337)
            ·
              refine ⟨8631049816560197628178753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11508066422080263504238337 8631049816560197628178753)
              ·
                refine ⟨6473287362420148221134065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8631049816560197628178753 6473287362420148221134065)
                ·
                  refine ⟨4854965521815111165850549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6473287362420148221134065 4854965521815111165850549)
                  ·
                    refine ⟨455153017670166671798489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4854965521815111165850549 455153017670166671798489)
                    ·
                      rfl

theorem cell23_2659222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2659222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659222 prefixEnd_2659222 := by exact prefixLift 2659222
  have htrace : WordTrace (prefixWord ++ tailWord_2659222) baseStart_2659222 baseEnd_2659222 := by
    simpa [prefixWord, tailWord_2659222, baseEnd_2659222] using wordTrace_append hprefix tailTrace_2659222
  have hstable : (prefixWord ++ tailWord_2659222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659222).length < 2 ^ (prefixWord ++ tailWord_2659222).sum := by decide
  have hdescent : baseEnd_2659222 < baseStart_2659222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659252 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_2659252 : Nat := 118140960795 + 2659252 * 2 ^ 59
def prefixEnd_2659252 : Nat := 4983230072969 + 3 ^ 40 * 2659252 * 2
def baseEnd_2659252 : Nat := 455158152476711632673443

theorem tailTrace_2659252 : CollatzResearch.WordTrace tailWord_2659252 prefixEnd_2659252 455158152476711632673443 := by
  unfold tailWord_2659252
  simp only [CollatzResearch.WordTrace]
  refine ⟨48495444280995821464430005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64660592374661095285906673 48495444280995821464430005)
  ·
    refine ⟨4546447901343358262290313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48495444280995821464430005 4546447901343358262290313)
    ·
      refine ⟨3409835926007518696717735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4546447901343358262290313 3409835926007518696717735)
      ·
        refine ⟨5114753889011278045076603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3409835926007518696717735 5114753889011278045076603)
        ·
          refine ⟨7672130833516917067614905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5114753889011278045076603 7672130833516917067614905)
          ·
            refine ⟨5754098125137687800711179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7672130833516917067614905 5754098125137687800711179)
            ·
              refine ⟨8631147187706531701066769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5754098125137687800711179 8631147187706531701066769)
              ·
                refine ⟨6473360390779898775800077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8631147187706531701066769 6473360390779898775800077)
                ·
                  refine ⟨2427510146542462040925029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6473360390779898775800077 2427510146542462040925029)
                  ·
                    refine ⟨455158152476711632673443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2427510146542462040925029 455158152476711632673443)
                    ·
                      rfl

theorem cell23_2659252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_2659252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659252 prefixEnd_2659252 := by exact prefixLift 2659252
  have htrace : WordTrace (prefixWord ++ tailWord_2659252) baseStart_2659252 baseEnd_2659252 := by
    simpa [prefixWord, tailWord_2659252, baseEnd_2659252] using wordTrace_append hprefix tailTrace_2659252
  have hstable : (prefixWord ++ tailWord_2659252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659252).length < 2 ^ (prefixWord ++ tailWord_2659252).sum := by decide
  have hdescent : baseEnd_2659252 < baseStart_2659252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659321 : List Nat := [1, 2, 1, 3, 1, 3, 3, 9]
def baseStart_2659321 : Nat := 118140960795 + 2659321 * 2 ^ 59
def prefixEnd_2659321 : Nat := 4983230072969 + 3 ^ 40 * 2659321 * 2
def baseEnd_2659321 : Nat := 50574440281307226965093

theorem tailTrace_2659321 : CollatzResearch.WordTrace tailWord_2659321 prefixEnd_2659321 50574440281307226965093 := by
  unfold tailWord_2659321
  simp only [CollatzResearch.WordTrace]
  refine ⟨96993405198741667713121817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64662270132494445142081211 96993405198741667713121817)
  ·
    refine ⟨72745053899056250784841363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96993405198741667713121817 72745053899056250784841363)
    ·
      refine ⟨109117580848584376177262045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72745053899056250784841363 109117580848584376177262045)
      ·
        refine ⟨40919092818219141066473267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109117580848584376177262045 40919092818219141066473267)
        ·
          refine ⟨61378639227328711599709901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40919092818219141066473267 61378639227328711599709901)
          ·
            refine ⟨23016989710248266849891213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61378639227328711599709901 23016989710248266849891213)
            ·
              refine ⟨8631371141343100068709205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23016989710248266849891213 8631371141343100068709205)
              ·
                refine ⟨50574440281307226965093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8631371141343100068709205 50574440281307226965093)
                ·
                  rfl

theorem cell23_2659321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 9].length) (baseStart_2659321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659321 prefixEnd_2659321 := by exact prefixLift 2659321
  have htrace : WordTrace (prefixWord ++ tailWord_2659321) baseStart_2659321 baseEnd_2659321 := by
    simpa [prefixWord, tailWord_2659321, baseEnd_2659321] using wordTrace_append hprefix tailTrace_2659321
  have hstable : (prefixWord ++ tailWord_2659321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659321).length < 2 ^ (prefixWord ++ tailWord_2659321).sum := by decide
  have hdescent : baseEnd_2659321 < baseStart_2659321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659335 : List Nat := [1, 1, 4, 3, 1, 1, 1, 5, 1, 2, 3]
def baseStart_2659335 : Nat := 118140960795 + 2659335 * 2 ^ 59
def prefixEnd_2659335 : Nat := 4983230072969 + 3 ^ 40 * 2659335 * 2
def baseEnd_2659335 : Nat := 1365517076324458073282447

theorem tailTrace_2659335 : CollatzResearch.WordTrace tailWord_2659335 prefixEnd_2659335 1365517076324458073282447 := by
  unfold tailWord_2659335
  simp only [CollatzResearch.WordTrace]
  refine ⟨96993915820690948104131459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64662610547127298736087639 96993915820690948104131459)
  ·
    refine ⟨145490873731036422156197189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96993915820690948104131459 145490873731036422156197189)
    ·
      refine ⟨27279538824569329154286973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145490873731036422156197189 27279538824569329154286973)
      ·
        refine ⟨10229827059213498432857615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27279538824569329154286973 10229827059213498432857615)
        ·
          refine ⟨15344740588820247649286423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10229827059213498432857615 15344740588820247649286423)
          ·
            refine ⟨23017110883230371473929635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15344740588820247649286423 23017110883230371473929635)
            ·
              refine ⟨34525666324845557210894453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23017110883230371473929635 34525666324845557210894453)
              ·
                refine ⟨3236781217954270988521355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34525666324845557210894453 3236781217954270988521355)
                ·
                  refine ⟨4855171826931406482782033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3236781217954270988521355 4855171826931406482782033)
                  ·
                    refine ⟨3641378870198554862086525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4855171826931406482782033 3641378870198554862086525)
                    ·
                      refine ⟨1365517076324458073282447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3641378870198554862086525 1365517076324458073282447)
                      ·
                        rfl

theorem cell23_2659335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_2659335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659335 prefixEnd_2659335 := by exact prefixLift 2659335
  have htrace : WordTrace (prefixWord ++ tailWord_2659335) baseStart_2659335 baseEnd_2659335 := by
    simpa [prefixWord, tailWord_2659335, baseEnd_2659335] using wordTrace_append hprefix tailTrace_2659335
  have hstable : (prefixWord ++ tailWord_2659335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659335).length < 2 ^ (prefixWord ++ tailWord_2659335).sum := by decide
  have hdescent : baseEnd_2659335 < baseStart_2659335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659338 : List Nat := [3, 1, 2, 2, 3, 3, 9]
def baseStart_2659338 : Nat := 118140960795 + 2659338 * 2 ^ 59
def prefixEnd_2659338 : Nat := 4983230072969 + 3 ^ 40 * 2659338 * 2
def baseEnd_2659338 : Nat := 16858254527980513105493

theorem tailTrace_2659338 : CollatzResearch.WordTrace tailWord_2659338 prefixEnd_2659338 16858254527980513105493 := by
  unfold tailWord_2659338
  simp only [CollatzResearch.WordTrace]
  refine ⟨24248506309920019904122667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64662683493120053077660445 24248506309920019904122667)
  ·
    refine ⟨36372759464880029856184001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24248506309920019904122667 36372759464880029856184001)
    ·
      refine ⟨27279569598660022392138001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36372759464880029856184001 27279569598660022392138001)
      ·
        refine ⟨20459677198995016794103501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27279569598660022392138001 20459677198995016794103501)
        ·
          refine ⟨7672378949623131297788813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20459677198995016794103501 7672378949623131297788813)
          ·
            refine ⟨2877142106108674236670805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7672378949623131297788813 2877142106108674236670805)
            ·
              refine ⟨16858254527980513105493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2877142106108674236670805 16858254527980513105493)
              ·
                rfl

theorem cell23_2659338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 9].length) (baseStart_2659338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659338 prefixEnd_2659338 := by exact prefixLift 2659338
  have htrace : WordTrace (prefixWord ++ tailWord_2659338) baseStart_2659338 baseEnd_2659338 := by
    simpa [prefixWord, tailWord_2659338, baseEnd_2659338] using wordTrace_append hprefix tailTrace_2659338
  have hstable : (prefixWord ++ tailWord_2659338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659338).length < 2 ^ (prefixWord ++ tailWord_2659338).sum := by decide
  have hdescent : baseEnd_2659338 < baseStart_2659338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659349 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 3, 2, 2]
def baseStart_2659349 : Nat := 118140960795 + 2659349 * 2 ^ 59
def prefixEnd_2659349 : Nat := 4983230072969 + 3 ^ 40 * 2659349 * 2
def baseEnd_2659349 : Nat := 1365524265053621018507383

theorem tailTrace_2659349 : CollatzResearch.WordTrace tailWord_2659349 prefixEnd_2659349 1365524265053621018507383 := by
  unfold tailWord_2659349
  simp only [CollatzResearch.WordTrace]
  refine ⟨96994426442640228495141101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64662950961760152330094067 96994426442640228495141101)
  ·
    refine ⟨36372909915990085685677913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96994426442640228495141101 36372909915990085685677913)
    ·
      refine ⟨27279682436992564264258435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36372909915990085685677913 27279682436992564264258435)
      ·
        refine ⟨40919523655488846396387653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27279682436992564264258435 40919523655488846396387653)
        ·
          refine ⟨7672410685404158699322685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40919523655488846396387653 7672410685404158699322685)
          ·
            refine ⟨2877154007026559512246007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7672410685404158699322685 2877154007026559512246007)
            ·
              refine ⟨4315731010539839268369011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2877154007026559512246007 4315731010539839268369011)
              ·
                refine ⟨6473596515809758902553517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4315731010539839268369011 6473596515809758902553517)
                ·
                  refine ⟨2427598693428659588457569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6473596515809758902553517 2427598693428659588457569)
                  ·
                    refine ⟨1820699020071494691343177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2427598693428659588457569 1820699020071494691343177)
                    ·
                      refine ⟨1365524265053621018507383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1820699020071494691343177 1365524265053621018507383)
                      ·
                        rfl

theorem cell23_2659349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_2659349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659349 prefixEnd_2659349 := by exact prefixLift 2659349
  have htrace : WordTrace (prefixWord ++ tailWord_2659349) baseStart_2659349 baseEnd_2659349 := by
    simpa [prefixWord, tailWord_2659349, baseEnd_2659349] using wordTrace_append hprefix tailTrace_2659349
  have hstable : (prefixWord ++ tailWord_2659349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659349).length < 2 ^ (prefixWord ++ tailWord_2659349).sum := by decide
  have hdescent : baseEnd_2659349 < baseStart_2659349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659382 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_2659382 : Nat := 118140960795 + 2659382 * 2 ^ 59
def prefixEnd_2659382 : Nat := 4983230072969 + 3 ^ 40 * 2659382 * 2
def baseEnd_2659382 : Nat := 1365541209915219389394731

theorem tailTrace_2659382 : CollatzResearch.WordTrace tailWord_2659382 prefixEnd_2659382 1365541209915219389394731 := by
  unfold tailWord_2659382
  simp only [CollatzResearch.WordTrace]
  refine ⟨6062226878220042195693275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64663753367680450087394933 6062226878220042195693275)
  ·
    refine ⟨9093340317330063293539913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6062226878220042195693275 9093340317330063293539913)
    ·
      refine ⟨6820005237997547470154935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9093340317330063293539913 6820005237997547470154935)
      ·
        refine ⟨10230007856996321205232403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6820005237997547470154935 10230007856996321205232403)
        ·
          refine ⟨15345011785494481807848605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10230007856996321205232403 15345011785494481807848605)
          ·
            refine ⟨5754379419560430677943227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15345011785494481807848605 5754379419560430677943227)
            ·
              refine ⟨8631569129340646016914841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5754379419560430677943227 8631569129340646016914841)
              ·
                refine ⟨6473676847005484512686131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8631569129340646016914841 6473676847005484512686131)
                ·
                  refine ⟨9710515270508226769029197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6473676847005484512686131 9710515270508226769029197)
                  ·
                    refine ⟨3641443226440585038385949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9710515270508226769029197 3641443226440585038385949)
                    ·
                      refine ⟨1365541209915219389394731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3641443226440585038385949 1365541209915219389394731)
                      ·
                        rfl

theorem cell23_2659382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_2659382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659382 prefixEnd_2659382 := by exact prefixLift 2659382
  have htrace : WordTrace (prefixWord ++ tailWord_2659382) baseStart_2659382 baseEnd_2659382 := by
    simpa [prefixWord, tailWord_2659382, baseEnd_2659382] using wordTrace_append hprefix tailTrace_2659382
  have hstable : (prefixWord ++ tailWord_2659382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659382).length < 2 ^ (prefixWord ++ tailWord_2659382).sum := by decide
  have hdescent : baseEnd_2659382 < baseStart_2659382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659405 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2659405 : Nat := 118140960795 + 2659405 * 2 ^ 59
def prefixEnd_2659405 : Nat := 4983230072969 + 3 ^ 40 * 2659405 * 2
def baseEnd_2659405 : Nat := 1365553019970272799407125

theorem tailTrace_2659405 : CollatzResearch.WordTrace tailWord_2659405 prefixEnd_2659405 1365553019970272799407125 := by
  unfold tailWord_2659405
  simp only [CollatzResearch.WordTrace]
  refine ⟨96996468930437350059179669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64664312620291566706119779 96996468930437350059179669)
  ·
    refine ⟨4546709481114250784024047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96996468930437350059179669 4546709481114250784024047)
    ·
      refine ⟨6820064221671376176036071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4546709481114250784024047 6820064221671376176036071)
      ·
        refine ⟨10230096332507064264054107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6820064221671376176036071 10230096332507064264054107)
        ·
          refine ⟨15345144498760596396081161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10230096332507064264054107 15345144498760596396081161)
          ·
            refine ⟨11508858374070447297060871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15345144498760596396081161 11508858374070447297060871)
            ·
              refine ⟨17263287561105670945591307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11508858374070447297060871 17263287561105670945591307)
              ·
                refine ⟨25894931341658506418386961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17263287561105670945591307 25894931341658506418386961)
                ·
                  refine ⟨19421198506243879813790221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25894931341658506418386961 19421198506243879813790221)
                  ·
                    refine ⟨7282949439841454930171333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19421198506243879813790221 7282949439841454930171333)
                    ·
                      refine ⟨1365553019970272799407125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7282949439841454930171333 1365553019970272799407125)
                      ·
                        rfl

theorem cell23_2659405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2659405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659405 prefixEnd_2659405 := by exact prefixLift 2659405
  have htrace : WordTrace (prefixWord ++ tailWord_2659405) baseStart_2659405 baseEnd_2659405 := by
    simpa [prefixWord, tailWord_2659405, baseEnd_2659405] using wordTrace_append hprefix tailTrace_2659405
  have hstable : (prefixWord ++ tailWord_2659405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659405).length < 2 ^ (prefixWord ++ tailWord_2659405).sum := by decide
  have hdescent : baseEnd_2659405 < baseStart_2659405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659468 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 1, 2, 5]
def baseStart_2659468 : Nat := 118140960795 + 2659468 * 2 ^ 59
def prefixEnd_2659468 : Nat := 4983230072969 + 3 ^ 40 * 2659468 * 2
def baseEnd_2659468 : Nat := 1365585369251506052919335

theorem tailTrace_2659468 : CollatzResearch.WordTrace tailWord_2659468 prefixEnd_2659468 1365585369251506052919335 := by
  unfold tailWord_2659468
  simp only [CollatzResearch.WordTrace]
  refine ⟨48499383364604555909361529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64665844486139407879148705 48499383364604555909361529)
  ·
    refine ⟨36374537523453416932021147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48499383364604555909361529 36374537523453416932021147)
    ·
      refine ⟨54561806285180125398031721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36374537523453416932021147 54561806285180125398031721)
      ·
        refine ⟨40921354713885094048523791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54561806285180125398031721 40921354713885094048523791)
        ·
          refine ⟨61382032070827641072785687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40921354713885094048523791 61382032070827641072785687)
          ·
            refine ⟨92073048106241461609178531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61382032070827641072785687 92073048106241461609178531)
            ·
              refine ⟨138109572159362192413767797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92073048106241461609178531 138109572159362192413767797)
              ·
                refine ⟨12947772389940205538790731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138109572159362192413767797 12947772389940205538790731)
                ·
                  refine ⟨19421658584910308308186097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12947772389940205538790731 19421658584910308308186097)
                  ·
                    refine ⟨14566243938682731231139573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19421658584910308308186097 14566243938682731231139573)
                    ·
                      refine ⟨1365585369251506052919335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14566243938682731231139573 1365585369251506052919335)
                      ·
                        rfl

theorem cell23_2659468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_2659468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659468 prefixEnd_2659468 := by exact prefixLift 2659468
  have htrace : WordTrace (prefixWord ++ tailWord_2659468) baseStart_2659468 baseEnd_2659468 := by
    simpa [prefixWord, tailWord_2659468, baseEnd_2659468] using wordTrace_append hprefix tailTrace_2659468
  have hstable : (prefixWord ++ tailWord_2659468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659468).length < 2 ^ (prefixWord ++ tailWord_2659468).sum := by decide
  have hdescent : baseEnd_2659468 < baseStart_2659468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659488 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 2, 8]
def baseStart_2659488 : Nat := 118140960795 + 2659488 * 2 ^ 59
def prefixEnd_2659488 : Nat := 4983230072969 + 3 ^ 40 * 2659488 * 2
def baseEnd_2659488 : Nat := 455198546288198658223081

theorem tailTrace_2659488 : CollatzResearch.WordTrace tailWord_2659488 prefixEnd_2659488 455198546288198658223081 := by
  unfold tailWord_2659488
  simp only [CollatzResearch.WordTrace]
  refine ⟨48499748094568327617225559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64666330792757770156300745 48499748094568327617225559)
  ·
    refine ⟨72749622141852491425838339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48499748094568327617225559 72749622141852491425838339)
    ·
      refine ⟨109124433212778737138757509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72749622141852491425838339 109124433212778737138757509)
      ·
        refine ⟨20460831227396013213517033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109124433212778737138757509 20460831227396013213517033)
        ·
          refine ⟨15345623420547009910137775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20460831227396013213517033 15345623420547009910137775)
          ·
            refine ⟨23018435130820514865206663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15345623420547009910137775 23018435130820514865206663)
            ·
              refine ⟨34527652696230772297809995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23018435130820514865206663 34527652696230772297809995)
              ·
                refine ⟨51791479044346158446714993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34527652696230772297809995 51791479044346158446714993)
                ·
                  refine ⟨38843609283259618835036245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51791479044346158446714993 38843609283259618835036245)
                  ·
                    refine ⟨455198546288198658223081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38843609283259618835036245 455198546288198658223081)
                    ·
                      rfl

theorem cell23_2659488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 8].length) (baseStart_2659488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659488 prefixEnd_2659488 := by exact prefixLift 2659488
  have htrace : WordTrace (prefixWord ++ tailWord_2659488) baseStart_2659488 baseEnd_2659488 := by
    simpa [prefixWord, tailWord_2659488, baseEnd_2659488] using wordTrace_append hprefix tailTrace_2659488
  have hstable : (prefixWord ++ tailWord_2659488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659488).length < 2 ^ (prefixWord ++ tailWord_2659488).sum := by decide
  have hdescent : baseEnd_2659488 < baseStart_2659488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659582 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2659582 : Nat := 118140960795 + 2659582 * 2 ^ 59
def prefixEnd_2659582 : Nat := 4983230072969 + 3 ^ 40 * 2659582 * 2
def baseEnd_2659582 : Nat := 455214635348706202297937

theorem tailTrace_2659582 : CollatzResearch.WordTrace tailWord_2659582 prefixEnd_2659582 455214635348706202297937 := by
  unfold tailWord_2659582
  simp only [CollatzResearch.WordTrace]
  refine ⟨12125365581349513661046625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64668616433864072858915333 12125365581349513661046625)
  ·
    refine ⟨9094024186012135245784969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12125365581349513661046625 9094024186012135245784969)
    ·
      refine ⟨6820518139509101434338727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9094024186012135245784969 6820518139509101434338727)
      ·
        refine ⟨10230777209263652151508091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6820518139509101434338727 10230777209263652151508091)
        ·
          refine ⟨15346165813895478227262137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10230777209263652151508091 15346165813895478227262137)
          ·
            refine ⟨11509624360421608670446603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15346165813895478227262137 11509624360421608670446603)
            ·
              refine ⟨17264436540632413005669905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11509624360421608670446603 17264436540632413005669905)
              ·
                refine ⟨12948327405474309754252429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17264436540632413005669905 12948327405474309754252429)
                ·
                  refine ⟨4855622777052866157844661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12948327405474309754252429 4855622777052866157844661)
                  ·
                    refine ⟨455214635348706202297937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4855622777052866157844661 455214635348706202297937)
                    ·
                      rfl

theorem cell23_2659582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2659582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659582 prefixEnd_2659582 := by exact prefixLift 2659582
  have htrace : WordTrace (prefixWord ++ tailWord_2659582) baseStart_2659582 baseEnd_2659582 := by
    simpa [prefixWord, tailWord_2659582, baseEnd_2659582] using wordTrace_append hprefix tailTrace_2659582
  have hstable : (prefixWord ++ tailWord_2659582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659582).length < 2 ^ (prefixWord ++ tailWord_2659582).sum := by decide
  have hdescent : baseEnd_2659582 < baseStart_2659582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659595 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 1, 6]
def baseStart_2659595 : Nat := 118140960795 + 2659595 * 2 ^ 59
def prefixEnd_2659595 : Nat := 4983230072969 + 3 ^ 40 * 2659595 * 2
def baseEnd_2659595 : Nat := 455216860431542352010417

theorem tailTrace_2659595 : CollatzResearch.WordTrace tailWord_2659595 prefixEnd_2659595 455216860431542352010417 := by
  unfold tailWord_2659595
  simp only [CollatzResearch.WordTrace]
  refine ⟨97003398799749012508596239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64668932533166008339064159 97003398799749012508596239)
  ·
    refine ⟨145505098199623518762894359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97003398799749012508596239 145505098199623518762894359)
    ·
      refine ⟨218257647299435278144341539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145505098199623518762894359 218257647299435278144341539)
      ·
        refine ⟨327386470949152917216512309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218257647299435278144341539 327386470949152917216512309)
        ·
          refine ⟨30692481651483085989048029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 327386470949152917216512309 30692481651483085989048029)
          ·
            refine ⟨11509680619306157245893011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30692481651483085989048029 11509680619306157245893011)
            ·
              refine ⟨17264520928959235868839517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11509680619306157245893011 17264520928959235868839517)
              ·
                refine ⟨6474195348359713450814819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17264520928959235868839517 6474195348359713450814819)
                ·
                  refine ⟨9711293022539570176222229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6474195348359713450814819 9711293022539570176222229)
                  ·
                    refine ⟨455216860431542352010417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9711293022539570176222229 455216860431542352010417)
                    ·
                      rfl

theorem cell23_2659595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 6].length) (baseStart_2659595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659595 prefixEnd_2659595 := by exact prefixLift 2659595
  have htrace : WordTrace (prefixWord ++ tailWord_2659595) baseStart_2659595 baseEnd_2659595 := by
    simpa [prefixWord, tailWord_2659595, baseEnd_2659595] using wordTrace_append hprefix tailTrace_2659595
  have hstable : (prefixWord ++ tailWord_2659595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659595).length < 2 ^ (prefixWord ++ tailWord_2659595).sum := by decide
  have hdescent : baseEnd_2659595 < baseStart_2659595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659613 : List Nat := [1, 4, 2, 3, 1, 2, 2, 3, 1, 1, 3]
def baseStart_2659613 : Nat := 118140960795 + 2659613 * 2 ^ 59
def prefixEnd_2659613 : Nat := 4983230072969 + 3 ^ 40 * 2659613 * 2
def baseEnd_2659613 : Nat := 1365659823946407985606169

theorem tailTrace_2659613 : CollatzResearch.WordTrace tailWord_2659613 prefixEnd_2659613 1365659823946407985606169 := by
  unfold tailWord_2659613
  simp only [CollatzResearch.WordTrace]
  refine ⟨97004055313683801582751493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64669370209122534388500995 97004055313683801582751493)
  ·
    refine ⟨18188260371315712796765905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97004055313683801582751493 18188260371315712796765905)
    ·
      refine ⟨13641195278486784597574429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18188260371315712796765905 13641195278486784597574429)
      ·
        refine ⟨5115448229432544224090411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13641195278486784597574429 5115448229432544224090411)
        ·
          refine ⟨7673172344148816336135617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5115448229432544224090411 7673172344148816336135617)
          ·
            refine ⟨5754879258111612252101713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7673172344148816336135617 5754879258111612252101713)
            ·
              refine ⟨4316159443583709189076285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5754879258111612252101713 4316159443583709189076285)
              ·
                refine ⟨1618559791343890945903607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4316159443583709189076285 1618559791343890945903607)
                ·
                  refine ⟨2427839687015836418855411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1618559791343890945903607 2427839687015836418855411)
                  ·
                    refine ⟨3641759530523754628283117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2427839687015836418855411 3641759530523754628283117)
                    ·
                      refine ⟨1365659823946407985606169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3641759530523754628283117 1365659823946407985606169)
                      ·
                        rfl

theorem cell23_2659613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_2659613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659613 prefixEnd_2659613 := by exact prefixLift 2659613
  have htrace : WordTrace (prefixWord ++ tailWord_2659613) baseStart_2659613 baseEnd_2659613 := by
    simpa [prefixWord, tailWord_2659613, baseEnd_2659613] using wordTrace_append hprefix tailTrace_2659613
  have hstable : (prefixWord ++ tailWord_2659613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659613).length < 2 ^ (prefixWord ++ tailWord_2659613).sum := by decide
  have hdescent : baseEnd_2659613 < baseStart_2659613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659616 : List Nat := [2, 1, 1, 5, 3, 2, 2, 1, 1, 5]
def baseStart_2659616 : Nat := 118140960795 + 2659616 * 2 ^ 59
def prefixEnd_2659616 : Nat := 4983230072969 + 3 ^ 40 * 2659616 * 2
def baseEnd_2659616 : Nat := 455220454796123824622885

theorem tailTrace_2659616 : CollatzResearch.WordTrace tailWord_2659616 prefixEnd_2659616 455220454796123824622885 := by
  unfold tailWord_2659616
  simp only [CollatzResearch.WordTrace]
  refine ⟨48502082366336466547555351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64669443155115288730073801 48502082366336466547555351)
  ·
    refine ⟨72753123549504699821333027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48502082366336466547555351 72753123549504699821333027)
    ·
      refine ⟨109129685324257049731999541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72753123549504699821333027 109129685324257049731999541)
      ·
        refine ⟨10230907999149098412374957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109129685324257049731999541 10230907999149098412374957)
        ·
          refine ⟨3836590499680911904640609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10230907999149098412374957 3836590499680911904640609)
          ·
            refine ⟨2877442874760683928480457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3836590499680911904640609 2877442874760683928480457)
            ·
              refine ⟨2158082156070512946360343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2877442874760683928480457 2158082156070512946360343)
              ·
                refine ⟨3237123234105769419540515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2158082156070512946360343 3237123234105769419540515)
                ·
                  refine ⟨4855684851158654129310773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3237123234105769419540515 4855684851158654129310773)
                  ·
                    refine ⟨455220454796123824622885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4855684851158654129310773 455220454796123824622885)
                    ·
                      rfl

theorem cell23_2659616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 1, 5].length) (baseStart_2659616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659616 prefixEnd_2659616 := by exact prefixLift 2659616
  have htrace : WordTrace (prefixWord ++ tailWord_2659616) baseStart_2659616 baseEnd_2659616 := by
    simpa [prefixWord, tailWord_2659616, baseEnd_2659616] using wordTrace_append hprefix tailTrace_2659616
  have hstable : (prefixWord ++ tailWord_2659616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659616).length < 2 ^ (prefixWord ++ tailWord_2659616).sum := by decide
  have hdescent : baseEnd_2659616 < baseStart_2659616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659619 : List Nat := [1, 1, 1, 4, 2, 3, 4, 1, 1, 1, 4]
def baseStart_2659619 : Nat := 118140960795 + 2659619 * 2 ^ 59
def prefixEnd_2659619 : Nat := 4983230072969 + 3 ^ 40 * 2659619 * 2
def baseEnd_2659619 : Nat := 1365662904830334962131141

theorem tailTrace_2659619 : CollatzResearch.WordTrace tailWord_2659619 prefixEnd_2659619 1365662904830334962131141 := by
  unfold tailWord_2659619
  simp only [CollatzResearch.WordTrace]
  refine ⟨97004274151662064607469911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64669516101108043071646607 97004274151662064607469911)
  ·
    refine ⟨145506411227493096911204867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97004274151662064607469911 145506411227493096911204867)
    ·
      refine ⟨218259616841239645366807301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145506411227493096911204867 218259616841239645366807301)
      ·
        refine ⟨40923678157732433506276369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218259616841239645366807301 40923678157732433506276369)
        ·
          refine ⟨30692758618299325129707277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40923678157732433506276369 30692758618299325129707277)
          ·
            refine ⟨11509784481862246923640229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30692758618299325129707277 11509784481862246923640229)
            ·
              refine ⟨2158084590349171298182543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11509784481862246923640229 2158084590349171298182543)
              ·
                refine ⟨3237126885523756947273815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2158084590349171298182543 3237126885523756947273815)
                ·
                  refine ⟨4855690328285635420910723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3237126885523756947273815 4855690328285635420910723)
                  ·
                    refine ⟨7283535492428453131366085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4855690328285635420910723 7283535492428453131366085)
                    ·
                      refine ⟨1365662904830334962131141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7283535492428453131366085 1365662904830334962131141)
                      ·
                        rfl

theorem cell23_2659619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_2659619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659619 prefixEnd_2659619 := by exact prefixLift 2659619
  have htrace : WordTrace (prefixWord ++ tailWord_2659619) baseStart_2659619 baseEnd_2659619 := by
    simpa [prefixWord, tailWord_2659619, baseEnd_2659619] using wordTrace_append hprefix tailTrace_2659619
  have hstable : (prefixWord ++ tailWord_2659619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659619).length < 2 ^ (prefixWord ++ tailWord_2659619).sum := by decide
  have hdescent : baseEnd_2659619 < baseStart_2659619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659646 : List Nat := [4, 2, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_2659646 : Nat := 118140960795 + 2659646 * 2 ^ 59
def prefixEnd_2659646 : Nat := 4983230072969 + 3 ^ 40 * 2659646 * 2
def baseEnd_2659646 : Nat := 455225589602668785497839

theorem tailTrace_2659646 : CollatzResearch.WordTrace tailWord_2659646 prefixEnd_2659646 455225589602668785497839 := by
  unfold tailWord_2659646
  simp only [CollatzResearch.WordTrace]
  refine ⟨12125657365320531027337849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64670172615042832145801861 12125657365320531027337849)
  ·
    refine ⟨9094243023990398270503387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12125657365320531027337849 9094243023990398270503387)
    ·
      refine ⟨13641364535985597405755081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9094243023990398270503387 13641364535985597405755081)
      ·
        refine ⟨10231023401989198054316311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13641364535985597405755081 10231023401989198054316311)
        ·
          refine ⟨15346535102983797081474467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10231023401989198054316311 15346535102983797081474467)
          ·
            refine ⟨23019802654475695622211701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15346535102983797081474467 23019802654475695622211701)
            ·
              refine ⟨2158106498857096464582347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23019802654475695622211701 2158106498857096464582347)
              ·
                refine ⟨3237159748285644696873521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2158106498857096464582347 3237159748285644696873521)
                ·
                  refine ⟨2427869811214233522655141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3237159748285644696873521 2427869811214233522655141)
                  ·
                    refine ⟨455225589602668785497839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2427869811214233522655141 455225589602668785497839)
                    ·
                      rfl

theorem cell23_2659646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_2659646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659646 prefixEnd_2659646 := by exact prefixLift 2659646
  have htrace : WordTrace (prefixWord ++ tailWord_2659646) baseStart_2659646 baseEnd_2659646 := by
    simpa [prefixWord, tailWord_2659646, baseEnd_2659646] using wordTrace_append hprefix tailTrace_2659646
  have hstable : (prefixWord ++ tailWord_2659646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659646).length < 2 ^ (prefixWord ++ tailWord_2659646).sum := by decide
  have hdescent : baseEnd_2659646 < baseStart_2659646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659649 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2659649 : Nat := 118140960795 + 2659649 * 2 ^ 59
def prefixEnd_2659649 : Nat := 4983230072969 + 3 ^ 40 * 2659649 * 2
def baseEnd_2659649 : Nat := 1365678309249969844756003

theorem tailTrace_2659649 : CollatzResearch.WordTrace tailWord_2659649 prefixEnd_2659649 1365678309249969844756003 := by
  unfold tailWord_2659649
  simp only [CollatzResearch.WordTrace]
  refine ⟨97005368341553379731062001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64670245561035586487374667 97005368341553379731062001)
  ·
    refine ⟨72754026256165034798296501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97005368341553379731062001 72754026256165034798296501)
    ·
      refine ⟨6820689961515472012340297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72754026256165034798296501 6820689961515472012340297)
      ·
        refine ⟨5115517471136604009255223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6820689961515472012340297 5115517471136604009255223)
        ·
          refine ⟨7673276206704906013882835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5115517471136604009255223 7673276206704906013882835)
          ·
            refine ⟨11509914310057359020824253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7673276206704906013882835 11509914310057359020824253)
            ·
              refine ⟨4316217866271509632809095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11509914310057359020824253 4316217866271509632809095)
              ·
                refine ⟨6474326799407264449213643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4316217866271509632809095 6474326799407264449213643)
                ·
                  refine ⟨9711490199110896673820465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6474326799407264449213643 9711490199110896673820465)
                  ·
                    refine ⟨7283617649333172505365349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9711490199110896673820465 7283617649333172505365349)
                    ·
                      refine ⟨1365678309249969844756003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7283617649333172505365349 1365678309249969844756003)
                      ·
                        rfl

theorem cell23_2659649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2659649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659649 prefixEnd_2659649 := by exact prefixLift 2659649
  have htrace : WordTrace (prefixWord ++ tailWord_2659649) baseStart_2659649 baseEnd_2659649 := by
    simpa [prefixWord, tailWord_2659649, baseEnd_2659649] using wordTrace_append hprefix tailTrace_2659649
  have hstable : (prefixWord ++ tailWord_2659649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659649).length < 2 ^ (prefixWord ++ tailWord_2659649).sum := by decide
  have hdescent : baseEnd_2659649 < baseStart_2659649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659665 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 1, 4, 5]
def baseStart_2659665 : Nat := 118140960795 + 2659665 * 2 ^ 59
def prefixEnd_2659665 : Nat := 4983230072969 + 3 ^ 40 * 2659665 * 2
def baseEnd_2659665 : Nat := 1365686524940441782155929

theorem tailTrace_2659665 : CollatzResearch.WordTrace tailWord_2659665 prefixEnd_2659665 1365686524940441782155929 := by
  unfold tailWord_2659665
  simp only [CollatzResearch.WordTrace]
  refine ⟨97005951909495414463644449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64670634606330276309096299 97005951909495414463644449)
  ·
    refine ⟨72754463932121560847733337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97005951909495414463644449 72754463932121560847733337)
    ·
      refine ⟨54565847949091170635800003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72754463932121560847733337 54565847949091170635800003)
      ·
        refine ⟨81848771923636755953700005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54565847949091170635800003 81848771923636755953700005)
        ·
          refine ⟨15346644735681891741318751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81848771923636755953700005 15346644735681891741318751)
          ·
            refine ⟨23019967103522837611978127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15346644735681891741318751 23019967103522837611978127)
            ·
              refine ⟨34529950655284256417967191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23019967103522837611978127 34529950655284256417967191)
              ·
                refine ⟨51794925982926384626950787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34529950655284256417967191 51794925982926384626950787)
                ·
                  refine ⟨77692388974389576940426181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51794925982926384626950787 77692388974389576940426181)
                  ·
                    refine ⟨14567322932698045676329909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77692388974389576940426181 14567322932698045676329909)
                    ·
                      refine ⟨1365686524940441782155929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14567322932698045676329909 1365686524940441782155929)
                      ·
                        rfl

theorem cell23_2659665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_2659665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659665 prefixEnd_2659665 := by exact prefixLift 2659665
  have htrace : WordTrace (prefixWord ++ tailWord_2659665) baseStart_2659665 baseEnd_2659665 := by
    simpa [prefixWord, tailWord_2659665, baseEnd_2659665] using wordTrace_append hprefix tailTrace_2659665
  have hstable : (prefixWord ++ tailWord_2659665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659665).length < 2 ^ (prefixWord ++ tailWord_2659665).sum := by decide
  have hdescent : baseEnd_2659665 < baseStart_2659665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659669 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 4, 1, 3]
def baseStart_2659669 : Nat := 118140960795 + 2659669 * 2 ^ 59
def prefixEnd_2659669 : Nat := 4983230072969 + 3 ^ 40 * 2659669 * 2
def baseEnd_2659669 : Nat := 1365688578863059766505911

theorem tailTrace_2659669 : CollatzResearch.WordTrace tailWord_2659669 prefixEnd_2659669 1365688578863059766505911 := by
  unfold tailWord_2659669
  simp only [CollatzResearch.WordTrace]
  refine ⟨97006097801480923146790061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64670731867653948764526707 97006097801480923146790061)
  ·
    refine ⟨36377286675555346180046273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97006097801480923146790061 36377286675555346180046273)
    ·
      refine ⟨27282965006666509635034705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36377286675555346180046273 27282965006666509635034705)
      ·
        refine ⟨20462223754999882226276029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27282965006666509635034705 20462223754999882226276029)
        ·
          refine ⟨7673333908124955834853511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20462223754999882226276029 7673333908124955834853511)
          ·
            refine ⟨11510000862187433752280267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7673333908124955834853511 11510000862187433752280267)
            ·
              refine ⟨17265001293281150628420401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11510000862187433752280267 17265001293281150628420401)
              ·
                refine ⟨12948750969960862971315301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17265001293281150628420401 12948750969960862971315301)
                ·
                  refine ⟨2427890806867661807121619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12948750969960862971315301 2427890806867661807121619)
                  ·
                    refine ⟨3641836210301492710682429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2427890806867661807121619 3641836210301492710682429)
                    ·
                      refine ⟨1365688578863059766505911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3641836210301492710682429 1365688578863059766505911)
                      ·
                        rfl

theorem cell23_2659669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_2659669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659669 prefixEnd_2659669 := by exact prefixLift 2659669
  have htrace : WordTrace (prefixWord ++ tailWord_2659669) baseStart_2659669 baseEnd_2659669 := by
    simpa [prefixWord, tailWord_2659669, baseEnd_2659669] using wordTrace_append hprefix tailTrace_2659669
  have hstable : (prefixWord ++ tailWord_2659669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659669).length < 2 ^ (prefixWord ++ tailWord_2659669).sum := by decide
  have hdescent : baseEnd_2659669 < baseStart_2659669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659682 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2659682 : Nat := 118140960795 + 2659682 * 2 ^ 59
def prefixEnd_2659682 : Nat := 4983230072969 + 3 ^ 40 * 2659682 * 2
def baseEnd_2659682 : Nat := 1365695254111568215643351

theorem tailTrace_2659682 : CollatzResearch.WordTrace tailWord_2659682 prefixEnd_2659682 1365695254111568215643351 := by
  unfold tailWord_2659682
  simp only [CollatzResearch.WordTrace]
  refine ⟨24251642987608456591753325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64671047966955884244675533 24251642987608456591753325)
  ·
    refine ⟨9094366120353171221907497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24251642987608456591753325 9094366120353171221907497)
    ·
      refine ⟨6820774590264878416430623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9094366120353171221907497 6820774590264878416430623)
      ·
        refine ⟨10231161885397317624645935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6820774590264878416430623 10231161885397317624645935)
        ·
          refine ⟨15346742828095976436968903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10231161885397317624645935 15346742828095976436968903)
          ·
            refine ⟨23020114242143964655453355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15346742828095976436968903 23020114242143964655453355)
            ·
              refine ⟨34530171363215946983180033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23020114242143964655453355 34530171363215946983180033)
              ·
                refine ⟨25897628522411960237385025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34530171363215946983180033 25897628522411960237385025)
                ·
                  refine ⟨19423221391808970178038769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25897628522411960237385025 19423221391808970178038769)
                  ·
                    refine ⟨14567416043856727633529077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19423221391808970178038769 14567416043856727633529077)
                    ·
                      refine ⟨1365695254111568215643351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14567416043856727633529077 1365695254111568215643351)
                      ·
                        rfl

theorem cell23_2659682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2659682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659682 prefixEnd_2659682 := by exact prefixLift 2659682
  have htrace : WordTrace (prefixWord ++ tailWord_2659682) baseStart_2659682 baseEnd_2659682 := by
    simpa [prefixWord, tailWord_2659682, baseEnd_2659682] using wordTrace_append hprefix tailTrace_2659682
  have hstable : (prefixWord ++ tailWord_2659682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659682).length < 2 ^ (prefixWord ++ tailWord_2659682).sum := by decide
  have hdescent : baseEnd_2659682 < baseStart_2659682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659695 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 5]
def baseStart_2659695 : Nat := 118140960795 + 2659695 * 2 ^ 59
def prefixEnd_2659695 : Nat := 4983230072969 + 3 ^ 40 * 2659695 * 2
def baseEnd_2659695 : Nat := 1365701929360076664780791

theorem tailTrace_2659695 : CollatzResearch.WordTrace tailWord_2659695 prefixEnd_2659695 1365701929360076664780791 := by
  unfold tailWord_2659695
  simp only [CollatzResearch.WordTrace]
  refine ⟨97007046099386729587236539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64671364066257819724824359 97007046099386729587236539)
  ·
    refine ⟨145510569149080094380854809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97007046099386729587236539 145510569149080094380854809)
    ·
      refine ⟨109132926861810070785641107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145510569149080094380854809 109132926861810070785641107)
      ·
        refine ⟨163699390292715106178461661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109132926861810070785641107 163699390292715106178461661)
        ·
          refine ⟨61387271359768164816923123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163699390292715106178461661 61387271359768164816923123)
          ·
            refine ⟨92080907039652247225384685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61387271359768164816923123 92080907039652247225384685)
            ·
              refine ⟨34530340139869592709519257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92080907039652247225384685 34530340139869592709519257)
              ·
                refine ⟨25897755104902194532139443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34530340139869592709519257 25897755104902194532139443)
                ·
                  refine ⟨38846632657353291798209165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25897755104902194532139443 38846632657353291798209165)
                  ·
                    refine ⟨14567487246507484424328437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38846632657353291798209165 14567487246507484424328437)
                    ·
                      refine ⟨1365701929360076664780791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14567487246507484424328437 1365701929360076664780791)
                      ·
                        rfl

theorem cell23_2659695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_2659695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659695 prefixEnd_2659695 := by exact prefixLift 2659695
  have htrace : WordTrace (prefixWord ++ tailWord_2659695) baseStart_2659695 baseEnd_2659695 := by
    simpa [prefixWord, tailWord_2659695, baseEnd_2659695] using wordTrace_append hprefix tailTrace_2659695
  have hstable : (prefixWord ++ tailWord_2659695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659695).length < 2 ^ (prefixWord ++ tailWord_2659695).sum := by decide
  have hdescent : baseEnd_2659695 < baseStart_2659695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659709 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 1, 4, 2]
def baseStart_2659709 : Nat := 118140960795 + 2659709 * 2 ^ 59
def prefixEnd_2659709 : Nat := 4983230072969 + 3 ^ 40 * 2659709 * 2
def baseEnd_2659709 : Nat := 1365709118089239610005727

theorem tailTrace_2659709 : CollatzResearch.WordTrace tailWord_2659709 prefixEnd_2659709 1365709118089239610005727 := by
  unfold tailWord_2659709
  simp only [CollatzResearch.WordTrace]
  refine ⟨97007556721336009978246181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64671704480890673318830787 97007556721336009978246181)
  ·
    refine ⟨18188916885250501870921159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97007556721336009978246181 18188916885250501870921159)
    ·
      refine ⟨27283375327875752806381739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18188916885250501870921159 27283375327875752806381739)
      ·
        refine ⟨40925062991813629209572609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27283375327875752806381739 40925062991813629209572609)
        ·
          refine ⟨30693797243860221907179457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40925062991813629209572609 30693797243860221907179457)
          ·
            refine ⟨23020347932895166430384593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30693797243860221907179457 23020347932895166430384593)
            ·
              refine ⟨17265260949671374822788445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23020347932895166430384593 17265260949671374822788445)
              ·
                refine ⟨6474472856126765558545667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17265260949671374822788445 6474472856126765558545667)
                ·
                  refine ⟨9711709284190148337818501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6474472856126765558545667 9711709284190148337818501)
                  ·
                    refine ⟨1820945490785652813340969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9711709284190148337818501 1820945490785652813340969)
                    ·
                      refine ⟨1365709118089239610005727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1820945490785652813340969 1365709118089239610005727)
                      ·
                        rfl

theorem cell23_2659709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_2659709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659709 prefixEnd_2659709 := by exact prefixLift 2659709
  have htrace : WordTrace (prefixWord ++ tailWord_2659709) baseStart_2659709 baseEnd_2659709 := by
    simpa [prefixWord, tailWord_2659709, baseEnd_2659709] using wordTrace_append hprefix tailTrace_2659709
  have hstable : (prefixWord ++ tailWord_2659709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659709).length < 2 ^ (prefixWord ++ tailWord_2659709).sum := by decide
  have hdescent : baseEnd_2659709 < baseStart_2659709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659743 : List Nat := [1, 1, 2, 5, 1, 3, 2, 2, 2, 2, 2]
def baseStart_2659743 : Nat := 118140960795 + 2659743 * 2 ^ 59
def prefixEnd_2659743 : Nat := 4983230072969 + 3 ^ 40 * 2659743 * 2
def baseEnd_2659743 : Nat := 1365726576431492476980571

theorem tailTrace_2659743 : CollatzResearch.WordTrace tailWord_2659743 prefixEnd_2659743 1365726576431492476980571 := by
  unfold tailWord_2659743
  simp only [CollatzResearch.WordTrace]
  refine ⟨97008796803212833784983883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64672531202141889189989255 97008796803212833784983883)
  ·
    refine ⟨145513195204819250677475825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97008796803212833784983883 145513195204819250677475825)
    ·
      refine ⟨109134896403614438008106869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145513195204819250677475825 109134896403614438008106869)
      ·
        refine ⟨10231396537838853563260019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109134896403614438008106869 10231396537838853563260019)
        ·
          refine ⟨15347094806758280344890029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10231396537838853563260019 15347094806758280344890029)
          ·
            refine ⟨5755160552534355129333761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15347094806758280344890029 5755160552534355129333761)
            ·
              refine ⟨4316370414400766347000321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5755160552534355129333761 4316370414400766347000321)
              ·
                refine ⟨3237277810800574760250241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4316370414400766347000321 3237277810800574760250241)
                ·
                  refine ⟨2427958358100431070187681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3237277810800574760250241 2427958358100431070187681)
                  ·
                    refine ⟨1820968768575323302640761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2427958358100431070187681 1820968768575323302640761)
                    ·
                      refine ⟨1365726576431492476980571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1820968768575323302640761 1365726576431492476980571)
                      ·
                        rfl

theorem cell23_2659743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_2659743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659743 prefixEnd_2659743 := by exact prefixLift 2659743
  have htrace : WordTrace (prefixWord ++ tailWord_2659743) baseStart_2659743 baseEnd_2659743 := by
    simpa [prefixWord, tailWord_2659743, baseEnd_2659743] using wordTrace_append hprefix tailTrace_2659743
  have hstable : (prefixWord ++ tailWord_2659743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659743).length < 2 ^ (prefixWord ++ tailWord_2659743).sum := by decide
  have hdescent : baseEnd_2659743 < baseStart_2659743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659755 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 7]
def baseStart_2659755 : Nat := 118140960795 + 2659755 * 2 ^ 59
def prefixEnd_2659755 : Nat := 4983230072969 + 3 ^ 40 * 2659755 * 2
def baseEnd_2659755 : Nat := 1365732738199346430030515

theorem tailTrace_2659755 : CollatzResearch.WordTrace tailWord_2659755 prefixEnd_2659755 1365732738199346430030515 := by
  unfold tailWord_2659755
  simp only [CollatzResearch.WordTrace]
  refine ⟨97009234479169359834420719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64672822986112906556280479 97009234479169359834420719)
  ·
    refine ⟨145513851718754039751631079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97009234479169359834420719 145513851718754039751631079)
    ·
      refine ⟨218270777578131059627446619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145513851718754039751631079 218270777578131059627446619)
      ·
        refine ⟨327406166367196589441169929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218270777578131059627446619 327406166367196589441169929)
        ·
          refine ⟨245554624775397442080877447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327406166367196589441169929 245554624775397442080877447)
          ·
            refine ⟨368331937163096163121316171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245554624775397442080877447 368331937163096163121316171)
            ·
              refine ⟨552497905744644244681974257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368331937163096163121316171 552497905744644244681974257)
              ·
                refine ⟨414373429308483183511480693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552497905744644244681974257 414373429308483183511480693)
                ·
                  refine ⟨38847508997670298454201315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 414373429308483183511480693 38847508997670298454201315)
                  ·
                    refine ⟨58271263496505447681301973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38847508997670298454201315 58271263496505447681301973)
                    ·
                      refine ⟨1365732738199346430030515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58271263496505447681301973 1365732738199346430030515)
                      ·
                        rfl

theorem cell23_2659755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 7].length) (baseStart_2659755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659755 prefixEnd_2659755 := by exact prefixLift 2659755
  have htrace : WordTrace (prefixWord ++ tailWord_2659755) baseStart_2659755 baseEnd_2659755 := by
    simpa [prefixWord, tailWord_2659755, baseEnd_2659755] using wordTrace_append hprefix tailTrace_2659755
  have hstable : (prefixWord ++ tailWord_2659755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659755).length < 2 ^ (prefixWord ++ tailWord_2659755).sum := by decide
  have hdescent : baseEnd_2659755 < baseStart_2659755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659809 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 3, 4]
def baseStart_2659809 : Nat := 118140960795 + 2659809 * 2 ^ 59
def prefixEnd_2659809 : Nat := 4983230072969 + 3 ^ 40 * 2659809 * 2
def baseEnd_2659809 : Nat := 455253488718229739585089

theorem tailTrace_2659809 : CollatzResearch.WordTrace tailWord_2659809 prefixEnd_2659809 455253488718229739585089 := by
  unfold tailWord_2659809
  simp only [CollatzResearch.WordTrace]
  refine ⟨97011204020973727056886481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64674136013982484704590987 97011204020973727056886481)
  ·
    refine ⟨72758403015730295292664861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97011204020973727056886481 72758403015730295292664861)
    ·
      refine ⟨27284401130898860734749323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72758403015730295292664861 27284401130898860734749323)
      ·
        refine ⟨40926601696348291102123985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27284401130898860734749323 40926601696348291102123985)
        ·
          refine ⟨30694951272261218326592989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40926601696348291102123985 30694951272261218326592989)
          ·
            refine ⟨11510606727097956872472371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30694951272261218326592989 11510606727097956872472371)
            ·
              refine ⟨17265910090646935308708557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11510606727097956872472371 17265910090646935308708557)
              ·
                refine ⟨6474716283992600740765709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17265910090646935308708557 6474716283992600740765709)
                ·
                  refine ⟨2428018606497225277787141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6474716283992600740765709 2428018606497225277787141)
                  ·
                    refine ⟨455253488718229739585089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2428018606497225277787141 455253488718229739585089)
                    ·
                      rfl

theorem cell23_2659809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_2659809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659809 prefixEnd_2659809 := by exact prefixLift 2659809
  have htrace : WordTrace (prefixWord ++ tailWord_2659809) baseStart_2659809 baseEnd_2659809 := by
    simpa [prefixWord, tailWord_2659809, baseEnd_2659809] using wordTrace_append hprefix tailTrace_2659809
  have hstable : (prefixWord ++ tailWord_2659809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659809).length < 2 ^ (prefixWord ++ tailWord_2659809).sum := by decide
  have hdescent : baseEnd_2659809 < baseStart_2659809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659826 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 3, 4]
def baseStart_2659826 : Nat := 118140960795 + 2659826 * 2 ^ 59
def prefixEnd_2659826 : Nat := 4983230072969 + 3 ^ 40 * 2659826 * 2
def baseEnd_2659826 : Nat := 455256398441938550747563

theorem tailTrace_2659826 : CollatzResearch.WordTrace tailWord_2659826 prefixEnd_2659826 455256398441938550747563 := by
  unfold tailWord_2659826
  simp only [CollatzResearch.WordTrace]
  refine ⟨24252956015478034740063833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64674549374608092640170221 24252956015478034740063833)
  ·
    refine ⟨18189717011608526055047875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24252956015478034740063833 18189717011608526055047875)
    ·
      refine ⟨27284575517412789082571813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18189717011608526055047875 27284575517412789082571813)
      ·
        refine ⟨5115857909514897952982215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27284575517412789082571813 5115857909514897952982215)
        ·
          refine ⟨7673786864272346929473323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5115857909514897952982215 7673786864272346929473323)
          ·
            refine ⟨11510680296408520394209985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7673786864272346929473323 11510680296408520394209985)
            ·
              refine ⟨8633010222306390295657489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11510680296408520394209985 8633010222306390295657489)
              ·
                refine ⟨6474757666729792721743117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8633010222306390295657489 6474757666729792721743117)
                ·
                  refine ⟨2428034125023672270653669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6474757666729792721743117 2428034125023672270653669)
                  ·
                    refine ⟨455256398441938550747563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2428034125023672270653669 455256398441938550747563)
                    ·
                      rfl

theorem cell23_2659826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_2659826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659826 prefixEnd_2659826 := by exact prefixLift 2659826
  have htrace : WordTrace (prefixWord ++ tailWord_2659826) baseStart_2659826 baseEnd_2659826 := by
    simpa [prefixWord, tailWord_2659826, baseEnd_2659826] using wordTrace_append hprefix tailTrace_2659826
  have hstable : (prefixWord ++ tailWord_2659826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659826).length < 2 ^ (prefixWord ++ tailWord_2659826).sum := by decide
  have hdescent : baseEnd_2659826 < baseStart_2659826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659860 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_2659860 : Nat := 118140960795 + 2659860 * 2 ^ 59
def prefixEnd_2659860 : Nat := 4983230072969 + 3 ^ 40 * 2659860 * 2
def baseEnd_2659860 : Nat := 455262217889356173072511

theorem tailTrace_2659860 : CollatzResearch.WordTrace tailWord_2659860 prefixEnd_2659860 455262217889356173072511 := by
  unfold tailWord_2659860
  simp only [CollatzResearch.WordTrace]
  refine ⟨48506532071894481383496517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64675376095859308511328689 48506532071894481383496517)
  ·
    refine ⟨9094974763480215259405597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48506532071894481383496517 9094974763480215259405597)
    ·
      refine ⟨3410615536305080722277099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9094974763480215259405597 3410615536305080722277099)
      ·
        refine ⟨5115923304457621083415649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3410615536305080722277099 5115923304457621083415649)
        ·
          refine ⟨3836942478343215812561737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5115923304457621083415649 3836942478343215812561737)
          ·
            refine ⟨2877706858757411859421303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3836942478343215812561737 2877706858757411859421303)
            ·
              refine ⟨4316560288136117789131955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2877706858757411859421303 4316560288136117789131955)
              ·
                refine ⟨6474840432204176683697933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4316560288136117789131955 6474840432204176683697933)
                ·
                  refine ⟨2428065162076566256386725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6474840432204176683697933 2428065162076566256386725)
                  ·
                    refine ⟨455262217889356173072511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2428065162076566256386725 455262217889356173072511)
                    ·
                      rfl

theorem cell23_2659860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_2659860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659860 prefixEnd_2659860 := by exact prefixLift 2659860
  have htrace : WordTrace (prefixWord ++ tailWord_2659860) baseStart_2659860 baseEnd_2659860 := by
    simpa [prefixWord, tailWord_2659860, baseEnd_2659860] using wordTrace_append hprefix tailTrace_2659860
  have hstable : (prefixWord ++ tailWord_2659860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659860).length < 2 ^ (prefixWord ++ tailWord_2659860).sum := by decide
  have hdescent : baseEnd_2659860 < baseStart_2659860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659869 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 3, 5]
def baseStart_2659869 : Nat := 118140960795 + 2659869 * 2 ^ 59
def prefixEnd_2659869 : Nat := 4983230072969 + 3 ^ 40 * 2659869 * 2
def baseEnd_2659869 : Nat := 455263758331319661334997

theorem tailTrace_2659869 : CollatzResearch.WordTrace tailWord_2659869 prefixEnd_2659869 455263758331319661334997 := by
  unfold tailWord_2659869
  simp only [CollatzResearch.WordTrace]
  refine ⟨97013392400756357304070661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64675594933837571536047107 97013392400756357304070661)
  ·
    refine ⟨18190011075141816994513249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97013392400756357304070661 18190011075141816994513249)
    ·
      refine ⟨13642508306356362745884937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18190011075141816994513249 13642508306356362745884937)
      ·
        refine ⟨10231881229767272059413703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13642508306356362745884937 10231881229767272059413703)
        ·
          refine ⟨15347821844650908089120555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10231881229767272059413703 15347821844650908089120555)
          ·
            refine ⟨23021732766976362133680833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15347821844650908089120555 23021732766976362133680833)
            ·
              refine ⟨17266299575232271600260625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23021732766976362133680833 17266299575232271600260625)
              ·
                refine ⟨12949724681424203700195469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17266299575232271600260625 12949724681424203700195469)
                ·
                  refine ⟨4856146755534076387573301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12949724681424203700195469 4856146755534076387573301)
                  ·
                    refine ⟨455263758331319661334997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4856146755534076387573301 455263758331319661334997)
                    ·
                      rfl

theorem cell23_2659869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_2659869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659869 prefixEnd_2659869 := by exact prefixLift 2659869
  have htrace : WordTrace (prefixWord ++ tailWord_2659869) baseStart_2659869 baseEnd_2659869 := by
    simpa [prefixWord, tailWord_2659869, baseEnd_2659869] using wordTrace_append hprefix tailTrace_2659869
  have hstable : (prefixWord ++ tailWord_2659869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659869).length < 2 ^ (prefixWord ++ tailWord_2659869).sum := by decide
  have hdescent : baseEnd_2659869 < baseStart_2659869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659886 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 3, 5]
def baseStart_2659886 : Nat := 118140960795 + 2659886 * 2 ^ 59
def prefixEnd_2659886 : Nat := 4983230072969 + 3 ^ 40 * 2659886 * 2
def baseEnd_2659886 : Nat := 455266668055028472497471

theorem tailTrace_2659886 : CollatzResearch.WordTrace tailWord_2659886 prefixEnd_2659886 455266668055028472497471 := by
  unfold tailWord_2659886
  simp only [CollatzResearch.WordTrace]
  refine ⟨12126751555211846150929939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64676008294463179471626341 12126751555211846150929939)
  ·
    refine ⟨18190127332817769226394909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12126751555211846150929939 18190127332817769226394909)
    ·
      refine ⟨6821297749806663459898091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18190127332817769226394909 6821297749806663459898091)
      ·
        refine ⟨10231946624709995189847137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6821297749806663459898091 10231946624709995189847137)
        ·
          refine ⟨7673959968532496392385353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10231946624709995189847137 7673959968532496392385353)
          ·
            refine ⟨5755469976399372294289015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7673959968532496392385353 5755469976399372294289015)
            ·
              refine ⟨8633204964599058441433523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5755469976399372294289015 8633204964599058441433523)
              ·
                refine ⟨12949807446898587662150285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8633204964599058441433523 12949807446898587662150285)
                ·
                  refine ⟨4856177792586970373306357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12949807446898587662150285 4856177792586970373306357)
                  ·
                    refine ⟨455266668055028472497471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4856177792586970373306357 455266668055028472497471)
                    ·
                      rfl

theorem cell23_2659886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_2659886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659886 prefixEnd_2659886 := by exact prefixLift 2659886
  have htrace : WordTrace (prefixWord ++ tailWord_2659886) baseStart_2659886 baseEnd_2659886 := by
    simpa [prefixWord, tailWord_2659886, baseEnd_2659886] using wordTrace_append hprefix tailTrace_2659886
  have hstable : (prefixWord ++ tailWord_2659886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659886).length < 2 ^ (prefixWord ++ tailWord_2659886).sum := by decide
  have hdescent : baseEnd_2659886 < baseStart_2659886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659893 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 2, 3, 2]
def baseStart_2659893 : Nat := 118140960795 + 2659893 * 2 ^ 59
def prefixEnd_2659893 : Nat := 4983230072969 + 3 ^ 40 * 2659893 * 2
def baseEnd_2659893 : Nat := 1365803598529666890104881

theorem tailTrace_2659893 : CollatzResearch.WordTrace tailWord_2659893 prefixEnd_2659893 1365803598529666890104881 := by
  unfold tailWord_2659893
  simp only [CollatzResearch.WordTrace]
  refine ⟨97014267752669409402944333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64676178501779606268629555 97014267752669409402944333)
  ·
    refine ⟨36380350407251028526104125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97014267752669409402944333 36380350407251028526104125)
    ·
      refine ⟨13642631402719135697289047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36380350407251028526104125 13642631402719135697289047)
      ·
        refine ⟨20463947104078703545933571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13642631402719135697289047 20463947104078703545933571)
        ·
          refine ⟨30695920656118055318900357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20463947104078703545933571 30695920656118055318900357)
          ·
            refine ⟨5755485123022135372293817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30695920656118055318900357 5755485123022135372293817)
            ·
              refine ⟨4316613842266601529220363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5755485123022135372293817 4316613842266601529220363)
              ·
                refine ⟨6474920763399902293830545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4316613842266601529220363 6474920763399902293830545)
                ·
                  refine ⟨4856190572549926720372909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6474920763399902293830545 4856190572549926720372909)
                  ·
                    refine ⟨1821071464706222520139841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4856190572549926720372909 1821071464706222520139841)
                    ·
                      refine ⟨1365803598529666890104881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1821071464706222520139841 1365803598529666890104881)
                      ·
                        rfl

theorem cell23_2659893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_2659893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659893 prefixEnd_2659893 := by exact prefixLift 2659893
  have htrace : WordTrace (prefixWord ++ tailWord_2659893) baseStart_2659893 baseEnd_2659893 := by
    simpa [prefixWord, tailWord_2659893, baseEnd_2659893] using wordTrace_append hprefix tailTrace_2659893
  have hstable : (prefixWord ++ tailWord_2659893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659893).length < 2 ^ (prefixWord ++ tailWord_2659893).sum := by decide
  have hdescent : baseEnd_2659893 < baseStart_2659893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659916 : List Nat := [2, 2, 1, 3, 1, 3, 1, 4, 2, 4]
def baseStart_2659916 : Nat := 118140960795 + 2659916 * 2 ^ 59
def prefixEnd_2659916 : Nat := 4983230072969 + 3 ^ 40 * 2659916 * 2
def baseEnd_2659916 : Nat := 455271802861573433372425

theorem tailTrace_2659916 : CollatzResearch.WordTrace tailWord_2659916 prefixEnd_2659916 455271802861573433372425 := by
  unfold tailWord_2659916
  simp only [CollatzResearch.WordTrace]
  refine ⟨48507553315793042165515801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64676737754390722887354401 48507553315793042165515801)
  ·
    refine ⟨36380664986844781624136851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48507553315793042165515801 36380664986844781624136851)
    ·
      refine ⟨54570997480267172436205277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36380664986844781624136851 54570997480267172436205277)
      ·
        refine ⟨20464124055100189663576979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54570997480267172436205277 20464124055100189663576979)
        ·
          refine ⟨30696186082650284495365469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20464124055100189663576979 30696186082650284495365469)
          ·
            refine ⟨11511069780993856685762051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30696186082650284495365469 11511069780993856685762051)
            ·
              refine ⟨17266604671490785028643077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11511069780993856685762051 17266604671490785028643077)
              ·
                refine ⟨3237488375904522192870577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17266604671490785028643077 3237488375904522192870577)
                ·
                  refine ⟨2428116281928391644652933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3237488375904522192870577 2428116281928391644652933)
                  ·
                    refine ⟨455271802861573433372425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2428116281928391644652933 455271802861573433372425)
                    ·
                      rfl

theorem cell23_2659916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_2659916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659916 prefixEnd_2659916 := by exact prefixLift 2659916
  have htrace : WordTrace (prefixWord ++ tailWord_2659916) baseStart_2659916 baseEnd_2659916 := by
    simpa [prefixWord, tailWord_2659916, baseEnd_2659916] using wordTrace_append hprefix tailTrace_2659916
  have hstable : (prefixWord ++ tailWord_2659916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659916).length < 2 ^ (prefixWord ++ tailWord_2659916).sum := by decide
  have hdescent : baseEnd_2659916 < baseStart_2659916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659917 : List Nat := [1, 6, 1, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_2659917 : Nat := 118140960795 + 2659917 * 2 ^ 59
def prefixEnd_2659917 : Nat := 4983230072969 + 3 ^ 40 * 2659917 * 2
def baseEnd_2659917 : Nat := 1365815922065374796204771

theorem tailTrace_2659917 : CollatzResearch.WordTrace tailWord_2659917 prefixEnd_2659917 1365815922065374796204771 := by
  unfold tailWord_2659917
  simp only [CollatzResearch.WordTrace]
  refine ⟨97015143104582461501818005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64676762069721641001212003 97015143104582461501818005)
  ·
    refine ⟨4547584833027302882897719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 97015143104582461501818005 4547584833027302882897719)
    ·
      refine ⟨6821377249540954324346579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4547584833027302882897719 6821377249540954324346579)
      ·
        refine ⟨10232065874311431486519869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6821377249540954324346579 10232065874311431486519869)
        ·
          refine ⟨3837024702866786807444951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10232065874311431486519869 3837024702866786807444951)
          ·
            refine ⟨5755537054300180211167427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3837024702866786807444951 5755537054300180211167427)
            ·
              refine ⟨8633305581450270316751141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5755537054300180211167427 8633305581450270316751141)
              ·
                refine ⟨1618744796521925684390839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8633305581450270316751141 1618744796521925684390839)
                ·
                  refine ⟨2428117194782888526586259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1618744796521925684390839 2428117194782888526586259)
                  ·
                    refine ⟨3642175792174332789879389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2428117194782888526586259 3642175792174332789879389)
                    ·
                      refine ⟨1365815922065374796204771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3642175792174332789879389 1365815922065374796204771)
                      ·
                        rfl

theorem cell23_2659917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_2659917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659917 prefixEnd_2659917 := by exact prefixLift 2659917
  have htrace : WordTrace (prefixWord ++ tailWord_2659917) baseStart_2659917 baseEnd_2659917 := by
    simpa [prefixWord, tailWord_2659917, baseEnd_2659917] using wordTrace_append hprefix tailTrace_2659917
  have hstable : (prefixWord ++ tailWord_2659917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659917).length < 2 ^ (prefixWord ++ tailWord_2659917).sum := by decide
  have hdescent : baseEnd_2659917 < baseStart_2659917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659946 : List Nat := [3, 1, 3, 2, 1, 3, 3, 7]
def baseStart_2659946 : Nat := 118140960795 + 2659946 * 2 ^ 59
def prefixEnd_2659946 : Nat := 4983230072969 + 3 ^ 40 * 2659946 * 2
def baseEnd_2659946 : Nat := 50586326407568710471931

theorem tailTrace_2659946 : CollatzResearch.WordTrace tailWord_2659946 prefixEnd_2659946 50586326407568710471931 := by
  unfold tailWord_2659946
  simp only [CollatzResearch.WordTrace]
  refine ⟨24254050205369349863655923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64677467214318266303082461 24254050205369349863655923)
  ·
    refine ⟨36381075308054024795483885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24254050205369349863655923 36381075308054024795483885)
    ·
      refine ⟨13642903240520259298306457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36381075308054024795483885 13642903240520259298306457)
      ·
        refine ⟨10232177430390194473729843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13642903240520259298306457 10232177430390194473729843)
        ·
          refine ⟨15348266145585291710594765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10232177430390194473729843 15348266145585291710594765)
          ·
            refine ⟨5755599804594484391473037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15348266145585291710594765 5755599804594484391473037)
            ·
              refine ⟨2158349926722931646802389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5755599804594484391473037 2158349926722931646802389)
              ·
                refine ⟨50586326407568710471931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2158349926722931646802389 50586326407568710471931)
                ·
                  rfl

theorem cell23_2659946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 7].length) (baseStart_2659946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659946 prefixEnd_2659946 := by exact prefixLift 2659946
  have htrace : WordTrace (prefixWord ++ tailWord_2659946) baseStart_2659946 baseEnd_2659946 := by
    simpa [prefixWord, tailWord_2659946, baseEnd_2659946] using wordTrace_append hprefix tailTrace_2659946
  have hstable : (prefixWord ++ tailWord_2659946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659946).length < 2 ^ (prefixWord ++ tailWord_2659946).sum := by decide
  have hdescent : baseEnd_2659946 < baseStart_2659946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2659957 : List Nat := [1, 3, 4, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_2659957 : Nat := 118140960795 + 2659957 * 2 ^ 59
def prefixEnd_2659957 : Nat := 4983230072969 + 3 ^ 40 * 2659957 * 2
def baseEnd_2659957 : Nat := 1365836461291554639704587

theorem tailTrace_2659957 : CollatzResearch.WordTrace tailWord_2659957 prefixEnd_2659957 1365836461291554639704587 := by
  unfold tailWord_2659957
  simp only [CollatzResearch.WordTrace]
  refine ⟨97016602024437548333274125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64677734682958365555516083 97016602024437548333274125)
  ·
    refine ⟨36381225759164080624977797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97016602024437548333274125 36381225759164080624977797)
    ·
      refine ⟨6821479829843265117183337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36381225759164080624977797 6821479829843265117183337)
      ·
        refine ⟨5116109872382448837887503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6821479829843265117183337 5116109872382448837887503)
        ·
          refine ⟨7674164808573673256831255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5116109872382448837887503 7674164808573673256831255)
          ·
            refine ⟨11511247212860509885246883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7674164808573673256831255 11511247212860509885246883)
            ·
              refine ⟨17266870819290764827870325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11511247212860509885246883 17266870819290764827870325)
              ·
                refine ⟨1618769139308509202612843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17266870819290764827870325 1618769139308509202612843)
                ·
                  refine ⟨2428153708962763803919265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1618769139308509202612843 2428153708962763803919265)
                  ·
                    refine ⟨1821115281722072852939449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2428153708962763803919265 1821115281722072852939449)
                    ·
                      refine ⟨1365836461291554639704587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1821115281722072852939449 1365836461291554639704587)
                      ·
                        rfl

theorem cell23_2659957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_2659957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2659957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2659957 prefixEnd_2659957 := by exact prefixLift 2659957
  have htrace : WordTrace (prefixWord ++ tailWord_2659957) baseStart_2659957 baseEnd_2659957 := by
    simpa [prefixWord, tailWord_2659957, baseEnd_2659957] using wordTrace_append hprefix tailTrace_2659957
  have hstable : (prefixWord ++ tailWord_2659957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2659957).length < 2 ^ (prefixWord ++ tailWord_2659957).sum := by decide
  have hdescent : baseEnd_2659957 < baseStart_2659957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2659957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660000 : List Nat := [2, 1, 1, 4, 3, 2, 2, 2, 1, 3, 2]
def baseStart_2660000 : Nat := 118140960795 + 2660000 * 2 ^ 59
def prefixEnd_2660000 : Nat := 4983230072969 + 3 ^ 40 * 2660000 * 2
def baseEnd_2660000 : Nat := 1365858540959697971466889

theorem tailTrace_2660000 : CollatzResearch.WordTrace tailWord_2660000 prefixEnd_2660000 1365858540959697971466889 := by
  unfold tailWord_2660000
  simp only [CollatzResearch.WordTrace]
  refine ⟨48509085181640883338544727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64678780242187844451392969 48509085181640883338544727)
  ·
    refine ⟨72763627772461325007817091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48509085181640883338544727 72763627772461325007817091)
    ·
      refine ⟨109145441658691987511725637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72763627772461325007817091 109145441658691987511725637)
      ·
        refine ⟨20464770311004747658448557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109145441658691987511725637 20464770311004747658448557)
        ·
          refine ⟨7674288866626780371918209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20464770311004747658448557 7674288866626780371918209)
          ·
            refine ⟨5755716649970085278938657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7674288866626780371918209 5755716649970085278938657)
            ·
              refine ⟨4316787487477563959203993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5755716649970085278938657 4316787487477563959203993)
              ·
                refine ⟨3237590615608172969402995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4316787487477563959203993 3237590615608172969402995)
                ·
                  refine ⟨4856385923412259454104493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3237590615608172969402995 4856385923412259454104493)
                  ·
                    refine ⟨1821144721279597295289185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4856385923412259454104493 1821144721279597295289185)
                    ·
                      refine ⟨1365858540959697971466889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1821144721279597295289185 1365858540959697971466889)
                      ·
                        rfl

theorem cell23_2660000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_2660000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660000 prefixEnd_2660000 := by exact prefixLift 2660000
  have htrace : WordTrace (prefixWord ++ tailWord_2660000) baseStart_2660000 baseEnd_2660000 := by
    simpa [prefixWord, tailWord_2660000, baseEnd_2660000] using wordTrace_append hprefix tailTrace_2660000
  have hstable : (prefixWord ++ tailWord_2660000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660000).length < 2 ^ (prefixWord ++ tailWord_2660000).sum := by decide
  have hdescent : baseEnd_2660000 < baseStart_2660000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660008 : List Nat := [2, 1, 7, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_2660008 : Nat := 118140960795 + 2660008 * 2 ^ 59
def prefixEnd_2660008 : Nat := 4983230072969 + 3 ^ 40 * 2660008 * 2
def baseEnd_2660008 : Nat := 1365862648804933940166853

theorem tailTrace_2660008 : CollatzResearch.WordTrace tailWord_2660008 prefixEnd_2660008 1365862648804933940166853 := by
  unfold tailWord_2660008
  simp only [CollatzResearch.WordTrace]
  refine ⟨48509231073626392021690339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64678974764835189362253785 48509231073626392021690339)
  ·
    refine ⟨72763846610439588032535509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48509231073626392021690339 72763846610439588032535509)
    ·
      refine ⟨1705402654932177844512551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 72763846610439588032535509 1705402654932177844512551)
      ·
        refine ⟨2558103982398266766768827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705402654932177844512551 2558103982398266766768827)
        ·
          refine ⟨3837155973597400150153241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2558103982398266766768827 3837155973597400150153241)
          ·
            refine ⟨2877866980198050112614931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3837155973597400150153241 2877866980198050112614931)
            ·
              refine ⟨4316800470297075168922397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2877866980198050112614931 4316800470297075168922397)
              ·
                refine ⟨1618800176361403188345899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4316800470297075168922397 1618800176361403188345899)
                ·
                  refine ⟨2428200264542104782518849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1618800176361403188345899 2428200264542104782518849)
                  ·
                    refine ⟨1821150198406578586889137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2428200264542104782518849 1821150198406578586889137)
                    ·
                      refine ⟨1365862648804933940166853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1821150198406578586889137 1365862648804933940166853)
                      ·
                        rfl

theorem cell23_2660008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_2660008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660008 prefixEnd_2660008 := by exact prefixLift 2660008
  have htrace : WordTrace (prefixWord ++ tailWord_2660008) baseStart_2660008 baseEnd_2660008 := by
    simpa [prefixWord, tailWord_2660008, baseEnd_2660008] using wordTrace_append hprefix tailTrace_2660008
  have hstable : (prefixWord ++ tailWord_2660008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660008).length < 2 ^ (prefixWord ++ tailWord_2660008).sum := by decide
  have hdescent : baseEnd_2660008 < baseStart_2660008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660013 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_2660013 : Nat := 118140960795 + 2660013 * 2 ^ 59
def prefixEnd_2660013 : Nat := 4983230072969 + 3 ^ 40 * 2660013 * 2
def baseEnd_2660013 : Nat := 1365865216208206420604329

theorem tailTrace_2660013 : CollatzResearch.WordTrace tailWord_2660013 prefixEnd_2660013 1365865216208206420604329 := by
  unfold tailWord_2660013
  simp only [CollatzResearch.WordTrace]
  refine ⟨97018644512234669897312693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64679096341489779931541795 97018644512234669897312693)
  ·
    refine ⟨9095497923022000302873065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97018644512234669897312693 9095497923022000302873065)
    ·
      refine ⟨6821623442266500227154799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9095497923022000302873065 6821623442266500227154799)
      ·
        refine ⟨10232435163399750340732199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6821623442266500227154799 10232435163399750340732199)
        ·
          refine ⟨15348652745099625511098299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10232435163399750340732199 15348652745099625511098299)
          ·
            refine ⟨23022979117649438266647449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15348652745099625511098299 23022979117649438266647449)
            ·
              refine ⟨17267234338237078699985587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23022979117649438266647449 17267234338237078699985587)
              ·
                refine ⟨25900851507355618049978381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17267234338237078699985587 25900851507355618049978381)
                ·
                  refine ⟨9712819315258356768741893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25900851507355618049978381 9712819315258356768741893)
                  ·
                    refine ⟨1821153621610941894139105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9712819315258356768741893 1821153621610941894139105)
                    ·
                      refine ⟨1365865216208206420604329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1821153621610941894139105 1365865216208206420604329)
                      ·
                        rfl

theorem cell23_2660013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_2660013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660013 prefixEnd_2660013 := by exact prefixLift 2660013
  have htrace : WordTrace (prefixWord ++ tailWord_2660013) baseStart_2660013 baseEnd_2660013 := by
    simpa [prefixWord, tailWord_2660013, baseEnd_2660013] using wordTrace_append hprefix tailTrace_2660013
  have hstable : (prefixWord ++ tailWord_2660013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660013).length < 2 ^ (prefixWord ++ tailWord_2660013).sum := by decide
  have hdescent : baseEnd_2660013 < baseStart_2660013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660029 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_2660029 : Nat := 118140960795 + 2660029 * 2 ^ 59
def prefixEnd_2660029 : Nat := 4983230072969 + 3 ^ 40 * 2660029 * 2
def baseEnd_2660029 : Nat := 1365873431898678358004255

theorem tailTrace_2660029 : CollatzResearch.WordTrace tailWord_2660029 prefixEnd_2660029 1365873431898678358004255 := by
  unfold tailWord_2660029
  simp only [CollatzResearch.WordTrace]
  refine ⟨97019228080176704629895141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64679485386784469753263427 97019228080176704629895141)
  ·
    refine ⟨18191105265033132118105339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97019228080176704629895141 18191105265033132118105339)
    ·
      refine ⟨27286657897549698177158009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18191105265033132118105339 27286657897549698177158009)
      ·
        refine ⟨20464993423162273632868507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27286657897549698177158009 20464993423162273632868507)
        ·
          refine ⟨30697490134743410449302761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20464993423162273632868507 30697490134743410449302761)
          ·
            refine ⟨23023117601057557836977071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30697490134743410449302761 23023117601057557836977071)
            ·
              refine ⟨34534676401586336755465607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23023117601057557836977071 34534676401586336755465607)
              ·
                refine ⟨51802014602379505133198411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34534676401586336755465607 51802014602379505133198411)
                ·
                  refine ⟨77703021903569257699797617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51802014602379505133198411 77703021903569257699797617)
                  ·
                    refine ⟨58277266427676943274848213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77703021903569257699797617 58277266427676943274848213)
                    ·
                      refine ⟨1365873431898678358004255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58277266427676943274848213 1365873431898678358004255)
                      ·
                        rfl

theorem cell23_2660029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_2660029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660029 prefixEnd_2660029 := by exact prefixLift 2660029
  have htrace : WordTrace (prefixWord ++ tailWord_2660029) baseStart_2660029 baseEnd_2660029 := by
    simpa [prefixWord, tailWord_2660029, baseEnd_2660029] using wordTrace_append hprefix tailTrace_2660029
  have hstable : (prefixWord ++ tailWord_2660029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660029).length < 2 ^ (prefixWord ++ tailWord_2660029).sum := by decide
  have hdescent : baseEnd_2660029 < baseStart_2660029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660030 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2]
def baseStart_2660030 : Nat := 118140960795 + 2660030 * 2 ^ 59
def prefixEnd_2660030 : Nat := 4983230072969 + 3 ^ 40 * 2660030 * 2
def baseEnd_2660030 : Nat := 1365873945379332854091751

theorem tailTrace_2660030 : CollatzResearch.WordTrace tailWord_2660030 prefixEnd_2660030 1365873945379332854091751 := by
  unfold tailWord_2660030
  simp only [CollatzResearch.WordTrace]
  refine ⟨12127408069146635225085193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64679509702115387867121029 12127408069146635225085193)
  ·
    refine ⟨9095556051859976418813895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12127408069146635225085193 9095556051859976418813895)
    ·
      refine ⟨13643334077789964628220843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9095556051859976418813895 13643334077789964628220843)
      ·
        refine ⟨20465001116684946942331265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13643334077789964628220843 20465001116684946942331265)
        ·
          refine ⟨15348750837513710206748449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20465001116684946942331265 15348750837513710206748449)
          ·
            refine ⟨11511563128135282655061337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15348750837513710206748449 11511563128135282655061337)
            ·
              refine ⟨8633672346101461991296003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11511563128135282655061337 8633672346101461991296003)
              ·
                refine ⟨12950508519152192986944005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8633672346101461991296003 12950508519152192986944005)
                ·
                  refine ⟨2428220347341036185052001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12950508519152192986944005 2428220347341036185052001)
                  ·
                    refine ⟨1821165260505777138789001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2428220347341036185052001 1821165260505777138789001)
                    ·
                      refine ⟨1365873945379332854091751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1821165260505777138789001 1365873945379332854091751)
                      ·
                        rfl

theorem cell23_2660030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_2660030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660030 prefixEnd_2660030 := by exact prefixLift 2660030
  have htrace : WordTrace (prefixWord ++ tailWord_2660030) baseStart_2660030 baseEnd_2660030 := by
    simpa [prefixWord, tailWord_2660030, baseEnd_2660030] using wordTrace_append hprefix tailTrace_2660030
  have hstable : (prefixWord ++ tailWord_2660030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660030).length < 2 ^ (prefixWord ++ tailWord_2660030).sum := by decide
  have hdescent : baseEnd_2660030 < baseStart_2660030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660046 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3]
def baseStart_2660046 : Nat := 118140960795 + 2660046 * 2 ^ 59
def prefixEnd_2660046 : Nat := 4983230072969 + 3 ^ 40 * 2660046 * 2
def baseEnd_2660046 : Nat := 1365882161069804791491677

theorem tailTrace_2660046 : CollatzResearch.WordTrace tailWord_2660046 prefixEnd_2660046 1365882161069804791491677 := by
  unfold tailWord_2660046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12127481015139389566657999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64679898747410077688842661 12127481015139389566657999)
  ·
    refine ⟨18191221522709084349986999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12127481015139389566657999 18191221522709084349986999)
    ·
      refine ⟨27286832284063626524980499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18191221522709084349986999 27286832284063626524980499)
      ·
        refine ⟨40930248426095439787470749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27286832284063626524980499 40930248426095439787470749)
        ·
          refine ⟨15348843159785789920301531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40930248426095439787470749 15348843159785789920301531)
          ·
            refine ⟨23023264739678684880452297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15348843159785789920301531 23023264739678684880452297)
            ·
              refine ⟨17267448554759013660339223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23023264739678684880452297 17267448554759013660339223)
              ·
                refine ⟨25901172832138520490508835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17267448554759013660339223 25901172832138520490508835)
                ·
                  refine ⟨38851759248207780735763253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25901172832138520490508835 38851759248207780735763253)
                  ·
                    refine ⟨3642352429519479443977805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38851759248207780735763253 3642352429519479443977805)
                    ·
                      refine ⟨1365882161069804791491677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3642352429519479443977805 1365882161069804791491677)
                      ·
                        rfl

theorem cell23_2660046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_2660046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660046 prefixEnd_2660046 := by exact prefixLift 2660046
  have htrace : WordTrace (prefixWord ++ tailWord_2660046) baseStart_2660046 baseEnd_2660046 := by
    simpa [prefixWord, tailWord_2660046, baseEnd_2660046] using wordTrace_append hprefix tailTrace_2660046
  have hstable : (prefixWord ++ tailWord_2660046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660046).length < 2 ^ (prefixWord ++ tailWord_2660046).sum := by decide
  have hdescent : baseEnd_2660046 < baseStart_2660046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660139 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 1, 11]
def baseStart_2660139 : Nat := 118140960795 + 2660139 * 2 ^ 59
def prefixEnd_2660139 : Nat := 4983230072969 + 3 ^ 40 * 2660139 * 2
def baseEnd_2660139 : Nat := 455309971590224309209583

theorem tailTrace_2660139 : CollatzResearch.WordTrace tailWord_2660139 prefixEnd_2660139 455309971590224309209583 := by
  unfold tailWord_2660139
  simp only [CollatzResearch.WordTrace]
  refine ⟨97023240109778193416399471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64682160073185462277599647 97023240109778193416399471)
  ·
    refine ⟨145534860164667290124599207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97023240109778193416399471 145534860164667290124599207)
    ·
      refine ⟨218302290247000935186898811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145534860164667290124599207 218302290247000935186898811)
      ·
        refine ⟨327453435370501402780348217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218302290247000935186898811 327453435370501402780348217)
        ·
          refine ⟨245590076527876052085261163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327453435370501402780348217 245590076527876052085261163)
          ·
            refine ⟨368385114791814078127891745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245590076527876052085261163 368385114791814078127891745)
            ·
              refine ⟨276288836093860558595918809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368385114791814078127891745 276288836093860558595918809)
              ·
                refine ⟨207216627070395418946939107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276288836093860558595918809 207216627070395418946939107)
                ·
                  refine ⟨310824940605593128420408661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207216627070395418946939107 310824940605593128420408661)
                  ·
                    refine ⟨455309971590224309209583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 310824940605593128420408661 455309971590224309209583)
                    ·
                      rfl

theorem cell23_2660139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 11].length) (baseStart_2660139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660139 prefixEnd_2660139 := by exact prefixLift 2660139
  have htrace : WordTrace (prefixWord ++ tailWord_2660139) baseStart_2660139 baseEnd_2660139 := by
    simpa [prefixWord, tailWord_2660139, baseEnd_2660139] using wordTrace_append hprefix tailTrace_2660139
  have hstable : (prefixWord ++ tailWord_2660139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660139).length < 2 ^ (prefixWord ++ tailWord_2660139).sum := by decide
  have hdescent : baseEnd_2660139 < baseStart_2660139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660146 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_2660146 : Nat := 118140960795 + 2660146 * 2 ^ 59
def prefixEnd_2660146 : Nat := 4983230072969 + 3 ^ 40 * 2660146 * 2
def baseEnd_2660146 : Nat := 1365933509135254400241217

theorem tailTrace_2660146 : CollatzResearch.WordTrace tailWord_2660146 prefixEnd_2660146 1365933509135254400241217 := by
  unfold tailWord_2660146
  simp only [CollatzResearch.WordTrace]
  refine ⟨24255873855188208402976073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64682330280501889074602861 24255873855188208402976073)
  ·
    refine ⟨18191905391391156302232055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24255873855188208402976073 18191905391391156302232055)
    ·
      refine ⟨27287858087086734453348083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18191905391391156302232055 27287858087086734453348083)
      ·
        refine ⟨40931787130630101680022125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27287858087086734453348083 40931787130630101680022125)
        ·
          refine ⟨15349420173986288130008297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40931787130630101680022125 15349420173986288130008297)
          ·
            refine ⟨11512065130489716097506223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15349420173986288130008297 11512065130489716097506223)
            ·
              refine ⟨17268097695734574146259335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11512065130489716097506223 17268097695734574146259335)
              ·
                refine ⟨25902146543601861219389003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17268097695734574146259335 25902146543601861219389003)
                ·
                  refine ⟨38853219815402791829083505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25902146543601861219389003 38853219815402791829083505)
                  ·
                    refine ⟨29139914861552093871812629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38853219815402791829083505 29139914861552093871812629)
                    ·
                      refine ⟨1365933509135254400241217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29139914861552093871812629 1365933509135254400241217)
                      ·
                        rfl

theorem cell23_2660146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_2660146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660146 prefixEnd_2660146 := by exact prefixLift 2660146
  have htrace : WordTrace (prefixWord ++ tailWord_2660146) baseStart_2660146 baseEnd_2660146 := by
    simpa [prefixWord, tailWord_2660146, baseEnd_2660146] using wordTrace_append hprefix tailTrace_2660146
  have hstable : (prefixWord ++ tailWord_2660146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660146).length < 2 ^ (prefixWord ++ tailWord_2660146).sum := by decide
  have hdescent : baseEnd_2660146 < baseStart_2660146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660156 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 5, 5]
def baseStart_2660156 : Nat := 118140960795 + 2660156 * 2 ^ 59
def prefixEnd_2660156 : Nat := 4983230072969 + 3 ^ 40 * 2660156 * 2
def baseEnd_2660156 : Nat := 455312881313933120372057

theorem tailTrace_2660156 : CollatzResearch.WordTrace tailWord_2660156 prefixEnd_2660156 455312881313933120372057 := by
  unfold tailWord_2660156
  simp only [CollatzResearch.WordTrace]
  refine ⟨48511930075358302659884161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64682573433811070213178881 48511930075358302659884161)
  ·
    refine ⟨36383947556518726994913121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48511930075358302659884161 36383947556518726994913121)
    ·
      refine ⟨27287960667389045246184841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36383947556518726994913121 27287960667389045246184841)
      ·
        refine ⟨20465970500541783934638631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27287960667389045246184841 20465970500541783934638631)
        ·
          refine ⟨30698955750812675901957947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20465970500541783934638631 30698955750812675901957947)
          ·
            refine ⟨46048433626219013852936921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30698955750812675901957947 46048433626219013852936921)
            ·
              refine ⟨34536325219664260389702691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46048433626219013852936921 34536325219664260389702691)
              ·
                refine ⟨51804487829496390584554037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34536325219664260389702691 51804487829496390584554037)
                ·
                  refine ⟨4856670734015286617301941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51804487829496390584554037 4856670734015286617301941)
                  ·
                    refine ⟨455312881313933120372057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4856670734015286617301941 455312881313933120372057)
                    ·
                      rfl

theorem cell23_2660156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_2660156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660156 prefixEnd_2660156 := by exact prefixLift 2660156
  have htrace : WordTrace (prefixWord ++ tailWord_2660156) baseStart_2660156 baseEnd_2660156 := by
    simpa [prefixWord, tailWord_2660156, baseEnd_2660156] using wordTrace_append hprefix tailTrace_2660156
  have hstable : (prefixWord ++ tailWord_2660156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660156).length < 2 ^ (prefixWord ++ tailWord_2660156).sum := by decide
  have hdescent : baseEnd_2660156 < baseStart_2660156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660163 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 1, 5, 2]
def baseStart_2660163 : Nat := 118140960795 + 2660163 * 2 ^ 59
def prefixEnd_2660163 : Nat := 4983230072969 + 3 ^ 40 * 2660163 * 2
def baseEnd_2660163 : Nat := 1365942238306380833728639

theorem tailTrace_2660163 : CollatzResearch.WordTrace tailWord_2660163 prefixEnd_2660163 1365942238306380833728639 := by
  unfold tailWord_2660163
  simp only [CollatzResearch.WordTrace]
  refine ⟨97024115461691245515273143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64682743641127497010182095 97024115461691245515273143)
  ·
    refine ⟨145536173192536868272909715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97024115461691245515273143 145536173192536868272909715)
    ·
      refine ⟨218304259788805302409364573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145536173192536868272909715 218304259788805302409364573)
      ·
        refine ⟨81864097420801988403511715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218304259788805302409364573 81864097420801988403511715)
        ·
          refine ⟨122796146131202982605267573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81864097420801988403511715 122796146131202982605267573)
          ·
            refine ⟨11512138699800279619243835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122796146131202982605267573 11512138699800279619243835)
            ·
              refine ⟨17268208049700419428865753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11512138699800279619243835 17268208049700419428865753)
              ·
                refine ⟨12951156037275314571649315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17268208049700419428865753 12951156037275314571649315)
                ·
                  refine ⟨19426734055912971857473973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12951156037275314571649315 19426734055912971857473973)
                  ·
                    refine ⟨1821256317741841111638185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19426734055912971857473973 1821256317741841111638185)
                    ·
                      refine ⟨1365942238306380833728639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1821256317741841111638185 1365942238306380833728639)
                      ·
                        rfl

theorem cell23_2660163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 5, 2].length) (baseStart_2660163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660163 prefixEnd_2660163 := by exact prefixLift 2660163
  have htrace : WordTrace (prefixWord ++ tailWord_2660163) baseStart_2660163 baseEnd_2660163 := by
    simpa [prefixWord, tailWord_2660163, baseEnd_2660163] using wordTrace_append hprefix tailTrace_2660163
  have hstable : (prefixWord ++ tailWord_2660163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660163).length < 2 ^ (prefixWord ++ tailWord_2660163).sum := by decide
  have hdescent : baseEnd_2660163 < baseStart_2660163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660180 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 1, 5, 2]
def baseStart_2660180 : Nat := 118140960795 + 2660180 * 2 ^ 59
def prefixEnd_2660180 : Nat := 4983230072969 + 3 ^ 40 * 2660180 * 2
def baseEnd_2660180 : Nat := 1365950967477507267216061

theorem tailTrace_2660180 : CollatzResearch.WordTrace tailWord_2660180 prefixEnd_2660180 1365950967477507267216061 := by
  unfold tailWord_2660180
  simp only [CollatzResearch.WordTrace]
  refine ⟨48512367751314828709320997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64683157001753104945761329 48512367751314828709320997)
  ·
    refine ⟨9096068953371530382997687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48512367751314828709320997 9096068953371530382997687)
    ·
      refine ⟨13644103430057295574496531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9096068953371530382997687 13644103430057295574496531)
      ·
        refine ⟨20466155145085943361744797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13644103430057295574496531 20466155145085943361744797)
        ·
          refine ⟨7674808179407228760654299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20466155145085943361744797 7674808179407228760654299)
          ·
            refine ⟨11512212269110843140981449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7674808179407228760654299 11512212269110843140981449)
            ·
              refine ⟨8634159201833132355736087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11512212269110843140981449 8634159201833132355736087)
              ·
                refine ⟨12951238802749698533604131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8634159201833132355736087 12951238802749698533604131)
                ·
                  refine ⟨19426858204124547800406197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12951238802749698533604131 19426858204124547800406197)
                  ·
                    refine ⟨1821267956636676356288081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19426858204124547800406197 1821267956636676356288081)
                    ·
                      refine ⟨1365950967477507267216061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1821267956636676356288081 1365950967477507267216061)
                      ·
                        rfl

theorem cell23_2660180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_2660180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660180 prefixEnd_2660180 := by exact prefixLift 2660180
  have htrace : WordTrace (prefixWord ++ tailWord_2660180) baseStart_2660180 baseEnd_2660180 := by
    simpa [prefixWord, tailWord_2660180, baseEnd_2660180] using wordTrace_append hprefix tailTrace_2660180
  have hstable : (prefixWord ++ tailWord_2660180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660180).length < 2 ^ (prefixWord ++ tailWord_2660180).sum := by decide
  have hdescent : baseEnd_2660180 < baseStart_2660180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660186 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 3, 6]
def baseStart_2660186 : Nat := 118140960795 + 2660186 * 2 ^ 59
def prefixEnd_2660186 : Nat := 4983230072969 + 3 ^ 40 * 2660186 * 2
def baseEnd_2660186 : Nat := 455318016120478081247011

theorem tailTrace_2660186 : CollatzResearch.WordTrace tailWord_2660186 prefixEnd_2660186 455318016120478081247011 := by
  unfold tailWord_2660186
  simp only [CollatzResearch.WordTrace]
  refine ⟨24256238585151980110840103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64683302893738613628906941 24256238585151980110840103)
  ·
    refine ⟨36384357877727970166260155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24256238585151980110840103 36384357877727970166260155)
    ·
      refine ⟨54576536816591955249390233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36384357877727970166260155 54576536816591955249390233)
      ·
        refine ⟨40932402612443966437042675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54576536816591955249390233 40932402612443966437042675)
        ·
          refine ⟨61398603918665949655564013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40932402612443966437042675 61398603918665949655564013)
          ·
            refine ⟨23024476469499731120836505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61398603918665949655564013 23024476469499731120836505)
            ·
              refine ⟨17268357352124798340627379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23024476469499731120836505 17268357352124798340627379)
              ·
                refine ⟨25902536028187197510941069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17268357352124798340627379 25902536028187197510941069)
                ·
                  refine ⟨9713451010570199066602901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25902536028187197510941069 9713451010570199066602901)
                  ·
                    refine ⟨455318016120478081247011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9713451010570199066602901 455318016120478081247011)
                    ·
                      rfl

theorem cell23_2660186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_2660186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660186 prefixEnd_2660186 := by exact prefixLift 2660186
  have htrace : WordTrace (prefixWord ++ tailWord_2660186) baseStart_2660186 baseEnd_2660186 := by
    simpa [prefixWord, tailWord_2660186, baseEnd_2660186] using wordTrace_append hprefix tailTrace_2660186
  have hstable : (prefixWord ++ tailWord_2660186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660186).length < 2 ^ (prefixWord ++ tailWord_2660186).sum := by decide
  have hdescent : baseEnd_2660186 < baseStart_2660186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660193 : List Nat := [1, 2, 3, 1, 1, 1, 3, 5, 1, 1, 4]
def baseStart_2660193 : Nat := 118140960795 + 2660193 * 2 ^ 59
def prefixEnd_2660193 : Nat := 4983230072969 + 3 ^ 40 * 2660193 * 2
def baseEnd_2660193 : Nat := 1365957642726015716353501

theorem tailTrace_2660193 : CollatzResearch.WordTrace tailWord_2660193 prefixEnd_2660193 1365957642726015716353501 := by
  unfold tailWord_2660193
  simp only [CollatzResearch.WordTrace]
  refine ⟨97025209651582560638865233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64683473101055040425910155 97025209651582560638865233)
  ·
    refine ⟨72768907238686920479148925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97025209651582560638865233 72768907238686920479148925)
    ·
      refine ⟨27288340214507595179680847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72768907238686920479148925 27288340214507595179680847)
      ·
        refine ⟨40932510321761392769521271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27288340214507595179680847 40932510321761392769521271)
        ·
          refine ⟨61398765482642089154281907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40932510321761392769521271 61398765482642089154281907)
          ·
            refine ⟨92098148223963133731422861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61398765482642089154281907 92098148223963133731422861)
            ·
              refine ⟨34536805583986175149283573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92098148223963133731422861 34536805583986175149283573)
              ·
                refine ⟨3237825523498703920245335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34536805583986175149283573 3237825523498703920245335)
                ·
                  refine ⟨4856738285248055880368003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3237825523498703920245335 4856738285248055880368003)
                  ·
                    refine ⟨7285107427872083820552005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4856738285248055880368003 7285107427872083820552005)
                    ·
                      refine ⟨1365957642726015716353501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7285107427872083820552005 1365957642726015716353501)
                      ·
                        rfl

theorem cell23_2660193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_2660193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660193 prefixEnd_2660193 := by exact prefixLift 2660193
  have htrace : WordTrace (prefixWord ++ tailWord_2660193) baseStart_2660193 baseEnd_2660193 := by
    simpa [prefixWord, tailWord_2660193, baseEnd_2660193] using wordTrace_append hprefix tailTrace_2660193
  have hstable : (prefixWord ++ tailWord_2660193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660193).length < 2 ^ (prefixWord ++ tailWord_2660193).sum := by decide
  have hdescent : baseEnd_2660193 < baseStart_2660193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660203 : List Nat := [1, 1, 1, 1, 2, 2, 3, 6, 2, 4]
def baseStart_2660203 : Nat := 118140960795 + 2660203 * 2 ^ 59
def prefixEnd_2660203 : Nat := 4983230072969 + 3 ^ 40 * 2660203 * 2
def baseEnd_2660203 : Nat := 455320925844186892409485

theorem tailTrace_2660203 : CollatzResearch.WordTrace tailWord_2660203 prefixEnd_2660203 455320925844186892409485 := by
  unfold tailWord_2660203
  simp only [CollatzResearch.WordTrace]
  refine ⟨97025574381546332346729263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64683716254364221564486175 97025574381546332346729263)
  ·
    refine ⟨145538361572319498520093895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97025574381546332346729263 145538361572319498520093895)
    ·
      refine ⟨218307542358479247780140843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145538361572319498520093895 218307542358479247780140843)
      ·
        refine ⟨327461313537718871670211265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218307542358479247780140843 327461313537718871670211265)
        ·
          refine ⟨245595985153289153752658449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327461313537718871670211265 245595985153289153752658449)
          ·
            refine ⟨184196988864966865314493837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245595985153289153752658449 184196988864966865314493837)
            ·
              refine ⟨69073870824362574492935189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184196988864966865314493837 69073870824362574492935189)
              ·
                refine ⟨3237837694891995679356337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69073870824362574492935189 3237837694891995679356337)
                ·
                  refine ⟨2428378271168996759517253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3237837694891995679356337 2428378271168996759517253)
                  ·
                    refine ⟨455320925844186892409485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2428378271168996759517253 455320925844186892409485)
                    ·
                      rfl

theorem cell23_2660203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 4].length) (baseStart_2660203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660203 prefixEnd_2660203 := by exact prefixLift 2660203
  have htrace : WordTrace (prefixWord ++ tailWord_2660203) baseStart_2660203 baseEnd_2660203 := by
    simpa [prefixWord, tailWord_2660203, baseEnd_2660203] using wordTrace_append hprefix tailTrace_2660203
  have hstable : (prefixWord ++ tailWord_2660203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660203).length < 2 ^ (prefixWord ++ tailWord_2660203).sum := by decide
  have hdescent : baseEnd_2660203 < baseStart_2660203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660204 : List Nat := [2, 2, 1, 1, 4, 3, 3, 2, 1, 1, 3]
def baseStart_2660204 : Nat := 118140960795 + 2660204 * 2 ^ 59
def prefixEnd_2660204 : Nat := 4983230072969 + 3 ^ 40 * 2660204 * 2
def baseEnd_2660204 : Nat := 1365963291013215173315951

theorem tailTrace_2660204 : CollatzResearch.WordTrace tailWord_2660204 prefixEnd_2660204 1365963291013215173315951 := by
  unfold tailWord_2660204
  simp only [CollatzResearch.WordTrace]
  refine ⟨48512805427271354758757833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64683740569695139678343777 48512805427271354758757833)
  ·
    refine ⟨36384604070453516069068375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48512805427271354758757833 36384604070453516069068375)
    ·
      refine ⟨54576906105680274103602563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36384604070453516069068375 54576906105680274103602563)
      ·
        refine ⟨81865359158520411155403845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54576906105680274103602563 81865359158520411155403845)
        ·
          refine ⟨15349754842222577091638221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81865359158520411155403845 15349754842222577091638221)
          ·
            refine ⟨5756158065833466409364333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15349754842222577091638221 5756158065833466409364333)
            ·
              refine ⟨2158559274687549903511625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5756158065833466409364333 2158559274687549903511625)
              ·
                refine ⟨1618919456015662427633719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2158559274687549903511625 1618919456015662427633719)
                ·
                  refine ⟨2428379184023493641450579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1618919456015662427633719 2428379184023493641450579)
                  ·
                    refine ⟨3642568776035240462175869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2428379184023493641450579 3642568776035240462175869)
                    ·
                      refine ⟨1365963291013215173315951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3642568776035240462175869 1365963291013215173315951)
                      ·
                        rfl

theorem cell23_2660204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 1, 1, 3].length) (baseStart_2660204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660204 prefixEnd_2660204 := by exact prefixLift 2660204
  have htrace : WordTrace (prefixWord ++ tailWord_2660204) baseStart_2660204 baseEnd_2660204 := by
    simpa [prefixWord, tailWord_2660204, baseEnd_2660204] using wordTrace_append hprefix tailTrace_2660204
  have hstable : (prefixWord ++ tailWord_2660204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660204).length < 2 ^ (prefixWord ++ tailWord_2660204).sum := by decide
  have hdescent : baseEnd_2660204 < baseStart_2660204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660213 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_2660213 : Nat := 118140960795 + 2660213 * 2 ^ 59
def prefixEnd_2660213 : Nat := 4983230072969 + 3 ^ 40 * 2660213 * 2
def baseEnd_2660213 : Nat := 1365967912339105638103409

theorem tailTrace_2660213 : CollatzResearch.WordTrace tailWord_2660213 prefixEnd_2660213 1365967912339105638103409 := by
  unfold tailWord_2660213
  simp only [CollatzResearch.WordTrace]
  refine ⟨97025939111510104054593293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64683959407673402703062195 97025939111510104054593293)
  ·
    refine ⟨36384727166816289020472485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97025939111510104054593293 36384727166816289020472485)
    ·
      refine ⟨6822136343778054191338591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36384727166816289020472485 6822136343778054191338591)
      ·
        refine ⟨10233204515667081287007887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6822136343778054191338591 10233204515667081287007887)
        ·
          refine ⟨15349806773500621930511831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10233204515667081287007887 15349806773500621930511831)
          ·
            refine ⟨23024710160250932895767747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15349806773500621930511831 23024710160250932895767747)
            ·
              refine ⟨34537065240376399343651621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23024710160250932895767747 34537065240376399343651621)
              ·
                refine ⟨6475699732570574876934679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34537065240376399343651621 6475699732570574876934679)
                ·
                  refine ⟨9713549598855862315402019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6475699732570574876934679 9713549598855862315402019)
                  ·
                    refine ⟨14570324398283793473103029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9713549598855862315402019 14570324398283793473103029)
                    ·
                      refine ⟨1365967912339105638103409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14570324398283793473103029 1365967912339105638103409)
                      ·
                        rfl

theorem cell23_2660213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_2660213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660213 prefixEnd_2660213 := by exact prefixLift 2660213
  have htrace : WordTrace (prefixWord ++ tailWord_2660213) baseStart_2660213 baseEnd_2660213 := by
    simpa [prefixWord, tailWord_2660213, baseEnd_2660213] using wordTrace_append hprefix tailTrace_2660213
  have hstable : (prefixWord ++ tailWord_2660213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660213).length < 2 ^ (prefixWord ++ tailWord_2660213).sum := by decide
  have hdescent : baseEnd_2660213 < baseStart_2660213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660247 : List Nat := [1, 1, 3, 3, 1, 4, 3, 1, 1, 2, 3]
def baseStart_2660247 : Nat := 118140960795 + 2660247 * 2 ^ 59
def prefixEnd_2660247 : Nat := 4983230072969 + 3 ^ 40 * 2660247 * 2
def baseEnd_2660247 : Nat := 1365985370681358505078253

theorem tailTrace_2660247 : CollatzResearch.WordTrace tailWord_2660247 prefixEnd_2660247 1365985370681358505078253 := by
  unfold tailWord_2660247
  simp only [CollatzResearch.WordTrace]
  refine ⟨97027179193386927861330995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64684786128924618574220663 97027179193386927861330995)
  ·
    refine ⟨145540768790080391791996493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97027179193386927861330995 145540768790080391791996493)
    ·
      refine ⟨54577788296280146921998685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145540768790080391791996493 54577788296280146921998685)
      ·
        refine ⟨20466670611105055095749507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54577788296280146921998685 20466670611105055095749507)
        ·
          refine ⟨30700005916657582643624261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20466670611105055095749507 30700005916657582643624261)
          ·
            refine ⟨5756251109373296745679549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30700005916657582643624261 5756251109373296745679549)
            ·
              refine ⟨2158594166014986279629831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5756251109373296745679549 2158594166014986279629831)
              ·
                refine ⟨3237891249022479419444747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2158594166014986279629831 3237891249022479419444747)
                ·
                  refine ⟨4856836873533719129167121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3237891249022479419444747 4856836873533719129167121)
                  ·
                    refine ⟨3642627655150289346875341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4856836873533719129167121 3642627655150289346875341)
                    ·
                      refine ⟨1365985370681358505078253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3642627655150289346875341 1365985370681358505078253)
                      ·
                        rfl

theorem cell23_2660247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_2660247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660247 prefixEnd_2660247 := by exact prefixLift 2660247
  have htrace : WordTrace (prefixWord ++ tailWord_2660247) baseStart_2660247 baseEnd_2660247 := by
    simpa [prefixWord, tailWord_2660247, baseEnd_2660247] using wordTrace_append hprefix tailTrace_2660247
  have hstable : (prefixWord ++ tailWord_2660247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660247).length < 2 ^ (prefixWord ++ tailWord_2660247).sum := by decide
  have hdescent : baseEnd_2660247 < baseStart_2660247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660263 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 2, 7]
def baseStart_2660263 : Nat := 118140960795 + 2660263 * 2 ^ 59
def prefixEnd_2660263 : Nat := 4983230072969 + 3 ^ 40 * 2660263 * 2
def baseEnd_2660263 : Nat := 455331195457276814159393

theorem tailTrace_2660263 : CollatzResearch.WordTrace tailWord_2660263 prefixEnd_2660263 455331195457276814159393 := by
  unfold tailWord_2660263
  simp only [CollatzResearch.WordTrace]
  refine ⟨97027762761328962593913443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64685175174219308395942295 97027762761328962593913443)
  ·
    refine ⟨145541644141993443890870165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97027762761328962593913443 145541644141993443890870165)
    ·
      refine ⟨6822264569155942682384539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 145541644141993443890870165 6822264569155942682384539)
      ·
        refine ⟨10233396853733914023576809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6822264569155942682384539 10233396853733914023576809)
        ·
          refine ⟨7675047640300435517682607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10233396853733914023576809 7675047640300435517682607)
          ·
            refine ⟨11512571460450653276523911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7675047640300435517682607 11512571460450653276523911)
            ·
              refine ⟨17268857190675979914785867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11512571460450653276523911 17268857190675979914785867)
              ·
                refine ⟨25903285786013969872178801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17268857190675979914785867 25903285786013969872178801)
                ·
                  refine ⟨19427464339510477404134101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25903285786013969872178801 19427464339510477404134101)
                  ·
                    refine ⟨455331195457276814159393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19427464339510477404134101 455331195457276814159393)
                    ·
                      rfl

theorem cell23_2660263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_2660263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660263 prefixEnd_2660263 := by exact prefixLift 2660263
  have htrace : WordTrace (prefixWord ++ tailWord_2660263) baseStart_2660263 baseEnd_2660263 := by
    simpa [prefixWord, tailWord_2660263, baseEnd_2660263] using wordTrace_append hprefix tailTrace_2660263
  have hstable : (prefixWord ++ tailWord_2660263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660263).length < 2 ^ (prefixWord ++ tailWord_2660263).sum := by decide
  have hdescent : baseEnd_2660263 < baseStart_2660263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660277 : List Nat := [1, 3, 3, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_2660277 : Nat := 118140960795 + 2660277 * 2 ^ 59
def prefixEnd_2660277 : Nat := 4983230072969 + 3 ^ 40 * 2660277 * 2
def baseEnd_2660277 : Nat := 1366000775100993387703115

theorem tailTrace_2660277 : CollatzResearch.WordTrace tailWord_2660277 prefixEnd_2660277 1366000775100993387703115 := by
  unfold tailWord_2660277
  simp only [CollatzResearch.WordTrace]
  refine ⟨97028273383278242984923085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64685515588852161989948723 97028273383278242984923085)
  ·
    refine ⟨36385602518729341119346157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97028273383278242984923085 36385602518729341119346157)
    ·
      refine ⟨13644600944523502919754809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36385602518729341119346157 13644600944523502919754809)
      ·
        refine ⟨10233450708392627189816107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13644600944523502919754809 10233450708392627189816107)
        ·
          refine ⟨15350176062588940784724161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10233450708392627189816107 15350176062588940784724161)
          ·
            refine ⟨11512632046941705588543121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15350176062588940784724161 11512632046941705588543121)
            ·
              refine ⟨8634474035206279191407341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11512632046941705588543121 8634474035206279191407341)
              ·
                refine ⟨3237927763202354696777753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8634474035206279191407341 3237927763202354696777753)
                ·
                  refine ⟨2428445822401766022583315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3237927763202354696777753 2428445822401766022583315)
                  ·
                    refine ⟨3642668733602649033874973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2428445822401766022583315 3642668733602649033874973)
                    ·
                      refine ⟨1366000775100993387703115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3642668733602649033874973 1366000775100993387703115)
                      ·
                        rfl

theorem cell23_2660277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_2660277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660277 prefixEnd_2660277 := by exact prefixLift 2660277
  have htrace : WordTrace (prefixWord ++ tailWord_2660277) baseStart_2660277 baseEnd_2660277 := by
    simpa [prefixWord, tailWord_2660277, baseEnd_2660277] using wordTrace_append hprefix tailTrace_2660277
  have hstable : (prefixWord ++ tailWord_2660277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660277).length < 2 ^ (prefixWord ++ tailWord_2660277).sum := by decide
  have hdescent : baseEnd_2660277 < baseStart_2660277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660323 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 7]
def baseStart_2660323 : Nat := 118140960795 + 2660323 * 2 ^ 59
def prefixEnd_2660323 : Nat := 4983230072969 + 3 ^ 40 * 2660323 * 2
def baseEnd_2660323 : Nat := 151780488356788911969767

theorem tailTrace_2660323 : CollatzResearch.WordTrace tailWord_2660323 prefixEnd_2660323 151780488356788911969767 := by
  unfold tailWord_2660323
  simp only [CollatzResearch.WordTrace]
  refine ⟨97029951141111592841097623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64686634094074395227398415 97029951141111592841097623)
  ·
    refine ⟨145544926711667389261646435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97029951141111592841097623 145544926711667389261646435)
    ·
      refine ⟨218317390067501083892469653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145544926711667389261646435 218317390067501083892469653)
      ·
        refine ⟨10233627659414113307459515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 218317390067501083892469653 10233627659414113307459515)
        ·
          refine ⟨15350441489121169961189273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10233627659414113307459515 15350441489121169961189273)
          ·
            refine ⟨11512831116840877470891955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15350441489121169961189273 11512831116840877470891955)
            ·
              refine ⟨17269246675261316206337933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11512831116840877470891955 17269246675261316206337933)
              ·
                refine ⟨6475967503222993577376725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17269246675261316206337933 6475967503222993577376725)
                ·
                  refine ⟨151780488356788911969767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6475967503222993577376725 151780488356788911969767)
                  ·
                    rfl

theorem cell23_2660323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 7].length) (baseStart_2660323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660323 prefixEnd_2660323 := by exact prefixLift 2660323
  have htrace : WordTrace (prefixWord ++ tailWord_2660323) baseStart_2660323 baseEnd_2660323 := by
    simpa [prefixWord, tailWord_2660323, baseEnd_2660323] using wordTrace_append hprefix tailTrace_2660323
  have hstable : (prefixWord ++ tailWord_2660323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660323).length < 2 ^ (prefixWord ++ tailWord_2660323).sum := by decide
  have hdescent : baseEnd_2660323 < baseStart_2660323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660334 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 1, 4, 2]
def baseStart_2660334 : Nat := 118140960795 + 2660334 * 2 ^ 59
def prefixEnd_2660334 : Nat := 4983230072969 + 3 ^ 40 * 2660334 * 2
def baseEnd_2660334 : Nat := 1366030043498299664690353

theorem tailTrace_2660334 : CollatzResearch.WordTrace tailWord_2660334 prefixEnd_2660334 1366030043498299664690353 := by
  unfold tailWord_2660334
  simp only [CollatzResearch.WordTrace]
  refine ⟨12128794043008967714968507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64686901562714494479832037 12128794043008967714968507)
  ·
    refine ⟨18193191064513451572452761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12128794043008967714968507 18193191064513451572452761)
    ·
      refine ⟨13644893298385088679339571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18193191064513451572452761 13644893298385088679339571)
      ·
        refine ⟨20467339947577633019009357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13644893298385088679339571 20467339947577633019009357)
        ·
          refine ⟨7675252480341612382128509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20467339947577633019009357 7675252480341612382128509)
          ·
            refine ⟨2878219680128104643298191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7675252480341612382128509 2878219680128104643298191)
            ·
              refine ⟨4317329520192156964947287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2878219680128104643298191 4317329520192156964947287)
              ·
                refine ⟨6475994280288235447420931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4317329520192156964947287 6475994280288235447420931)
                ·
                  refine ⟨9713991420432353171131397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6475994280288235447420931 9713991420432353171131397)
                  ·
                    refine ⟨1821373391331066219587137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9713991420432353171131397 1821373391331066219587137)
                    ·
                      refine ⟨1366030043498299664690353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1821373391331066219587137 1366030043498299664690353)
                      ·
                        rfl

theorem cell23_2660334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_2660334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660334 prefixEnd_2660334 := by exact prefixLift 2660334
  have htrace : WordTrace (prefixWord ++ tailWord_2660334) baseStart_2660334 baseEnd_2660334 := by
    simpa [prefixWord, tailWord_2660334, baseEnd_2660334] using wordTrace_append hprefix tailTrace_2660334
  have hstable : (prefixWord ++ tailWord_2660334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660334).length < 2 ^ (prefixWord ++ tailWord_2660334).sum := by decide
  have hdescent : baseEnd_2660334 < baseStart_2660334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660353 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 1, 7]
def baseStart_2660353 : Nat := 118140960795 + 2660353 * 2 ^ 59
def prefixEnd_2660353 : Nat := 4983230072969 + 3 ^ 40 * 2660353 * 2
def baseEnd_2660353 : Nat := 455346599876911696784255

theorem tailTrace_2660353 : CollatzResearch.WordTrace tailWord_2660353 prefixEnd_2660353 455346599876911696784255 := by
  unfold tailWord_2660353
  simp only [CollatzResearch.WordTrace]
  refine ⟨97031045331002907964689713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64687363554001938643126475 97031045331002907964689713)
  ·
    refine ⟨72773283998252180973517285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97031045331002907964689713 72773283998252180973517285)
    ·
      refine ⟨13644990749672283932534491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72773283998252180973517285 13644990749672283932534491)
      ·
        refine ⟨20467486124508425898801737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13644990749672283932534491 20467486124508425898801737)
        ·
          refine ⟨15350614593381319424101303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20467486124508425898801737 15350614593381319424101303)
          ·
            refine ⟨23025921890071979136151955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15350614593381319424101303 23025921890071979136151955)
            ·
              refine ⟨34538882835107968704227933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23025921890071979136151955 34538882835107968704227933)
              ·
                refine ⟨12952081063165488264085475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34538882835107968704227933 12952081063165488264085475)
                ·
                  refine ⟨19428121594748232396128213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12952081063165488264085475 19428121594748232396128213)
                  ·
                    refine ⟨455346599876911696784255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19428121594748232396128213 455346599876911696784255)
                    ·
                      rfl

theorem cell23_2660353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_2660353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660353 prefixEnd_2660353 := by exact prefixLift 2660353
  have htrace : WordTrace (prefixWord ++ tailWord_2660353) baseStart_2660353 baseEnd_2660353 := by
    simpa [prefixWord, tailWord_2660353, baseEnd_2660353] using wordTrace_append hprefix tailTrace_2660353
  have hstable : (prefixWord ++ tailWord_2660353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660353).length < 2 ^ (prefixWord ++ tailWord_2660353).sum := by decide
  have hdescent : baseEnd_2660353 < baseStart_2660353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660357 : List Nat := [1, 3, 1, 1, 2, 6, 1, 3, 5]
def baseStart_2660357 : Nat := 118140960795 + 2660357 * 2 ^ 59
def prefixEnd_2660357 : Nat := 4983230072969 + 3 ^ 40 * 2660357 * 2
def baseEnd_2660357 : Nat := 151782428172594786078083

theorem tailTrace_2660357 : CollatzResearch.WordTrace tailWord_2660357 prefixEnd_2660357 151782428172594786078083 := by
  unfold tailWord_2660357
  simp only [CollatzResearch.WordTrace]
  refine ⟨97031191222988416647835325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64687460815325611098556883 97031191222988416647835325)
  ·
    refine ⟨36386696708620656242938247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97031191222988416647835325 36386696708620656242938247)
    ·
      refine ⟨54580045062930984364407371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36386696708620656242938247 54580045062930984364407371)
      ·
        refine ⟨81870067594396476546611057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54580045062930984364407371 81870067594396476546611057)
        ·
          refine ⟨61402550695797357409958293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81870067594396476546611057 61402550695797357409958293)
          ·
            refine ⟨2878244563865501128591795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61402550695797357409958293 2878244563865501128591795)
            ·
              refine ⟨4317366845798251692887693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2878244563865501128591795 4317366845798251692887693)
              ·
                refine ⟨1619012567174344384832885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4317366845798251692887693 1619012567174344384832885)
                ·
                  refine ⟨151782428172594786078083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1619012567174344384832885 151782428172594786078083)
                  ·
                    rfl

theorem cell23_2660357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 5].length) (baseStart_2660357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660357 prefixEnd_2660357 := by exact prefixLift 2660357
  have htrace : WordTrace (prefixWord ++ tailWord_2660357) baseStart_2660357 baseEnd_2660357 := by
    simpa [prefixWord, tailWord_2660357, baseEnd_2660357] using wordTrace_append hprefix tailTrace_2660357
  have hstable : (prefixWord ++ tailWord_2660357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660357).length < 2 ^ (prefixWord ++ tailWord_2660357).sum := by decide
  have hdescent : baseEnd_2660357 < baseStart_2660357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660363 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 5]
def baseStart_2660363 : Nat := 118140960795 + 2660363 * 2 ^ 59
def prefixEnd_2660363 : Nat := 4983230072969 + 3 ^ 40 * 2660363 * 2
def baseEnd_2660363 : Nat := 1366044934437280051227719

theorem tailTrace_2660363 : CollatzResearch.WordTrace tailWord_2660363 prefixEnd_2660363 1366044934437280051227719 := by
  unfold tailWord_2660363
  simp only [CollatzResearch.WordTrace]
  refine ⟨97031410060966679672553743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64687606707311119781702495 97031410060966679672553743)
  ·
    refine ⟨145547115091450019508830615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97031410060966679672553743 145547115091450019508830615)
    ·
      refine ⟨218320672637175029263245923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145547115091450019508830615 218320672637175029263245923)
      ·
        refine ⟨327481008955762543894868885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218320672637175029263245923 327481008955762543894868885)
        ·
          refine ⟨15350672294801369245071979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 327481008955762543894868885 15350672294801369245071979)
          ·
            refine ⟨23026008442202053867607969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15350672294801369245071979 23026008442202053867607969)
            ·
              refine ⟨17269506331651540400705977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23026008442202053867607969 17269506331651540400705977)
              ·
                refine ⟨12952129748738655300529483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17269506331651540400705977 12952129748738655300529483)
                ·
                  refine ⟨19428194623107982950794225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12952129748738655300529483 19428194623107982950794225)
                  ·
                    refine ⟨14571145967330987213095669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19428194623107982950794225 14571145967330987213095669)
                    ·
                      refine ⟨1366044934437280051227719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14571145967330987213095669 1366044934437280051227719)
                      ·
                        rfl

theorem cell23_2660363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 5].length) (baseStart_2660363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660363 prefixEnd_2660363 := by exact prefixLift 2660363
  have htrace : WordTrace (prefixWord ++ tailWord_2660363) baseStart_2660363 baseEnd_2660363 := by
    simpa [prefixWord, tailWord_2660363, baseEnd_2660363] using wordTrace_append hprefix tailTrace_2660363
  have hstable : (prefixWord ++ tailWord_2660363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660363).length < 2 ^ (prefixWord ++ tailWord_2660363).sum := by decide
  have hdescent : baseEnd_2660363 < baseStart_2660363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660380 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_2660380 : Nat := 118140960795 + 2660380 * 2 ^ 59
def prefixEnd_2660380 : Nat := 4983230072969 + 3 ^ 40 * 2660380 * 2
def baseEnd_2660380 : Nat := 1366053663608406484715141

theorem tailTrace_2660380 : CollatzResearch.WordTrace tailWord_2660380 prefixEnd_2660380 1366053663608406484715141 := by
  unfold tailWord_2660380
  simp only [CollatzResearch.WordTrace]
  refine ⟨48516015050952545787961297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64688020067936727717281729 48516015050952545787961297)
  ·
    refine ⟨36387011288214409340970973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48516015050952545787961297 36387011288214409340970973)
    ·
      refine ⟨13645129233080403502864115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36387011288214409340970973 13645129233080403502864115)
      ·
        refine ⟨20467693849620605254296173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13645129233080403502864115 20467693849620605254296173)
        ·
          refine ⟨7675385193607726970361065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20467693849620605254296173 7675385193607726970361065)
          ·
            refine ⟨5756538895205795227770799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7675385193607726970361065 5756538895205795227770799)
            ·
              refine ⟨8634808342808692841656199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5756538895205795227770799 8634808342808692841656199)
              ·
                refine ⟨12952212514213039262484299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8634808342808692841656199 12952212514213039262484299)
                ·
                  refine ⟨19428318771319558893726449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12952212514213039262484299 19428318771319558893726449)
                  ·
                    refine ⟨14571239078489669170294837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19428318771319558893726449 14571239078489669170294837)
                    ·
                      refine ⟨1366053663608406484715141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14571239078489669170294837 1366053663608406484715141)
                      ·
                        rfl

theorem cell23_2660380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_2660380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660380 prefixEnd_2660380 := by exact prefixLift 2660380
  have htrace : WordTrace (prefixWord ++ tailWord_2660380) baseStart_2660380 baseEnd_2660380 := by
    simpa [prefixWord, tailWord_2660380, baseEnd_2660380] using wordTrace_append hprefix tailTrace_2660380
  have hstable : (prefixWord ++ tailWord_2660380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660380).length < 2 ^ (prefixWord ++ tailWord_2660380).sum := by decide
  have hdescent : baseEnd_2660380 < baseStart_2660380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660403 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 4]
def baseStart_2660403 : Nat := 118140960795 + 2660403 * 2 ^ 59
def prefixEnd_2660403 : Nat := 4983230072969 + 3 ^ 40 * 2660403 * 2
def baseEnd_2660403 : Nat := 1366065473663459894727535

theorem tailTrace_2660403 : CollatzResearch.WordTrace tailWord_2660403 prefixEnd_2660403 1366065473663459894727535 := by
  unfold tailWord_2660403
  simp only [CollatzResearch.WordTrace]
  refine ⟨97032868980821766504009863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64688579320547844336006575 97032868980821766504009863)
  ·
    refine ⟨145549303471232649756014795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97032868980821766504009863 145549303471232649756014795)
    ·
      refine ⟨218323955206848974634022193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145549303471232649756014795 218323955206848974634022193)
      ·
        refine ⟨163742966405136730975516645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218323955206848974634022193 163742966405136730975516645)
        ·
          refine ⟨30701806200963137057909371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163742966405136730975516645 30701806200963137057909371)
          ·
            refine ⟨46052709301444705586864057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30701806200963137057909371 46052709301444705586864057)
            ·
              refine ⟨34539531976083529190148043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46052709301444705586864057 34539531976083529190148043)
              ·
                refine ⟨51809297964125293785222065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34539531976083529190148043 51809297964125293785222065)
                ·
                  refine ⟨38856973473093970338916549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51809297964125293785222065 38856973473093970338916549)
                  ·
                    refine ⟨7285682526205119438546853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38856973473093970338916549 7285682526205119438546853)
                    ·
                      refine ⟨1366065473663459894727535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7285682526205119438546853 1366065473663459894727535)
                      ·
                        rfl

theorem cell23_2660403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_2660403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660403 prefixEnd_2660403 := by exact prefixLift 2660403
  have htrace : WordTrace (prefixWord ++ tailWord_2660403) baseStart_2660403 baseEnd_2660403 := by
    simpa [prefixWord, tailWord_2660403, baseEnd_2660403] using wordTrace_append hprefix tailTrace_2660403
  have hstable : (prefixWord ++ tailWord_2660403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660403).length < 2 ^ (prefixWord ++ tailWord_2660403).sum := by decide
  have hdescent : baseEnd_2660403 < baseStart_2660403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660404 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_2660404 : Nat := 118140960795 + 2660404 * 2 ^ 59
def prefixEnd_2660404 : Nat := 4983230072969 + 3 ^ 40 * 2660404 * 2
def baseEnd_2660404 : Nat := 455355329048038130271677

theorem tailTrace_2660404 : CollatzResearch.WordTrace tailWord_2660404 prefixEnd_2660404 455355329048038130271677 := by
  unfold tailWord_2660404
  simp only [CollatzResearch.WordTrace]
  refine ⟨48516452726909071837398133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64688603635878762449864177 48516452726909071837398133)
  ·
    refine ⟨4548417443147725484756075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48516452726909071837398133 4548417443147725484756075)
    ·
      refine ⟨6822626164721588227134113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4548417443147725484756075 6822626164721588227134113)
      ·
        refine ⟨5116969623541191170350585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6822626164721588227134113 5116969623541191170350585)
        ·
          refine ⟨3837727217655893377762939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5116969623541191170350585 3837727217655893377762939)
          ·
            refine ⟨5756590826483840066644409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3837727217655893377762939 5756590826483840066644409)
            ·
              refine ⟨4317443119862880049983307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5756590826483840066644409 4317443119862880049983307)
              ·
                refine ⟨6476164679794320074974961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4317443119862880049983307 6476164679794320074974961)
                ·
                  refine ⟨4857123509845740056231221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6476164679794320074974961 4857123509845740056231221)
                  ·
                    refine ⟨455355329048038130271677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4857123509845740056231221 455355329048038130271677)
                    ·
                      rfl

theorem cell23_2660404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_2660404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660404 prefixEnd_2660404 := by exact prefixLift 2660404
  have htrace : WordTrace (prefixWord ++ tailWord_2660404) baseStart_2660404 baseEnd_2660404 := by
    simpa [prefixWord, tailWord_2660404, baseEnd_2660404] using wordTrace_append hprefix tailTrace_2660404
  have hstable : (prefixWord ++ tailWord_2660404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660404).length < 2 ^ (prefixWord ++ tailWord_2660404).sum := by decide
  have hdescent : baseEnd_2660404 < baseStart_2660404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660430 : List Nat := [4, 1, 1, 1, 1, 4, 1, 4, 6]
def baseStart_2660430 : Nat := 118140960795 + 2660430 * 2 ^ 59
def prefixEnd_2660430 : Nat := 4983230072969 + 3 ^ 40 * 2660430 * 2
def baseEnd_2660430 : Nat := 151786593071236809898879

theorem tailTrace_2660430 : CollatzResearch.WordTrace tailWord_2660430 prefixEnd_2660430 151786593071236809898879 := by
  unfold tailWord_2660430
  simp only [CollatzResearch.WordTrace]
  refine ⟨12129231718965493764405343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64689235834482633410161829 12129231718965493764405343)
  ·
    refine ⟨18193847578448240646608015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12129231718965493764405343 18193847578448240646608015)
    ·
      refine ⟨27290771367672360969912023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18193847578448240646608015 27290771367672360969912023)
      ·
        refine ⟨40936157051508541454868035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27290771367672360969912023 40936157051508541454868035)
        ·
          refine ⟨61404235577262812182302053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40936157051508541454868035 61404235577262812182302053)
          ·
            refine ⟨11513294170736777284181635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61404235577262812182302053 11513294170736777284181635)
            ·
              refine ⟨17269941256105165926272453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11513294170736777284181635 17269941256105165926272453)
              ·
                refine ⟨3238113985519718611176085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17269941256105165926272453 3238113985519718611176085)
                ·
                  refine ⟨151786593071236809898879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3238113985519718611176085 151786593071236809898879)
                  ·
                    rfl

theorem cell23_2660430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_2660430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660430 prefixEnd_2660430 := by exact prefixLift 2660430
  have htrace : WordTrace (prefixWord ++ tailWord_2660430) baseStart_2660430 baseEnd_2660430 := by
    simpa [prefixWord, tailWord_2660430, baseEnd_2660430] using wordTrace_append hprefix tailTrace_2660430
  have hstable : (prefixWord ++ tailWord_2660430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660430).length < 2 ^ (prefixWord ++ tailWord_2660430).sum := by decide
  have hdescent : baseEnd_2660430 < baseStart_2660430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660433 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 1, 2, 6]
def baseStart_2660433 : Nat := 118140960795 + 2660433 * 2 ^ 59
def prefixEnd_2660433 : Nat := 4983230072969 + 3 ^ 40 * 2660433 * 2
def baseEnd_2660433 : Nat := 1366080878083094777352397

theorem tailTrace_2660433 : CollatzResearch.WordTrace tailWord_2660433 prefixEnd_2660433 1366080878083094777352397 := by
  unfold tailWord_2660433
  simp only [CollatzResearch.WordTrace]
  refine ⟨97033963170713081627601953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64689308780475387751734635 97033963170713081627601953)
  ·
    refine ⟨72775472378034811220701465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97033963170713081627601953 72775472378034811220701465)
    ·
      refine ⟨54581604283526108415526099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72775472378034811220701465 54581604283526108415526099)
      ·
        refine ⟨81872406425289162623289149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54581604283526108415526099 81872406425289162623289149)
        ·
          refine ⟨30702152409483435983733431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81872406425289162623289149 30702152409483435983733431)
          ·
            refine ⟨46053228614225153975600147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30702152409483435983733431 46053228614225153975600147)
            ·
              refine ⟨69079842921337730963400221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46053228614225153975600147 69079842921337730963400221)
              ·
                refine ⟨25904941095501649111275083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69079842921337730963400221 25904941095501649111275083)
                ·
                  refine ⟨38857411643252473666912625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25904941095501649111275083 38857411643252473666912625)
                  ·
                    refine ⟨29143058732439355250184469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38857411643252473666912625 29143058732439355250184469)
                    ·
                      refine ⟨1366080878083094777352397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29143058732439355250184469 1366080878083094777352397)
                      ·
                        rfl

theorem cell23_2660433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_2660433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660433 prefixEnd_2660433 := by exact prefixLift 2660433
  have htrace : WordTrace (prefixWord ++ tailWord_2660433) baseStart_2660433 baseEnd_2660433 := by
    simpa [prefixWord, tailWord_2660433, baseEnd_2660433] using wordTrace_append hprefix tailTrace_2660433
  have hstable : (prefixWord ++ tailWord_2660433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660433).length < 2 ^ (prefixWord ++ tailWord_2660433).sum := by decide
  have hdescent : baseEnd_2660433 < baseStart_2660433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660457 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 3, 1, 3]
def baseStart_2660457 : Nat := 118140960795 + 2660457 * 2 ^ 59
def prefixEnd_2660457 : Nat := 4983230072969 + 3 ^ 40 * 2660457 * 2
def baseEnd_2660457 : Nat := 1366093201618802683452287

theorem tailTrace_2660457 : CollatzResearch.WordTrace tailWord_2660457 prefixEnd_2660457 1366093201618802683452287 := by
  unfold tailWord_2660457
  simp only [CollatzResearch.WordTrace]
  refine ⟨97034838522626133726475625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64689892348417422484317083 97034838522626133726475625)
  ·
    refine ⟨72776128891969600294856719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97034838522626133726475625 72776128891969600294856719)
    ·
      refine ⟨109164193337954400442285079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72776128891969600294856719 109164193337954400442285079)
      ·
        refine ⟨163746290006931600663427619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109164193337954400442285079 163746290006931600663427619)
        ·
          refine ⟨245619435010397400995141429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163746290006931600663427619 245619435010397400995141429)
          ·
            refine ⟨23026822032224756343294509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 245619435010397400995141429 23026822032224756343294509)
            ·
              refine ⟨8635058262084283628735441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23026822032224756343294509 8635058262084283628735441)
              ·
                refine ⟨6476293696563212721551581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8635058262084283628735441 6476293696563212721551581)
                ·
                  refine ⟨2428610136211204770581843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6476293696563212721551581 2428610136211204770581843)
                  ·
                    refine ⟨3642915204316807155872765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2428610136211204770581843 3642915204316807155872765)
                    ·
                      refine ⟨1366093201618802683452287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3642915204316807155872765 1366093201618802683452287)
                      ·
                        rfl

theorem cell23_2660457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 1, 3].length) (baseStart_2660457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660457 prefixEnd_2660457 := by exact prefixLift 2660457
  have htrace : WordTrace (prefixWord ++ tailWord_2660457) baseStart_2660457 baseEnd_2660457 := by
    simpa [prefixWord, tailWord_2660457, baseEnd_2660457] using wordTrace_append hprefix tailTrace_2660457
  have hstable : (prefixWord ++ tailWord_2660457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660457).length < 2 ^ (prefixWord ++ tailWord_2660457).sum := by decide
  have hdescent : baseEnd_2660457 < baseStart_2660457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660460 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 3, 5]
def baseStart_2660460 : Nat := 118140960795 + 2660460 * 2 ^ 59
def prefixEnd_2660460 : Nat := 4983230072969 + 3 ^ 40 * 2660460 * 2
def baseEnd_2660460 : Nat := 455364914020255390571591

theorem tailTrace_2660460 : CollatzResearch.WordTrace tailWord_2660460 prefixEnd_2660460 455364914020255390571591 := by
  unfold tailWord_2660460
  simp only [CollatzResearch.WordTrace]
  refine ⟨48517473970807632619417417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64689965294410176825889889 48517473970807632619417417)
  ·
    refine ⟨36388105478105724464563063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48517473970807632619417417 36388105478105724464563063)
    ·
      refine ⟨54582158217158586696844595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36388105478105724464563063 54582158217158586696844595)
      ·
        refine ⟨81873237325737880045266893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54582158217158586696844595 81873237325737880045266893)
        ·
          refine ⟨30702463997151705016975085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81873237325737880045266893 30702463997151705016975085)
          ·
            refine ⟨11513423998931889381365657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30702463997151705016975085 11513423998931889381365657)
            ·
              refine ⟨8635067999198917036024243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11513423998931889381365657 8635067999198917036024243)
              ·
                refine ⟨12952601998798375554036365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8635067999198917036024243 12952601998798375554036365)
                ·
                  refine ⟨4857225749549390832763637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12952601998798375554036365 4857225749549390832763637)
                  ·
                    refine ⟨455364914020255390571591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4857225749549390832763637 455364914020255390571591)
                    ·
                      rfl

theorem cell23_2660460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_2660460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660460 prefixEnd_2660460 := by exact prefixLift 2660460
  have htrace : WordTrace (prefixWord ++ tailWord_2660460) baseStart_2660460 baseEnd_2660460 := by
    simpa [prefixWord, tailWord_2660460, baseEnd_2660460] using wordTrace_append hprefix tailTrace_2660460
  have hstable : (prefixWord ++ tailWord_2660460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660460).length < 2 ^ (prefixWord ++ tailWord_2660460).sum := by decide
  have hdescent : baseEnd_2660460 < baseStart_2660460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660477 : List Nat := [1, 4, 1, 1, 3, 3, 1, 3, 1, 5]
def baseStart_2660477 : Nat := 118140960795 + 2660477 * 2 ^ 59
def prefixEnd_2660477 : Nat := 4983230072969 + 3 ^ 40 * 2660477 * 2
def baseEnd_2660477 : Nat := 455367823743964201734065

theorem tailTrace_2660477 : CollatzResearch.WordTrace tailWord_2660477 prefixEnd_2660477 455367823743964201734065 := by
  unfold tailWord_2660477
  simp only [CollatzResearch.WordTrace]
  refine ⟨97035567982553677142203685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64690378655035784761469123 97035567982553677142203685)
  ·
    refine ⟨18194168996728814464163191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97035567982553677142203685 18194168996728814464163191)
    ·
      refine ⟨27291253495093221696244787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18194168996728814464163191 27291253495093221696244787)
      ·
        refine ⟨40936880242639832544367181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27291253495093221696244787 40936880242639832544367181)
        ·
          refine ⟨15351330090989937204137693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40936880242639832544367181 15351330090989937204137693)
          ·
            refine ⟨5756748784121226451551635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15351330090989937204137693 5756748784121226451551635)
            ·
              refine ⟨8635123176181839677327453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5756748784121226451551635 8635123176181839677327453)
              ·
                refine ⟨3238171191068189878997795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8635123176181839677327453 3238171191068189878997795)
                ·
                  refine ⟨4857256786602284818496693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3238171191068189878997795 4857256786602284818496693)
                  ·
                    refine ⟨455367823743964201734065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4857256786602284818496693 455367823743964201734065)
                    ·
                      rfl

theorem cell23_2660477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_2660477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660477 prefixEnd_2660477 := by exact prefixLift 2660477
  have htrace : WordTrace (prefixWord ++ tailWord_2660477) baseStart_2660477 baseEnd_2660477 := by
    simpa [prefixWord, tailWord_2660477, baseEnd_2660477] using wordTrace_append hprefix tailTrace_2660477
  have hstable : (prefixWord ++ tailWord_2660477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660477).length < 2 ^ (prefixWord ++ tailWord_2660477).sum := by decide
  have hdescent : baseEnd_2660477 < baseStart_2660477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660514 : List Nat := [3, 3, 1, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_2660514 : Nat := 118140960795 + 2660514 * 2 ^ 59
def prefixEnd_2660514 : Nat := 4983230072969 + 3 ^ 40 * 2660514 * 2
def baseEnd_2660514 : Nat := 1366122470016108960439525

theorem tailTrace_2660514 : CollatzResearch.WordTrace tailWord_2660514 prefixEnd_2660514 1366122470016108960439525 := by
  unfold tailWord_2660514
  simp only [CollatzResearch.WordTrace]
  refine ⟨24259229370854908115325149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64691278322279754974200397 24259229370854908115325149)
  ·
    refine ⟨9097211014070590543246931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24259229370854908115325149 9097211014070590543246931)
    ·
      refine ⟨13645816521105885814870397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9097211014070590543246931 13645816521105885814870397)
      ·
        refine ⟨5117181195414707180576399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13645816521105885814870397 5117181195414707180576399)
        ·
          refine ⟨7675771793122060770864599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5117181195414707180576399 7675771793122060770864599)
          ·
            refine ⟨11513657689683091156296899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7675771793122060770864599 11513657689683091156296899)
            ·
              refine ⟨17270486534524636734445349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11513657689683091156296899 17270486534524636734445349)
              ·
                refine ⟨3238216225223369387708503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17270486534524636734445349 3238216225223369387708503)
                ·
                  refine ⟨4857324337835054081562755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3238216225223369387708503 4857324337835054081562755)
                  ·
                    refine ⟨7285986506752581122344133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4857324337835054081562755 7285986506752581122344133)
                    ·
                      refine ⟨1366122470016108960439525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7285986506752581122344133 1366122470016108960439525)
                      ·
                        rfl

theorem cell23_2660514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_2660514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660514 prefixEnd_2660514 := by exact prefixLift 2660514
  have htrace : WordTrace (prefixWord ++ tailWord_2660514) baseStart_2660514 baseEnd_2660514 := by
    simpa [prefixWord, tailWord_2660514, baseEnd_2660514] using wordTrace_append hprefix tailTrace_2660514
  have hstable : (prefixWord ++ tailWord_2660514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660514).length < 2 ^ (prefixWord ++ tailWord_2660514).sum := by decide
  have hdescent : baseEnd_2660514 < baseStart_2660514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660548 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_2660548 : Nat := 118140960795 + 2660548 * 2 ^ 59
def prefixEnd_2660548 : Nat := 4983230072969 + 3 ^ 40 * 2660548 * 2
def baseEnd_2660548 : Nat := 1366139928358361827414369

theorem tailTrace_2660548 : CollatzResearch.WordTrace tailWord_2660548 prefixEnd_2660548 1366139928358361827414369 := by
  unfold tailWord_2660548
  simp only [CollatzResearch.WordTrace]
  refine ⟨48519078782648228134019149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64692105043530970845358865 48519078782648228134019149)
  ·
    refine ⟨18194654543493085550257181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48519078782648228134019149 18194654543493085550257181)
    ·
      refine ⟨6822995453809907081346443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18194654543493085550257181 6822995453809907081346443)
      ·
        refine ⟨10234493180714860622019665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6822995453809907081346443 10234493180714860622019665)
        ·
          refine ⟨7675869885536145466514749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10234493180714860622019665 7675869885536145466514749)
          ·
            refine ⟨2878451207076054549943031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7675869885536145466514749 2878451207076054549943031)
            ·
              refine ⟨4317676810614081824914547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2878451207076054549943031 4317676810614081824914547)
              ·
                refine ⟨6476515215921122737371821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4317676810614081824914547 6476515215921122737371821)
                ·
                  refine ⟨2428693205970421026514433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6476515215921122737371821 2428693205970421026514433)
                  ·
                    refine ⟨1821519904477815769885825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2428693205970421026514433 1821519904477815769885825)
                    ·
                      refine ⟨1366139928358361827414369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1821519904477815769885825 1366139928358361827414369)
                      ·
                        rfl

theorem cell23_2660548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_2660548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660548 prefixEnd_2660548 := by exact prefixLift 2660548
  have htrace : WordTrace (prefixWord ++ tailWord_2660548) baseStart_2660548 baseEnd_2660548 := by
    simpa [prefixWord, tailWord_2660548, baseEnd_2660548] using wordTrace_append hprefix tailTrace_2660548
  have hstable : (prefixWord ++ tailWord_2660548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660548).length < 2 ^ (prefixWord ++ tailWord_2660548).sum := by decide
  have hdescent : baseEnd_2660548 < baseStart_2660548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660578 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2660578 : Nat := 118140960795 + 2660578 * 2 ^ 59
def prefixEnd_2660578 : Nat := 4983230072969 + 3 ^ 40 * 2660578 * 2
def baseEnd_2660578 : Nat := 1366155332777996710039231

theorem tailTrace_2660578 : CollatzResearch.WordTrace tailWord_2660578 prefixEnd_2660578 1366155332777996710039231 := by
  unfold tailWord_2660578
  simp only [CollatzResearch.WordTrace]
  refine ⟨24259812938796942847907597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64692834503458514261086925 24259812938796942847907597)
  ·
    refine ⟨9097429852048853567965349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24259812938796942847907597 9097429852048853567965349)
    ·
      refine ⟨1705768097259160043993503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9097429852048853567965349 1705768097259160043993503)
      ·
        refine ⟨2558652145888740065990255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705768097259160043993503 2558652145888740065990255)
        ·
          refine ⟨3837978218833110098985383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2558652145888740065990255 3837978218833110098985383)
          ·
            refine ⟨5756967328249665148478075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3837978218833110098985383 5756967328249665148478075)
            ·
              refine ⟨8635450992374497722717113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5756967328249665148478075 8635450992374497722717113)
              ·
                refine ⟨6476588244280873292037835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8635450992374497722717113 6476588244280873292037835)
                ·
                  refine ⟨9714882366421309938056753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6476588244280873292037835 9714882366421309938056753)
                  ·
                    refine ⟨7286161774815982453542565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9714882366421309938056753 7286161774815982453542565)
                    ·
                      refine ⟨1366155332777996710039231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7286161774815982453542565 1366155332777996710039231)
                      ·
                        rfl

theorem cell23_2660578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2660578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660578 prefixEnd_2660578 := by exact prefixLift 2660578
  have htrace : WordTrace (prefixWord ++ tailWord_2660578) baseStart_2660578 baseEnd_2660578 := by
    simpa [prefixWord, tailWord_2660578, baseEnd_2660578] using wordTrace_append hprefix tailTrace_2660578
  have hstable : (prefixWord ++ tailWord_2660578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660578).length < 2 ^ (prefixWord ++ tailWord_2660578).sum := by decide
  have hdescent : baseEnd_2660578 < baseStart_2660578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660580 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 4, 6]
def baseStart_2660580 : Nat := 118140960795 + 2660580 * 2 ^ 59
def prefixEnd_2660580 : Nat := 4983230072969 + 3 ^ 40 * 2660580 * 2
def baseEnd_2660580 : Nat := 455385453246435234071407

theorem tailTrace_2660580 : CollatzResearch.WordTrace tailWord_2660580 prefixEnd_2660580 455385453246435234071407 := by
  unfold tailWord_2660580
  simp only [CollatzResearch.WordTrace]
  refine ⟨48519662350590262866601597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64692883134120350488802129 48519662350590262866601597)
  ·
    refine ⟨18194873381471348574975599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48519662350590262866601597 18194873381471348574975599)
    ·
      refine ⟨27292310072207022862463399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18194873381471348574975599 27292310072207022862463399)
      ·
        refine ⟨40938465108310534293695099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27292310072207022862463399 40938465108310534293695099)
        ·
          refine ⟨61407697662465801440542649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40938465108310534293695099 61407697662465801440542649)
          ·
            refine ⟨46055773246849351080406987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61407697662465801440542649 46055773246849351080406987)
            ·
              refine ⟨69083659870274026620610481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46055773246849351080406987 69083659870274026620610481)
              ·
                refine ⟨51812744902705519965457861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69083659870274026620610481 51812744902705519965457861)
                ·
                  refine ⟨9714889669257284993523349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51812744902705519965457861 9714889669257284993523349)
                  ·
                    refine ⟨455385453246435234071407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9714889669257284993523349 455385453246435234071407)
                    ·
                      rfl

theorem cell23_2660580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_2660580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660580 prefixEnd_2660580 := by exact prefixLift 2660580
  have htrace : WordTrace (prefixWord ++ tailWord_2660580) baseStart_2660580 baseEnd_2660580 := by
    simpa [prefixWord, tailWord_2660580, baseEnd_2660580] using wordTrace_append hprefix tailTrace_2660580
  have hstable : (prefixWord ++ tailWord_2660580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660580).length < 2 ^ (prefixWord ++ tailWord_2660580).sum := by decide
  have hdescent : baseEnd_2660580 < baseStart_2660580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660600 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 3, 4, 4]
def baseStart_2660600 : Nat := 118140960795 + 2660600 * 2 ^ 59
def prefixEnd_2660600 : Nat := 4983230072969 + 3 ^ 40 * 2660600 * 2
def baseEnd_2660600 : Nat := 1366166629352395623964129

theorem tailTrace_2660600 : CollatzResearch.WordTrace tailWord_2660600 prefixEnd_2660600 1366166629352395623964129 := by
  unfold tailWord_2660600
  simp only [CollatzResearch.WordTrace]
  refine ⟨48520027080554034574465627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64693369440738712765954169 48520027080554034574465627)
  ·
    refine ⟨72780040620831051861698441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48520027080554034574465627 72780040620831051861698441)
    ·
      refine ⟨54585030465623288896273831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72780040620831051861698441 54585030465623288896273831)
      ·
        refine ⟨81877545698434933344410747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54585030465623288896273831 81877545698434933344410747)
        ·
          refine ⟨122816318547652400016616121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81877545698434933344410747 122816318547652400016616121)
          ·
            refine ⟨92112238910739300012462091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122816318547652400016616121 92112238910739300012462091)
            ·
              refine ⟨138168358366108950018693137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92112238910739300012462091 138168358366108950018693137)
              ·
                refine ⟨103626268774581712514019853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138168358366108950018693137 103626268774581712514019853)
                ·
                  refine ⟨38859850790468142192757445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103626268774581712514019853 38859850790468142192757445)
                  ·
                    refine ⟨7286222023212776661142021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38859850790468142192757445 7286222023212776661142021)
                    ·
                      refine ⟨1366166629352395623964129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7286222023212776661142021 1366166629352395623964129)
                      ·
                        rfl

theorem cell23_2660600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_2660600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660600 prefixEnd_2660600 := by exact prefixLift 2660600
  have htrace : WordTrace (prefixWord ++ tailWord_2660600) baseStart_2660600 baseEnd_2660600 := by
    simpa [prefixWord, tailWord_2660600, baseEnd_2660600] using wordTrace_append hprefix tailTrace_2660600
  have hstable : (prefixWord ++ tailWord_2660600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660600).length < 2 ^ (prefixWord ++ tailWord_2660600).sum := by decide
  have hdescent : baseEnd_2660600 < baseStart_2660600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660617 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 2, 2, 4]
def baseStart_2660617 : Nat := 118140960795 + 2660617 * 2 ^ 59
def prefixEnd_2660617 : Nat := 4983230072969 + 3 ^ 40 * 2660617 * 2
def baseEnd_2660617 : Nat := 1366175358523522057451551

theorem tailTrace_2660617 : CollatzResearch.WordTrace tailWord_2660617 prefixEnd_2660617 1366175358523522057451551 := by
  unfold tailWord_2660617
  simp only [CollatzResearch.WordTrace]
  refine ⟨97040674202046481052300105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64693782801364320701533403 97040674202046481052300105)
  ·
    refine ⟨72780505651534860789225079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97040674202046481052300105 72780505651534860789225079)
    ·
      refine ⟨109170758477302291183837619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72780505651534860789225079 109170758477302291183837619)
      ·
        refine ⟨163756137715953436775756429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109170758477302291183837619 163756137715953436775756429)
        ·
          refine ⟨61408551643482538790908661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163756137715953436775756429 61408551643482538790908661)
          ·
            refine ⟨5757051716576488011647687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61408551643482538790908661 5757051716576488011647687)
            ·
              refine ⟨8635577574864732017471531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5757051716576488011647687 8635577574864732017471531)
              ·
                refine ⟨12953366362297098026207297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8635577574864732017471531 12953366362297098026207297)
                ·
                  refine ⟨9715024771722823519655473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12953366362297098026207297 9715024771722823519655473)
                  ·
                    refine ⟨7286268578792117639741605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9715024771722823519655473 7286268578792117639741605)
                    ·
                      refine ⟨1366175358523522057451551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7286268578792117639741605 1366175358523522057451551)
                      ·
                        rfl

theorem cell23_2660617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 2, 4].length) (baseStart_2660617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660617 prefixEnd_2660617 := by exact prefixLift 2660617
  have htrace : WordTrace (prefixWord ++ tailWord_2660617) baseStart_2660617 baseEnd_2660617 := by
    simpa [prefixWord, tailWord_2660617, baseEnd_2660617] using wordTrace_append hprefix tailTrace_2660617
  have hstable : (prefixWord ++ tailWord_2660617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660617).length < 2 ^ (prefixWord ++ tailWord_2660617).sum := by decide
  have hdescent : baseEnd_2660617 < baseStart_2660617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660638 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_2660638 : Nat := 118140960795 + 2660638 * 2 ^ 59
def prefixEnd_2660638 : Nat := 4983230072969 + 3 ^ 40 * 2660638 * 2
def baseEnd_2660638 : Nat := 1366186141617266475288955

theorem tailTrace_2660638 : CollatzResearch.WordTrace tailWord_2660638 prefixEnd_2660638 1366186141617266475288955 := by
  unfold tailWord_2660638
  simp only [CollatzResearch.WordTrace]
  refine ⟨12130180016871300204851821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64694293423313601092543045 12130180016871300204851821)
  ·
    refine ⟨4548817506326737576819433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12130180016871300204851821 4548817506326737576819433)
    ·
      refine ⟨3411613129745053182614575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4548817506326737576819433 3411613129745053182614575)
      ·
        refine ⟨5117419694617579773921863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3411613129745053182614575 5117419694617579773921863)
        ·
          refine ⟨7676129541926369660882795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5117419694617579773921863 7676129541926369660882795)
          ·
            refine ⟨11514194312889554491324193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7676129541926369660882795 11514194312889554491324193)
            ·
              refine ⟨8635645734667165868493145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11514194312889554491324193 8635645734667165868493145)
              ·
                refine ⟨6476734301000374401369859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8635645734667165868493145 6476734301000374401369859)
                ·
                  refine ⟨9715101451500561602054789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6476734301000374401369859 9715101451500561602054789)
                  ·
                    refine ⟨1821581522156355300385273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9715101451500561602054789 1821581522156355300385273)
                    ·
                      refine ⟨1366186141617266475288955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1821581522156355300385273 1366186141617266475288955)
                      ·
                        rfl

theorem cell23_2660638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_2660638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660638 prefixEnd_2660638 := by exact prefixLift 2660638
  have htrace : WordTrace (prefixWord ++ tailWord_2660638) baseStart_2660638 baseEnd_2660638 := by
    simpa [prefixWord, tailWord_2660638, baseEnd_2660638] using wordTrace_append hprefix tailTrace_2660638
  have hstable : (prefixWord ++ tailWord_2660638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660638).length < 2 ^ (prefixWord ++ tailWord_2660638).sum := by decide
  have hdescent : baseEnd_2660638 < baseStart_2660638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660644 : List Nat := [2, 3, 1, 3, 1, 2, 1, 5, 5]
def baseStart_2660644 : Nat := 118140960795 + 2660644 * 2 ^ 59
def prefixEnd_2660644 : Nat := 4983230072969 + 3 ^ 40 * 2660644 * 2
def baseEnd_2660644 : Nat := 151798802500132605757103

theorem tailTrace_2660644 : CollatzResearch.WordTrace tailWord_2660644 prefixEnd_2660644 151798802500132605757103 := by
  unfold tailWord_2660644
  simp only [CollatzResearch.WordTrace]
  refine ⟨48520829486474332331766493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64694439315299109775688657 48520829486474332331766493)
  ·
    refine ⟨18195311057427874624412435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48520829486474332331766493 18195311057427874624412435)
    ·
      refine ⟨27292966586141811936618653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18195311057427874624412435 27292966586141811936618653)
      ·
        refine ⟨10234862469803179476231995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27292966586141811936618653 10234862469803179476231995)
        ·
          refine ⟨15352293704704769214347993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10234862469803179476231995 15352293704704769214347993)
          ·
            refine ⟨11514220278528576910760995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15352293704704769214347993 11514220278528576910760995)
            ·
              refine ⟨17271330417792865366141493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11514220278528576910760995 17271330417792865366141493)
              ·
                refine ⟨1619187226668081128075765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17271330417792865366141493 1619187226668081128075765)
                ·
                  refine ⟨151798802500132605757103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1619187226668081128075765 151798802500132605757103)
                  ·
                    rfl

theorem cell23_2660644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_2660644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660644 prefixEnd_2660644 := by exact prefixLift 2660644
  have htrace : WordTrace (prefixWord ++ tailWord_2660644) baseStart_2660644 baseEnd_2660644 := by
    simpa [prefixWord, tailWord_2660644, baseEnd_2660644] using wordTrace_append hprefix tailTrace_2660644
  have hstable : (prefixWord ++ tailWord_2660644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660644).length < 2 ^ (prefixWord ++ tailWord_2660644).sum := by decide
  have hdescent : baseEnd_2660644 < baseStart_2660644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660687 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 5, 4]
def baseStart_2660687 : Nat := 118140960795 + 2660687 * 2 ^ 59
def prefixEnd_2660687 : Nat := 4983230072969 + 3 ^ 40 * 2660687 * 2
def baseEnd_2660687 : Nat := 455403767389778927858743

theorem tailTrace_2660687 : CollatzResearch.WordTrace tailWord_2660687 prefixEnd_2660687 455403767389778927858743 := by
  unfold tailWord_2660687
  simp only [CollatzResearch.WordTrace]
  refine ⟨97043227311792883007348315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64695484874528588671565543 97043227311792883007348315)
  ·
    refine ⟨145564840967689324511022473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97043227311792883007348315 145564840967689324511022473)
    ·
      refine ⟨109173630725766993383266855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145564840967689324511022473 109173630725766993383266855)
      ·
        refine ⟨163760446088650490074900283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109173630725766993383266855 163760446088650490074900283)
        ·
          refine ⟨245640669132975735112350425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163760446088650490074900283 245640669132975735112350425)
          ·
            refine ⟨184230501849731801334262819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245640669132975735112350425 184230501849731801334262819)
            ·
              refine ⟨276345752774597702001394229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184230501849731801334262819 276345752774597702001394229)
              ·
                refine ⟨25907414322618534562630709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 276345752774597702001394229 25907414322618534562630709)
                ·
                  refine ⟨2428820092745487615246629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25907414322618534562630709 2428820092745487615246629)
                  ·
                    refine ⟨455403767389778927858743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2428820092745487615246629 455403767389778927858743)
                    ·
                      rfl

theorem cell23_2660687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 4].length) (baseStart_2660687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660687 prefixEnd_2660687 := by exact prefixLift 2660687
  have htrace : WordTrace (prefixWord ++ tailWord_2660687) baseStart_2660687 baseEnd_2660687 := by
    simpa [prefixWord, tailWord_2660687, baseEnd_2660687] using wordTrace_append hprefix tailTrace_2660687
  have hstable : (prefixWord ++ tailWord_2660687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660687).length < 2 ^ (prefixWord ++ tailWord_2660687).sum := by decide
  have hdescent : baseEnd_2660687 < baseStart_2660687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660717 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 8]
def baseStart_2660717 : Nat := 118140960795 + 2660717 * 2 ^ 59
def prefixEnd_2660717 : Nat := 4983230072969 + 3 ^ 40 * 2660717 * 2
def baseEnd_2660717 : Nat := 151802967398774629577899

theorem tailTrace_2660717 : CollatzResearch.WordTrace tailWord_2660717 prefixEnd_2660717 151802967398774629577899 := by
  unfold tailWord_2660717
  simp only [CollatzResearch.WordTrace]
  refine ⟨97044321501684198130940405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64696214334456132087293603 97044321501684198130940405)
  ·
    refine ⟨9097905140782893574775663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97044321501684198130940405 9097905140782893574775663)
    ·
      refine ⟨13646857711174340362163495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9097905140782893574775663 13646857711174340362163495)
      ·
        refine ⟨20470286566761510543245243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13646857711174340362163495 20470286566761510543245243)
        ·
          refine ⟨30705429850142265814867865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20470286566761510543245243 30705429850142265814867865)
          ·
            refine ⟨23029072387606699361150899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30705429850142265814867865 23029072387606699361150899)
            ·
              refine ⟨34543608581410049041726349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23029072387606699361150899 34543608581410049041726349)
              ·
                refine ⟨12953853218028768390647381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34543608581410049041726349 12953853218028768390647381)
                ·
                  refine ⟨151802967398774629577899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12953853218028768390647381 151802967398774629577899)
                  ·
                    rfl

theorem cell23_2660717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_2660717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660717 prefixEnd_2660717 := by exact prefixLift 2660717
  have htrace : WordTrace (prefixWord ++ tailWord_2660717) baseStart_2660717 baseEnd_2660717 := by
    simpa [prefixWord, tailWord_2660717, baseEnd_2660717] using wordTrace_append hprefix tailTrace_2660717
  have hstable : (prefixWord ++ tailWord_2660717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660717).length < 2 ^ (prefixWord ++ tailWord_2660717).sum := by decide
  have hdescent : baseEnd_2660717 < baseStart_2660717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660727 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 3]
def baseStart_2660727 : Nat := 118140960795 + 2660727 * 2 ^ 59
def prefixEnd_2660727 : Nat := 4983230072969 + 3 ^ 40 * 2660727 * 2
def baseEnd_2660727 : Nat := 1366231841395516627076045

theorem tailTrace_2660727 : CollatzResearch.WordTrace tailWord_2660727 prefixEnd_2660727 1366231841395516627076045 := by
  unfold tailWord_2660727
  simp only [CollatzResearch.WordTrace]
  refine ⟨97044686231647969838804435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64696457487765313225869623 97044686231647969838804435)
  ·
    refine ⟨145567029347471954758206653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97044686231647969838804435 145567029347471954758206653)
    ·
      refine ⟨54587636005301983034327495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145567029347471954758206653 54587636005301983034327495)
      ·
        refine ⟨81881454007952974551491243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54587636005301983034327495 81881454007952974551491243)
        ·
          refine ⟨122822181011929461827236865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81881454007952974551491243 122822181011929461827236865)
          ·
            refine ⟨92116635758947096370427649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122822181011929461827236865 92116635758947096370427649)
            ·
              refine ⟨69087476819210322277820737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92116635758947096370427649 69087476819210322277820737)
              ·
                refine ⟨51815607614407741708365553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69087476819210322277820737 51815607614407741708365553)
                ·
                  refine ⟨38861705710805806281274165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51815607614407741708365553 38861705710805806281274165)
                  ·
                    refine ⟨3643284910388044338869453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38861705710805806281274165 3643284910388044338869453)
                    ·
                      refine ⟨1366231841395516627076045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3643284910388044338869453 1366231841395516627076045)
                      ·
                        rfl

theorem cell23_2660727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_2660727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660727 prefixEnd_2660727 := by exact prefixLift 2660727
  have htrace : WordTrace (prefixWord ++ tailWord_2660727) baseStart_2660727 baseEnd_2660727 := by
    simpa [prefixWord, tailWord_2660727, baseEnd_2660727] using wordTrace_append hprefix tailTrace_2660727
  have hstable : (prefixWord ++ tailWord_2660727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660727).length < 2 ^ (prefixWord ++ tailWord_2660727).sum := by decide
  have hdescent : baseEnd_2660727 < baseStart_2660727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660771 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 2, 3, 2]
def baseStart_2660771 : Nat := 118140960795 + 2660771 * 2 ^ 59
def prefixEnd_2660771 : Nat := 4983230072969 + 3 ^ 40 * 2660771 * 2
def baseEnd_2660771 : Nat := 1366254434544314454925843

theorem tailTrace_2660771 : CollatzResearch.WordTrace tailWord_2660771 prefixEnd_2660771 1366254434544314454925843 := by
  unfold tailWord_2660771
  simp only [CollatzResearch.WordTrace]
  refine ⟨97046291043488565353406167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64697527362325710235604111 97046291043488565353406167)
  ·
    refine ⟨145569436565232848030109251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97046291043488565353406167 145569436565232848030109251)
    ·
      refine ⟨218354154847849272045163877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145569436565232848030109251 218354154847849272045163877)
      ·
        refine ⟨40941404033971738508468227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218354154847849272045163877 40941404033971738508468227)
        ·
          refine ⟨61412106050957607762702341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40941404033971738508468227 61412106050957607762702341)
          ·
            refine ⟨11514769884554551455506689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61412106050957607762702341 11514769884554551455506689)
            ·
              refine ⟨8636077413415913591630017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11514769884554551455506689 8636077413415913591630017)
              ·
                refine ⟨6477058060061935193722513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8636077413415913591630017 6477058060061935193722513)
                ·
                  refine ⟨4857793545046451395291885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6477058060061935193722513 4857793545046451395291885)
                  ·
                    refine ⟨1821672579392419273234457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4857793545046451395291885 1821672579392419273234457)
                    ·
                      refine ⟨1366254434544314454925843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1821672579392419273234457 1366254434544314454925843)
                      ·
                        rfl

theorem cell23_2660771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_2660771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660771 prefixEnd_2660771 := by exact prefixLift 2660771
  have htrace : WordTrace (prefixWord ++ tailWord_2660771) baseStart_2660771 baseEnd_2660771 := by
    simpa [prefixWord, tailWord_2660771, baseEnd_2660771] using wordTrace_append hprefix tailTrace_2660771
  have hstable : (prefixWord ++ tailWord_2660771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660771).length < 2 ^ (prefixWord ++ tailWord_2660771).sum := by decide
  have hdescent : baseEnd_2660771 < baseStart_2660771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660835 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 3, 2, 2]
def baseStart_2660835 : Nat := 118140960795 + 2660835 * 2 ^ 59
def prefixEnd_2660835 : Nat := 4983230072969 + 3 ^ 40 * 2660835 * 2
def baseEnd_2660835 : Nat := 1366287297306202204525549

theorem tailTrace_2660835 : CollatzResearch.WordTrace tailWord_2660835 prefixEnd_2660835 1366287297306202204525549 := by
  unfold tailWord_2660835
  simp only [CollatzResearch.WordTrace]
  refine ⟨97048625315256704283735959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64699083543504469522490639 97048625315256704283735959)
  ·
    refine ⟨145572937972885056425603939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97048625315256704283735959 145572937972885056425603939)
    ·
      refine ⟨218359406959327584638405909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145572937972885056425603939 218359406959327584638405909)
      ·
        refine ⟨10235597201218480529925277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 218359406959327584638405909 10235597201218480529925277)
        ·
          refine ⟨3838348950456930198721979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10235597201218480529925277 3838348950456930198721979)
          ·
            refine ⟨5757523425685395298082969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3838348950456930198721979 5757523425685395298082969)
            ·
              refine ⟨4318142569264046473562227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5757523425685395298082969 4318142569264046473562227)
              ·
                refine ⟨6477213853896069710343341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4318142569264046473562227 6477213853896069710343341)
                ·
                  refine ⟨2428955195211026141378753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6477213853896069710343341 2428955195211026141378753)
                  ·
                    refine ⟨1821716396408269606034065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2428955195211026141378753 1821716396408269606034065)
                    ·
                      refine ⟨1366287297306202204525549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1821716396408269606034065 1366287297306202204525549)
                      ·
                        rfl

theorem cell23_2660835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_2660835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660835 prefixEnd_2660835 := by exact prefixLift 2660835
  have htrace : WordTrace (prefixWord ++ tailWord_2660835) baseStart_2660835 baseEnd_2660835 := by
    simpa [prefixWord, tailWord_2660835, baseEnd_2660835] using wordTrace_append hprefix tailTrace_2660835
  have hstable : (prefixWord ++ tailWord_2660835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660835).length < 2 ^ (prefixWord ++ tailWord_2660835).sum := by decide
  have hdescent : baseEnd_2660835 < baseStart_2660835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660845 : List Nat := [1, 5, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_2660845 : Nat := 118140960795 + 2660845 * 2 ^ 59
def prefixEnd_2660845 : Nat := 4983230072969 + 3 ^ 40 * 2660845 * 2
def baseEnd_2660845 : Nat := 455430810704249055133501

theorem tailTrace_2660845 : CollatzResearch.WordTrace tailWord_2660845 prefixEnd_2660845 455430810704249055133501 := by
  unfold tailWord_2660845
  simp only [CollatzResearch.WordTrace]
  refine ⟨97048990045220475991599989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64699326696813650661066659 97048990045220475991599989)
  ·
    refine ⟨9098342816739419624212499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97048990045220475991599989 9098342816739419624212499)
    ·
      refine ⟨13647514225109129436318749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9098342816739419624212499 13647514225109129436318749)
      ·
        refine ⟨5117817834415923538619531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13647514225109129436318749 5117817834415923538619531)
        ·
          refine ⟨7676726751623885307929297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5117817834415923538619531 7676726751623885307929297)
          ·
            refine ⟨5757545063717913980946973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7676726751623885307929297 5757545063717913980946973)
            ·
              refine ⟨2159079398894217742855115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5757545063717913980946973 2159079398894217742855115)
              ·
                refine ⟨3238619098341326614282673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159079398894217742855115 3238619098341326614282673)
                ·
                  refine ⟨2428964323755994960712005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3238619098341326614282673 2428964323755994960712005)
                  ·
                    refine ⟨455430810704249055133501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2428964323755994960712005 455430810704249055133501)
                    ·
                      rfl

theorem cell23_2660845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_2660845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660845 prefixEnd_2660845 := by exact prefixLift 2660845
  have htrace : WordTrace (prefixWord ++ tailWord_2660845) baseStart_2660845 baseEnd_2660845 := by
    simpa [prefixWord, tailWord_2660845, baseEnd_2660845] using wordTrace_append hprefix tailTrace_2660845
  have hstable : (prefixWord ++ tailWord_2660845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660845).length < 2 ^ (prefixWord ++ tailWord_2660845).sum := by decide
  have hdescent : baseEnd_2660845 < baseStart_2660845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660868 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_2660868 : Nat := 118140960795 + 2660868 * 2 ^ 59
def prefixEnd_2660868 : Nat := 4983230072969 + 3 ^ 40 * 2660868 * 2
def baseEnd_2660868 : Nat := 1366304242167800575412897

theorem tailTrace_2660868 : CollatzResearch.WordTrace tailWord_2660868 prefixEnd_2660868 1366304242167800575412897 := by
  unfold tailWord_2660868
  simp only [CollatzResearch.WordTrace]
  refine ⟨48524914462068575459843629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64699885949424767279791505 48524914462068575459843629)
  ·
    refine ⟨18196842923275715797441361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48524914462068575459843629 18196842923275715797441361)
    ·
      refine ⟨13647632192456786848081021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18196842923275715797441361 13647632192456786848081021)
      ·
        refine ⟨5117862072171295068030383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13647632192456786848081021 5117862072171295068030383)
        ·
          refine ⟨7676793108256942602045575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5117862072171295068030383 7676793108256942602045575)
          ·
            refine ⟨11515189662385413903068363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7676793108256942602045575 11515189662385413903068363)
            ·
              refine ⟨17272784493578120854602545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11515189662385413903068363 17272784493578120854602545)
              ·
                refine ⟨12954588370183590640951909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17272784493578120854602545 12954588370183590640951909)
                ·
                  refine ⟨2428985319409423245178483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12954588370183590640951909 2428985319409423245178483)
                  ·
                    refine ⟨3643477979114134867767725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2428985319409423245178483 3643477979114134867767725)
                    ·
                      refine ⟨1366304242167800575412897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3643477979114134867767725 1366304242167800575412897)
                      ·
                        rfl

theorem cell23_2660868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_2660868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660868 prefixEnd_2660868 := by exact prefixLift 2660868
  have htrace : WordTrace (prefixWord ++ tailWord_2660868) baseStart_2660868 baseEnd_2660868 := by
    simpa [prefixWord, tailWord_2660868, baseEnd_2660868] using wordTrace_append hprefix tailTrace_2660868
  have hstable : (prefixWord ++ tailWord_2660868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660868).length < 2 ^ (prefixWord ++ tailWord_2660868).sum := by decide
  have hdescent : baseEnd_2660868 < baseStart_2660868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660914 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 7]
def baseStart_2660914 : Nat := 118140960795 + 2660914 * 2 ^ 59
def prefixEnd_2660914 : Nat := 4983230072969 + 3 ^ 40 * 2660914 * 2
def baseEnd_2660914 : Nat := 151814206919767488381965

theorem tailTrace_2660914 : CollatzResearch.WordTrace tailWord_2660914 prefixEnd_2660914 151814206919767488381965 := by
  unfold tailWord_2660914
  simp only [CollatzResearch.WordTrace]
  refine ⟨24262876670492625193965449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64701004454647000517241197 24262876670492625193965449)
  ·
    refine ⟨18197157502869468895474087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24262876670492625193965449 18197157502869468895474087)
    ·
      refine ⟨27295736254304203343211131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18197157502869468895474087 27295736254304203343211131)
      ·
        refine ⟨40943604381456305014816697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27295736254304203343211131 40943604381456305014816697)
        ·
          refine ⟨30707703286092228761112523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40943604381456305014816697 30707703286092228761112523)
          ·
            refine ⟨46061554929138343141668785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30707703286092228761112523 46061554929138343141668785)
            ·
              refine ⟨34546166196853757356251589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46061554929138343141668785 34546166196853757356251589)
              ·
                refine ⟨6477406161910079504297173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34546166196853757356251589 6477406161910079504297173)
                ·
                  refine ⟨151814206919767488381965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6477406161910079504297173 151814206919767488381965)
                  ·
                    rfl

theorem cell23_2660914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_2660914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660914 prefixEnd_2660914 := by exact prefixLift 2660914
  have htrace : WordTrace (prefixWord ++ tailWord_2660914) baseStart_2660914 baseEnd_2660914 := by
    simpa [prefixWord, tailWord_2660914, baseEnd_2660914] using wordTrace_append hprefix tailTrace_2660914
  have hstable : (prefixWord ++ tailWord_2660914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660914).length < 2 ^ (prefixWord ++ tailWord_2660914).sum := by decide
  have hdescent : baseEnd_2660914 < baseStart_2660914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660944 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 4, 5]
def baseStart_2660944 : Nat := 118140960795 + 2660944 * 2 ^ 59
def prefixEnd_2660944 : Nat := 4983230072969 + 3 ^ 40 * 2660944 * 2
def baseEnd_2660944 : Nat := 455447755565847426020849

theorem tailTrace_2660944 : CollatzResearch.WordTrace tailWord_2660944 prefixEnd_2660944 455447755565847426020849 := by
  unfold tailWord_2660944
  simp only [CollatzResearch.WordTrace]
  refine ⟨48526300435930907949726943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64701733914574543932969257 48526300435930907949726943)
  ·
    refine ⟨72789450653896361924590415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48526300435930907949726943 72789450653896361924590415)
    ·
      refine ⟨109184175980844542886885623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72789450653896361924590415 109184175980844542886885623)
      ·
        refine ⟨163776263971266814330328435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109184175980844542886885623 163776263971266814330328435)
        ·
          refine ⟨245664395956900221495492653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163776263971266814330328435 245664395956900221495492653)
          ·
            refine ⟨92124148483837583060809745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245664395956900221495492653 92124148483837583060809745)
            ·
              refine ⟨69093111362878187295607309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92124148483837583060809745 69093111362878187295607309)
              ·
                refine ⟨25909916761079320235852741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69093111362878187295607309 25909916761079320235852741)
                ·
                  refine ⟨4858109392702372544222389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25909916761079320235852741 4858109392702372544222389)
                  ·
                    refine ⟨455447755565847426020849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4858109392702372544222389 455447755565847426020849)
                    ·
                      rfl

theorem cell23_2660944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 4, 5].length) (baseStart_2660944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660944 prefixEnd_2660944 := by exact prefixLift 2660944
  have htrace : WordTrace (prefixWord ++ tailWord_2660944) baseStart_2660944 baseEnd_2660944 := by
    simpa [prefixWord, tailWord_2660944, baseEnd_2660944] using wordTrace_append hprefix tailTrace_2660944
  have hstable : (prefixWord ++ tailWord_2660944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660944).length < 2 ^ (prefixWord ++ tailWord_2660944).sum := by decide
  have hdescent : baseEnd_2660944 < baseStart_2660944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660948 : List Nat := [2, 4, 1, 1, 1, 4, 1, 4, 5]
def baseStart_2660948 : Nat := 118140960795 + 2660948 * 2 ^ 59
def prefixEnd_2660948 : Nat := 4983230072969 + 3 ^ 40 * 2660948 * 2
def baseEnd_2660948 : Nat := 151816146735573362490281

theorem tailTrace_2660948 : CollatzResearch.WordTrace tailWord_2660948 prefixEnd_2660948 151816146735573362490281 := by
  unfold tailWord_2660948
  simp only [CollatzResearch.WordTrace]
  refine ⟨48526373381923662291299749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64701831175898216388399665 48526373381923662291299749)
  ·
    refine ⟨9098695009110686679618703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48526373381923662291299749 9098695009110686679618703)
    ·
      refine ⟨13648042513666030019428055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9098695009110686679618703 13648042513666030019428055)
      ·
        refine ⟨20472063770499045029142083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13648042513666030019428055 20472063770499045029142083)
        ·
          refine ⟨30708095655748567543713125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20472063770499045029142083 30708095655748567543713125)
          ·
            refine ⟨5757767935452856414446211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30708095655748567543713125 5757767935452856414446211)
            ·
              refine ⟨8636651903179284621669317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5757767935452856414446211 8636651903179284621669317)
              ·
                refine ⟨1619372231846115866562997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8636651903179284621669317 1619372231846115866562997)
                ·
                  refine ⟨151816146735573362490281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1619372231846115866562997 151816146735573362490281)
                  ·
                    rfl

theorem cell23_2660948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_2660948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660948 prefixEnd_2660948 := by exact prefixLift 2660948
  have htrace : WordTrace (prefixWord ++ tailWord_2660948) baseStart_2660948 baseEnd_2660948 := by
    simpa [prefixWord, tailWord_2660948, baseEnd_2660948] using wordTrace_append hprefix tailTrace_2660948
  have hstable : (prefixWord ++ tailWord_2660948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660948).length < 2 ^ (prefixWord ++ tailWord_2660948).sum := by decide
  have hdescent : baseEnd_2660948 < baseStart_2660948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2660951 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 1, 7, 2]
def baseStart_2660951 : Nat := 118140960795 + 2660951 * 2 ^ 59
def prefixEnd_2660951 : Nat := 4983230072969 + 3 ^ 40 * 2660951 * 2
def baseEnd_2660951 : Nat := 1366346861062123750675015

theorem tailTrace_2660951 : CollatzResearch.WordTrace tailWord_2660951 prefixEnd_2660951 1366346861062123750675015 := by
  unfold tailWord_2660951
  simp only [CollatzResearch.WordTrace]
  refine ⟨97052856182836456094958707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64701904121890970729972471 97052856182836456094958707)
  ·
    refine ⟨145579284274254684142438061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97052856182836456094958707 145579284274254684142438061)
    ·
      refine ⟨54592231602845506553414273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145579284274254684142438061 54592231602845506553414273)
      ·
        refine ⟨40944173702134129915060705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54592231602845506553414273 40944173702134129915060705)
        ·
          refine ⟨30708130276600597436295529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40944173702134129915060705 30708130276600597436295529)
          ·
            refine ⟨23031097707450448077221647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30708130276600597436295529 23031097707450448077221647)
            ·
              refine ⟨34546646561175672115832471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23031097707450448077221647 34546646561175672115832471)
              ·
                refine ⟨51819969841763508173748707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34546646561175672115832471 51819969841763508173748707)
                ·
                  refine ⟨77729954762645262260623061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51819969841763508173748707 77729954762645262260623061)
                  ·
                    refine ⟨1821795814749498334233353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 77729954762645262260623061 1821795814749498334233353)
                    ·
                      refine ⟨1366346861062123750675015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1821795814749498334233353 1366346861062123750675015)
                      ·
                        rfl

theorem cell23_2660951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_2660951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2660951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2660951 prefixEnd_2660951 := by exact prefixLift 2660951
  have htrace : WordTrace (prefixWord ++ tailWord_2660951) baseStart_2660951 baseEnd_2660951 := by
    simpa [prefixWord, tailWord_2660951, baseEnd_2660951] using wordTrace_append hprefix tailTrace_2660951
  have hstable : (prefixWord ++ tailWord_2660951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2660951).length < 2 ^ (prefixWord ++ tailWord_2660951).sum := by decide
  have hdescent : baseEnd_2660951 < baseStart_2660951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2660951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661001 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 4, 2, 3]
def baseStart_2661001 : Nat := 118140960795 + 2661001 * 2 ^ 59
def prefixEnd_2661001 : Nat := 4983230072969 + 3 ^ 40 * 2661001 * 2
def baseEnd_2661001 : Nat := 1366372535094848555049785

theorem tailTrace_2661001 : CollatzResearch.WordTrace tailWord_2661001 prefixEnd_2661001 1366372535094848555049785 := by
  unfold tailWord_2661001
  simp only [CollatzResearch.WordTrace]
  refine ⟨97054679832655314634278857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64703119888436876422852571 97054679832655314634278857)
  ·
    refine ⟨72791009874491485975709143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97054679832655314634278857 72791009874491485975709143)
    ·
      refine ⟨109186514811737228963563715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72791009874491485975709143 109186514811737228963563715)
      ·
        refine ⟨163779772217605843445345573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109186514811737228963563715 163779772217605843445345573)
        ·
          refine ⟨30708707290801095646002295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163779772217605843445345573 30708707290801095646002295)
          ·
            refine ⟨46063060936201643469003443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30708707290801095646002295 46063060936201643469003443)
            ·
              refine ⟨69094591404302465203505165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46063060936201643469003443 69094591404302465203505165)
              ·
                refine ⟨25910471776613424451314437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69094591404302465203505165 25910471776613424451314437)
                ·
                  refine ⟨4858213458115017084621457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25910471776613424451314437 4858213458115017084621457)
                  ·
                    refine ⟨3643660093586262813466093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4858213458115017084621457 3643660093586262813466093)
                    ·
                      refine ⟨1366372535094848555049785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3643660093586262813466093 1366372535094848555049785)
                      ·
                        rfl

theorem cell23_2661001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 2, 3].length) (baseStart_2661001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661001 prefixEnd_2661001 := by exact prefixLift 2661001
  have htrace : WordTrace (prefixWord ++ tailWord_2661001) baseStart_2661001 baseEnd_2661001 := by
    simpa [prefixWord, tailWord_2661001, baseEnd_2661001] using wordTrace_append hprefix tailTrace_2661001
  have hstable : (prefixWord ++ tailWord_2661001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661001).length < 2 ^ (prefixWord ++ tailWord_2661001).sum := by decide
  have hdescent : baseEnd_2661001 < baseStart_2661001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661021 : List Nat := [1, 4, 2, 1, 1, 1, 2, 5, 6]
def baseStart_2661021 : Nat := 118140960795 + 2661021 * 2 ^ 59
def prefixEnd_2661021 : Nat := 4983230072969 + 3 ^ 40 * 2661021 * 2
def baseEnd_2661021 : Nat := 151820311634215386311077

theorem tailTrace_2661021 : CollatzResearch.WordTrace tailWord_2661021 prefixEnd_2661021 151820311634215386311077 := by
  unfold tailWord_2661021
  simp only [CollatzResearch.WordTrace]
  refine ⟨97055409292582858050006917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64703606195055238700004611 97055409292582858050006917)
  ·
    refine ⟨18197889242359285884376297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97055409292582858050006917 18197889242359285884376297)
    ·
      refine ⟨13648416931769464413282223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18197889242359285884376297 13648416931769464413282223)
      ·
        refine ⟨20472625397654196619923335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13648416931769464413282223 20472625397654196619923335)
        ·
          refine ⟨30708938096481294929885003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20472625397654196619923335 30708938096481294929885003)
          ·
            refine ⟨46063407144721942394827505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30708938096481294929885003 46063407144721942394827505)
            ·
              refine ⟨34547555358541456796120629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46063407144721942394827505 34547555358541456796120629)
              ·
                refine ⟨3238833314863261574636309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34547555358541456796120629 3238833314863261574636309)
                ·
                  refine ⟨151820311634215386311077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3238833314863261574636309 151820311634215386311077)
                  ·
                    rfl

theorem cell23_2661021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_2661021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661021 prefixEnd_2661021 := by exact prefixLift 2661021
  have htrace : WordTrace (prefixWord ++ tailWord_2661021) baseStart_2661021 baseEnd_2661021 := by
    simpa [prefixWord, tailWord_2661021, baseEnd_2661021] using wordTrace_append hprefix tailTrace_2661021
  have hstable : (prefixWord ++ tailWord_2661021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661021).length < 2 ^ (prefixWord ++ tailWord_2661021).sum := by decide
  have hdescent : baseEnd_2661021 < baseStart_2661021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661038 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 8]
def baseStart_2661038 : Nat := 118140960795 + 2661038 * 2 ^ 59
def prefixEnd_2661038 : Nat := 4983230072969 + 3 ^ 40 * 2661038 * 2
def baseEnd_2661038 : Nat := 151821281542118323365235

theorem tailTrace_2661038 : CollatzResearch.WordTrace tailWord_2661038 prefixEnd_2661038 151821281542118323365235 := by
  unfold tailWord_2661038
  simp only [CollatzResearch.WordTrace]
  refine ⟨12132003666690158744171971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64704019555680846635583845 12132003666690158744171971)
  ·
    refine ⟨18198005500035238116257957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12132003666690158744171971 18198005500035238116257957)
    ·
      refine ⟨3412126031256607146798367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18198005500035238116257957 3412126031256607146798367)
      ·
        refine ⟨5118189046884910720197551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3412126031256607146798367 5118189046884910720197551)
        ·
          refine ⟨7677283570327366080296327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5118189046884910720197551 7677283570327366080296327)
          ·
            refine ⟨11515925355491049120444491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7677283570327366080296327 11515925355491049120444491)
            ·
              refine ⟨17273888033236573680666737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11515925355491049120444491 17273888033236573680666737)
              ·
                refine ⟨12955416024927430260500053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17273888033236573680666737 12955416024927430260500053)
                ·
                  refine ⟨151821281542118323365235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12955416024927430260500053 151821281542118323365235)
                  ·
                    rfl

theorem cell23_2661038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_2661038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661038 prefixEnd_2661038 := by exact prefixLift 2661038
  have htrace : WordTrace (prefixWord ++ tailWord_2661038) baseStart_2661038 baseEnd_2661038 := by
    simpa [prefixWord, tailWord_2661038, baseEnd_2661038] using wordTrace_append hprefix tailTrace_2661038
  have hstable : (prefixWord ++ tailWord_2661038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661038).length < 2 ^ (prefixWord ++ tailWord_2661038).sum := by decide
  have hdescent : baseEnd_2661038 < baseStart_2661038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661081 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 1, 6]
def baseStart_2661081 : Nat := 118140960795 + 2661081 * 2 ^ 59
def prefixEnd_2661081 : Nat := 4983230072969 + 3 ^ 40 * 2661081 * 2
def baseEnd_2661081 : Nat := 455471204515736080683139

theorem tailTrace_2661081 : CollatzResearch.WordTrace tailWord_2661081 prefixEnd_2661081 455471204515736080683139 := by
  unfold tailWord_2661081
  simp only [CollatzResearch.WordTrace]
  refine ⟨97057597672365488297191097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64705065114910325531460731 97057597672365488297191097)
  ·
    refine ⟨72793198254274116222893323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97057597672365488297191097 72793198254274116222893323)
    ·
      refine ⟨109189797381411174334339985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72793198254274116222893323 109189797381411174334339985)
      ·
        refine ⟨81892348036058380750754989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109189797381411174334339985 81892348036058380750754989)
        ·
          refine ⟨30709630513521892781533121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81892348036058380750754989 30709630513521892781533121)
          ·
            refine ⟨23032222885141419586149841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30709630513521892781533121 23032222885141419586149841)
            ·
              refine ⟨17274167163856064689612381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23032222885141419586149841 17274167163856064689612381)
              ·
                refine ⟨6477812686446024258604643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17274167163856064689612381 6477812686446024258604643)
                ·
                  refine ⟨9716719029669036387906965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6477812686446024258604643 9716719029669036387906965)
                  ·
                    refine ⟨455471204515736080683139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9716719029669036387906965 455471204515736080683139)
                    ·
                      rfl

theorem cell23_2661081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 6].length) (baseStart_2661081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661081 prefixEnd_2661081 := by exact prefixLift 2661081
  have htrace : WordTrace (prefixWord ++ tailWord_2661081) baseStart_2661081 baseEnd_2661081 := by
    simpa [prefixWord, tailWord_2661081, baseEnd_2661081] using wordTrace_append hprefix tailTrace_2661081
  have hstable : (prefixWord ++ tailWord_2661081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661081).length < 2 ^ (prefixWord ++ tailWord_2661081).sum := by decide
  have hdescent : baseEnd_2661081 < baseStart_2661081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661105 : List Nat := [1, 2, 2, 2, 2, 2, 5, 1, 1, 1, 4]
def baseStart_2661105 : Nat := 118140960795 + 2661105 * 2 ^ 59
def prefixEnd_2661105 : Nat := 4983230072969 + 3 ^ 40 * 2661105 * 2
def baseEnd_2661105 : Nat := 1366425937082916148149307

theorem tailTrace_2661105 : CollatzResearch.WordTrace tailWord_2661105 prefixEnd_2661105 1366425937082916148149307 := by
  unfold tailWord_2661105
  simp only [CollatzResearch.WordTrace]
  refine ⟨97058473024278540396064769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64705648682852360264043179 97058473024278540396064769)
  ·
    refine ⟨72793854768208905297048577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97058473024278540396064769 72793854768208905297048577)
    ·
      refine ⟨54595391076156678972786433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72793854768208905297048577 54595391076156678972786433)
      ·
        refine ⟨40946543307117509229589825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54595391076156678972786433 40946543307117509229589825)
        ·
          refine ⟨30709907480338131922192369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40946543307117509229589825 30709907480338131922192369)
          ·
            refine ⟨23032430610253598941644277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30709907480338131922192369 23032430610253598941644277)
            ·
              refine ⟨2159290369711274900779151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23032430610253598941644277 2159290369711274900779151)
              ·
                refine ⟨3238935554566912351168727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159290369711274900779151 3238935554566912351168727)
                ·
                  refine ⟨4858403331850368526753091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3238935554566912351168727 4858403331850368526753091)
                  ·
                    refine ⟨7287604997775552790129637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4858403331850368526753091 7287604997775552790129637)
                    ·
                      refine ⟨1366425937082916148149307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7287604997775552790129637 1366425937082916148149307)
                      ·
                        rfl

theorem cell23_2661105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_2661105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661105 prefixEnd_2661105 := by exact prefixLift 2661105
  have htrace : WordTrace (prefixWord ++ tailWord_2661105) baseStart_2661105 baseEnd_2661105 := by
    simpa [prefixWord, tailWord_2661105, baseEnd_2661105] using wordTrace_append hprefix tailTrace_2661105
  have hstable : (prefixWord ++ tailWord_2661105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661105).length < 2 ^ (prefixWord ++ tailWord_2661105).sum := by decide
  have hdescent : baseEnd_2661105 < baseStart_2661105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661128 : List Nat := [2, 1, 3, 2, 2, 4, 1, 8]
def baseStart_2661128 : Nat := 118140960795 + 2661128 * 2 ^ 59
def prefixEnd_2661128 : Nat := 4983230072969 + 3 ^ 40 * 2661128 * 2
def baseEnd_2661128 : Nat := 50608805449554428080063

theorem tailTrace_2661128 : CollatzResearch.WordTrace tailWord_2661128 prefixEnd_2661128 50608805449554428080063 := by
  unfold tailWord_2661128
  simp only [CollatzResearch.WordTrace]
  refine ⟨48529655951597607662076019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64706207935463476882768025 48529655951597607662076019)
  ·
    refine ⟨72794483927396411493114029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48529655951597607662076019 72794483927396411493114029)
    ·
      refine ⟨27297931472773654309917761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72794483927396411493114029 27297931472773654309917761)
      ·
        refine ⟨20473448604580240732438321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27297931472773654309917761 20473448604580240732438321)
        ·
          refine ⟨15355086453435180549328741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20473448604580240732438321 15355086453435180549328741)
          ·
            refine ⟨2879078710019096352999139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15355086453435180549328741 2879078710019096352999139)
            ·
              refine ⟨4318618065028644529498709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2879078710019096352999139 4318618065028644529498709)
              ·
                refine ⟨50608805449554428080063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4318618065028644529498709 50608805449554428080063)
                ·
                  rfl

theorem cell23_2661128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 8].length) (baseStart_2661128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661128 prefixEnd_2661128 := by exact prefixLift 2661128
  have htrace : WordTrace (prefixWord ++ tailWord_2661128) baseStart_2661128 baseEnd_2661128 := by
    simpa [prefixWord, tailWord_2661128, baseEnd_2661128] using wordTrace_append hprefix tailTrace_2661128
  have hstable : (prefixWord ++ tailWord_2661128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661128).length < 2 ^ (prefixWord ++ tailWord_2661128).sum := by decide
  have hdescent : baseEnd_2661128 < baseStart_2661128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661141 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 2, 7]
def baseStart_2661141 : Nat := 118140960795 + 2661141 * 2 ^ 59
def prefixEnd_2661141 : Nat := 4983230072969 + 3 ^ 40 * 2661141 * 2
def baseEnd_2661141 : Nat := 455481474128826002433047

theorem tailTrace_2661141 : CollatzResearch.WordTrace tailWord_2661141 prefixEnd_2661141 455481474128826002433047 := by
  unfold tailWord_2661141
  simp only [CollatzResearch.WordTrace]
  refine ⟨97059786052148118544375277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64706524034765412362916851 97059786052148118544375277)
  ·
    refine ⟨36397419769555544454140729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97059786052148118544375277 36397419769555544454140729)
    ·
      refine ⟨27298064827166658340605547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36397419769555544454140729 27298064827166658340605547)
      ·
        refine ⟨40947097240749987510908321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27298064827166658340605547 40947097240749987510908321)
        ·
          refine ⟨30710322930562490633181241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40947097240749987510908321 30710322930562490633181241)
          ·
            refine ⟨23032742197921867974885931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30710322930562490633181241 23032742197921867974885931)
            ·
              refine ⟨34549113296882801962328897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23032742197921867974885931 34549113296882801962328897)
              ·
                refine ⟨25911834972662101471746673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34549113296882801962328897 25911834972662101471746673)
                ·
                  refine ⟨19433876229496576103810005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25911834972662101471746673 19433876229496576103810005)
                  ·
                    refine ⟨455481474128826002433047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19433876229496576103810005 455481474128826002433047)
                    ·
                      rfl

theorem cell23_2661141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_2661141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661141 prefixEnd_2661141 := by exact prefixLift 2661141
  have htrace : WordTrace (prefixWord ++ tailWord_2661141) baseStart_2661141 baseEnd_2661141 := by
    simpa [prefixWord, tailWord_2661141, baseEnd_2661141] using wordTrace_append hprefix tailTrace_2661141
  have hstable : (prefixWord ++ tailWord_2661141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661141).length < 2 ^ (prefixWord ++ tailWord_2661141).sum := by decide
  have hdescent : baseEnd_2661141 < baseStart_2661141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661156 : List Nat := [2, 3, 1, 3, 3, 1, 2, 3, 1, 2, 2]
def baseStart_2661156 : Nat := 118140960795 + 2661156 * 2 ^ 59
def prefixEnd_2661156 : Nat := 4983230072969 + 3 ^ 40 * 2661156 * 2
def baseEnd_2661156 : Nat := 1366452124596295448611573

theorem tailTrace_2661156 : CollatzResearch.WordTrace tailWord_2661156 prefixEnd_2661156 1366452124596295448611573 := by
  unfold tailWord_2661156
  simp only [CollatzResearch.WordTrace]
  refine ⟨48530166573546888053085661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64706888764729184070780881 48530166573546888053085661)
  ·
    refine ⟨18198812465080083019907123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48530166573546888053085661 18198812465080083019907123)
    ·
      refine ⟨27298218697620124529860685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18198812465080083019907123 27298218697620124529860685)
      ·
        refine ⟨10236832011607546698697757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27298218697620124529860685 10236832011607546698697757)
        ·
          refine ⟨3838812004352830012011659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10236832011607546698697757 3838812004352830012011659)
          ·
            refine ⟨5758218006529245018017489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3838812004352830012011659 5758218006529245018017489)
            ·
              refine ⟨4318663504896933763513117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5758218006529245018017489 4318663504896933763513117)
              ·
                refine ⟨1619498814336350161317419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4318663504896933763513117 1619498814336350161317419)
                ·
                  refine ⟨2429248221504525241976129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619498814336350161317419 2429248221504525241976129)
                  ·
                    refine ⟨1821936166128393931482097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2429248221504525241976129 1821936166128393931482097)
                    ·
                      refine ⟨1366452124596295448611573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1821936166128393931482097 1366452124596295448611573)
                      ·
                        rfl

theorem cell23_2661156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_2661156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661156 prefixEnd_2661156 := by exact prefixLift 2661156
  have htrace : WordTrace (prefixWord ++ tailWord_2661156) baseStart_2661156 baseEnd_2661156 := by
    simpa [prefixWord, tailWord_2661156, baseEnd_2661156] using wordTrace_append hprefix tailTrace_2661156
  have hstable : (prefixWord ++ tailWord_2661156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661156).length < 2 ^ (prefixWord ++ tailWord_2661156).sum := by decide
  have hdescent : baseEnd_2661156 < baseStart_2661156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661161 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 4, 3, 4]
def baseStart_2661161 : Nat := 118140960795 + 2661161 * 2 ^ 59
def prefixEnd_2661161 : Nat := 4983230072969 + 3 ^ 40 * 2661161 * 2
def baseEnd_2661161 : Nat := 1366454691999567929049049

theorem tailTrace_2661161 : CollatzResearch.WordTrace tailWord_2661161 prefixEnd_2661161 1366454691999567929049049 := by
  unfold tailWord_2661161
  simp only [CollatzResearch.WordTrace]
  refine ⟨97060515512075661960103337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64707010341383774640068891 97060515512075661960103337)
  ·
    refine ⟨72795386634056746470077503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97060515512075661960103337 72795386634056746470077503)
    ·
      refine ⟨109193079951085119705116255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72795386634056746470077503 109193079951085119705116255)
      ·
        refine ⟨163789619926627679557674383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109193079951085119705116255 163789619926627679557674383)
        ·
          refine ⟨245684429889941519336511575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163789619926627679557674383 245684429889941519336511575)
          ·
            refine ⟨368526644834912279004767363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245684429889941519336511575 368526644834912279004767363)
            ·
              refine ⟨552789967252368418507151045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368526644834912279004767363 552789967252368418507151045)
              ·
                refine ⟨103648118859819078470090821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 552789967252368418507151045 103648118859819078470090821)
                ·
                  refine ⟨19434022286216077213142029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103648118859819078470090821 19434022286216077213142029)
                  ·
                    refine ⟨7287758357331028954928261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19434022286216077213142029 7287758357331028954928261)
                    ·
                      refine ⟨1366454691999567929049049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7287758357331028954928261 1366454691999567929049049)
                      ·
                        rfl

theorem cell23_2661161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_2661161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661161 prefixEnd_2661161 := by exact prefixLift 2661161
  have htrace : WordTrace (prefixWord ++ tailWord_2661161) baseStart_2661161 baseEnd_2661161 := by
    simpa [prefixWord, tailWord_2661161, baseEnd_2661161] using wordTrace_append hprefix tailTrace_2661161
  have hstable : (prefixWord ++ tailWord_2661161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661161).length < 2 ^ (prefixWord ++ tailWord_2661161).sum := by decide
  have hdescent : baseEnd_2661161 < baseStart_2661161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661198 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3]
def baseStart_2661198 : Nat := 118140960795 + 2661198 * 2 ^ 59
def prefixEnd_2661198 : Nat := 4983230072969 + 3 ^ 40 * 2661198 * 2
def baseEnd_2661198 : Nat := 1366473690783784284286379

theorem tailTrace_2661198 : CollatzResearch.WordTrace tailWord_2661198 prefixEnd_2661198 1366473690783784284286379 := by
  unfold tailWord_2661198
  simp only [CollatzResearch.WordTrace]
  refine ⟨12132733126617702159900031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64707910008627744852800165 12132733126617702159900031)
  ·
    refine ⟨18199099689926553239850047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12132733126617702159900031 18199099689926553239850047)
    ·
      refine ⟨27298649534889829859775071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18199099689926553239850047 27298649534889829859775071)
      ·
        refine ⟨40947974302334744789662607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27298649534889829859775071 40947974302334744789662607)
        ·
          refine ⟨61421961453502117184493911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40947974302334744789662607 61421961453502117184493911)
          ·
            refine ⟨92132942180253175776740867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61421961453502117184493911 92132942180253175776740867)
            ·
              refine ⟨138199413270379763665111301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92132942180253175776740867 138199413270379763665111301)
              ·
                refine ⟨25912389988196205687208369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138199413270379763665111301 25912389988196205687208369)
                ·
                  refine ⟨19434292491147154265406277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25912389988196205687208369 19434292491147154265406277)
                  ·
                    refine ⟨3643929842090091424763677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19434292491147154265406277 3643929842090091424763677)
                    ·
                      refine ⟨1366473690783784284286379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3643929842090091424763677 1366473690783784284286379)
                      ·
                        rfl

theorem cell23_2661198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_2661198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661198 prefixEnd_2661198 := by exact prefixLift 2661198
  have htrace : WordTrace (prefixWord ++ tailWord_2661198) baseStart_2661198 baseEnd_2661198 := by
    simpa [prefixWord, tailWord_2661198, baseEnd_2661198] using wordTrace_append hprefix tailTrace_2661198
  have hstable : (prefixWord ++ tailWord_2661198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661198).length < 2 ^ (prefixWord ++ tailWord_2661198).sum := by decide
  have hdescent : baseEnd_2661198 < baseStart_2661198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661250 : List Nat := [3, 4, 2, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_2661250 : Nat := 118140960795 + 2661250 * 2 ^ 59
def prefixEnd_2661250 : Nat := 4983230072969 + 3 ^ 40 * 2661250 * 2
def baseEnd_2661250 : Nat := 1366500391777818080836141

theorem tailTrace_2661250 : CollatzResearch.WordTrace tailWord_2661250 prefixEnd_2661250 1366500391777818080836141 := by
  unfold tailWord_2661250
  simp only [CollatzResearch.WordTrace]
  refine ⟨24265940402188307540023301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64709174405835486773395469 24265940402188307540023301)
  ·
    refine ⟨4549863825410307663754369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24265940402188307540023301 4549863825410307663754369)
    ·
      refine ⟨3412397869057730747815777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4549863825410307663754369 3412397869057730747815777)
      ·
        refine ⟨2559298401793298060861833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3412397869057730747815777 2559298401793298060861833)
        ·
          refine ⟨1919473801344973545646375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2559298401793298060861833 1919473801344973545646375)
          ·
            refine ⟨2879210702017460318469563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919473801344973545646375 2879210702017460318469563)
            ·
              refine ⟨4318816053026190477704345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2879210702017460318469563 4318816053026190477704345)
              ·
                refine ⟨3239112039769642858278259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4318816053026190477704345 3239112039769642858278259)
                ·
                  refine ⟨4858668059654464287417389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3239112039769642858278259 4858668059654464287417389)
                  ·
                    refine ⟨1822000522370424107781521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4858668059654464287417389 1822000522370424107781521)
                    ·
                      refine ⟨1366500391777818080836141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1822000522370424107781521 1366500391777818080836141)
                      ·
                        rfl

theorem cell23_2661250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_2661250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661250 prefixEnd_2661250 := by exact prefixLift 2661250
  have htrace : WordTrace (prefixWord ++ tailWord_2661250) baseStart_2661250 baseEnd_2661250 := by
    simpa [prefixWord, tailWord_2661250, baseEnd_2661250] using wordTrace_append hprefix tailTrace_2661250
  have hstable : (prefixWord ++ tailWord_2661250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661250).length < 2 ^ (prefixWord ++ tailWord_2661250).sum := by decide
  have hdescent : baseEnd_2661250 < baseStart_2661250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2661298 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_2661298 : Nat := 118140960795 + 2661298 * 2 ^ 59
def prefixEnd_2661298 : Nat := 4983230072969 + 3 ^ 40 * 2661298 * 2
def baseEnd_2661298 : Nat := 1366525038849233893035919

theorem tailTrace_2661298 : CollatzResearch.WordTrace tailWord_2661298 prefixEnd_2661298 1366525038849233893035919 := by
  unfold tailWord_2661298
  simp only [CollatzResearch.WordTrace]
  refine ⟨24266378078144833589460137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64710341541719556238560365 24266378078144833589460137)
  ·
    refine ⟨18199783558608625192095103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24266378078144833589460137 18199783558608625192095103)
    ·
      refine ⟨27299675337912937788142655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18199783558608625192095103 27299675337912937788142655)
      ·
        refine ⟨40949513006869406682213983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27299675337912937788142655 40949513006869406682213983)
        ·
          refine ⟨61424269510304110023320975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40949513006869406682213983 61424269510304110023320975)
          ·
            refine ⟨92136404265456165034981463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61424269510304110023320975 92136404265456165034981463)
            ·
              refine ⟨138204606398184247552472195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92136404265456165034981463 138204606398184247552472195)
              ·
                refine ⟨207306909597276371328708293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138204606398184247552472195 207306909597276371328708293)
                ·
                  refine ⟨38870045549489319624132805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 207306909597276371328708293 38870045549489319624132805)
                  ·
                    refine ⟨7288133540529247429524901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38870045549489319624132805 7288133540529247429524901)
                    ·
                      refine ⟨1366525038849233893035919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7288133540529247429524901 1366525038849233893035919)
                      ·
                        rfl

theorem cell23_2661298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_2661298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2661298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2661298 prefixEnd_2661298 := by exact prefixLift 2661298
  have htrace : WordTrace (prefixWord ++ tailWord_2661298) baseStart_2661298 baseEnd_2661298 := by
    simpa [prefixWord, tailWord_2661298, baseEnd_2661298] using wordTrace_append hprefix tailTrace_2661298
  have hstable : (prefixWord ++ tailWord_2661298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2661298).length < 2 ^ (prefixWord ++ tailWord_2661298).sum := by decide
  have hdescent : baseEnd_2661298 < baseStart_2661298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2661298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
