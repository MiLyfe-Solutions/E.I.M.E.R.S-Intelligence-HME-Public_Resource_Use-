import V185TrunkScan23Chunk0764

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4524338 : List Nat := [3, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2]
def baseStart_4524338 : Nat := 118140960795 + 4524338 * 2 ^ 59
def prefixEnd_4524338 : Nat := 4983230072969 + 3 ^ 40 * 4524338 * 2
def baseEnd_4524338 : Nat := 2323160037401624740467955

theorem tailTrace_4524338 : CollatzResearch.WordTrace tailWord_4524338 prefixEnd_4524338 2323160037401624740467955 := by
  unfold tailWord_4524338
  simp only [CollatzResearch.WordTrace]
  refine ⟨41254040870775899064521417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110010775655402397505390445 41254040870775899064521417)
  ·
    refine ⟨30940530653081924298391063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41254040870775899064521417 30940530653081924298391063)
    ·
      refine ⟨46410795979622886447586595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30940530653081924298391063 46410795979622886447586595)
      ·
        refine ⟨69616193969434329671379893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46410795979622886447586595 69616193969434329671379893)
        ·
          refine ⟨6526518184634468406691865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69616193969434329671379893 6526518184634468406691865)
          ·
            refine ⟨4894888638475851305018899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6526518184634468406691865 4894888638475851305018899)
            ·
              refine ⟨7342332957713776957528349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4894888638475851305018899 7342332957713776957528349)
              ·
                refine ⟨2753374859142666359073131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7342332957713776957528349 2753374859142666359073131)
                ·
                  refine ⟨4130062288713999538609697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2753374859142666359073131 4130062288713999538609697)
                  ·
                    refine ⟨3097546716535499653957273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4130062288713999538609697 3097546716535499653957273)
                    ·
                      refine ⟨2323160037401624740467955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3097546716535499653957273 2323160037401624740467955)
                      ·
                        rfl

theorem cell23_4524338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_4524338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524338 prefixEnd_4524338 := by exact prefixLift 4524338
  have htrace : WordTrace (prefixWord ++ tailWord_4524338) baseStart_4524338 baseEnd_4524338 := by
    simpa [prefixWord, tailWord_4524338, baseEnd_4524338] using wordTrace_append hprefix tailTrace_4524338
  have hstable : (prefixWord ++ tailWord_4524338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524338).length < 2 ^ (prefixWord ++ tailWord_4524338).sum := by decide
  have hdescent : baseEnd_4524338 < baseStart_4524338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524383 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 7]
def baseStart_4524383 : Nat := 118140960795 + 4524383 * 2 ^ 59
def prefixEnd_4524383 : Nat := 4983230072969 + 3 ^ 40 * 4524383 * 2
def baseEnd_4524383 : Nat := 258131460447897451600583

theorem tailTrace_4524383 : CollatzResearch.WordTrace tailWord_4524383 prefixEnd_4524383 258131460447897451600583 := by
  unfold tailWord_4524383
  simp only [CollatzResearch.WordTrace]
  refine ⟨165017804767940568943473803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110011869845293712628982535 165017804767940568943473803)
  ·
    refine ⟨247526707151910853415210705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165017804767940568943473803 247526707151910853415210705)
    ·
      refine ⟨185645030363933140061408029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247526707151910853415210705 185645030363933140061408029)
      ·
        refine ⟨69616886386474927523028011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185645030363933140061408029 69616886386474927523028011)
        ·
          refine ⟨104425329579712391284542017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69616886386474927523028011 104425329579712391284542017)
          ·
            refine ⟨78318997184784293463406513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104425329579712391284542017 78318997184784293463406513)
            ·
              refine ⟨58739247888588220097554885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78318997184784293463406513 58739247888588220097554885)
              ·
                refine ⟨11013608979110291268291541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58739247888588220097554885 11013608979110291268291541)
                ·
                  refine ⟨258131460447897451600583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11013608979110291268291541 258131460447897451600583)
                  ·
                    rfl

theorem cell23_4524383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 7].length) (baseStart_4524383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524383 prefixEnd_4524383 := by exact prefixLift 4524383
  have htrace : WordTrace (prefixWord ++ tailWord_4524383) baseStart_4524383 baseEnd_4524383 := by
    simpa [prefixWord, tailWord_4524383, baseEnd_4524383] using wordTrace_append hprefix tailTrace_4524383
  have hstable : (prefixWord ++ tailWord_4524383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524383).length < 2 ^ (prefixWord ++ tailWord_4524383).sum := by decide
  have hdescent : baseEnd_4524383 < baseStart_4524383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524394 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 1, 4, 2]
def baseStart_4524394 : Nat := 118140960795 + 4524394 * 2 ^ 59
def prefixEnd_4524394 : Nat := 4983230072969 + 3 ^ 40 * 4524394 * 2
def baseEnd_4524394 : Nat := 2323188792318276521367697

theorem tailTrace_4524394 : CollatzResearch.WordTrace tailWord_4524394 prefixEnd_4524394 2323188792318276521367697 := by
  unfold tailWord_4524394
  simp only [CollatzResearch.WordTrace]
  refine ⟨41254551492725179455531059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110012137313933811881416157 41254551492725179455531059)
  ·
    refine ⟨61881827239087769183296589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41254551492725179455531059 61881827239087769183296589)
    ·
      refine ⟨23205685214657913443736221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61881827239087769183296589 23205685214657913443736221)
      ·
        refine ⟨8702131955496717541401083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23205685214657913443736221 8702131955496717541401083)
        ·
          refine ⟨13053197933245076312101625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8702131955496717541401083 13053197933245076312101625)
          ·
            refine ⟨9789898449933807234076219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13053197933245076312101625 9789898449933807234076219)
            ·
              refine ⟨14684847674900710851114329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9789898449933807234076219 14684847674900710851114329)
              ·
                refine ⟨11013635756175533138335747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14684847674900710851114329 11013635756175533138335747)
                ·
                  refine ⟨16520453634263299707503621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11013635756175533138335747 16520453634263299707503621)
                  ·
                    refine ⟨3097585056424368695156929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16520453634263299707503621 3097585056424368695156929)
                    ·
                      refine ⟨2323188792318276521367697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3097585056424368695156929 2323188792318276521367697)
                      ·
                        rfl

theorem cell23_4524394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_4524394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524394 prefixEnd_4524394 := by exact prefixLift 4524394
  have htrace : WordTrace (prefixWord ++ tailWord_4524394) baseStart_4524394 baseEnd_4524394 := by
    simpa [prefixWord, tailWord_4524394, baseEnd_4524394] using wordTrace_append hprefix tailTrace_4524394
  have hstable : (prefixWord ++ tailWord_4524394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524394).length < 2 ^ (prefixWord ++ tailWord_4524394).sum := by decide
  have hdescent : baseEnd_4524394 < baseStart_4524394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524460 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 7, 4]
def baseStart_4524460 : Nat := 118140960795 + 4524460 * 2 ^ 59
def prefixEnd_4524460 : Nat := 4983230072969 + 3 ^ 40 * 4524460 * 2
def baseEnd_4524460 : Nat := 774407560680491087714131

theorem tailTrace_4524460 : CollatzResearch.WordTrace tailWord_4524460 prefixEnd_4524460 774407560680491087714131 := by
  unfold tailWord_4524460
  simp only [CollatzResearch.WordTrace]
  refine ⟨82510306594330805547013417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110013742125774407396017889 82510306594330805547013417)
  ·
    refine ⟨61882729945748104160260063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82510306594330805547013417 61882729945748104160260063)
    ·
      refine ⟨92824094918622156240390095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61882729945748104160260063 92824094918622156240390095)
      ·
        refine ⟨139236142377933234360585143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92824094918622156240390095 139236142377933234360585143)
        ·
          refine ⟨208854213566899851540877715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139236142377933234360585143 208854213566899851540877715)
          ·
            refine ⟨313281320350349777311316573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208854213566899851540877715 313281320350349777311316573)
            ·
              refine ⟨117480495131381166491743715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 313281320350349777311316573 117480495131381166491743715)
              ·
                refine ⟨176220742697071749737615573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117480495131381166491743715 176220742697071749737615573)
                ·
                  refine ⟨4130173656962619134475365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 176220742697071749737615573 4130173656962619134475365)
                  ·
                    refine ⟨774407560680491087714131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4130173656962619134475365 774407560680491087714131)
                    ·
                      rfl

theorem cell23_4524460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_4524460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524460 prefixEnd_4524460 := by exact prefixLift 4524460
  have htrace : WordTrace (prefixWord ++ tailWord_4524460) baseStart_4524460 baseEnd_4524460 := by
    simpa [prefixWord, tailWord_4524460, baseEnd_4524460] using wordTrace_append hprefix tailTrace_4524460
  have hstable : (prefixWord ++ tailWord_4524460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524460).length < 2 ^ (prefixWord ++ tailWord_4524460).sum := by decide
  have hdescent : baseEnd_4524460 < baseStart_4524460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524477 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 3, 4]
def baseStart_4524477 : Nat := 118140960795 + 4524477 * 2 ^ 59
def prefixEnd_4524477 : Nat := 4983230072969 + 3 ^ 40 * 4524477 * 2
def baseEnd_4524477 : Nat := 774410470404199898876605

theorem tailTrace_4524477 : CollatzResearch.WordTrace tailWord_4524477 prefixEnd_4524477 774410470404199898876605 := by
  unfold tailWord_4524477
  simp only [CollatzResearch.WordTrace]
  refine ⟨165021233229600022997395685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110014155486400015331597123 165021233229600022997395685)
  ·
    refine ⟨30941481230550004312011691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165021233229600022997395685 30941481230550004312011691)
    ·
      refine ⟨46412221845825006468017537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30941481230550004312011691 46412221845825006468017537)
      ·
        refine ⟨34809166384368754851013153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46412221845825006468017537 34809166384368754851013153)
        ·
          refine ⟨26106874788276566138259865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34809166384368754851013153 26106874788276566138259865)
          ·
            refine ⟨19580156091207424603694899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26106874788276566138259865 19580156091207424603694899)
            ·
              refine ⟨29370234136811136905542349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19580156091207424603694899 29370234136811136905542349)
              ·
                refine ⟨11013837801304176339578381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29370234136811136905542349 11013837801304176339578381)
                ·
                  refine ⟨4130189175489066127341893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11013837801304176339578381 4130189175489066127341893)
                  ·
                    refine ⟨774410470404199898876605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4130189175489066127341893 774410470404199898876605)
                    ·
                      rfl

theorem cell23_4524477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_4524477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524477 prefixEnd_4524477 := by exact prefixLift 4524477
  have htrace : WordTrace (prefixWord ++ tailWord_4524477) baseStart_4524477 baseEnd_4524477 := by
    simpa [prefixWord, tailWord_4524477, baseEnd_4524477] using wordTrace_append hprefix tailTrace_4524477
  have hstable : (prefixWord ++ tailWord_4524477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524477).length < 2 ^ (prefixWord ++ tailWord_4524477).sum := by decide
  have hdescent : baseEnd_4524477 < baseStart_4524477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524511 : List Nat := [1, 1, 2, 3, 3, 4, 1, 3, 1, 4]
def baseStart_4524511 : Nat := 118140960795 + 4524511 * 2 ^ 59
def prefixEnd_4524511 : Nat := 4983230072969 + 3 ^ 40 * 4524511 * 2
def baseEnd_4524511 : Nat := 774416289851617521201553

theorem tailTrace_4524511 : CollatzResearch.WordTrace tailWord_4524511 prefixEnd_4524511 774416289851617521201553 := by
  unfold tailWord_4524511
  simp only [CollatzResearch.WordTrace]
  refine ⟨165022473311476846804133387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110014982207651231202755591 165022473311476846804133387)
  ·
    refine ⟨247533709967215270206200081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165022473311476846804133387 247533709967215270206200081)
    ·
      refine ⟨185650282475411452654650061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247533709967215270206200081 185650282475411452654650061)
      ·
        refine ⟨69618855928279294745493773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185650282475411452654650061 69618855928279294745493773)
        ·
          refine ⟨26107070973104735529560165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69618855928279294745493773 26107070973104735529560165)
          ·
            refine ⟨4895075807457137911792531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26107070973104735529560165 4895075807457137911792531)
            ·
              refine ⟨7342613711185706867688797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4895075807457137911792531 7342613711185706867688797)
              ·
                refine ⟨2753480141694640075383299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7342613711185706867688797 2753480141694640075383299)
                ·
                  refine ⟨4130220212541960113074949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2753480141694640075383299 4130220212541960113074949)
                  ·
                    refine ⟨774416289851617521201553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4130220212541960113074949 774416289851617521201553)
                    ·
                      rfl

theorem cell23_4524511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 1, 4].length) (baseStart_4524511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524511 prefixEnd_4524511 := by exact prefixLift 4524511
  have htrace : WordTrace (prefixWord ++ tailWord_4524511) baseStart_4524511 baseEnd_4524511 := by
    simpa [prefixWord, tailWord_4524511, baseEnd_4524511] using wordTrace_append hprefix tailTrace_4524511
  have hstable : (prefixWord ++ tailWord_4524511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524511).length < 2 ^ (prefixWord ++ tailWord_4524511).sum := by decide
  have hdescent : baseEnd_4524511 < baseStart_4524511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524540 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_4524540 : Nat := 118140960795 + 4524540 * 2 ^ 59
def prefixEnd_4524540 : Nat := 4983230072969 + 3 ^ 40 * 4524540 * 2
def baseEnd_4524540 : Nat := 2323263760493832950142025

theorem tailTrace_4524540 : CollatzResearch.WordTrace tailWord_4524540 prefixEnd_4524540 2323263760493832950142025 := by
  unfold tailWord_4524540
  simp only [CollatzResearch.WordTrace]
  refine ⟨82511765514185892378469537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110015687352247856504626049 82511765514185892378469537)
  ·
    refine ⟨61883824135639419283852153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82511765514185892378469537 61883824135639419283852153)
    ·
      refine ⟨46412868101729564462889115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61883824135639419283852153 46412868101729564462889115)
      ·
        refine ⟨69619302152594346694333673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46412868101729564462889115 69619302152594346694333673)
        ·
          refine ⟨52214476614445760020750255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69619302152594346694333673 52214476614445760020750255)
          ·
            refine ⟨78321714921668640031125383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52214476614445760020750255 78321714921668640031125383)
            ·
              refine ⟨117482572382502960046688075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78321714921668640031125383 117482572382502960046688075)
              ·
                refine ⟨176223858573754440070032113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117482572382502960046688075 176223858573754440070032113)
                ·
                  refine ⟨132167893930315830052524085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176223858573754440070032113 132167893930315830052524085)
                  ·
                    refine ⟨12390740055967109067424133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 132167893930315830052524085 12390740055967109067424133)
                    ·
                      refine ⟨2323263760493832950142025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12390740055967109067424133 2323263760493832950142025)
                      ·
                        rfl

theorem cell23_4524540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_4524540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524540 prefixEnd_4524540 := by exact prefixLift 4524540
  have htrace : WordTrace (prefixWord ++ tailWord_4524540) baseStart_4524540 baseEnd_4524540 := by
    simpa [prefixWord, tailWord_4524540, baseEnd_4524540] using wordTrace_append hprefix tailTrace_4524540
  have hstable : (prefixWord ++ tailWord_4524540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524540).length < 2 ^ (prefixWord ++ tailWord_4524540).sum := by decide
  have hdescent : baseEnd_4524540 < baseStart_4524540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524604 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 1, 2, 4]
def baseStart_4524604 : Nat := 118140960795 + 4524604 * 2 ^ 59
def prefixEnd_4524604 : Nat := 4983230072969 + 3 ^ 40 * 4524604 * 2
def baseEnd_4524604 : Nat := 2323296623255720699741731

theorem tailTrace_4524604 : CollatzResearch.WordTrace tailWord_4524604 prefixEnd_4524604 2323296623255720699741731 := by
  unfold tailWord_4524604
  simp only [CollatzResearch.WordTrace]
  refine ⟨82512932650069961843634433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110017243533426615791512577 82512932650069961843634433)
  ·
    refine ⟨61884699487552471382725825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82512932650069961843634433 61884699487552471382725825)
    ·
      refine ⟨46413524615664353537044369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61884699487552471382725825 46413524615664353537044369)
      ·
        refine ⟨34810143461748265152783277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46413524615664353537044369 34810143461748265152783277)
        ·
          refine ⟨13053803798155599432293729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34810143461748265152783277 13053803798155599432293729)
          ·
            refine ⟨9790352848616699574220297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13053803798155599432293729 9790352848616699574220297)
            ·
              refine ⟨7342764636462524680665223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9790352848616699574220297 7342764636462524680665223)
              ·
                refine ⟨11014146954693787020997835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7342764636462524680665223 11014146954693787020997835)
                ·
                  refine ⟨16521220432040680531496753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11014146954693787020997835 16521220432040680531496753)
                  ·
                    refine ⟨12390915324030510398622565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16521220432040680531496753 12390915324030510398622565)
                    ·
                      refine ⟨2323296623255720699741731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12390915324030510398622565 2323296623255720699741731)
                      ·
                        rfl

theorem cell23_4524604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_4524604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524604 prefixEnd_4524604 := by exact prefixLift 4524604
  have htrace : WordTrace (prefixWord ++ tailWord_4524604) baseStart_4524604 baseEnd_4524604 := by
    simpa [prefixWord, tailWord_4524604, baseEnd_4524604] using wordTrace_append hprefix tailTrace_4524604
  have hstable : (prefixWord ++ tailWord_4524604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524604).length < 2 ^ (prefixWord ++ tailWord_4524604).sum := by decide
  have hdescent : baseEnd_4524604 < baseStart_4524604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524612 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_4524612 : Nat := 118140960795 + 4524612 * 2 ^ 59
def prefixEnd_4524612 : Nat := 4983230072969 + 3 ^ 40 * 4524612 * 2
def baseEnd_4524612 : Nat := 2323300731100956668441695

theorem tailTrace_4524612 : CollatzResearch.WordTrace tailWord_4524612 prefixEnd_4524612 2323300731100956668441695 := by
  unfold tailWord_4524612
  simp only [CollatzResearch.WordTrace]
  refine ⟨82513078542055470526780045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110017438056073960702373393 82513078542055470526780045)
  ·
    refine ⟨30942404453270801447542517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82513078542055470526780045 30942404453270801447542517)
    ·
      refine ⟨2900850417494137635707111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30942404453270801447542517 2900850417494137635707111)
      ·
        refine ⟨4351275626241206453560667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2900850417494137635707111 4351275626241206453560667)
        ·
          refine ⟨6526913439361809680341001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4351275626241206453560667 6526913439361809680341001)
          ·
            refine ⟨4895185079521357260255751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6526913439361809680341001 4895185079521357260255751)
            ·
              refine ⟨7342777619282035890383627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4895185079521357260255751 7342777619282035890383627)
              ·
                refine ⟨11014166428923053835575441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7342777619282035890383627 11014166428923053835575441)
                ·
                  refine ⟨8260624821692290376681581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11014166428923053835575441 8260624821692290376681581)
                  ·
                    refine ⟨3097734308134608891255593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8260624821692290376681581 3097734308134608891255593)
                    ·
                      refine ⟨2323300731100956668441695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3097734308134608891255593 2323300731100956668441695)
                      ·
                        rfl

theorem cell23_4524612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_4524612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524612 prefixEnd_4524612 := by exact prefixLift 4524612
  have htrace : WordTrace (prefixWord ++ tailWord_4524612) baseStart_4524612 baseEnd_4524612 := by
    simpa [prefixWord, tailWord_4524612, baseEnd_4524612] using wordTrace_append hprefix tailTrace_4524612
  have hstable : (prefixWord ++ tailWord_4524612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524612).length < 2 ^ (prefixWord ++ tailWord_4524612).sum := by decide
  have hdescent : baseEnd_4524612 < baseStart_4524612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524628 : List Nat := [2, 4, 1, 1, 1, 5, 2, 1, 1, 2, 3]
def baseStart_4524628 : Nat := 118140960795 + 4524628 * 2 ^ 59
def prefixEnd_4524628 : Nat := 4983230072969 + 3 ^ 40 * 4524628 * 2
def baseEnd_4524628 : Nat := 2323308946791428605841621

theorem tailTrace_4524628 : CollatzResearch.WordTrace tailWord_4524628 prefixEnd_4524628 2323308946791428605841621 := by
  unfold tailWord_4524628
  simp only [CollatzResearch.WordTrace]
  refine ⟨82513370326026487893071269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110017827101368650524095025 82513370326026487893071269)
  ·
    refine ⟨15471256936129966479950863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82513370326026487893071269 15471256936129966479950863)
    ·
      refine ⟨23206885404194949719926295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15471256936129966479950863 23206885404194949719926295)
      ·
        refine ⟨34810328106292424579889443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23206885404194949719926295 34810328106292424579889443)
        ·
          refine ⟨52215492159438636869834165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34810328106292424579889443 52215492159438636869834165)
          ·
            refine ⟨4895202389947372206546953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52215492159438636869834165 4895202389947372206546953)
            ·
              refine ⟨3671401792460529154910215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4895202389947372206546953 3671401792460529154910215)
              ·
                refine ⟨5507102688690793732365323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3671401792460529154910215 5507102688690793732365323)
                ·
                  refine ⟨8260654033036190598547985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5507102688690793732365323 8260654033036190598547985)
                  ·
                    refine ⟨6195490524777142948910989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8260654033036190598547985 6195490524777142948910989)
                    ·
                      refine ⟨2323308946791428605841621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6195490524777142948910989 2323308946791428605841621)
                      ·
                        rfl

theorem cell23_4524628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_4524628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524628 prefixEnd_4524628 := by exact prefixLift 4524628
  have htrace : WordTrace (prefixWord ++ tailWord_4524628) baseStart_4524628 baseEnd_4524628 := by
    simpa [prefixWord, tailWord_4524628, baseEnd_4524628] using wordTrace_append hprefix tailTrace_4524628
  have hstable : (prefixWord ++ tailWord_4524628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524628).length < 2 ^ (prefixWord ++ tailWord_4524628).sum := by decide
  have hdescent : baseEnd_4524628 < baseStart_4524628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524641 : List Nat := [1, 2, 3, 1, 1, 4, 3, 2, 2, 1, 3]
def baseStart_4524641 : Nat := 118140960795 + 4524641 * 2 ^ 59
def prefixEnd_4524641 : Nat := 4983230072969 + 3 ^ 40 * 4524641 * 2
def baseEnd_4524641 : Nat := 2323315622039937054979061

theorem tailTrace_4524641 : CollatzResearch.WordTrace tailWord_4524641 prefixEnd_4524641 2323315622039937054979061 := by
  unfold tailWord_4524641
  simp only [CollatzResearch.WordTrace]
  refine ⟨165027214801005879006365777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110018143200670586004243851 165027214801005879006365777)
  ·
    refine ⟨123770411100754409254774333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165027214801005879006365777 123770411100754409254774333)
    ·
      refine ⟨46413904162782903470540375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123770411100754409254774333 46413904162782903470540375)
      ·
        refine ⟨69620856244174355205810563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46413904162782903470540375 69620856244174355205810563)
        ·
          refine ⟨104431284366261532808715845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69620856244174355205810563 104431284366261532808715845)
          ·
            refine ⟨19580865818674037401634221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104431284366261532808715845 19580865818674037401634221)
            ·
              refine ⟨7342824682002764025612833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19580865818674037401634221 7342824682002764025612833)
              ·
                refine ⟨5507118511502073019209625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7342824682002764025612833 5507118511502073019209625)
                ·
                  refine ⟨4130338883626554764407219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5507118511502073019209625 4130338883626554764407219)
                  ·
                    refine ⟨6195508325439832146610829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4130338883626554764407219 6195508325439832146610829)
                    ·
                      refine ⟨2323315622039937054979061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6195508325439832146610829 2323315622039937054979061)
                      ·
                        rfl

theorem cell23_4524641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_4524641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524641 prefixEnd_4524641 := by exact prefixLift 4524641
  have htrace : WordTrace (prefixWord ++ tailWord_4524641) baseStart_4524641 baseEnd_4524641 := by
    simpa [prefixWord, tailWord_4524641, baseEnd_4524641] using wordTrace_append hprefix tailTrace_4524641
  have hstable : (prefixWord ++ tailWord_4524641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524641).length < 2 ^ (prefixWord ++ tailWord_4524641).sum := by decide
  have hdescent : baseEnd_4524641 < baseStart_4524641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524658 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 1, 3, 3]
def baseStart_4524658 : Nat := 118140960795 + 4524658 * 2 ^ 59
def prefixEnd_4524658 : Nat := 4983230072969 + 3 ^ 40 * 4524658 * 2
def baseEnd_4524658 : Nat := 2323324351211063488466483

theorem tailTrace_4524658 : CollatzResearch.WordTrace tailWord_4524658 prefixEnd_4524658 2323324351211063488466483 := by
  unfold tailWord_4524658
  simp only [CollatzResearch.WordTrace]
  refine ⟨41256958710486072727433657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110018556561296193939823085 41256958710486072727433657)
  ·
    refine ⟨30942719032864554545575243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41256958710486072727433657 30942719032864554545575243)
    ·
      refine ⟨46414078549296831818362865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30942719032864554545575243 46414078549296831818362865)
      ·
        refine ⟨34810558911972623863772149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46414078549296831818362865 34810558911972623863772149)
        ·
          refine ⟨3263489897997433487228639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34810558911972623863772149 3263489897997433487228639)
          ·
            refine ⟨4895234846996150230842959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3263489897997433487228639 4895234846996150230842959)
            ·
              refine ⟨7342852270494225346264439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4895234846996150230842959 7342852270494225346264439)
              ·
                refine ⟨11014278405741338019396659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7342852270494225346264439 11014278405741338019396659)
                ·
                  refine ⟨16521417608612007029094989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11014278405741338019396659 16521417608612007029094989)
                  ·
                    refine ⟨6195531603229502635910621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16521417608612007029094989 6195531603229502635910621)
                    ·
                      refine ⟨2323324351211063488466483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6195531603229502635910621 2323324351211063488466483)
                      ·
                        rfl

theorem cell23_4524658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_4524658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524658 prefixEnd_4524658 := by exact prefixLift 4524658
  have htrace : WordTrace (prefixWord ++ tailWord_4524658) baseStart_4524658 baseEnd_4524658 := by
    simpa [prefixWord, tailWord_4524658, baseEnd_4524658] using wordTrace_append hprefix tailTrace_4524658
  have hstable : (prefixWord ++ tailWord_4524658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524658).length < 2 ^ (prefixWord ++ tailWord_4524658).sum := by decide
  have hdescent : baseEnd_4524658 < baseStart_4524658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524771 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 1, 6, 2]
def baseStart_4524771 : Nat := 118140960795 + 4524771 * 2 ^ 59
def prefixEnd_4524771 : Nat := 4983230072969 + 3 ^ 40 * 4524771 * 2
def baseEnd_4524771 : Nat := 2323382374525021546353463

theorem tailTrace_4524771 : CollatzResearch.WordTrace tailWord_4524771 prefixEnd_4524771 2323382374525021546353463 := by
  unfold tailWord_4524771
  simp only [CollatzResearch.WordTrace]
  refine ⟨165031956290534911208598167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110021304193689940805732111 165031956290534911208598167)
  ·
    refine ⟨247547934435802366812897251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165031956290534911208598167 247547934435802366812897251)
    ·
      refine ⟨371321901653703550219345877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247547934435802366812897251 371321901653703550219345877)
      ·
        refine ⟨8702857070008676958265919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 371321901653703550219345877 8702857070008676958265919)
        ·
          refine ⟨13054285605013015437398879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8702857070008676958265919 13054285605013015437398879)
          ·
            refine ⟨19581428407519523156098319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13054285605013015437398879 19581428407519523156098319)
            ·
              refine ⟨29372142611279284734147479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19581428407519523156098319 29372142611279284734147479)
              ·
                refine ⟨44058213916918927101221219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29372142611279284734147479 44058213916918927101221219)
                ·
                  refine ⟨66087320875378390651831829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44058213916918927101221219 66087320875378390651831829)
                  ·
                    refine ⟨3097843166033362061804617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66087320875378390651831829 3097843166033362061804617)
                    ·
                      refine ⟨2323382374525021546353463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3097843166033362061804617 2323382374525021546353463)
                      ·
                        rfl

theorem cell23_4524771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_4524771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524771 prefixEnd_4524771 := by exact prefixLift 4524771
  have htrace : WordTrace (prefixWord ++ tailWord_4524771) baseStart_4524771 baseEnd_4524771 := by
    simpa [prefixWord, tailWord_4524771, baseEnd_4524771] using wordTrace_append hprefix tailTrace_4524771
  have hstable : (prefixWord ++ tailWord_4524771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524771).length < 2 ^ (prefixWord ++ tailWord_4524771).sum := by decide
  have hdescent : baseEnd_4524771 < baseStart_4524771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524781 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_4524781 : Nat := 118140960795 + 4524781 * 2 ^ 59
def prefixEnd_4524781 : Nat := 4983230072969 + 3 ^ 40 * 4524781 * 2
def baseEnd_4524781 : Nat := 774462503110522169076139

theorem tailTrace_4524781 : CollatzResearch.WordTrace tailWord_4524781 prefixEnd_4524781 774462503110522169076139 := by
  unfold tailWord_4524781
  simp only [CollatzResearch.WordTrace]
  refine ⟨165032321020498682916462197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110021547346999121944308131 165032321020498682916462197)
  ·
    refine ⟨15471780095671751523418331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165032321020498682916462197 15471780095671751523418331)
    ·
      refine ⟨23207670143507627285127497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15471780095671751523418331 23207670143507627285127497)
      ·
        refine ⟨17405752607630720463845623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23207670143507627285127497 17405752607630720463845623)
        ·
          refine ⟨26108628911446080695768435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17405752607630720463845623 26108628911446080695768435)
          ·
            refine ⟨39162943367169121043652653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26108628911446080695768435 39162943367169121043652653)
            ·
              refine ⟨14686103762688420391369745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39162943367169121043652653 14686103762688420391369745)
              ·
                refine ⟨11014577822016315293527309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14686103762688420391369745 11014577822016315293527309)
                ·
                  refine ⟨4130466683256118235072741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11014577822016315293527309 4130466683256118235072741)
                  ·
                    refine ⟨774462503110522169076139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4130466683256118235072741 774462503110522169076139)
                    ·
                      rfl

theorem cell23_4524781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_4524781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524781 prefixEnd_4524781 := by exact prefixLift 4524781
  have htrace : WordTrace (prefixWord ++ tailWord_4524781) baseStart_4524781 baseEnd_4524781 := by
    simpa [prefixWord, tailWord_4524781, baseEnd_4524781] using wordTrace_append hprefix tailTrace_4524781
  have hstable : (prefixWord ++ tailWord_4524781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524781).length < 2 ^ (prefixWord ++ tailWord_4524781).sum := by decide
  have hdescent : baseEnd_4524781 < baseStart_4524781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524831 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 1, 5, 2]
def baseStart_4524831 : Nat := 118140960795 + 4524831 * 2 ^ 59
def prefixEnd_4524831 : Nat := 4983230072969 + 3 ^ 40 * 4524831 * 2
def baseEnd_4524831 : Nat := 2323413183364291311603187

theorem tailTrace_4524831 : CollatzResearch.WordTrace tailWord_4524831 prefixEnd_4524831 2323413183364291311603187 := by
  unfold tailWord_4524831
  simp only [CollatzResearch.WordTrace]
  refine ⟨165034144670317541455782347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110022763113545027637188231 165034144670317541455782347)
  ·
    refine ⟨247551217005476312183673521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165034144670317541455782347 247551217005476312183673521)
    ·
      refine ⟨185663412754107234137755141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247551217005476312183673521 185663412754107234137755141)
      ·
        refine ⟨34811889891395106400829089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185663412754107234137755141 34811889891395106400829089)
        ·
          refine ⟨26108917418546329800621817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34811889891395106400829089 26108917418546329800621817)
          ·
            refine ⟨19581688063909747350466363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26108917418546329800621817 19581688063909747350466363)
            ·
              refine ⟨29372532095864621025699545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19581688063909747350466363 29372532095864621025699545)
              ·
                refine ⟨22029399071898465769274659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29372532095864621025699545 22029399071898465769274659)
                ·
                  refine ⟨33044098607847698653911989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22029399071898465769274659 33044098607847698653911989)
                  ·
                    refine ⟨3097884244485721748804249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33044098607847698653911989 3097884244485721748804249)
                    ·
                      refine ⟨2323413183364291311603187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3097884244485721748804249 2323413183364291311603187)
                      ·
                        rfl

theorem cell23_4524831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_4524831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524831 prefixEnd_4524831 := by exact prefixLift 4524831
  have htrace : WordTrace (prefixWord ++ tailWord_4524831) baseStart_4524831 baseEnd_4524831 := by
    simpa [prefixWord, tailWord_4524831, baseEnd_4524831] using wordTrace_append hprefix tailTrace_4524831
  have hstable : (prefixWord ++ tailWord_4524831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524831).length < 2 ^ (prefixWord ++ tailWord_4524831).sum := by decide
  have hdescent : baseEnd_4524831 < baseStart_4524831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524871 : List Nat := [1, 1, 4, 1, 2, 1, 1, 6, 2, 4]
def baseStart_4524871 : Nat := 118140960795 + 4524871 * 2 ^ 59
def prefixEnd_4524871 : Nat := 4983230072969 + 3 ^ 40 * 4524871 * 2
def baseEnd_4524871 : Nat := 774477907530157051701001

theorem tailTrace_4524871 : CollatzResearch.WordTrace tailWord_4524871 prefixEnd_4524871 774477907530157051701001 := by
  unfold tailWord_4524871
  simp only [CollatzResearch.WordTrace]
  refine ⟨165035603590172628287238467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110023735726781752191492311 165035603590172628287238467)
  ·
    refine ⟨247553405385258942430857701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165035603590172628287238467 247553405385258942430857701)
    ·
      refine ⟨46416263509736051705785819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 247553405385258942430857701 46416263509736051705785819)
      ·
        refine ⟨69624395264604077558678729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46416263509736051705785819 69624395264604077558678729)
        ·
          refine ⟨52218296448453058169009047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69624395264604077558678729 52218296448453058169009047)
          ·
            refine ⟨78327444672679587253513571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52218296448453058169009047 78327444672679587253513571)
            ·
              refine ⟨117491167009019380880270357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78327444672679587253513571 117491167009019380880270357)
              ·
                refine ⟨5507398453547783478762673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117491167009019380880270357 5507398453547783478762673)
                ·
                  refine ⟨4130548840160837609072005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5507398453547783478762673 4130548840160837609072005)
                  ·
                    refine ⟨774477907530157051701001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4130548840160837609072005 774477907530157051701001)
                    ·
                      rfl

theorem cell23_4524871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_4524871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524871 prefixEnd_4524871 := by exact prefixLift 4524871
  have htrace : WordTrace (prefixWord ++ tailWord_4524871) baseStart_4524871 baseEnd_4524871 := by
    simpa [prefixWord, tailWord_4524871, baseEnd_4524871] using wordTrace_append hprefix tailTrace_4524871
  have hstable : (prefixWord ++ tailWord_4524871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524871).length < 2 ^ (prefixWord ++ tailWord_4524871).sum := by decide
  have hdescent : baseEnd_4524871 < baseStart_4524871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524874 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_4524874 : Nat := 118140960795 + 4524874 * 2 ^ 59
def prefixEnd_4524874 : Nat := 4983230072969 + 3 ^ 40 * 4524874 * 2
def baseEnd_4524874 : Nat := 2323435263032434643365489

theorem tailTrace_4524874 : CollatzResearch.WordTrace tailWord_4524874 prefixEnd_4524874 2323435263032434643365489 := by
  unfold tailWord_4524874
  simp only [CollatzResearch.WordTrace]
  refine ⟨41258928252290439949899419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110023808672774506533065117 41258928252290439949899419)
  ·
    refine ⟨61888392378435659924849129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41258928252290439949899419 61888392378435659924849129)
    ·
      refine ⟨46416294283826744943636847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61888392378435659924849129 46416294283826744943636847)
      ·
        refine ⟨69624441425740117415455271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46416294283826744943636847 69624441425740117415455271)
        ·
          refine ⟨104436662138610176123182907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69624441425740117415455271 104436662138610176123182907)
          ·
            refine ⟨156654993207915264184774361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104436662138610176123182907 156654993207915264184774361)
            ·
              refine ⟨117491244905936448138580771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156654993207915264184774361 117491244905936448138580771)
              ·
                refine ⟨176236867358904672207871157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117491244905936448138580771 176236867358904672207871157)
                ·
                  refine ⟨16522206314897313019487921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 176236867358904672207871157 16522206314897313019487921)
                  ·
                    refine ⟨12391654736172984764615941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16522206314897313019487921 12391654736172984764615941)
                    ·
                      refine ⟨2323435263032434643365489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12391654736172984764615941 2323435263032434643365489)
                      ·
                        rfl

theorem cell23_4524874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_4524874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524874 prefixEnd_4524874 := by exact prefixLift 4524874
  have htrace : WordTrace (prefixWord ++ tailWord_4524874) baseStart_4524874 baseEnd_4524874 := by
    simpa [prefixWord, tailWord_4524874, baseEnd_4524874] using wordTrace_append hprefix tailTrace_4524874
  have hstable : (prefixWord ++ tailWord_4524874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524874).length < 2 ^ (prefixWord ++ tailWord_4524874).sum := by decide
  have hdescent : baseEnd_4524874 < baseStart_4524874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524911 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 6, 1, 3]
def baseStart_4524911 : Nat := 118140960795 + 4524911 * 2 ^ 59
def prefixEnd_4524911 : Nat := 4983230072969 + 3 ^ 40 * 4524911 * 2
def baseEnd_4524911 : Nat := 2323454261816650998602819

theorem tailTrace_4524911 : CollatzResearch.WordTrace tailWord_4524911 prefixEnd_4524911 2323454261816650998602819 := by
  unfold tailWord_4524911
  simp only [CollatzResearch.WordTrace]
  refine ⟨165037062510027715118694587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110024708340018476745796391 165037062510027715118694587)
  ·
    refine ⟨247555593765041572678041881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165037062510027715118694587 247555593765041572678041881)
    ·
      refine ⟨185666695323781179508531411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247555593765041572678041881 185666695323781179508531411)
      ·
        refine ⟨278500042985671769262797117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185666695323781179508531411 278500042985671769262797117)
        ·
          refine ⟨104437516119626913473548919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 278500042985671769262797117 104437516119626913473548919)
          ·
            refine ⟨156656274179440370210323379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104437516119626913473548919 156656274179440370210323379)
            ·
              refine ⟨234984411269160555315485069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156656274179440370210323379 234984411269160555315485069)
              ·
                refine ⟨88119154225935208243306901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234984411269160555315485069 88119154225935208243306901)
                ·
                  refine ⟨4130585354340712886405011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88119154225935208243306901 4130585354340712886405011)
                  ·
                    refine ⟨6195878031511069329607517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4130585354340712886405011 6195878031511069329607517)
                    ·
                      refine ⟨2323454261816650998602819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6195878031511069329607517 2323454261816650998602819)
                      ·
                        rfl

theorem cell23_4524911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 1, 3].length) (baseStart_4524911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524911 prefixEnd_4524911 := by exact prefixLift 4524911
  have htrace : WordTrace (prefixWord ++ tailWord_4524911) baseStart_4524911 baseEnd_4524911 := by
    simpa [prefixWord, tailWord_4524911, baseEnd_4524911] using wordTrace_append hprefix tailTrace_4524911
  have hstable : (prefixWord ++ tailWord_4524911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524911).length < 2 ^ (prefixWord ++ tailWord_4524911).sum := by decide
  have hdescent : baseEnd_4524911 < baseStart_4524911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524924 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_4524924 : Nat := 118140960795 + 4524924 * 2 ^ 59
def prefixEnd_4524924 : Nat := 4983230072969 + 3 ^ 40 * 4524924 * 2
def baseEnd_4524924 : Nat := 2323460937065159447740259

theorem tailTrace_4524924 : CollatzResearch.WordTrace tailWord_4524924 prefixEnd_4524924 2323460937065159447740259 := by
  unfold tailWord_4524924
  simp only [CollatzResearch.WordTrace]
  refine ⟨82518768329490309169458913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110025024439320412225945217 82518768329490309169458913)
  ·
    refine ⟨61889076247117731877094185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82518768329490309169458913 61889076247117731877094185)
    ·
      refine ⟨46416807185338298907820639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61889076247117731877094185 46416807185338298907820639)
      ·
        refine ⟨69625210778007448361730959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46416807185338298907820639 69625210778007448361730959)
        ·
          refine ⟨104437816167011172542596439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69625210778007448361730959 104437816167011172542596439)
          ·
            refine ⟨156656724250516758813894659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104437816167011172542596439 156656724250516758813894659)
            ·
              refine ⟨234985086375775138220841989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156656724250516758813894659 234985086375775138220841989)
              ·
                refine ⟨44059703695457838416407873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 234985086375775138220841989 44059703695457838416407873)
                ·
                  refine ⟨33044777771593378812305905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44059703695457838416407873 33044777771593378812305905)
                  ·
                    refine ⟨24783583328695034109229429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33044777771593378812305905 24783583328695034109229429)
                    ·
                      refine ⟨2323460937065159447740259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24783583328695034109229429 2323460937065159447740259)
                      ·
                        rfl

theorem cell23_4524924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_4524924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524924 prefixEnd_4524924 := by exact prefixLift 4524924
  have htrace : WordTrace (prefixWord ++ tailWord_4524924) baseStart_4524924 baseEnd_4524924 := by
    simpa [prefixWord, tailWord_4524924, baseEnd_4524924] using wordTrace_append hprefix tailTrace_4524924
  have hstable : (prefixWord ++ tailWord_4524924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524924).length < 2 ^ (prefixWord ++ tailWord_4524924).sum := by decide
  have hdescent : baseEnd_4524924 < baseStart_4524924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524981 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_4524981 : Nat := 118140960795 + 4524981 * 2 ^ 59
def prefixEnd_4524981 : Nat := 4983230072969 + 3 ^ 40 * 4524981 * 2
def baseEnd_4524981 : Nat := 2323490205462465724727497

theorem tailTrace_4524981 : CollatzResearch.WordTrace tailWord_4524981 prefixEnd_4524981 2323490205462465724727497 := by
  unfold tailWord_4524981
  simp only [CollatzResearch.WordTrace]
  refine ⟨165039615619774117073742797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110026410413182744715828531 165039615619774117073742797)
  ·
    refine ⟨61889855857415293902653549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165039615619774117073742797 61889855857415293902653549)
    ·
      refine ⟨23208695946530735213495081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61889855857415293902653549 23208695946530735213495081)
      ·
        refine ⟨17406521959898051410121311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23208695946530735213495081 17406521959898051410121311)
        ·
          refine ⟨26109782939847077115181967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17406521959898051410121311 26109782939847077115181967)
          ·
            refine ⟨39164674409770615672772951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26109782939847077115181967 39164674409770615672772951)
            ·
              refine ⟨58747011614655923509159427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39164674409770615672772951 58747011614655923509159427)
              ·
                refine ⟨88120517421983885263739141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58747011614655923509159427 88120517421983885263739141)
                ·
                  refine ⟨16522597016621978486951089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88120517421983885263739141 16522597016621978486951089)
                  ·
                    refine ⟨12391947762466483865213317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16522597016621978486951089 12391947762466483865213317)
                    ·
                      refine ⟨2323490205462465724727497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12391947762466483865213317 2323490205462465724727497)
                      ·
                        rfl

theorem cell23_4524981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_4524981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524981 prefixEnd_4524981 := by exact prefixLift 4524981
  have htrace : WordTrace (prefixWord ++ tailWord_4524981) baseStart_4524981 baseEnd_4524981 := by
    simpa [prefixWord, tailWord_4524981, baseEnd_4524981] using wordTrace_append hprefix tailTrace_4524981
  have hstable : (prefixWord ++ tailWord_4524981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524981).length < 2 ^ (prefixWord ++ tailWord_4524981).sum := by decide
  have hdescent : baseEnd_4524981 < baseStart_4524981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4524985 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 4, 2, 2]
def baseStart_4524985 : Nat := 118140960795 + 4524985 * 2 ^ 59
def prefixEnd_4524985 : Nat := 4983230072969 + 3 ^ 40 * 4524985 * 2
def baseEnd_4524985 : Nat := 2323492259385083709077479

theorem tailTrace_4524985 : CollatzResearch.WordTrace tailWord_4524985 prefixEnd_4524985 2323492259385083709077479 := by
  unfold tailWord_4524985
  simp only [CollatzResearch.WordTrace]
  refine ⟨165039761511759625756888409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110026507674506417171258939 165039761511759625756888409)
  ·
    refine ⟨123779821133819719317666307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165039761511759625756888409 123779821133819719317666307)
    ·
      refine ⟨185669731700729578976499461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123779821133819719317666307 185669731700729578976499461)
      ·
        refine ⟨34813074693886796058093649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185669731700729578976499461 34813074693886796058093649)
        ·
          refine ⟨26109806020415097043570237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34813074693886796058093649 26109806020415097043570237)
          ·
            refine ⟨9791177257655661391338839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26109806020415097043570237 9791177257655661391338839)
            ·
              refine ⟨14686765886483492087008259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9791177257655661391338839 14686765886483492087008259)
              ·
                refine ⟨22030148829725238130512389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14686765886483492087008259 22030148829725238130512389)
                ·
                  refine ⟨4130652905573482149471073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22030148829725238130512389 4130652905573482149471073)
                  ·
                    refine ⟨3097989679180111612103305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4130652905573482149471073 3097989679180111612103305)
                    ·
                      refine ⟨2323492259385083709077479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3097989679180111612103305 2323492259385083709077479)
                      ·
                        rfl

theorem cell23_4524985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_4524985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4524985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4524985 prefixEnd_4524985 := by exact prefixLift 4524985
  have htrace : WordTrace (prefixWord ++ tailWord_4524985) baseStart_4524985 baseEnd_4524985 := by
    simpa [prefixWord, tailWord_4524985, baseEnd_4524985] using wordTrace_append hprefix tailTrace_4524985
  have hstable : (prefixWord ++ tailWord_4524985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4524985).length < 2 ^ (prefixWord ++ tailWord_4524985).sum := by decide
  have hdescent : baseEnd_4524985 < baseStart_4524985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4524985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525042 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 7]
def baseStart_4525042 : Nat := 118140960795 + 4525042 * 2 ^ 59
def prefixEnd_4525042 : Nat := 4983230072969 + 3 ^ 40 * 4525042 * 2
def baseEnd_4525042 : Nat := 258169058642487776229413

theorem tailTrace_4525042 : CollatzResearch.WordTrace tailWord_4525042 prefixEnd_4525042 258169058642487776229413 := by
  unfold tailWord_4525042
  simp only [CollatzResearch.WordTrace]
  refine ⟨41260460118138281122928345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110027893648368749661142253 41260460118138281122928345)
  ·
    refine ⟨30945345088603710842196259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41260460118138281122928345 30945345088603710842196259)
    ·
      refine ⟨46418017632905566263294389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30945345088603710842196259 46418017632905566263294389)
      ·
        refine ⟨4351689153084896837183849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46418017632905566263294389 4351689153084896837183849)
        ·
          refine ⟨3263766864813672627887887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4351689153084896837183849 3263766864813672627887887)
          ·
            refine ⟨4895650297220508941831831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3263766864813672627887887 4895650297220508941831831)
            ·
              refine ⟨7343475445830763412747747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4895650297220508941831831 7343475445830763412747747)
              ·
                refine ⟨11015213168746145119121621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7343475445830763412747747 11015213168746145119121621)
                ·
                  refine ⟨258169058642487776229413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11015213168746145119121621 258169058642487776229413)
                  ·
                    rfl

theorem cell23_4525042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_4525042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525042 prefixEnd_4525042 := by exact prefixLift 4525042
  have htrace : WordTrace (prefixWord ++ tailWord_4525042) baseStart_4525042 baseEnd_4525042 := by
    simpa [prefixWord, tailWord_4525042, baseEnd_4525042] using wordTrace_append hprefix tailTrace_4525042
  have hstable : (prefixWord ++ tailWord_4525042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525042).length < 2 ^ (prefixWord ++ tailWord_4525042).sum := by decide
  have hdescent : baseEnd_4525042 < baseStart_4525042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525102 : List Nat := [4, 1, 3, 1, 1, 1, 3, 4, 1, 4]
def baseStart_4525102 : Nat := 118140960795 + 4525102 * 2 ^ 59
def prefixEnd_4525102 : Nat := 4983230072969 + 3 ^ 40 * 4525102 * 2
def baseEnd_4525102 : Nat := 774517445540553250438147

theorem tailTrace_4525102 : CollatzResearch.WordTrace tailWord_4525102 prefixEnd_4525102 774517445540553250438147 := by
  unfold tailWord_4525102
  simp only [CollatzResearch.WordTrace]
  refine ⟨20630503606541969342362195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110029352568223836492598373 20630503606541969342362195)
  ·
    refine ⟨30945755409812954013543293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20630503606541969342362195 30945755409812954013543293)
    ·
      refine ⟨11604658278679857755078735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30945755409812954013543293 11604658278679857755078735)
      ·
        refine ⟨17406987418019786632618103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11604658278679857755078735 17406987418019786632618103)
        ·
          refine ⟨26110481127029679948927155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17406987418019786632618103 26110481127029679948927155)
          ·
            refine ⟨39165721690544519923390733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26110481127029679948927155 39165721690544519923390733)
            ·
              refine ⟨14687145633954194971271525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39165721690544519923390733 14687145633954194971271525)
              ·
                refine ⟨2753839806366411557113411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14687145633954194971271525 2753839806366411557113411)
                ·
                  refine ⟨4130759709549617335670117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2753839806366411557113411 4130759709549617335670117)
                  ·
                    refine ⟨774517445540553250438147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4130759709549617335670117 774517445540553250438147)
                    ·
                      rfl

theorem cell23_4525102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_4525102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525102 prefixEnd_4525102 := by exact prefixLift 4525102
  have htrace : WordTrace (prefixWord ++ tailWord_4525102) baseStart_4525102 baseEnd_4525102 := by
    simpa [prefixWord, tailWord_4525102, baseEnd_4525102] using wordTrace_append hprefix tailTrace_4525102
  have hstable : (prefixWord ++ tailWord_4525102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525102).length < 2 ^ (prefixWord ++ tailWord_4525102).sum := by decide
  have hdescent : baseEnd_4525102 < baseStart_4525102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525128 : List Nat := [2, 1, 3, 1, 1, 1, 4, 4, 1, 5]
def baseStart_4525128 : Nat := 118140960795 + 4525128 * 2 ^ 59
def prefixEnd_4525128 : Nat := 4983230072969 + 3 ^ 40 * 4525128 * 2
def baseEnd_4525128 : Nat := 774521895706225549863107

theorem tailTrace_4525128 : CollatzResearch.WordTrace tailWord_4525128 prefixEnd_4525128 774521895706225549863107 := by
  unfold tailWord_4525128
  simp only [CollatzResearch.WordTrace]
  refine ⟨82522488575120780589672019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110029984766827707452896025 82522488575120780589672019)
  ·
    refine ⟨123783732862681170884508029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82522488575120780589672019 123783732862681170884508029)
    ·
      refine ⟨46418899823505439081690511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123783732862681170884508029 46418899823505439081690511)
      ·
        refine ⟨69628349735258158622535767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46418899823505439081690511 69628349735258158622535767)
        ·
          refine ⟨104442524602887237933803651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69628349735258158622535767 104442524602887237933803651)
          ·
            refine ⟨156663786904330856900705477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104442524602887237933803651 156663786904330856900705477)
            ·
              refine ⟨29374460044562035668882277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156663786904330856900705477 29374460044562035668882277)
              ·
                refine ⟨5507711258355381687915427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29374460044562035668882277 5507711258355381687915427)
                ·
                  refine ⟨8261566887533072531873141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5507711258355381687915427 8261566887533072531873141)
                  ·
                    refine ⟨774521895706225549863107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8261566887533072531873141 774521895706225549863107)
                    ·
                      rfl

theorem cell23_4525128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_4525128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525128 prefixEnd_4525128 := by exact prefixLift 4525128
  have htrace : WordTrace (prefixWord ++ tailWord_4525128) baseStart_4525128 baseEnd_4525128 := by
    simpa [prefixWord, tailWord_4525128, baseEnd_4525128] using wordTrace_append hprefix tailTrace_4525128
  have hstable : (prefixWord ++ tailWord_4525128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525128).length < 2 ^ (prefixWord ++ tailWord_4525128).sum := by decide
  have hdescent : baseEnd_4525128 < baseStart_4525128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525149 : List Nat := [1, 4, 4, 1, 3, 1, 1, 2, 6]
def baseStart_4525149 : Nat := 118140960795 + 4525149 * 2 ^ 59
def prefixEnd_4525149 : Nat := 4983230072969 + 3 ^ 40 * 4525149 * 2
def baseEnd_4525149 : Nat := 258175163356935674158525

theorem tailTrace_4525149 : CollatzResearch.WordTrace tailWord_4525149 prefixEnd_4525149 258175163356935674158525 := by
  unfold tailWord_4525149
  simp only [CollatzResearch.WordTrace]
  refine ⟨165045743083165481765858501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110030495388776987843905667 165045743083165481765858501)
  ·
    refine ⟨30946076828093527831098469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165045743083165481765858501 30946076828093527831098469)
    ·
      refine ⟨5802389405267536468330963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30946076828093527831098469 5802389405267536468330963)
      ·
        refine ⟨8703584107901304702496445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5802389405267536468330963 8703584107901304702496445)
        ·
          refine ⟨3263844040462989263436167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8703584107901304702496445 3263844040462989263436167)
          ·
            refine ⟨4895766060694483895154251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3263844040462989263436167 4895766060694483895154251)
            ·
              refine ⟨7343649091041725842731377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4895766060694483895154251 7343649091041725842731377)
              ·
                refine ⟨5507736818281294382048533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7343649091041725842731377 5507736818281294382048533)
                ·
                  refine ⟨258175163356935674158525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5507736818281294382048533 258175163356935674158525)
                  ·
                    rfl

theorem cell23_4525149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_4525149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525149 prefixEnd_4525149 := by exact prefixLift 4525149
  have htrace : WordTrace (prefixWord ++ tailWord_4525149) baseStart_4525149 baseEnd_4525149 := by
    simpa [prefixWord, tailWord_4525149, baseEnd_4525149] using wordTrace_append hprefix tailTrace_4525149
  have hstable : (prefixWord ++ tailWord_4525149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525149).length < 2 ^ (prefixWord ++ tailWord_4525149).sum := by decide
  have hdescent : baseEnd_4525149 < baseStart_4525149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525168 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 5]
def baseStart_4525168 : Nat := 118140960795 + 4525168 * 2 ^ 59
def prefixEnd_4525168 : Nat := 4983230072969 + 3 ^ 40 * 4525168 * 2
def baseEnd_4525168 : Nat := 2323586226344856493089137

theorem tailTrace_4525168 : CollatzResearch.WordTrace tailWord_4525168 prefixEnd_4525168 2323586226344856493089137 := by
  unfold tailWord_4525168
  simp only [CollatzResearch.WordTrace]
  refine ⟨82523218035048324005400079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110030957380064432007200105 82523218035048324005400079)
  ·
    refine ⟨123784827052572486008100119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82523218035048324005400079 123784827052572486008100119)
    ·
      refine ⟨185677240578858729012150179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123784827052572486008100119 185677240578858729012150179)
      ·
        refine ⟨278515860868288093518225269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185677240578858729012150179 278515860868288093518225269)
        ·
          refine ⟨26110861956402008767333619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 278515860868288093518225269 26110861956402008767333619)
          ·
            refine ⟨39166292934603013151000429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26110861956402008767333619 39166292934603013151000429)
            ·
              refine ⟨14687359850476129931625161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39166292934603013151000429 14687359850476129931625161)
              ·
                refine ⟨11015519887857097448718871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14687359850476129931625161 11015519887857097448718871)
                ·
                  refine ⟨16523279831785646173078307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11015519887857097448718871 16523279831785646173078307)
                  ·
                    refine ⟨24784919747678469259617461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16523279831785646173078307 24784919747678469259617461)
                    ·
                      refine ⟨2323586226344856493089137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24784919747678469259617461 2323586226344856493089137)
                      ·
                        rfl

theorem cell23_4525168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 5].length) (baseStart_4525168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525168 prefixEnd_4525168 := by exact prefixLift 4525168
  have htrace : WordTrace (prefixWord ++ tailWord_4525168) baseStart_4525168 baseEnd_4525168 := by
    simpa [prefixWord, tailWord_4525168, baseEnd_4525168] using wordTrace_append hprefix tailTrace_4525168
  have hstable : (prefixWord ++ tailWord_4525168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525168).length < 2 ^ (prefixWord ++ tailWord_4525168).sum := by decide
  have hdescent : baseEnd_4525168 < baseStart_4525168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525188 : List Nat := [2, 3, 2, 1, 2, 3, 1, 9]
def baseStart_4525188 : Nat := 118140960795 + 4525188 * 2 ^ 59
def prefixEnd_4525188 : Nat := 4983230072969 + 3 ^ 40 * 4525188 * 2
def baseEnd_4525188 : Nat := 86059129479923941290335

theorem tailTrace_4525188 : CollatzResearch.WordTrace tailWord_4525188 prefixEnd_4525188 86059129479923941290335 := by
  unfold tailWord_4525188
  simp only [CollatzResearch.WordTrace]
  refine ⟨82523582765012095713264109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110031443686682794284352145 82523582765012095713264109)
  ·
    refine ⟨30946343536879535892474041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82523582765012095713264109 30946343536879535892474041)
    ·
      refine ⟨23209757652659651919355531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30946343536879535892474041 23209757652659651919355531)
      ·
        refine ⟨34814636478989477879033297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23209757652659651919355531 34814636478989477879033297)
        ·
          refine ⟨26110977359242108409274973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34814636478989477879033297 26110977359242108409274973)
          ·
            refine ⟨9791616509715790653478115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26110977359242108409274973 9791616509715790653478115)
            ·
              refine ⟨14687424764573685980217173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9791616509715790653478115 14687424764573685980217173)
              ·
                refine ⟨86059129479923941290335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14687424764573685980217173 86059129479923941290335)
                ·
                  rfl

theorem cell23_4525188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 9].length) (baseStart_4525188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525188 prefixEnd_4525188 := by exact prefixLift 4525188
  have htrace : WordTrace (prefixWord ++ tailWord_4525188) baseStart_4525188 baseEnd_4525188 := by
    simpa [prefixWord, tailWord_4525188, baseEnd_4525188] using wordTrace_append hprefix tailTrace_4525188
  have hstable : (prefixWord ++ tailWord_4525188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525188).length < 2 ^ (prefixWord ++ tailWord_4525188).sum := by decide
  have hdescent : baseEnd_4525188 < baseStart_4525188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525202 : List Nat := [3, 2, 3, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_4525202 : Nat := 118140960795 + 4525202 * 2 ^ 59
def prefixEnd_4525202 : Nat := 4983230072969 + 3 ^ 40 * 4525202 * 2
def baseEnd_4525202 : Nat := 2323603684687109360063981

theorem tailTrace_4525202 : CollatzResearch.WordTrace tailWord_4525202 prefixEnd_4525202 2323603684687109360063981 := by
  unfold tailWord_4525202
  simp only [CollatzResearch.WordTrace]
  refine ⟨41261919037993367954384465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110031784101315647878358573 41261919037993367954384465)
  ·
    refine ⟨30946439278495025965788349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41261919037993367954384465 30946439278495025965788349)
    ·
      refine ⟨11604914729435634737170631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30946439278495025965788349 11604914729435634737170631)
      ·
        refine ⟨17407372094153452105755947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11604914729435634737170631 17407372094153452105755947)
        ·
          refine ⟨26111058141230178158633921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17407372094153452105755947 26111058141230178158633921)
          ·
            refine ⟨19583293605922633618975441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26111058141230178158633921 19583293605922633618975441)
            ·
              refine ⟨14687470204441975214231581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19583293605922633618975441 14687470204441975214231581)
              ·
                refine ⟨5507801326665740705336843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14687470204441975214231581 5507801326665740705336843)
                ·
                  refine ⟨8261701989998611058005265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5507801326665740705336843 8261701989998611058005265)
                  ·
                    refine ⟨6196276492498958293503949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8261701989998611058005265 6196276492498958293503949)
                    ·
                      refine ⟨2323603684687109360063981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6196276492498958293503949 2323603684687109360063981)
                      ·
                        rfl

theorem cell23_4525202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_4525202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525202 prefixEnd_4525202 := by exact prefixLift 4525202
  have htrace : WordTrace (prefixWord ++ tailWord_4525202) baseStart_4525202 baseEnd_4525202 := by
    simpa [prefixWord, tailWord_4525202, baseEnd_4525202] using wordTrace_append hprefix tailTrace_4525202
  have hstable : (prefixWord ++ tailWord_4525202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525202).length < 2 ^ (prefixWord ++ tailWord_4525202).sum := by decide
  have hdescent : baseEnd_4525202 < baseStart_4525202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525211 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 7]
def baseStart_4525211 : Nat := 118140960795 + 4525211 * 2 ^ 59
def prefixEnd_4525211 : Nat := 4983230072969 + 3 ^ 40 * 4525211 * 2
def baseEnd_4525211 : Nat := 2323608306012999824851439

theorem tailTrace_4525211 : CollatzResearch.WordTrace tailWord_4525211 prefixEnd_4525211 2323608306012999824851439 := by
  unfold tailWord_4525211
  simp only [CollatzResearch.WordTrace]
  refine ⟨165048004408940866354615487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110032002939293910903076991 165048004408940866354615487)
  ·
    refine ⟨247572006613411299531923231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165048004408940866354615487 247572006613411299531923231)
    ·
      refine ⟨371358009920116949297884847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247572006613411299531923231 371358009920116949297884847)
      ·
        refine ⟨557037014880175423946827271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371358009920116949297884847 557037014880175423946827271)
        ·
          refine ⟨835555522320263135920240907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557037014880175423946827271 835555522320263135920240907)
          ·
            refine ⟨1253333283480394703880361361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 835555522320263135920240907 1253333283480394703880361361)
            ·
              refine ⟨939999962610296027910271021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1253333283480394703880361361 939999962610296027910271021)
              ·
                refine ⟨352499985978861010466351633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 939999962610296027910271021 352499985978861010466351633)
                ·
                  refine ⟨264374989484145757849763725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352499985978861010466351633 264374989484145757849763725)
                  ·
                    refine ⟨99140621056554659193661397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 264374989484145757849763725 99140621056554659193661397)
                    ·
                      refine ⟨2323608306012999824851439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99140621056554659193661397 2323608306012999824851439)
                      ·
                        rfl

theorem cell23_4525211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 7].length) (baseStart_4525211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525211 prefixEnd_4525211 := by exact prefixLift 4525211
  have htrace : WordTrace (prefixWord ++ tailWord_4525211) baseStart_4525211 baseEnd_4525211 := by
    simpa [prefixWord, tailWord_4525211, baseEnd_4525211] using wordTrace_append hprefix tailTrace_4525211
  have hstable : (prefixWord ++ tailWord_4525211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525211).length < 2 ^ (prefixWord ++ tailWord_4525211).sum := by decide
  have hdescent : baseEnd_4525211 < baseStart_4525211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525216 : List Nat := [2, 1, 1, 4, 2, 1, 5, 2, 1, 2, 2]
def baseStart_4525216 : Nat := 118140960795 + 4525216 * 2 ^ 59
def prefixEnd_4525216 : Nat := 4983230072969 + 3 ^ 40 * 4525216 * 2
def baseEnd_4525216 : Nat := 2323610873416272305288917

theorem tailTrace_4525216 : CollatzResearch.WordTrace tailWord_4525216 prefixEnd_4525216 2323610873416272305288917 := by
  unfold tailWord_4525216
  simp only [CollatzResearch.WordTrace]
  refine ⟨82524093386961376104273751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110032124515948501472365001 82524093386961376104273751)
  ·
    refine ⟨123786140080442064156410627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82524093386961376104273751 123786140080442064156410627)
    ·
      refine ⟨185679210120663096234615941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123786140080442064156410627 185679210120663096234615941)
      ·
        refine ⟨34814851897624330543990489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185679210120663096234615941 34814851897624330543990489)
        ·
          refine ⟨26111138923218247907992867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34814851897624330543990489 26111138923218247907992867)
          ·
            refine ⟨39166708384827371861989301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26111138923218247907992867 39166708384827371861989301)
            ·
              refine ⟨3671878911077566112061497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39166708384827371861989301 3671878911077566112061497)
              ·
                refine ⟨2753909183308174584046123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3671878911077566112061497 2753909183308174584046123)
                ·
                  refine ⟨4130863774962261876069185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2753909183308174584046123 4130863774962261876069185)
                  ·
                    refine ⟨3098147831221696407051889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4130863774962261876069185 3098147831221696407051889)
                    ·
                      refine ⟨2323610873416272305288917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3098147831221696407051889 2323610873416272305288917)
                      ·
                        rfl

theorem cell23_4525216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_4525216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525216 prefixEnd_4525216 := by exact prefixLift 4525216
  have htrace : WordTrace (prefixWord ++ tailWord_4525216) baseStart_4525216 baseEnd_4525216 := by
    simpa [prefixWord, tailWord_4525216, baseEnd_4525216] using wordTrace_append hprefix tailTrace_4525216
  have hstable : (prefixWord ++ tailWord_4525216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525216).length < 2 ^ (prefixWord ++ tailWord_4525216).sum := by decide
  have hdescent : baseEnd_4525216 < baseStart_4525216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525226 : List Nat := [3, 1, 5, 1, 1, 3, 2, 1, 2, 4]
def baseStart_4525226 : Nat := 118140960795 + 4525226 * 2 ^ 59
def prefixEnd_4525226 : Nat := 4983230072969 + 3 ^ 40 * 4525226 * 2
def baseEnd_4525226 : Nat := 774538669407605755387957

theorem tailTrace_4525226 : CollatzResearch.WordTrace tailWord_4525226 prefixEnd_4525226 774538669407605755387957 := by
  unfold tailWord_4525226
  simp only [CollatzResearch.WordTrace]
  refine ⟨41262137875971630979102883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110032367669257682610941021 41262137875971630979102883)
  ·
    refine ⟨61893206813957446468654325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41262137875971630979102883 61893206813957446468654325)
    ·
      refine ⟨5802488138808510606436343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61893206813957446468654325 5802488138808510606436343)
      ·
        refine ⟨8703732208212765909654515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5802488138808510606436343 8703732208212765909654515)
        ·
          refine ⟨13055598312319148864481773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8703732208212765909654515 13055598312319148864481773)
          ·
            refine ⟨4895849367119680824180665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13055598312319148864481773 4895849367119680824180665)
            ·
              refine ⟨3671887025339760618135499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4895849367119680824180665 3671887025339760618135499)
              ·
                refine ⟨5507830538009640927203249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3671887025339760618135499 5507830538009640927203249)
                ·
                  refine ⟨4130872903507230695402437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5507830538009640927203249 4130872903507230695402437)
                  ·
                    refine ⟨774538669407605755387957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4130872903507230695402437 774538669407605755387957)
                    ·
                      rfl

theorem cell23_4525226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_4525226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525226 prefixEnd_4525226 := by exact prefixLift 4525226
  have htrace : WordTrace (prefixWord ++ tailWord_4525226) baseStart_4525226 baseEnd_4525226 := by
    simpa [prefixWord, tailWord_4525226, baseEnd_4525226] using wordTrace_append hprefix tailTrace_4525226
  have hstable : (prefixWord ++ tailWord_4525226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525226).length < 2 ^ (prefixWord ++ tailWord_4525226).sum := by decide
  have hdescent : baseEnd_4525226 < baseStart_4525226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525295 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 7]
def baseStart_4525295 : Nat := 118140960795 + 4525295 * 2 ^ 59
def prefixEnd_4525295 : Nat := 4983230072969 + 3 ^ 40 * 4525295 * 2
def baseEnd_4525295 : Nat := 258183493154219721800117

theorem tailTrace_4525295 : CollatzResearch.WordTrace tailWord_4525295 prefixEnd_4525295 258183493154219721800117 := by
  unfold tailWord_4525295
  simp only [CollatzResearch.WordTrace]
  refine ⟨165051068140636548700673339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110034045427091032467115559 165051068140636548700673339)
  ·
    refine ⟨247576602210954823051010009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165051068140636548700673339 247576602210954823051010009)
    ·
      refine ⟨185682451658216117288257507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247576602210954823051010009 185682451658216117288257507)
      ·
        refine ⟨278523677487324175932386261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185682451658216117288257507 278523677487324175932386261)
        ·
          refine ⟨6527898691109160373415303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 278523677487324175932386261 6527898691109160373415303)
          ·
            refine ⟨9791848036663740560122955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6527898691109160373415303 9791848036663740560122955)
            ·
              refine ⟨14687772054995610840184433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9791848036663740560122955 14687772054995610840184433)
              ·
                refine ⟨11015829041246708130138325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14687772054995610840184433 11015829041246708130138325)
                ·
                  refine ⟨258183493154219721800117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11015829041246708130138325 258183493154219721800117)
                  ·
                    rfl

theorem cell23_4525295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 7].length) (baseStart_4525295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525295 prefixEnd_4525295 := by exact prefixLift 4525295
  have htrace : WordTrace (prefixWord ++ tailWord_4525295) baseStart_4525295 baseEnd_4525295 := by
    simpa [prefixWord, tailWord_4525295, baseEnd_4525295] using wordTrace_append hprefix tailTrace_4525295
  have hstable : (prefixWord ++ tailWord_4525295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525295).length < 2 ^ (prefixWord ++ tailWord_4525295).sum := by decide
  have hdescent : baseEnd_4525295 < baseStart_4525295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525402 : List Nat := [3, 1, 1, 2, 1, 2, 6, 1, 6]
def baseStart_4525402 : Nat := 118140960795 + 4525402 * 2 ^ 59
def prefixEnd_4525402 : Nat := 4983230072969 + 3 ^ 40 * 4525402 * 2
def baseEnd_4525402 : Nat := 258189597868667619729229

theorem tailTrace_4525402 : CollatzResearch.WordTrace tailWord_4525402 prefixEnd_4525402 258189597868667619729229 := by
  unfold tailWord_4525402
  simp only [CollatzResearch.WordTrace]
  refine ⟨41263742687812226493704615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110036647167499270649878973 41263742687812226493704615)
  ·
    refine ⟨61895614031718339740556923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41263742687812226493704615 61895614031718339740556923)
    ·
      refine ⟨92843421047577509610835385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61895614031718339740556923 92843421047577509610835385)
      ·
        refine ⟨69632565785683132208126539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92843421047577509610835385 69632565785683132208126539)
        ·
          refine ⟨104448848678524698312189809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69632565785683132208126539 104448848678524698312189809)
          ·
            refine ⟨78336636508893523734142357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104448848678524698312189809 78336636508893523734142357)
            ·
              refine ⟨3672029836354383925037923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78336636508893523734142357 3672029836354383925037923)
              ·
                refine ⟨5508044754531575887556885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3672029836354383925037923 5508044754531575887556885)
                ·
                  refine ⟨258189597868667619729229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5508044754531575887556885 258189597868667619729229)
                  ·
                    rfl

theorem cell23_4525402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 6].length) (baseStart_4525402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525402 prefixEnd_4525402 := by exact prefixLift 4525402
  have htrace : WordTrace (prefixWord ++ tailWord_4525402) baseStart_4525402 baseEnd_4525402 := by
    simpa [prefixWord, tailWord_4525402, baseEnd_4525402] using wordTrace_append hprefix tailTrace_4525402
  have hstable : (prefixWord ++ tailWord_4525402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525402).length < 2 ^ (prefixWord ++ tailWord_4525402).sum := by decide
  have hdescent : baseEnd_4525402 < baseStart_4525402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525472 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 3]
def baseStart_4525472 : Nat := 118140960795 + 4525472 * 2 ^ 59
def prefixEnd_4525472 : Nat := 4983230072969 + 3 ^ 40 * 4525472 * 2
def baseEnd_4525472 : Nat := 2323742324463823303687739

theorem tailTrace_4525472 : CollatzResearch.WordTrace tailWord_4525472 prefixEnd_4525472 2323742324463823303687739 := by
  unfold tailWord_4525472
  simp only [CollatzResearch.WordTrace]
  refine ⟨82528761930497653964933335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110038349240663538619911113 82528761930497653964933335)
  ·
    refine ⟨123793142895746480947400003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82528761930497653964933335 123793142895746480947400003)
    ·
      refine ⟨185689714343619721421100005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123793142895746480947400003 185689714343619721421100005)
      ·
        refine ⟨34816821439428697766456251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185689714343619721421100005 34816821439428697766456251)
        ·
          refine ⟨52225232159143046649684377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34816821439428697766456251 52225232159143046649684377)
          ·
            refine ⟨39168924119357284987263283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52225232159143046649684377 39168924119357284987263283)
            ·
              refine ⟨58753386179035927480894925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39168924119357284987263283 58753386179035927480894925)
              ·
                refine ⟨22032519817138472805335597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58753386179035927480894925 22032519817138472805335597)
                ·
                  refine ⟨8262194931426927302000849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22032519817138472805335597 8262194931426927302000849)
                  ·
                    refine ⟨6196646198570195476500637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8262194931426927302000849 6196646198570195476500637)
                    ·
                      refine ⟨2323742324463823303687739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6196646198570195476500637 2323742324463823303687739)
                      ·
                        rfl

theorem cell23_4525472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_4525472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525472 prefixEnd_4525472 := by exact prefixLift 4525472
  have htrace : WordTrace (prefixWord ++ tailWord_4525472) baseStart_4525472 baseEnd_4525472 := by
    simpa [prefixWord, tailWord_4525472, baseEnd_4525472] using wordTrace_append hprefix tailTrace_4525472
  have hstable : (prefixWord ++ tailWord_4525472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525472).length < 2 ^ (prefixWord ++ tailWord_4525472).sum := by decide
  have hdescent : baseEnd_4525472 < baseStart_4525472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525480 : List Nat := [2, 1, 6, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_4525480 : Nat := 118140960795 + 4525480 * 2 ^ 59
def prefixEnd_4525480 : Nat := 4983230072969 + 3 ^ 40 * 4525480 * 2
def baseEnd_4525480 : Nat := 2323746432309059272387703

theorem tailTrace_4525480 : CollatzResearch.WordTrace tailWord_4525480 prefixEnd_4525480 2323746432309059272387703 := by
  unfold tailWord_4525480
  simp only [CollatzResearch.WordTrace]
  refine ⟨82528907822483162648078947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110038543763310883530771929 82528907822483162648078947)
  ·
    refine ⟨123793361733724743972118421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82528907822483162648078947 123793361733724743972118421)
    ·
      refine ⟨5802813831268347373693051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 123793361733724743972118421 5802813831268347373693051)
      ·
        refine ⟨8704220746902521060539577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5802813831268347373693051 8704220746902521060539577)
        ·
          refine ⟨6528165560176890795404683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8704220746902521060539577 6528165560176890795404683)
          ·
            refine ⟨9792248340265336193107025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6528165560176890795404683 9792248340265336193107025)
            ·
              refine ⟨7344186255199002144830269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9792248340265336193107025 7344186255199002144830269)
              ·
                refine ⟨2754069845699625804311351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7344186255199002144830269 2754069845699625804311351)
                ·
                  refine ⟨4131104768549438706467027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2754069845699625804311351 4131104768549438706467027)
                  ·
                    refine ⟨6196657152824158059700541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4131104768549438706467027 6196657152824158059700541)
                    ·
                      refine ⟨2323746432309059272387703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6196657152824158059700541 2323746432309059272387703)
                      ·
                        rfl

theorem cell23_4525480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_4525480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525480 prefixEnd_4525480 := by exact prefixLift 4525480
  have htrace : WordTrace (prefixWord ++ tailWord_4525480) baseStart_4525480 baseEnd_4525480 := by
    simpa [prefixWord, tailWord_4525480, baseEnd_4525480] using wordTrace_append hprefix tailTrace_4525480
  have hstable : (prefixWord ++ tailWord_4525480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525480).length < 2 ^ (prefixWord ++ tailWord_4525480).sum := by decide
  have hdescent : baseEnd_4525480 < baseStart_4525480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525489 : List Nat := [1, 2, 2, 4, 1, 1, 3, 3, 1, 2, 3]
def baseStart_4525489 : Nat := 118140960795 + 4525489 * 2 ^ 59
def prefixEnd_4525489 : Nat := 4983230072969 + 3 ^ 40 * 4525489 * 2
def baseEnd_4525489 : Nat := 2323751053634949737175161

theorem tailTrace_4525489 : CollatzResearch.WordTrace tailWord_4525489 prefixEnd_4525489 2323751053634949737175161 := by
  unfold tailWord_4525489
  simp only [CollatzResearch.WordTrace]
  refine ⟨165058143901933719833235521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110038762601289146555490347 165058143901933719833235521)
  ·
    refine ⟨123793607926450289874926641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165058143901933719833235521 123793607926450289874926641)
    ·
      refine ⟨92845205944837717406194981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123793607926450289874926641 92845205944837717406194981)
      ·
        refine ⟨17408476114657072013661559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92845205944837717406194981 17408476114657072013661559)
        ·
          refine ⟨26112714171985608020492339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17408476114657072013661559 26112714171985608020492339)
          ·
            refine ⟨39169071257978412030738509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26112714171985608020492339 39169071257978412030738509)
            ·
              refine ⟨14688401721741904511526941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39169071257978412030738509 14688401721741904511526941)
              ·
                refine ⟨5508150645653214191822603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14688401721741904511526941 5508150645653214191822603)
                ·
                  refine ⟨8262225968479821287733905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5508150645653214191822603 8262225968479821287733905)
                  ·
                    refine ⟨6196669476359865965800429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8262225968479821287733905 6196669476359865965800429)
                    ·
                      refine ⟨2323751053634949737175161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6196669476359865965800429 2323751053634949737175161)
                      ·
                        rfl

theorem cell23_4525489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_4525489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525489 prefixEnd_4525489 := by exact prefixLift 4525489
  have htrace : WordTrace (prefixWord ++ tailWord_4525489) baseStart_4525489 baseEnd_4525489 := by
    simpa [prefixWord, tailWord_4525489, baseEnd_4525489] using wordTrace_append hprefix tailTrace_4525489
  have hstable : (prefixWord ++ tailWord_4525489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525489).length < 2 ^ (prefixWord ++ tailWord_4525489).sum := by decide
  have hdescent : baseEnd_4525489 < baseStart_4525489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525519 : List Nat := [1, 1, 2, 1, 1, 4, 2, 5, 2, 1, 3]
def baseStart_4525519 : Nat := 118140960795 + 4525519 * 2 ^ 59
def prefixEnd_4525519 : Nat := 4983230072969 + 3 ^ 40 * 4525519 * 2
def baseEnd_4525519 : Nat := 2323766458054584619800023

theorem tailTrace_4525519 : CollatzResearch.WordTrace tailWord_4525519 prefixEnd_4525519 2323766458054584619800023 := by
  unfold tailWord_4525519
  simp only [CollatzResearch.WordTrace]
  refine ⟨165059238091825034956827611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110039492061216689971218407 165059238091825034956827611)
  ·
    refine ⟨247588857137737552435241417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165059238091825034956827611 247588857137737552435241417)
    ·
      refine ⟨185691642853303164326431063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247588857137737552435241417 185691642853303164326431063)
      ·
        refine ⟨278537464279954746489646595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185691642853303164326431063 278537464279954746489646595)
        ·
          refine ⟨417806196419932119734469893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278537464279954746489646595 417806196419932119734469893)
          ·
            refine ⟨78338661828737272450213105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 417806196419932119734469893 78338661828737272450213105)
            ·
              refine ⟨58753996371552954337659829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78338661828737272450213105 58753996371552954337659829)
              ·
                refine ⟨5508187159833089469155609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58753996371552954337659829 5508187159833089469155609)
                ·
                  refine ⟨4131140369874817101866707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5508187159833089469155609 4131140369874817101866707)
                  ·
                    refine ⟨6196710554812225652800061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4131140369874817101866707 6196710554812225652800061)
                    ·
                      refine ⟨2323766458054584619800023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6196710554812225652800061 2323766458054584619800023)
                      ·
                        rfl

theorem cell23_4525519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 1, 3].length) (baseStart_4525519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525519 prefixEnd_4525519 := by exact prefixLift 4525519
  have htrace : WordTrace (prefixWord ++ tailWord_4525519) baseStart_4525519 baseEnd_4525519 := by
    simpa [prefixWord, tailWord_4525519, baseEnd_4525519] using wordTrace_append hprefix tailTrace_4525519
  have hstable : (prefixWord ++ tailWord_4525519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525519).length < 2 ^ (prefixWord ++ tailWord_4525519).sum := by decide
  have hdescent : baseEnd_4525519 < baseStart_4525519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525526 : List Nat := [5, 2, 1, 1, 1, 4, 2, 7]
def baseStart_4525526 : Nat := 118140960795 + 4525526 * 2 ^ 59
def prefixEnd_4525526 : Nat := 4983230072969 + 3 ^ 40 * 4525526 * 2
def baseEnd_4525526 : Nat := 86065557497006151570833

theorem tailTrace_4525526 : CollatzResearch.WordTrace tailWord_4525526 prefixEnd_4525526 86065557497006151570833 := by
  unfold tailWord_4525526
  simp only [CollatzResearch.WordTrace]
  refine ⟨10316218337674979697020777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110039662268533116768221621 10316218337674979697020777)
  ·
    refine ⟨7737163753256234772765583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10316218337674979697020777 7737163753256234772765583)
    ·
      refine ⟨11605745629884352159148375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7737163753256234772765583 11605745629884352159148375)
      ·
        refine ⟨17408618444826528238722563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11605745629884352159148375 17408618444826528238722563)
        ·
          refine ⟨26112927667239792358083845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17408618444826528238722563 26112927667239792358083845)
          ·
            refine ⟨4896173937607461067140721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26112927667239792358083845 4896173937607461067140721)
            ·
              refine ⟨3672130453205595800355541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4896173937607461067140721 3672130453205595800355541)
              ·
                refine ⟨86065557497006151570833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3672130453205595800355541 86065557497006151570833)
                ·
                  rfl

theorem cell23_4525526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_4525526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525526 prefixEnd_4525526 := by exact prefixLift 4525526
  have htrace : WordTrace (prefixWord ++ tailWord_4525526) baseStart_4525526 baseEnd_4525526 := by
    simpa [prefixWord, tailWord_4525526, baseEnd_4525526] using wordTrace_append hprefix tailTrace_4525526
  have hstable : (prefixWord ++ tailWord_4525526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525526).length < 2 ^ (prefixWord ++ tailWord_4525526).sum := by decide
  have hdescent : baseEnd_4525526 < baseStart_4525526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525555 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 6]
def baseStart_4525555 : Nat := 118140960795 + 4525555 * 2 ^ 59
def prefixEnd_4525555 : Nat := 4983230072969 + 3 ^ 40 * 4525555 * 2
def baseEnd_4525555 : Nat := 2323784943358146478949857

theorem tailTrace_4525555 : CollatzResearch.WordTrace tailWord_4525555 prefixEnd_4525555 2323784943358146478949857 := by
  unfold tailWord_4525555
  simp only [CollatzResearch.WordTrace]
  refine ⟨165060551119694613105138119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110040367413129742070092079 165060551119694613105138119)
  ·
    refine ⟨247590826679541919657707179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165060551119694613105138119 247590826679541919657707179)
    ·
      refine ⟨371386240019312879486560769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247590826679541919657707179 371386240019312879486560769)
      ·
        refine ⟨278539680014484659614920577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371386240019312879486560769 278539680014484659614920577)
        ·
          refine ⟨208904760010863494711190433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278539680014484659614920577 208904760010863494711190433)
          ·
            refine ⟨156678570008147621033392825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208904760010863494711190433 156678570008147621033392825)
            ·
              refine ⟨117508927506110715775044619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156678570008147621033392825 117508927506110715775044619)
              ·
                refine ⟨176263391259166073662566929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117508927506110715775044619 176263391259166073662566929)
                ·
                  refine ⟨132197543444374555246925197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176263391259166073662566929 132197543444374555246925197)
                  ·
                    refine ⟨49574078791640458217596949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 132197543444374555246925197 49574078791640458217596949)
                    ·
                      refine ⟨2323784943358146478949857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49574078791640458217596949 2323784943358146478949857)
                      ·
                        rfl

theorem cell23_4525555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_4525555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525555 prefixEnd_4525555 := by exact prefixLift 4525555
  have htrace : WordTrace (prefixWord ++ tailWord_4525555) baseStart_4525555 baseEnd_4525555 := by
    simpa [prefixWord, tailWord_4525555, baseEnd_4525555] using wordTrace_append hprefix tailTrace_4525555
  have hstable : (prefixWord ++ tailWord_4525555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525555).length < 2 ^ (prefixWord ++ tailWord_4525555).sum := by decide
  have hdescent : baseEnd_4525555 < baseStart_4525555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525562 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3]
def baseStart_4525562 : Nat := 118140960795 + 4525562 * 2 ^ 59
def prefixEnd_4525562 : Nat := 4983230072969 + 3 ^ 40 * 4525562 * 2
def baseEnd_4525562 : Nat := 2323788537722727951562325

theorem tailTrace_4525562 : CollatzResearch.WordTrace tailWord_4525562 prefixEnd_4525562 2323788537722727951562325 := by
  unfold tailWord_4525562
  simp only [CollatzResearch.WordTrace]
  refine ⟨41265201607667313325160735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110040537620446168867095293 41265201607667313325160735)
  ·
    refine ⟨61897802411500969987741103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41265201607667313325160735 61897802411500969987741103)
    ·
      refine ⟨92846703617251454981611655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61897802411500969987741103 92846703617251454981611655)
      ·
        refine ⟨139270055425877182472417483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92846703617251454981611655 139270055425877182472417483)
        ·
          refine ⟨208905083138815773708626225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139270055425877182472417483 208905083138815773708626225)
          ·
            refine ⟨156678812354111830281469669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208905083138815773708626225 156678812354111830281469669)
            ·
              refine ⟨29377277316395968177775563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156678812354111830281469669 29377277316395968177775563)
              ·
                refine ⟨44065915974593952266663345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29377277316395968177775563 44065915974593952266663345)
                ·
                  refine ⟨33049436980945464199997509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44065915974593952266663345 33049436980945464199997509)
                  ·
                    refine ⟨6196769433927274537499533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33049436980945464199997509 6196769433927274537499533)
                    ·
                      refine ⟨2323788537722727951562325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6196769433927274537499533 2323788537722727951562325)
                      ·
                        rfl

theorem cell23_4525562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_4525562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525562 prefixEnd_4525562 := by exact prefixLift 4525562
  have htrace : WordTrace (prefixWord ++ tailWord_4525562) baseStart_4525562 baseEnd_4525562 := by
    simpa [prefixWord, tailWord_4525562, baseEnd_4525562] using wordTrace_append hprefix tailTrace_4525562
  have hstable : (prefixWord ++ tailWord_4525562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525562).length < 2 ^ (prefixWord ++ tailWord_4525562).sum := by decide
  have hdescent : baseEnd_4525562 < baseStart_4525562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525570 : List Nat := [3, 4, 1, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_4525570 : Nat := 118140960795 + 4525570 * 2 ^ 59
def prefixEnd_4525570 : Nat := 4983230072969 + 3 ^ 40 * 4525570 * 2
def baseEnd_4525570 : Nat := 2323792645567963920262289

theorem tailTrace_4525570 : CollatzResearch.WordTrace tailWord_4525570 prefixEnd_4525570 2323792645567963920262289 := by
  unfold tailWord_4525570
  simp only [CollatzResearch.WordTrace]
  refine ⟨41265274553660067666733541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110040732143093513777956109 41265274553660067666733541)
  ·
    refine ⟨7737238978811262687512539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41265274553660067666733541 7737238978811262687512539)
    ·
      refine ⟨11605858468216894031268809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7737238978811262687512539 11605858468216894031268809)
      ·
        refine ⟨8704393851162670523451607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11605858468216894031268809 8704393851162670523451607)
        ·
          refine ⟨13056590776744005785177411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8704393851162670523451607 13056590776744005785177411)
          ·
            refine ⟨19584886165116008677766117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13056590776744005785177411 19584886165116008677766117)
            ·
              refine ⟨3672166155959251627081147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19584886165116008677766117 3672166155959251627081147)
              ·
                refine ⟨5508249233938877440621721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3672166155959251627081147 5508249233938877440621721)
                ·
                  refine ⟨4131186925454158080466291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5508249233938877440621721 4131186925454158080466291)
                  ·
                    refine ⟨6196780388181237120699437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4131186925454158080466291 6196780388181237120699437)
                    ·
                      refine ⟨2323792645567963920262289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6196780388181237120699437 2323792645567963920262289)
                      ·
                        rfl

theorem cell23_4525570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_4525570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525570 prefixEnd_4525570 := by exact prefixLift 4525570
  have htrace : WordTrace (prefixWord ++ tailWord_4525570) baseStart_4525570 baseEnd_4525570 := by
    simpa [prefixWord, tailWord_4525570, baseEnd_4525570] using wordTrace_append hprefix tailTrace_4525570
  have hstable : (prefixWord ++ tailWord_4525570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525570).length < 2 ^ (prefixWord ++ tailWord_4525570).sum := by decide
  have hdescent : baseEnd_4525570 < baseStart_4525570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525574 : List Nat := [6, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_4525574 : Nat := 118140960795 + 4525574 * 2 ^ 59
def prefixEnd_4525574 : Nat := 4983230072969 + 3 ^ 40 * 4525574 * 2
def baseEnd_4525574 : Nat := 2323794699490581904612271

theorem tailTrace_4525574 : CollatzResearch.WordTrace tailWord_4525574 prefixEnd_4525574 2323794699490581904612271 := by
  unfold tailWord_4525574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5158163878332055604689993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 110040829404417186233386517 5158163878332055604689993)
  ·
    refine ⟨3868622908749041703517495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5158163878332055604689993 3868622908749041703517495)
    ·
      refine ⟨5802934363123562555276243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3868622908749041703517495 5802934363123562555276243)
      ·
        refine ⟨8704401544685343832914365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5802934363123562555276243 8704401544685343832914365)
        ·
          refine ⟨3264150579257003937342887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8704401544685343832914365 3264150579257003937342887)
          ·
            refine ⟨4896225868885505906014331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264150579257003937342887 4896225868885505906014331)
            ·
              refine ⟨7344338803328258859021497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4896225868885505906014331 7344338803328258859021497)
              ·
                refine ⟨5508254102496194144266123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7344338803328258859021497 5508254102496194144266123)
                ·
                  refine ⟨8262381153744291216399185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5508254102496194144266123 8262381153744291216399185)
                  ·
                    refine ⟨6196785865308218412299389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8262381153744291216399185 6196785865308218412299389)
                    ·
                      refine ⟨2323794699490581904612271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6196785865308218412299389 2323794699490581904612271)
                      ·
                        rfl

theorem cell23_4525574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_4525574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525574 prefixEnd_4525574 := by exact prefixLift 4525574
  have htrace : WordTrace (prefixWord ++ tailWord_4525574) baseStart_4525574 baseEnd_4525574 := by
    simpa [prefixWord, tailWord_4525574, baseEnd_4525574] using wordTrace_append hprefix tailTrace_4525574
  have hstable : (prefixWord ++ tailWord_4525574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525574).length < 2 ^ (prefixWord ++ tailWord_4525574).sum := by decide
  have hdescent : baseEnd_4525574 < baseStart_4525574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525580 : List Nat := [2, 2, 1, 2, 6, 1, 1, 2, 1, 3, 2]
def baseStart_4525580 : Nat := 118140960795 + 4525580 * 2 ^ 59
def prefixEnd_4525580 : Nat := 4983230072969 + 3 ^ 40 * 4525580 * 2
def baseEnd_4525580 : Nat := 2323797780374508881137243

theorem tailTrace_4525580 : CollatzResearch.WordTrace tailWord_4525580 prefixEnd_4525580 2323797780374508881137243 := by
  unfold tailWord_4525580
  simp only [CollatzResearch.WordTrace]
  refine ⟨82530731472302021187399097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110040975296402694916532129 82530731472302021187399097)
  ·
    refine ⟨61898048604226515890549323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82530731472302021187399097 61898048604226515890549323)
    ·
      refine ⟨92847072906339773835823985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61898048604226515890549323 92847072906339773835823985)
      ·
        refine ⟨69635304679754830376867989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92847072906339773835823985 69635304679754830376867989)
        ·
          refine ⟨3264154906863507673915687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69635304679754830376867989 3264154906863507673915687)
          ·
            refine ⟨4896232360295261510873531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264154906863507673915687 4896232360295261510873531)
            ·
              refine ⟨7344348540442892266310297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4896232360295261510873531 7344348540442892266310297)
              ·
                refine ⟨5508261405332169199732723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7344348540442892266310297 5508261405332169199732723)
                ·
                  refine ⟨8262392107998253799599085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5508261405332169199732723 8262392107998253799599085)
                  ·
                    refine ⟨3098397040499345174849657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8262392107998253799599085 3098397040499345174849657)
                    ·
                      refine ⟨2323797780374508881137243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3098397040499345174849657 2323797780374508881137243)
                      ·
                        rfl

theorem cell23_4525580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_4525580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525580 prefixEnd_4525580 := by exact prefixLift 4525580
  have htrace : WordTrace (prefixWord ++ tailWord_4525580) baseStart_4525580 baseEnd_4525580 := by
    simpa [prefixWord, tailWord_4525580, baseEnd_4525580] using wordTrace_append hprefix tailTrace_4525580
  have hstable : (prefixWord ++ tailWord_4525580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525580).length < 2 ^ (prefixWord ++ tailWord_4525580).sum := by decide
  have hdescent : baseEnd_4525580 < baseStart_4525580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525619 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 2, 5, 2]
def baseStart_4525619 : Nat := 118140960795 + 4525619 * 2 ^ 59
def prefixEnd_4525619 : Nat := 4983230072969 + 3 ^ 40 * 4525619 * 2
def baseEnd_4525619 : Nat := 2323817806120034228549563

theorem tailTrace_4525619 : CollatzResearch.WordTrace tailWord_4525619 prefixEnd_4525619 2323817806120034228549563 := by
  unfold tailWord_4525619
  simp only [CollatzResearch.WordTrace]
  refine ⟨165062885391462752035467911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110041923594308501356978607 165062885391462752035467911)
  ·
    refine ⟨247594328087194128053201867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165062885391462752035467911 247594328087194128053201867)
    ·
      refine ⟨371391492130791192079802801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247594328087194128053201867 371391492130791192079802801)
      ·
        refine ⟨278543619098093394059852101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371391492130791192079802801 278543619098093394059852101)
        ·
          refine ⟨52226928580892511386222269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 278543619098093394059852101 52226928580892511386222269)
          ·
            refine ⟨19585098217834691769833351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52226928580892511386222269 19585098217834691769833351)
            ·
              refine ⟨29377647326752037654750027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19585098217834691769833351 29377647326752037654750027)
              ·
                refine ⟨44066470990128056482125041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29377647326752037654750027 44066470990128056482125041)
                ·
                  refine ⟨33049853242596042361593781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44066470990128056482125041 33049853242596042361593781)
                  ·
                    refine ⟨3098423741493378971399417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33049853242596042361593781 3098423741493378971399417)
                    ·
                      refine ⟨2323817806120034228549563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3098423741493378971399417 2323817806120034228549563)
                      ·
                        rfl

theorem cell23_4525619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 5, 2].length) (baseStart_4525619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525619 prefixEnd_4525619 := by exact prefixLift 4525619
  have htrace : WordTrace (prefixWord ++ tailWord_4525619) baseStart_4525619 baseEnd_4525619 := by
    simpa [prefixWord, tailWord_4525619, baseEnd_4525619] using wordTrace_append hprefix tailTrace_4525619
  have hstable : (prefixWord ++ tailWord_4525619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525619).length < 2 ^ (prefixWord ++ tailWord_4525619).sum := by decide
  have hdescent : baseEnd_4525619 < baseStart_4525619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525632 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 4]
def baseStart_4525632 : Nat := 118140960795 + 4525632 * 2 ^ 59
def prefixEnd_4525632 : Nat := 4983230072969 + 3 ^ 40 * 4525632 * 2
def baseEnd_4525632 : Nat := 2323824481368542677687003

theorem tailTrace_4525632 : CollatzResearch.WordTrace tailWord_4525632 prefixEnd_4525632 2323824481368542677687003 := by
  unfold tailWord_4525632
  simp only [CollatzResearch.WordTrace]
  refine ⟨82531679770207827627845575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110042239693610436837127433 82531679770207827627845575)
  ·
    refine ⟨123797519655311741441768363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82531679770207827627845575 123797519655311741441768363)
    ·
      refine ⟨185696279482967612162652545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123797519655311741441768363 185696279482967612162652545)
      ·
        refine ⟨139272209612225709121989409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185696279482967612162652545 139272209612225709121989409)
        ·
          refine ⟨104454157209169281841492057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139272209612225709121989409 104454157209169281841492057)
          ·
            refine ⟨78340617906876961381119043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104454157209169281841492057 78340617906876961381119043)
            ·
              refine ⟨117510926860315442071678565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78340617906876961381119043 117510926860315442071678565)
              ·
                refine ⟨22033298786309145388439731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117510926860315442071678565 22033298786309145388439731)
                ·
                  refine ⟨33049948179463718082659597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22033298786309145388439731 33049948179463718082659597)
                  ·
                    refine ⟨12393730567298894280997349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33049948179463718082659597 12393730567298894280997349)
                    ·
                      refine ⟨2323824481368542677687003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12393730567298894280997349 2323824481368542677687003)
                      ·
                        rfl

theorem cell23_4525632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_4525632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525632 prefixEnd_4525632 := by exact prefixLift 4525632
  have htrace : WordTrace (prefixWord ++ tailWord_4525632) baseStart_4525632 baseEnd_4525632 := by
    simpa [prefixWord, tailWord_4525632, baseEnd_4525632] using wordTrace_append hprefix tailTrace_4525632
  have hstable : (prefixWord ++ tailWord_4525632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525632).length < 2 ^ (prefixWord ++ tailWord_4525632).sum := by decide
  have hdescent : baseEnd_4525632 < baseStart_4525632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525649 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 1, 6, 2]
def baseStart_4525649 : Nat := 118140960795 + 4525649 * 2 ^ 59
def prefixEnd_4525649 : Nat := 4983230072969 + 3 ^ 40 * 4525649 * 2
def baseEnd_4525649 : Nat := 2323833210539669111174425

theorem tailTrace_4525649 : CollatzResearch.WordTrace tailWord_4525649 prefixEnd_4525649 2323833210539669111174425 := by
  unfold tailWord_4525649
  simp only [CollatzResearch.WordTrace]
  refine ⟨165063979581354067159060001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110042653054236044772706667 165063979581354067159060001)
  ·
    refine ⟨123797984686015550369295001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165063979581354067159060001 123797984686015550369295001)
    ·
      refine ⟨92848488514511662776971251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123797984686015550369295001 92848488514511662776971251)
      ·
        refine ⟨139272732771767494165456877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92848488514511662776971251 139272732771767494165456877)
        ·
          refine ⟨52227274789412810312046329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139272732771767494165456877 52227274789412810312046329)
          ·
            refine ⟨39170456092059607734034747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52227274789412810312046329 39170456092059607734034747)
            ·
              refine ⟨58755684138089411601052121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39170456092059607734034747 58755684138089411601052121)
              ·
                refine ⟨44066763103567058700789091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58755684138089411601052121 44066763103567058700789091)
                ·
                  refine ⟨66100144655350588051183637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44066763103567058700789091 66100144655350588051183637)
                  ·
                    refine ⟨3098444280719558814899233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66100144655350588051183637 3098444280719558814899233)
                    ·
                      refine ⟨2323833210539669111174425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3098444280719558814899233 2323833210539669111174425)
                      ·
                        rfl

theorem cell23_4525649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 6, 2].length) (baseStart_4525649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525649 prefixEnd_4525649 := by exact prefixLift 4525649
  have htrace : WordTrace (prefixWord ++ tailWord_4525649) baseStart_4525649 baseEnd_4525649 := by
    simpa [prefixWord, tailWord_4525649, baseEnd_4525649] using wordTrace_append hprefix tailTrace_4525649
  have hstable : (prefixWord ++ tailWord_4525649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525649).length < 2 ^ (prefixWord ++ tailWord_4525649).sum := by decide
  have hdescent : baseEnd_4525649 < baseStart_4525649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525686 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_4525686 : Nat := 118140960795 + 4525686 * 2 ^ 59
def prefixEnd_4525686 : Nat := 4983230072969 + 3 ^ 40 * 4525686 * 2
def baseEnd_4525686 : Nat := 2323852209323885466411755

theorem tailTrace_4525686 : CollatzResearch.WordTrace tailWord_4525686 prefixEnd_4525686 2323852209323885466411755 := by
  unfold tailWord_4525686
  simp only [CollatzResearch.WordTrace]
  refine ⟨10316583067638751404884807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110043552721480014985437941 10316583067638751404884807)
  ·
    refine ⟨15474874601458127107327211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10316583067638751404884807 15474874601458127107327211)
    ·
      refine ⟨23212311902187190660990817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15474874601458127107327211 23212311902187190660990817)
      ·
        refine ⟨17409233926640392995743113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23212311902187190660990817 17409233926640392995743113)
        ·
          refine ⟨13056925444980294746807335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17409233926640392995743113 13056925444980294746807335)
          ·
            refine ⟨19585388167470442120211003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13056925444980294746807335 19585388167470442120211003)
            ·
              refine ⟨29378082251205663180316505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19585388167470442120211003 29378082251205663180316505)
              ·
                refine ⟨22033561688404247385237379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29378082251205663180316505 22033561688404247385237379)
                ·
                  refine ⟨33050342532606371077856069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22033561688404247385237379 33050342532606371077856069)
                  ·
                    refine ⟨6196939224863694577098013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33050342532606371077856069 6196939224863694577098013)
                    ·
                      refine ⟨2323852209323885466411755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6196939224863694577098013 2323852209323885466411755)
                      ·
                        rfl

theorem cell23_4525686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_4525686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525686 prefixEnd_4525686 := by exact prefixLift 4525686
  have htrace : WordTrace (prefixWord ++ tailWord_4525686) baseStart_4525686 baseEnd_4525686 := by
    simpa [prefixWord, tailWord_4525686, baseEnd_4525686] using wordTrace_append hprefix tailTrace_4525686
  have hstable : (prefixWord ++ tailWord_4525686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525686).length < 2 ^ (prefixWord ++ tailWord_4525686).sum := by decide
  have hdescent : baseEnd_4525686 < baseStart_4525686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525692 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_4525692 : Nat := 118140960795 + 4525692 * 2 ^ 59
def prefixEnd_4525692 : Nat := 4983230072969 + 3 ^ 40 * 4525692 * 2
def baseEnd_4525692 : Nat := 2323855290207812442936727

theorem tailTrace_4525692 : CollatzResearch.WordTrace tailWord_4525692 prefixEnd_4525692 2323855290207812442936727 := by
  unfold tailWord_4525692
  simp only [CollatzResearch.WordTrace]
  refine ⟨82532773960099142751437665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110043698613465523668583553 82532773960099142751437665)
  ·
    refine ⟨61899580470074357063578249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82532773960099142751437665 61899580470074357063578249)
    ·
      refine ⟨46424685352555767797683687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61899580470074357063578249 46424685352555767797683687)
      ·
        refine ⟨69637028028833651696525531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46424685352555767797683687 69637028028833651696525531)
        ·
          refine ⟨104455542043250477544788297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69637028028833651696525531 104455542043250477544788297)
          ·
            refine ⟨78341656532437858158591223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104455542043250477544788297 78341656532437858158591223)
            ·
              refine ⟨117512484798656787237886835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78341656532437858158591223 117512484798656787237886835)
              ·
                refine ⟨176268727197985180856830253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117512484798656787237886835 176268727197985180856830253)
                ·
                  refine ⟨66100772699244442821311345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176268727197985180856830253 66100772699244442821311345)
                  ·
                    refine ⟨49575579524433332115983509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66100772699244442821311345 49575579524433332115983509)
                    ·
                      refine ⟨2323855290207812442936727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49575579524433332115983509 2323855290207812442936727)
                      ·
                        rfl

theorem cell23_4525692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_4525692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525692 prefixEnd_4525692 := by exact prefixLift 4525692
  have htrace : WordTrace (prefixWord ++ tailWord_4525692) baseStart_4525692 baseEnd_4525692 := by
    simpa [prefixWord, tailWord_4525692, baseEnd_4525692] using wordTrace_append hprefix tailTrace_4525692
  have hstable : (prefixWord ++ tailWord_4525692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525692).length < 2 ^ (prefixWord ++ tailWord_4525692).sum := by decide
  have hdescent : baseEnd_4525692 < baseStart_4525692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525710 : List Nat := [4, 1, 1, 3, 1, 4, 1, 3, 1, 4]
def baseStart_4525710 : Nat := 118140960795 + 4525710 * 2 ^ 59
def prefixEnd_4525710 : Nat := 4983230072969 + 3 ^ 40 * 4525710 * 2
def baseEnd_4525710 : Nat := 774621510953197790837215

theorem tailTrace_4525710 : CollatzResearch.WordTrace tailWord_4525710 prefixEnd_4525710 774621510953197790837215 := by
  unfold tailWord_4525710
  simp only [CollatzResearch.WordTrace]
  refine ⟨20633275554266634322128823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110044136289422049718020389 20633275554266634322128823)
  ·
    refine ⟨30949913331399951483193235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20633275554266634322128823 30949913331399951483193235)
    ·
      refine ⟨46424869997099927224789853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30949913331399951483193235 46424869997099927224789853)
      ·
        refine ⟨17409326248912472709296195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46424869997099927224789853 17409326248912472709296195)
        ·
          refine ⟨26113989373368709063944293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17409326248912472709296195 26113989373368709063944293)
          ·
            refine ⟨4896373007506632949489555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26113989373368709063944293 4896373007506632949489555)
            ·
              refine ⟨7344559511259949424234333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4896373007506632949489555 7344559511259949424234333)
              ·
                refine ⟨2754209816722481034087875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7344559511259949424234333 2754209816722481034087875)
                ·
                  refine ⟨4131314725083721551131813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2754209816722481034087875 4131314725083721551131813)
                  ·
                    refine ⟨774621510953197790837215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4131314725083721551131813 774621510953197790837215)
                    ·
                      rfl

theorem cell23_4525710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_4525710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525710 prefixEnd_4525710 := by exact prefixLift 4525710
  have htrace : WordTrace (prefixWord ++ tailWord_4525710) baseStart_4525710 baseEnd_4525710 := by
    simpa [prefixWord, tailWord_4525710, baseEnd_4525710] using wordTrace_append hprefix tailTrace_4525710
  have hstable : (prefixWord ++ tailWord_4525710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525710).length < 2 ^ (prefixWord ++ tailWord_4525710).sum := by decide
  have hdescent : baseEnd_4525710 < baseStart_4525710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525727 : List Nat := [1, 1, 2, 7, 1, 1, 3, 2, 1, 4]
def baseStart_4525727 : Nat := 118140960795 + 4525727 * 2 ^ 59
def prefixEnd_4525727 : Nat := 4983230072969 + 3 ^ 40 * 4525727 * 2
def baseEnd_4525727 : Nat := 774624420676906601999689

theorem tailTrace_4525727 : CollatzResearch.WordTrace tailWord_4525727 prefixEnd_4525727 774624420676906601999689 := by
  unfold tailWord_4525727
  simp only [CollatzResearch.WordTrace]
  refine ⟨165066824475071486480399435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110044549650047657653599623 165066824475071486480399435)
  ·
    refine ⟨247600236712607229720599153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165066824475071486480399435 247600236712607229720599153)
    ·
      refine ⟨185700177534455422290449365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247600236712607229720599153 185700177534455422290449365)
      ·
        refine ⟨4352347910963798959932407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 185700177534455422290449365 4352347910963798959932407)
        ·
          refine ⟨6528521866445698439898611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4352347910963798959932407 6528521866445698439898611)
          ·
            refine ⟨9792782799668547659847917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6528521866445698439898611 9792782799668547659847917)
            ·
              refine ⟨3672293549875705372442969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9792782799668547659847917 3672293549875705372442969)
              ·
                refine ⟨2754220162406779029332227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3672293549875705372442969 2754220162406779029332227)
                ·
                  refine ⟨4131330243610168543998341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2754220162406779029332227 4131330243610168543998341)
                  ·
                    refine ⟨774624420676906601999689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4131330243610168543998341 774624420676906601999689)
                    ·
                      rfl

theorem cell23_4525727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 1, 4].length) (baseStart_4525727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525727 prefixEnd_4525727 := by exact prefixLift 4525727
  have htrace : WordTrace (prefixWord ++ tailWord_4525727) baseStart_4525727 baseEnd_4525727 := by
    simpa [prefixWord, tailWord_4525727, baseEnd_4525727] using wordTrace_append hprefix tailTrace_4525727
  have hstable : (prefixWord ++ tailWord_4525727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525727).length < 2 ^ (prefixWord ++ tailWord_4525727).sum := by decide
  have hdescent : baseEnd_4525727 < baseStart_4525727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525733 : List Nat := [1, 3, 1, 2, 1, 2, 2, 6, 1, 1, 3]
def baseStart_4525733 : Nat := 118140960795 + 4525733 * 2 ^ 59
def prefixEnd_4525733 : Nat := 4983230072969 + 3 ^ 40 * 4525733 * 2
def baseEnd_4525733 : Nat := 2323876342914646782524039

theorem tailTrace_4525733 : CollatzResearch.WordTrace tailWord_4525733 prefixEnd_4525733 2323876342914646782524039 := by
  unfold tailWord_4525733
  simp only [CollatzResearch.WordTrace]
  refine ⟨165067043313049749505117853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110044695542033166336745235 165067043313049749505117853)
  ·
    refine ⟨61900141242393656064419195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165067043313049749505117853 61900141242393656064419195)
    ·
      refine ⟨92850211863590484096628793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61900141242393656064419195 92850211863590484096628793)
      ·
        refine ⟨69637658897692863072471595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92850211863590484096628793 69637658897692863072471595)
        ·
          refine ⟨104456488346539294608707393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69637658897692863072471595 104456488346539294608707393)
          ·
            refine ⟨78342366259904470956530545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104456488346539294608707393 78342366259904470956530545)
            ·
              refine ⟨58756774694928353217397909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78342366259904470956530545 58756774694928353217397909)
              ·
                refine ⟨2754223813824766557065527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58756774694928353217397909 2754223813824766557065527)
                ·
                  refine ⟨4131335720737149835598291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2754223813824766557065527 4131335720737149835598291)
                  ·
                    refine ⟨6197003581105724753397437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4131335720737149835598291 6197003581105724753397437)
                    ·
                      refine ⟨2323876342914646782524039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6197003581105724753397437 2323876342914646782524039)
                      ·
                        rfl

theorem cell23_4525733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_4525733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525733 prefixEnd_4525733 := by exact prefixLift 4525733
  have htrace : WordTrace (prefixWord ++ tailWord_4525733) baseStart_4525733 baseEnd_4525733 := by
    simpa [prefixWord, tailWord_4525733, baseEnd_4525733] using wordTrace_append hprefix tailTrace_4525733
  have hstable : (prefixWord ++ tailWord_4525733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525733).length < 2 ^ (prefixWord ++ tailWord_4525733).sum := by decide
  have hdescent : baseEnd_4525733 < baseStart_4525733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525756 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_4525756 : Nat := 118140960795 + 4525756 * 2 ^ 59
def prefixEnd_4525756 : Nat := 4983230072969 + 3 ^ 40 * 4525756 * 2
def baseEnd_4525756 : Nat := 2323888152969700192536433

theorem tailTrace_4525756 : CollatzResearch.WordTrace tailWord_4525756 prefixEnd_4525756 2323888152969700192536433 := by
  unfold tailWord_4525756
  simp only [CollatzResearch.WordTrace]
  refine ⟨82533941095983212216602561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110045254794644282955470081 82533941095983212216602561)
  ·
    refine ⟨61900455821987409162451921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82533941095983212216602561 61900455821987409162451921)
    ·
      refine ⟨46425341866490556871838941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61900455821987409162451921 46425341866490556871838941)
      ·
        refine ⟨17409503199933958826939603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46425341866490556871838941 17409503199933958826939603)
        ·
          refine ⟨26114254799900938240409405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17409503199933958826939603 26114254799900938240409405)
          ·
            refine ⟨9792845549962851840153527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26114254799900938240409405 9792845549962851840153527)
            ·
              refine ⟨14689268324944277760230291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9792845549962851840153527 14689268324944277760230291)
              ·
                refine ⟨22033902487416416640345437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14689268324944277760230291 22033902487416416640345437)
                ·
                  refine ⟨8262713432781156240129539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22033902487416416640345437 8262713432781156240129539)
                  ·
                    refine ⟨12394070149171734360194309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8262713432781156240129539 12394070149171734360194309)
                    ·
                      refine ⟨2323888152969700192536433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12394070149171734360194309 2323888152969700192536433)
                      ·
                        rfl

theorem cell23_4525756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_4525756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525756 prefixEnd_4525756 := by exact prefixLift 4525756
  have htrace : WordTrace (prefixWord ++ tailWord_4525756) baseStart_4525756 baseEnd_4525756 := by
    simpa [prefixWord, tailWord_4525756, baseEnd_4525756] using wordTrace_append hprefix tailTrace_4525756
  have hstable : (prefixWord ++ tailWord_4525756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525756).length < 2 ^ (prefixWord ++ tailWord_4525756).sum := by decide
  have hdescent : baseEnd_4525756 < baseStart_4525756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525854 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_4525854 : Nat := 118140960795 + 4525854 * 2 ^ 59
def prefixEnd_4525854 : Nat := 4983230072969 + 3 ^ 40 * 4525854 * 2
def baseEnd_4525854 : Nat := 2323938474073840809110983

theorem tailTrace_4525854 : CollatzResearch.WordTrace tailWord_4525854 prefixEnd_4525854 2323938474073840809110983 := by
  unfold tailWord_4525854
  simp only [CollatzResearch.WordTrace]
  refine ⟨20633932068201423396284077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110047637697074258113515077 20633932068201423396284077)
  ·
    refine ⟨7737724525575533773606529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20633932068201423396284077 7737724525575533773606529)
    ·
      refine ⟨5803293394181650330204897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7737724525575533773606529 5803293394181650330204897)
      ·
        refine ⟨4352470045636237747653673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5803293394181650330204897 4352470045636237747653673)
        ·
          refine ⟨3264352534227178310740255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4352470045636237747653673 3264352534227178310740255)
          ·
            refine ⟨4896528801340767466110383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264352534227178310740255 4896528801340767466110383)
            ·
              refine ⟨7344793202011151199165575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4896528801340767466110383 7344793202011151199165575)
              ·
                refine ⟨11017189803016726798748363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7344793202011151199165575 11017189803016726798748363)
                ·
                  refine ⟨16525784704525090198122545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11017189803016726798748363 16525784704525090198122545)
                  ·
                    refine ⟨12394338528393817648591909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16525784704525090198122545 12394338528393817648591909)
                    ·
                      refine ⟨2323938474073840809110983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12394338528393817648591909 2323938474073840809110983)
                      ·
                        rfl

theorem cell23_4525854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_4525854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525854 prefixEnd_4525854 := by exact prefixLift 4525854
  have htrace : WordTrace (prefixWord ++ tailWord_4525854) baseStart_4525854 baseEnd_4525854 := by
    simpa [prefixWord, tailWord_4525854, baseEnd_4525854] using wordTrace_append hprefix tailTrace_4525854
  have hstable : (prefixWord ++ tailWord_4525854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525854).length < 2 ^ (prefixWord ++ tailWord_4525854).sum := by decide
  have hdescent : baseEnd_4525854 < baseStart_4525854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525929 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 2, 8]
def baseStart_4525929 : Nat := 118140960795 + 4525929 * 2 ^ 59
def prefixEnd_4525929 : Nat := 4983230072969 + 3 ^ 40 * 4525929 * 2
def baseEnd_4525929 : Nat := 774658995040976005224379

theorem tailTrace_4525929 : CollatzResearch.WordTrace tailWord_4525929 prefixEnd_4525929 774658995040976005224379 := by
  unfold tailWord_4525929
  simp only [CollatzResearch.WordTrace]
  refine ⟨165074192020339674979252841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110049461346893116652835227 165074192020339674979252841)
  ·
    refine ⟨123805644015254756234439631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165074192020339674979252841 123805644015254756234439631)
    ·
      refine ⟨185708466022882134351659447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123805644015254756234439631 185708466022882134351659447)
      ·
        refine ⟨278562699034323201527489171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185708466022882134351659447 278562699034323201527489171)
        ·
          refine ⟨417844048551484802291233757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278562699034323201527489171 417844048551484802291233757)
          ·
            refine ⟨156691518206806800859212659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 417844048551484802291233757 156691518206806800859212659)
            ·
              refine ⟨235037277310210201288818989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156691518206806800859212659 235037277310210201288818989)
              ·
                refine ⟨88138978991328825483307121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235037277310210201288818989 88138978991328825483307121)
                ·
                  refine ⟨66104234243496619112480341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88138978991328825483307121 66104234243496619112480341)
                  ·
                    refine ⟨774658995040976005224379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66104234243496619112480341 774658995040976005224379)
                    ·
                      rfl

theorem cell23_4525929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 8].length) (baseStart_4525929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525929 prefixEnd_4525929 := by exact prefixLift 4525929
  have htrace : WordTrace (prefixWord ++ tailWord_4525929) baseStart_4525929 baseEnd_4525929 := by
    simpa [prefixWord, tailWord_4525929, baseEnd_4525929] using wordTrace_append hprefix tailTrace_4525929
  have hstable : (prefixWord ++ tailWord_4525929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525929).length < 2 ^ (prefixWord ++ tailWord_4525929).sum := by decide
  have hdescent : baseEnd_4525929 < baseStart_4525929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525950 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_4525950 : Nat := 118140960795 + 4525950 * 2 ^ 59
def prefixEnd_4525950 : Nat := 4983230072969 + 3 ^ 40 * 4525950 * 2
def baseEnd_4525950 : Nat := 774662589405557477836847

theorem tailTrace_4525950 : CollatzResearch.WordTrace tailWord_4525950 prefixEnd_4525950 774662589405557477836847 := by
  unfold tailWord_4525950
  simp only [CollatzResearch.WordTrace]
  refine ⟨20634369744157949445720913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110049971968842397043844869 20634369744157949445720913)
  ·
    refine ⟨15475777308118462084290685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20634369744157949445720913 15475777308118462084290685)
    ·
      refine ⟨5803416490544423281609007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15475777308118462084290685 5803416490544423281609007)
      ·
        refine ⟨8705124735816634922413511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5803416490544423281609007 8705124735816634922413511)
        ·
          refine ⟨13057687103724952383620267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8705124735816634922413511 13057687103724952383620267)
          ·
            refine ⟨19586530655587428575430401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13057687103724952383620267 19586530655587428575430401)
            ·
              refine ⟨14689897991690571431572801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19586530655587428575430401 14689897991690571431572801)
              ·
                refine ⟨11017423493767928573679601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14689897991690571431572801 11017423493767928573679601)
                ·
                  refine ⟨8263067620325946430259701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11017423493767928573679601 8263067620325946430259701)
                  ·
                    refine ⟨774662589405557477836847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8263067620325946430259701 774662589405557477836847)
                    ·
                      rfl

theorem cell23_4525950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_4525950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525950 prefixEnd_4525950 := by exact prefixLift 4525950
  have htrace : WordTrace (prefixWord ++ tailWord_4525950) baseStart_4525950 baseEnd_4525950 := by
    simpa [prefixWord, tailWord_4525950, baseEnd_4525950] using wordTrace_append hprefix tailTrace_4525950
  have hstable : (prefixWord ++ tailWord_4525950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525950).length < 2 ^ (prefixWord ++ tailWord_4525950).sum := by decide
  have hdescent : baseEnd_4525950 < baseStart_4525950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525970 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_4525970 : Nat := 118140960795 + 4525970 * 2 ^ 59
def prefixEnd_4525970 : Nat := 4983230072969 + 3 ^ 40 * 4525970 * 2
def baseEnd_4525970 : Nat := 2323998037829762355260449

theorem tailTrace_4525970 : CollatzResearch.WordTrace tailWord_4525970 prefixEnd_4525970 2323998037829762355260449 := by
  unfold tailWord_4525970
  simp only [CollatzResearch.WordTrace]
  refine ⟨41268921853297784745373841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110050458275460759320996909 41268921853297784745373841)
  ·
    refine ⟨30951691389973338559030381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41268921853297784745373841 30951691389973338559030381)
    ·
      refine ⟨11606884271240001959636393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30951691389973338559030381 11606884271240001959636393)
      ·
        refine ⟨8705163203430001469727295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11606884271240001959636393 8705163203430001469727295)
        ·
          refine ⟨13057744805145002204590943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8705163203430001469727295 13057744805145002204590943)
          ·
            refine ⟨19586617207717503306886415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13057744805145002204590943 19586617207717503306886415)
            ·
              refine ⟨29379925811576254960329623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19586617207717503306886415 29379925811576254960329623)
              ·
                refine ⟨44069888717364382440494435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29379925811576254960329623 44069888717364382440494435)
                ·
                  refine ⟨66104833076046573660741653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44069888717364382440494435 66104833076046573660741653)
                  ·
                    refine ⟨3098664050439683140347265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66104833076046573660741653 3098664050439683140347265)
                    ·
                      refine ⟨2323998037829762355260449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3098664050439683140347265 2323998037829762355260449)
                      ·
                        rfl

theorem cell23_4525970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_4525970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525970 prefixEnd_4525970 := by exact prefixLift 4525970
  have htrace : WordTrace (prefixWord ++ tailWord_4525970) baseStart_4525970 baseEnd_4525970 := by
    simpa [prefixWord, tailWord_4525970, baseEnd_4525970] using wordTrace_append hprefix tailTrace_4525970
  have hstable : (prefixWord ++ tailWord_4525970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525970).length < 2 ^ (prefixWord ++ tailWord_4525970).sum := by decide
  have hdescent : baseEnd_4525970 < baseStart_4525970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4525980 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 3, 4]
def baseStart_4525980 : Nat := 118140960795 + 4525980 * 2 ^ 59
def prefixEnd_4525980 : Nat := 4983230072969 + 3 ^ 40 * 4525980 * 2
def baseEnd_4525980 : Nat := 774667724212102438711801

theorem tailTrace_4525980 : CollatzResearch.WordTrace tailWord_4525980 prefixEnd_4525980 774667724212102438711801 := by
  unfold tailWord_4525980
  simp only [CollatzResearch.WordTrace]
  refine ⟨82538026071577455344679697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110050701428769940459572929 82538026071577455344679697)
  ·
    refine ⟨61903519553683091508509773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82538026071577455344679697 61903519553683091508509773)
    ·
      refine ⟨23213819832631159315691165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61903519553683091508509773 23213819832631159315691165)
      ·
        refine ⟨8705182437236684743384187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23213819832631159315691165 8705182437236684743384187)
        ·
          refine ⟨13057773655855027115076281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8705182437236684743384187 13057773655855027115076281)
          ·
            refine ⟨9793330241891270336307211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13057773655855027115076281 9793330241891270336307211)
            ·
              refine ⟨14689995362836905504460817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9793330241891270336307211 14689995362836905504460817)
              ·
                refine ⟨11017496522127679128345613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14689995362836905504460817 11017496522127679128345613)
                ·
                  refine ⟨4131561195797879673129605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11017496522127679128345613 4131561195797879673129605)
                  ·
                    refine ⟨774667724212102438711801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4131561195797879673129605 774667724212102438711801)
                    ·
                      rfl

theorem cell23_4525980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_4525980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4525980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4525980 prefixEnd_4525980 := by exact prefixLift 4525980
  have htrace : WordTrace (prefixWord ++ tailWord_4525980) baseStart_4525980 baseEnd_4525980 := by
    simpa [prefixWord, tailWord_4525980, baseEnd_4525980] using wordTrace_append hprefix tailTrace_4525980
  have hstable : (prefixWord ++ tailWord_4525980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4525980).length < 2 ^ (prefixWord ++ tailWord_4525980).sum := by decide
  have hdescent : baseEnd_4525980 < baseStart_4525980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4525980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526003 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 5, 1, 3]
def baseStart_4526003 : Nat := 118140960795 + 4526003 * 2 ^ 59
def prefixEnd_4526003 : Nat := 4983230072969 + 3 ^ 40 * 4526003 * 2
def baseEnd_4526003 : Nat := 2324014982691360726147797

theorem tailTrace_4526003 : CollatzResearch.WordTrace tailWord_4526003 prefixEnd_4526003 2324014982691360726147797 := by
  unfold tailWord_4526003
  simp only [CollatzResearch.WordTrace]
  refine ⟨165076891022071585617446663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110051260681381057078297775 165076891022071585617446663)
  ·
    refine ⟨247615336533107378426169995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165076891022071585617446663 247615336533107378426169995)
    ·
      refine ⟨371423004799661067639254993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247615336533107378426169995 371423004799661067639254993)
      ·
        refine ⟨278567253599745800729441245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371423004799661067639254993 278567253599745800729441245)
        ·
          refine ⟨104462720099904675273540467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 278567253599745800729441245 104462720099904675273540467)
          ·
            refine ⟨156694080149857012910310701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104462720099904675273540467 156694080149857012910310701)
            ·
              refine ⟨58760280056196379841366513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156694080149857012910310701 58760280056196379841366513)
              ·
                refine ⟨44070210042147284881024885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58760280056196379841366513 44070210042147284881024885)
                ·
                  refine ⟨4131582191451307957596083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44070210042147284881024885 4131582191451307957596083)
                  ·
                    refine ⟨6197373287176961936394125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4131582191451307957596083 6197373287176961936394125)
                    ·
                      refine ⟨2324014982691360726147797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6197373287176961936394125 2324014982691360726147797)
                      ·
                        rfl

theorem cell23_4526003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 1, 3].length) (baseStart_4526003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526003 prefixEnd_4526003 := by exact prefixLift 4526003
  have htrace : WordTrace (prefixWord ++ tailWord_4526003) baseStart_4526003 baseEnd_4526003 := by
    simpa [prefixWord, tailWord_4526003, baseEnd_4526003] using wordTrace_append hprefix tailTrace_4526003
  have hstable : (prefixWord ++ tailWord_4526003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526003).length < 2 ^ (prefixWord ++ tailWord_4526003).sum := by decide
  have hdescent : baseEnd_4526003 < baseStart_4526003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526060 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 5, 2, 2]
def baseStart_4526060 : Nat := 118140960795 + 4526060 * 2 ^ 59
def prefixEnd_4526060 : Nat := 4983230072969 + 3 ^ 40 * 4526060 * 2
def baseEnd_4526060 : Nat := 2324044251088667003135035

theorem tailTrace_4526060 : CollatzResearch.WordTrace tailWord_4526060 prefixEnd_4526060 2324044251088667003135035 := by
  unfold tailWord_4526060
  simp only [CollatzResearch.WordTrace]
  refine ⟨82539484991432542176135817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110052646655243389568181089 82539484991432542176135817)
  ·
    refine ⟨61904613743574406632101863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82539484991432542176135817 61904613743574406632101863)
    ·
      refine ⟨92856920615361609948152795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61904613743574406632101863 92856920615361609948152795)
      ·
        refine ⟨139285380923042414922229193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92856920615361609948152795 139285380923042414922229193)
        ·
          refine ⟨104464035692281811191671895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139285380923042414922229193 104464035692281811191671895)
          ·
            refine ⟨156696053538422716787507843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104464035692281811191671895 156696053538422716787507843)
            ·
              refine ⟨235044080307634075181261765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156696053538422716787507843 235044080307634075181261765)
              ·
                refine ⟨44070765057681389096486581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 235044080307634075181261765 44070765057681389096486581)
                ·
                  refine ⟨4131634224157630227795617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44070765057681389096486581 4131634224157630227795617)
                  ·
                    refine ⟨3098725668118222670846713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4131634224157630227795617 3098725668118222670846713)
                    ·
                      refine ⟨2324044251088667003135035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3098725668118222670846713 2324044251088667003135035)
                      ·
                        rfl

theorem cell23_4526060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 2, 2].length) (baseStart_4526060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526060 prefixEnd_4526060 := by exact prefixLift 4526060
  have htrace : WordTrace (prefixWord ++ tailWord_4526060) baseStart_4526060 baseEnd_4526060 := by
    simpa [prefixWord, tailWord_4526060, baseEnd_4526060] using wordTrace_append hprefix tailTrace_4526060
  have hstable : (prefixWord ++ tailWord_4526060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526060).length < 2 ^ (prefixWord ++ tailWord_4526060).sum := by decide
  have hdescent : baseEnd_4526060 < baseStart_4526060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526063 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 5]
def baseStart_4526063 : Nat := 118140960795 + 4526063 * 2 ^ 59
def prefixEnd_4526063 : Nat := 4983230072969 + 3 ^ 40 * 4526063 * 2
def baseEnd_4526063 : Nat := 2324045791530630491397521

theorem tailTrace_4526063 : CollatzResearch.WordTrace tailWord_4526063 prefixEnd_4526063 2324045791530630491397521 := by
  unfold tailWord_4526063
  simp only [CollatzResearch.WordTrace]
  refine ⟨165079079401854215864630843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110052719601236143909753895 165079079401854215864630843)
  ·
    refine ⟨247618619102781323796946265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165079079401854215864630843 247618619102781323796946265)
    ·
      refine ⟨185713964327085992847709699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247618619102781323796946265 185713964327085992847709699)
      ·
        refine ⟨278570946490628989271564549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185713964327085992847709699 278570946490628989271564549)
        ·
          refine ⟨52232052466992935488418353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 278570946490628989271564549 52232052466992935488418353)
          ·
            refine ⟨39174039350244701616313765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52232052466992935488418353 39174039350244701616313765)
            ·
              refine ⟨7345132378170881553058831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39174039350244701616313765 7345132378170881553058831)
              ·
                refine ⟨11017698567256322329588247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7345132378170881553058831 11017698567256322329588247)
                ·
                  refine ⟨16526547850884483494382371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11017698567256322329588247 16526547850884483494382371)
                  ·
                    refine ⟨24789821776326725241573557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16526547850884483494382371 24789821776326725241573557)
                    ·
                      refine ⟨2324045791530630491397521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24789821776326725241573557 2324045791530630491397521)
                      ·
                        rfl

theorem cell23_4526063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 5].length) (baseStart_4526063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526063 prefixEnd_4526063 := by exact prefixLift 4526063
  have htrace : WordTrace (prefixWord ++ tailWord_4526063) baseStart_4526063 baseEnd_4526063 := by
    simpa [prefixWord, tailWord_4526063, baseEnd_4526063] using wordTrace_append hprefix tailTrace_4526063
  have hstable : (prefixWord ++ tailWord_4526063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526063).length < 2 ^ (prefixWord ++ tailWord_4526063).sum := by decide
  have hdescent : baseEnd_4526063 < baseStart_4526063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526077 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 3, 2, 2]
def baseStart_4526077 : Nat := 118140960795 + 4526077 * 2 ^ 59
def prefixEnd_4526077 : Nat := 4983230072969 + 3 ^ 40 * 4526077 * 2
def baseEnd_4526077 : Nat := 2324052980259793436622457

theorem tailTrace_4526077 : CollatzResearch.WordTrace tailWord_4526077 prefixEnd_4526077 2324052980259793436622457 := by
  unfold tailWord_4526077
  simp only [CollatzResearch.WordTrace]
  refine ⟨165079590023803496255640485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110053060015868997503760323 165079590023803496255640485)
  ·
    refine ⟨30952423129463155547932591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165079590023803496255640485 30952423129463155547932591)
    ·
      refine ⟨46428634694194733321898887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30952423129463155547932591 46428634694194733321898887)
      ·
        refine ⟨69642952041292099982848331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46428634694194733321898887 69642952041292099982848331)
        ·
          refine ⟨104464428061938149974272497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69642952041292099982848331 104464428061938149974272497)
          ·
            refine ⟨78348321046453612480704373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104464428061938149974272497 78348321046453612480704373)
            ·
              refine ⟨7345155098105026170066035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78348321046453612480704373 7345155098105026170066035)
              ·
                refine ⟨11017732647157539255099053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7345155098105026170066035 11017732647157539255099053)
                ·
                  refine ⟨4131649742684077220662145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11017732647157539255099053 4131649742684077220662145)
                  ·
                    refine ⟨3098737307013057915496609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4131649742684077220662145 3098737307013057915496609)
                    ·
                      refine ⟨2324052980259793436622457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3098737307013057915496609 2324052980259793436622457)
                      ·
                        rfl

theorem cell23_4526077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_4526077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526077 prefixEnd_4526077 := by exact prefixLift 4526077
  have htrace : WordTrace (prefixWord ++ tailWord_4526077) baseStart_4526077 baseEnd_4526077 := by
    simpa [prefixWord, tailWord_4526077, baseEnd_4526077] using wordTrace_append hprefix tailTrace_4526077
  have hstable : (prefixWord ++ tailWord_4526077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526077).length < 2 ^ (prefixWord ++ tailWord_4526077).sum := by decide
  have hdescent : baseEnd_4526077 < baseStart_4526077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526087 : List Nat := [1, 1, 4, 3, 1, 2, 4, 1, 2, 4]
def baseStart_4526087 : Nat := 118140960795 + 4526087 * 2 ^ 59
def prefixEnd_4526087 : Nat := 4983230072969 + 3 ^ 40 * 4526087 * 2
def baseEnd_4526087 : Nat := 774686038355446132499137

theorem tailTrace_4526087 : CollatzResearch.WordTrace tailWord_4526087 prefixEnd_4526087 774686038355446132499137 := by
  unfold tailWord_4526087
  simp only [CollatzResearch.WordTrace]
  refine ⟨165079954753767267963504515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110053303169178178642336343 165079954753767267963504515)
  ·
    refine ⟨247619932130650901945256773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165079954753767267963504515 247619932130650901945256773)
    ·
      refine ⟨46428737274497044114735645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 247619932130650901945256773 46428737274497044114735645)
      ·
        refine ⟨17410776477936391543025867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46428737274497044114735645 17410776477936391543025867)
        ·
          refine ⟨26116164716904587314538801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17410776477936391543025867 26116164716904587314538801)
          ·
            refine ⟨19587123537678440485904101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26116164716904587314538801 19587123537678440485904101)
            ·
              refine ⟨3672585663314707591107019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19587123537678440485904101 3672585663314707591107019)
              ·
                refine ⟨5508878494972061386660529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3672585663314707591107019 5508878494972061386660529)
                ·
                  refine ⟨4131658871229046039995397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5508878494972061386660529 4131658871229046039995397)
                  ·
                    refine ⟨774686038355446132499137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4131658871229046039995397 774686038355446132499137)
                    ·
                      rfl

theorem cell23_4526087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_4526087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526087 prefixEnd_4526087 := by exact prefixLift 4526087
  have htrace : WordTrace (prefixWord ++ tailWord_4526087) baseStart_4526087 baseEnd_4526087 := by
    simpa [prefixWord, tailWord_4526087, baseEnd_4526087] using wordTrace_append hprefix tailTrace_4526087
  have hstable : (prefixWord ++ tailWord_4526087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526087).length < 2 ^ (prefixWord ++ tailWord_4526087).sum := by decide
  have hdescent : baseEnd_4526087 < baseStart_4526087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526096 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 2, 7]
def baseStart_4526096 : Nat := 118140960795 + 4526096 * 2 ^ 59
def prefixEnd_4526096 : Nat := 4983230072969 + 3 ^ 40 * 4526096 * 2
def baseEnd_4526096 : Nat := 774687578797409620761623

theorem tailTrace_4526096 : CollatzResearch.WordTrace tailWord_4526096 prefixEnd_4526096 774687578797409620761623 := by
  unfold tailWord_4526096
  simp only [CollatzResearch.WordTrace]
  refine ⟨82540141505367331250291071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110053522007156441667054761 82540141505367331250291071)
  ·
    refine ⟨123810212258050996875436607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82540141505367331250291071 123810212258050996875436607)
    ·
      refine ⟨185715318387076495313154911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123810212258050996875436607 185715318387076495313154911)
      ·
        refine ⟨278572977580614742969732367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185715318387076495313154911 278572977580614742969732367)
        ·
          refine ⟨417859466370922114454598551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278572977580614742969732367 417859466370922114454598551)
          ·
            refine ⟨626789199556383171681897827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417859466370922114454598551 626789199556383171681897827)
            ·
              refine ⟨940183799334574757522846741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626789199556383171681897827 940183799334574757522846741)
              ·
                refine ⟨44071115593808191758883441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 940183799334574757522846741 44071115593808191758883441)
                ·
                  refine ⟨33053336695356143819162581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44071115593808191758883441 33053336695356143819162581)
                  ·
                    refine ⟨774687578797409620761623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33053336695356143819162581 774687578797409620761623)
                    ·
                      rfl

theorem cell23_4526096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2, 7].length) (baseStart_4526096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526096 prefixEnd_4526096 := by exact prefixLift 4526096
  have htrace : WordTrace (prefixWord ++ tailWord_4526096) baseStart_4526096 baseEnd_4526096 := by
    simpa [prefixWord, tailWord_4526096, baseEnd_4526096] using wordTrace_append hprefix tailTrace_4526096
  have hstable : (prefixWord ++ tailWord_4526096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526096).length < 2 ^ (prefixWord ++ tailWord_4526096).sum := by decide
  have hdescent : baseEnd_4526096 < baseStart_4526096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526133 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_4526133 : Nat := 118140960795 + 4526133 * 2 ^ 59
def prefixEnd_4526133 : Nat := 4983230072969 + 3 ^ 40 * 4526133 * 2
def baseEnd_4526133 : Nat := 2324081735176445217522199

theorem tailTrace_4526133 : CollatzResearch.WordTrace tailWord_4526133 prefixEnd_4526133 2324081735176445217522199 := by
  unfold tailWord_4526133
  simp only [CollatzResearch.WordTrace]
  refine ⟨165081632511600617819679053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110054421674400411879786035 165081632511600617819679053)
  ·
    refine ⟨61905612191850231682379645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165081632511600617819679053 61905612191850231682379645)
    ·
      refine ⟨23214604571943836880892367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61905612191850231682379645 23214604571943836880892367)
      ·
        refine ⟨34821906857915755321338551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23214604571943836880892367 34821906857915755321338551)
        ·
          refine ⟨52232860286873632982007827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34821906857915755321338551 52232860286873632982007827)
          ·
            refine ⟨78349290430310449473011741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52232860286873632982007827 78349290430310449473011741)
            ·
              refine ⟨29380983911366418552379403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78349290430310449473011741 29380983911366418552379403)
              ·
                refine ⟨44071475867049627828569105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29380983911366418552379403 44071475867049627828569105)
                ·
                  refine ⟨33053606900287220871426829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44071475867049627828569105 33053606900287220871426829)
                  ·
                    refine ⟨12395102587607707826785061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33053606900287220871426829 12395102587607707826785061)
                    ·
                      refine ⟨2324081735176445217522199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12395102587607707826785061 2324081735176445217522199)
                      ·
                        rfl

theorem cell23_4526133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_4526133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526133 prefixEnd_4526133 := by exact prefixLift 4526133
  have htrace : WordTrace (prefixWord ++ tailWord_4526133) baseStart_4526133 baseEnd_4526133 := by
    simpa [prefixWord, tailWord_4526133, baseEnd_4526133] using wordTrace_append hprefix tailTrace_4526133
  have hstable : (prefixWord ++ tailWord_4526133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526133).length < 2 ^ (prefixWord ++ tailWord_4526133).sum := by decide
  have hdescent : baseEnd_4526133 < baseStart_4526133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526153 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 2, 4, 3]
def baseStart_4526153 : Nat := 118140960795 + 4526153 * 2 ^ 59
def prefixEnd_4526153 : Nat := 4983230072969 + 3 ^ 40 * 4526153 * 2
def baseEnd_4526153 : Nat := 2324092004789535139272107

theorem tailTrace_4526153 : CollatzResearch.WordTrace tailWord_4526153 prefixEnd_4526153 2324092004789535139272107 := by
  unfold tailWord_4526153
  simp only [CollatzResearch.WordTrace]
  refine ⟨165082361971528161235407113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110054907981018774156938075 165082361971528161235407113)
  ·
    refine ⟨123811771478646120926555335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165082361971528161235407113 123811771478646120926555335)
    ·
      refine ⟨185717657217969181389833003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123811771478646120926555335 185717657217969181389833003)
      ·
        refine ⟨278576485826953772084749505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185717657217969181389833003 278576485826953772084749505)
        ·
          refine ⟨208932364370215329063562129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278576485826953772084749505 208932364370215329063562129)
          ·
            refine ⟨156699273277661496797671597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208932364370215329063562129 156699273277661496797671597)
            ·
              refine ⟨58762227479123061299126849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156699273277661496797671597 58762227479123061299126849)
              ·
                refine ⟨44071670609342295974345137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58762227479123061299126849 44071670609342295974345137)
                ·
                  refine ⟨33053752957006721980758853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44071670609342295974345137 33053752957006721980758853)
                  ·
                    refine ⟨6197578679438760371392285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33053752957006721980758853 6197578679438760371392285)
                    ·
                      refine ⟨2324092004789535139272107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6197578679438760371392285 2324092004789535139272107)
                      ·
                        rfl

theorem cell23_4526153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 4, 3].length) (baseStart_4526153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526153 prefixEnd_4526153 := by exact prefixLift 4526153
  have htrace : WordTrace (prefixWord ++ tailWord_4526153) baseStart_4526153 baseEnd_4526153 := by
    simpa [prefixWord, tailWord_4526153, baseEnd_4526153] using wordTrace_append hprefix tailTrace_4526153
  have hstable : (prefixWord ++ tailWord_4526153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526153).length < 2 ^ (prefixWord ++ tailWord_4526153).sum := by decide
  have hdescent : baseEnd_4526153 < baseStart_4526153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526178 : List Nat := [3, 3, 2, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_4526178 : Nat := 118140960795 + 4526178 * 2 ^ 59
def prefixEnd_4526178 : Nat := 4983230072969 + 3 ^ 40 * 4526178 * 2
def baseEnd_4526178 : Nat := 2324104841805897541459493

theorem tailTrace_4526178 : CollatzResearch.WordTrace tailWord_4526178 prefixEnd_4526178 2324104841805897541459493 := by
  unfold tailWord_4526178
  simp only [CollatzResearch.WordTrace]
  refine ⟨41270818449109397626266797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110055515864291727003378125 41270818449109397626266797)
  ·
    refine ⟨15476556918416024109850049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41270818449109397626266797 15476556918416024109850049)
    ·
      refine ⟨11607417688812018082387537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15476556918416024109850049 11607417688812018082387537)
      ·
        refine ⟨8705563266609013561790653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11607417688812018082387537 8705563266609013561790653)
        ·
          refine ⟨3264586224978380085671495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8705563266609013561790653 3264586224978380085671495)
          ·
            refine ⟨4896879337467570128507243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264586224978380085671495 4896879337467570128507243)
            ·
              refine ⟨7345319006201355192760865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4896879337467570128507243 7345319006201355192760865)
              ·
                refine ⟨5508989254651016394570649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7345319006201355192760865 5508989254651016394570649)
                ·
                  refine ⟨4131741940988262295927987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5508989254651016394570649 4131741940988262295927987)
                  ·
                    refine ⟨6197612911482393443891981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4131741940988262295927987 6197612911482393443891981)
                    ·
                      refine ⟨2324104841805897541459493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6197612911482393443891981 2324104841805897541459493)
                      ·
                        rfl

theorem cell23_4526178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_4526178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526178 prefixEnd_4526178 := by exact prefixLift 4526178
  have htrace : WordTrace (prefixWord ++ tailWord_4526178) baseStart_4526178 baseEnd_4526178 := by
    simpa [prefixWord, tailWord_4526178, baseEnd_4526178] using wordTrace_append hprefix tailTrace_4526178
  have hstable : (prefixWord ++ tailWord_4526178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526178).length < 2 ^ (prefixWord ++ tailWord_4526178).sum := by decide
  have hdescent : baseEnd_4526178 < baseStart_4526178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526190 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 7]
def baseStart_4526190 : Nat := 118140960795 + 4526190 * 2 ^ 59
def prefixEnd_4526190 : Nat := 4983230072969 + 3 ^ 40 * 4526190 * 2
def baseEnd_4526190 : Nat := 258234555952639054945493

theorem tailTrace_4526190 : CollatzResearch.WordTrace tailWord_4526190 prefixEnd_4526190 258234555952639054945493 := by
  unfold tailWord_4526190
  simp only [CollatzResearch.WordTrace]
  refine ⟨20635463934049264569313003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110055807648262744369669349 20635463934049264569313003)
  ·
    refine ⟨30953195901073896853969505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20635463934049264569313003 30953195901073896853969505)
    ·
      refine ⟨23214896925805422640477129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30953195901073896853969505 23214896925805422640477129)
      ·
        refine ⟨17411172694354066980357847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23214896925805422640477129 17411172694354066980357847)
        ·
          refine ⟨26116759041531100470536771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17411172694354066980357847 26116759041531100470536771)
          ·
            refine ⟨39175138562296650705805157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26116759041531100470536771 39175138562296650705805157)
            ·
              refine ⟨7345338480430622007338467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39175138562296650705805157 7345338480430622007338467)
              ·
                refine ⟨11018007720645933011007701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7345338480430622007338467 11018007720645933011007701)
                ·
                  refine ⟨258234555952639054945493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11018007720645933011007701 258234555952639054945493)
                  ·
                    rfl

theorem cell23_4526190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_4526190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526190 prefixEnd_4526190 := by exact prefixLift 4526190
  have htrace : WordTrace (prefixWord ++ tailWord_4526190) baseStart_4526190 baseEnd_4526190 := by
    simpa [prefixWord, tailWord_4526190, baseEnd_4526190] using wordTrace_append hprefix tailTrace_4526190
  have hstable : (prefixWord ++ tailWord_4526190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526190).length < 2 ^ (prefixWord ++ tailWord_4526190).sum := by decide
  have hdescent : baseEnd_4526190 < baseStart_4526190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526201 : List Nat := [1, 2, 1, 3, 4, 2, 3, 1, 2, 2, 2]
def baseStart_4526201 : Nat := 118140960795 + 4526201 * 2 ^ 59
def prefixEnd_4526201 : Nat := 4983230072969 + 3 ^ 40 * 4526201 * 2
def baseEnd_4526201 : Nat := 2324116651860950951471887

theorem tailTrace_4526201 : CollatzResearch.WordTrace tailWord_4526201 prefixEnd_4526201 2324116651860950951471887 := by
  unfold tailWord_4526201
  simp only [CollatzResearch.WordTrace]
  refine ⟨165084112675354265433154457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110056075116902843622102971 165084112675354265433154457)
  ·
    refine ⟨123813084506515699074865843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165084112675354265433154457 123813084506515699074865843)
    ·
      refine ⟨185719626759773548612298765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123813084506515699074865843 185719626759773548612298765)
      ·
        refine ⟨69644860034915080729612037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185719626759773548612298765 69644860034915080729612037)
        ·
          refine ⟨13058411256546577636802257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69644860034915080729612037 13058411256546577636802257)
          ·
            refine ⟨9793808442409933227601693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13058411256546577636802257 9793808442409933227601693)
            ·
              refine ⟨3672678165903724960350635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9793808442409933227601693 3672678165903724960350635)
              ·
                refine ⟨5509017248855587440525953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3672678165903724960350635 5509017248855587440525953)
                ·
                  refine ⟨4131762936641690580394465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5509017248855587440525953 4131762936641690580394465)
                  ·
                    refine ⟨3098822202481267935295849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4131762936641690580394465 3098822202481267935295849)
                    ·
                      refine ⟨2324116651860950951471887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3098822202481267935295849 2324116651860950951471887)
                      ·
                        rfl

theorem cell23_4526201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_4526201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526201 prefixEnd_4526201 := by exact prefixLift 4526201
  have htrace : WordTrace (prefixWord ++ tailWord_4526201) baseStart_4526201 baseEnd_4526201 := by
    simpa [prefixWord, tailWord_4526201, baseEnd_4526201] using wordTrace_append hprefix tailTrace_4526201
  have hstable : (prefixWord ++ tailWord_4526201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526201).length < 2 ^ (prefixWord ++ tailWord_4526201).sum := by decide
  have hdescent : baseEnd_4526201 < baseStart_4526201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526240 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 4]
def baseStart_4526240 : Nat := 118140960795 + 4526240 * 2 ^ 59
def prefixEnd_4526240 : Nat := 4983230072969 + 3 ^ 40 * 4526240 * 2
def baseEnd_4526240 : Nat := 2324136677606476298884207

theorem tailTrace_4526240 : CollatzResearch.WordTrace tailWord_4526240 prefixEnd_4526240 2324136677606476298884207 := by
  unfold tailWord_4526240
  simp only [CollatzResearch.WordTrace]
  refine ⟨82542767561106487546912087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110057023414808650062549449 82542767561106487546912087)
  ·
    refine ⟨123814151341659731320368131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82542767561106487546912087 123814151341659731320368131)
    ·
      refine ⟨185721227012489596980552197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123814151341659731320368131 185721227012489596980552197)
      ·
        refine ⟨34822730064841799433853537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185721227012489596980552197 34822730064841799433853537)
        ·
          refine ⟨26117047548631349575390153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34822730064841799433853537 26117047548631349575390153)
          ·
            refine ⟨19587785661473512181542615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26117047548631349575390153 19587785661473512181542615)
            ·
              refine ⟨29381678492210268272313923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19587785661473512181542615 29381678492210268272313923)
              ·
                refine ⟨44072517738315402408470885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29381678492210268272313923 44072517738315402408470885)
                ·
                  refine ⟨8263597075934137951588291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44072517738315402408470885 8263597075934137951588291)
                  ·
                    refine ⟨12395395613901206927382437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8263597075934137951588291 12395395613901206927382437)
                    ·
                      refine ⟨2324136677606476298884207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12395395613901206927382437 2324136677606476298884207)
                      ·
                        rfl

theorem cell23_4526240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_4526240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526240 prefixEnd_4526240 := by exact prefixLift 4526240
  have htrace : WordTrace (prefixWord ++ tailWord_4526240) baseStart_4526240 baseEnd_4526240 := by
    simpa [prefixWord, tailWord_4526240, baseEnd_4526240] using wordTrace_append hprefix tailTrace_4526240
  have hstable : (prefixWord ++ tailWord_4526240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526240).length < 2 ^ (prefixWord ++ tailWord_4526240).sum := by decide
  have hdescent : baseEnd_4526240 < baseStart_4526240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526247 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_4526247 : Nat := 118140960795 + 4526247 * 2 ^ 59
def prefixEnd_4526247 : Nat := 4983230072969 + 3 ^ 40 * 4526247 * 2
def baseEnd_4526247 : Nat := 2324140271971057771496675

theorem tailTrace_4526247 : CollatzResearch.WordTrace tailWord_4526247 prefixEnd_4526247 2324140271971057771496675 := by
  unfold tailWord_4526247
  simp only [CollatzResearch.WordTrace]
  refine ⟨165085790433187615289328995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110057193622125076859552663 165085790433187615289328995)
  ·
    refine ⟨247628685649781422933993493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165085790433187615289328995 247628685649781422933993493)
    ·
      refine ⟨11607594639833504200030945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 247628685649781422933993493 11607594639833504200030945)
      ·
        refine ⟨8705695979875128150023209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11607594639833504200030945 8705695979875128150023209)
        ·
          refine ⟨6529271984906346112517407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8705695979875128150023209 6529271984906346112517407)
          ·
            refine ⟨9793907977359519168776111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6529271984906346112517407 9793907977359519168776111)
            ·
              refine ⟨14690861966039278753164167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9793907977359519168776111 14690861966039278753164167)
              ·
                refine ⟨22036292949058918129746251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14690861966039278753164167 22036292949058918129746251)
                ·
                  refine ⟨33054439423588377194619377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22036292949058918129746251 33054439423588377194619377)
                  ·
                    refine ⟨24790829567691282895964533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33054439423588377194619377 24790829567691282895964533)
                    ·
                      refine ⟨2324140271971057771496675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24790829567691282895964533 2324140271971057771496675)
                      ·
                        rfl

theorem cell23_4526247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_4526247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526247 prefixEnd_4526247 := by exact prefixLift 4526247
  have htrace : WordTrace (prefixWord ++ tailWord_4526247) baseStart_4526247 baseEnd_4526247 := by
    simpa [prefixWord, tailWord_4526247, baseEnd_4526247] using wordTrace_append hprefix tailTrace_4526247
  have hstable : (prefixWord ++ tailWord_4526247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526247).length < 2 ^ (prefixWord ++ tailWord_4526247).sum := by decide
  have hdescent : baseEnd_4526247 < baseStart_4526247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526301 : List Nat := [1, 4, 3, 2, 1, 2, 1, 4, 1, 4]
def baseStart_4526301 : Nat := 118140960795 + 4526301 * 2 ^ 59
def prefixEnd_4526301 : Nat := 4983230072969 + 3 ^ 40 * 4526301 * 2
def baseEnd_4526301 : Nat := 774722666642133520073809

theorem tailTrace_4526301 : CollatzResearch.WordTrace tailWord_4526301 prefixEnd_4526301 774722666642133520073809 := by
  unfold tailWord_4526301
  simp only [CollatzResearch.WordTrace]
  refine ⟨165087759974991982511794757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110058506649994655007863171 165087759974991982511794757)
  ·
    refine ⟨30953954995310996720961517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165087759974991982511794757 30953954995310996720961517)
    ·
      refine ⟨11607733123241623770360569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30953954995310996720961517 11607733123241623770360569)
      ·
        refine ⟨8705799842431217827770427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11607733123241623770360569 8705799842431217827770427)
        ·
          refine ⟨13058699763646826741655641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8705799842431217827770427 13058699763646826741655641)
          ·
            refine ⟨9794024822735120056241731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13058699763646826741655641 9794024822735120056241731)
            ·
              refine ⟨14691037234102680084362597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9794024822735120056241731 14691037234102680084362597)
              ·
                refine ⟨2754569481394252515817987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14691037234102680084362597 2754569481394252515817987)
                ·
                  refine ⟨4131854222091378773726981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2754569481394252515817987 4131854222091378773726981)
                  ·
                    refine ⟨774722666642133520073809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4131854222091378773726981 774722666642133520073809)
                    ·
                      rfl

theorem cell23_4526301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_4526301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526301 prefixEnd_4526301 := by exact prefixLift 4526301
  have htrace : WordTrace (prefixWord ++ tailWord_4526301) baseStart_4526301 baseEnd_4526301 := by
    simpa [prefixWord, tailWord_4526301, baseEnd_4526301] using wordTrace_append hprefix tailTrace_4526301
  have hstable : (prefixWord ++ tailWord_4526301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526301).length < 2 ^ (prefixWord ++ tailWord_4526301).sum := by decide
  have hdescent : baseEnd_4526301 < baseStart_4526301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526334 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_4526334 : Nat := 118140960795 + 4526334 * 2 ^ 59
def prefixEnd_4526334 : Nat := 4983230072969 + 3 ^ 40 * 4526334 * 2
def baseEnd_4526334 : Nat := 2324184944787998931108775

theorem tailTrace_4526334 : CollatzResearch.WordTrace tailWord_4526334 prefixEnd_4526334 2324184944787998931108775 := by
  unfold tailWord_4526334
  simp only [CollatzResearch.WordTrace]
  refine ⟨20636120447984053643468257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110059309055914952765164037 20636120447984053643468257)
  ·
    refine ⟨15477090335988040232601193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20636120447984053643468257 15477090335988040232601193)
    ·
      refine ⟨11607817751991030174450895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15477090335988040232601193 11607817751991030174450895)
      ·
        refine ⟨17411726627986545261676343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11607817751991030174450895 17411726627986545261676343)
        ·
          refine ⟨26117589941979817892514515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17411726627986545261676343 26117589941979817892514515)
          ·
            refine ⟨39176384912969726838771773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26117589941979817892514515 39176384912969726838771773)
            ·
              refine ⟨14691144342363647564539415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39176384912969726838771773 14691144342363647564539415)
              ·
                refine ⟨22036716513545471346809123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14691144342363647564539415 22036716513545471346809123)
                ·
                  refine ⟨33055074770318207020213685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22036716513545471346809123 33055074770318207020213685)
                  ·
                    refine ⟨3098913259717331908145033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33055074770318207020213685 3098913259717331908145033)
                    ·
                      refine ⟨2324184944787998931108775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3098913259717331908145033 2324184944787998931108775)
                      ·
                        rfl

theorem cell23_4526334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_4526334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526334 prefixEnd_4526334 := by exact prefixLift 4526334
  have htrace : WordTrace (prefixWord ++ tailWord_4526334) baseStart_4526334 baseEnd_4526334 := by
    simpa [prefixWord, tailWord_4526334, baseEnd_4526334] using wordTrace_append hprefix tailTrace_4526334
  have hstable : (prefixWord ++ tailWord_4526334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526334).length < 2 ^ (prefixWord ++ tailWord_4526334).sum := by decide
  have hdescent : baseEnd_4526334 < baseStart_4526334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526344 : List Nat := [2, 1, 3, 2, 3, 1, 4, 1, 1, 5]
def baseStart_4526344 : Nat := 118140960795 + 4526344 * 2 ^ 59
def prefixEnd_4526344 : Nat := 4983230072969 + 3 ^ 40 * 4526344 * 2
def baseEnd_4526344 : Nat := 774730026531514630661243

theorem tailTrace_4526344 : CollatzResearch.WordTrace tailWord_4526344 prefixEnd_4526344 774730026531514630661243 := by
  unfold tailWord_4526344
  simp only [CollatzResearch.WordTrace]
  refine ⟨82544664156918100427805043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110059552209224133903740057 82544664156918100427805043)
  ·
    refine ⟨123816996235377150641707565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82544664156918100427805043 123816996235377150641707565)
    ·
      refine ⟨46431373588266431490640337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123816996235377150641707565 46431373588266431490640337)
      ·
        refine ⟨34823530191199823617980253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46431373588266431490640337 34823530191199823617980253)
        ·
          refine ⟨13058823821699933856742595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34823530191199823617980253 13058823821699933856742595)
          ·
            refine ⟨19588235732549900785113893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13058823821699933856742595 19588235732549900785113893)
            ·
              refine ⟨3672794199853106397208855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19588235732549900785113893 3672794199853106397208855)
              ·
                refine ⟨5509191299779659595813283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3672794199853106397208855 5509191299779659595813283)
                ·
                  refine ⟨8263786949669489393719925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5509191299779659595813283 8263786949669489393719925)
                  ·
                    refine ⟨774730026531514630661243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8263786949669489393719925 774730026531514630661243)
                    ·
                      rfl

theorem cell23_4526344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_4526344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526344 prefixEnd_4526344 := by exact prefixLift 4526344
  have htrace : WordTrace (prefixWord ++ tailWord_4526344) baseStart_4526344 baseEnd_4526344 := by
    simpa [prefixWord, tailWord_4526344, baseEnd_4526344] using wordTrace_append hprefix tailTrace_4526344
  have hstable : (prefixWord ++ tailWord_4526344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526344).length < 2 ^ (prefixWord ++ tailWord_4526344).sum := by decide
  have hdescent : baseEnd_4526344 < baseStart_4526344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526347 : List Nat := [1, 1, 1, 1, 5, 2, 3, 3, 1, 1, 4]
def baseStart_4526347 : Nat := 118140960795 + 4526347 * 2 ^ 59
def prefixEnd_4526347 : Nat := 4983230072969 + 3 ^ 40 * 4526347 * 2
def baseEnd_4526347 : Nat := 2324191620036507380246215

theorem tailTrace_4526347 : CollatzResearch.WordTrace tailWord_4526347 prefixEnd_4526347 2324191620036507380246215 := by
  unfold tailWord_4526347
  simp only [CollatzResearch.WordTrace]
  refine ⟨165089437732825332367969295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110059625155216888245312863 165089437732825332367969295)
  ·
    refine ⟨247634156599237998551953943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165089437732825332367969295 247634156599237998551953943)
    ·
      refine ⟨371451234898856997827930915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247634156599237998551953943 371451234898856997827930915)
      ·
        refine ⟨557176852348285496741896373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371451234898856997827930915 557176852348285496741896373)
        ·
          refine ⟨52235329907651765319552785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 557176852348285496741896373 52235329907651765319552785)
          ·
            refine ⟨39176497430738823989664589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52235329907651765319552785 39176497430738823989664589)
            ·
              refine ⟨14691186536527058996124221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39176497430738823989664589 14691186536527058996124221)
              ·
                refine ⟨5509194951197647123546583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14691186536527058996124221 5509194951197647123546583)
                ·
                  refine ⟨8263792426796470685319875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5509194951197647123546583 8263792426796470685319875)
                  ·
                    refine ⟨12395688640194706027979813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8263792426796470685319875 12395688640194706027979813)
                    ·
                      refine ⟨2324191620036507380246215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12395688640194706027979813 2324191620036507380246215)
                      ·
                        rfl

theorem cell23_4526347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 1, 4].length) (baseStart_4526347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526347 prefixEnd_4526347 := by exact prefixLift 4526347
  have htrace : WordTrace (prefixWord ++ tailWord_4526347) baseStart_4526347 baseEnd_4526347 := by
    simpa [prefixWord, tailWord_4526347, baseEnd_4526347] using wordTrace_append hprefix tailTrace_4526347
  have hstable : (prefixWord ++ tailWord_4526347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526347).length < 2 ^ (prefixWord ++ tailWord_4526347).sum := by decide
  have hdescent : baseEnd_4526347 < baseStart_4526347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526360 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 1, 1, 6]
def baseStart_4526360 : Nat := 118140960795 + 4526360 * 2 ^ 59
def prefixEnd_4526360 : Nat := 4983230072969 + 3 ^ 40 * 4526360 * 2
def baseEnd_4526360 : Nat := 2324198295285015829383655

theorem tailTrace_4526360 : CollatzResearch.WordTrace tailWord_4526360 prefixEnd_4526360 2324198295285015829383655 := by
  unfold tailWord_4526360
  simp only [CollatzResearch.WordTrace]
  refine ⟨82544955940889117794096267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110059941254518823725461689 82544955940889117794096267)
  ·
    refine ⟨123817433911333676691144401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82544955940889117794096267 123817433911333676691144401)
    ·
      refine ⟨92863075433500257518358301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123817433911333676691144401 92863075433500257518358301)
      ·
        refine ⟨34823653287562596569384363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92863075433500257518358301 34823653287562596569384363)
        ·
          refine ⟨52235479931343894854076545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34823653287562596569384363 52235479931343894854076545)
          ·
            refine ⟨39176609948507921140557409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52235479931343894854076545 39176609948507921140557409)
            ·
              refine ⟨29382457461380940855418057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39176609948507921140557409 29382457461380940855418057)
              ·
                refine ⟨22036843096035705641563543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29382457461380940855418057 22036843096035705641563543)
                ·
                  refine ⟨33055264644053558462345315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22036843096035705641563543 33055264644053558462345315)
                  ·
                    refine ⟨49582896966080337693517973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33055264644053558462345315 49582896966080337693517973)
                    ·
                      refine ⟨2324198295285015829383655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49582896966080337693517973 2324198295285015829383655)
                      ·
                        rfl

theorem cell23_4526360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_4526360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526360 prefixEnd_4526360 := by exact prefixLift 4526360
  have htrace : WordTrace (prefixWord ++ tailWord_4526360) baseStart_4526360 baseEnd_4526360 := by
    simpa [prefixWord, tailWord_4526360, baseEnd_4526360] using wordTrace_append hprefix tailTrace_4526360
  have hstable : (prefixWord ++ tailWord_4526360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526360).length < 2 ^ (prefixWord ++ tailWord_4526360).sum := by decide
  have hdescent : baseEnd_4526360 < baseStart_4526360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526367 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 5]
def baseStart_4526367 : Nat := 118140960795 + 4526367 * 2 ^ 59
def prefixEnd_4526367 : Nat := 4983230072969 + 3 ^ 40 * 4526367 * 2
def baseEnd_4526367 : Nat := 2324201889649597301996123

theorem tailTrace_4526367 : CollatzResearch.WordTrace tailWord_4526367 prefixEnd_4526367 2324201889649597301996123 := by
  unfold tailWord_4526367
  simp only [CollatzResearch.WordTrace]
  refine ⟨165090167192752875783697355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110060111461835250522464903 165090167192752875783697355)
  ·
    refine ⟨247635250789129313675546033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165090167192752875783697355 247635250789129313675546033)
    ·
      refine ⟨185726438091846985256659525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247635250789129313675546033 185726438091846985256659525)
      ·
        refine ⟨34823707142221309735623661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185726438091846985256659525 34823707142221309735623661)
        ·
          refine ⟨13058890178332991150858873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34823707142221309735623661 13058890178332991150858873)
          ·
            refine ⟨9794167633749743363144155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13058890178332991150858873 9794167633749743363144155)
            ·
              refine ⟨14691251450624615044716233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9794167633749743363144155 14691251450624615044716233)
              ·
                refine ⟨11018438587968461283537175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14691251450624615044716233 11018438587968461283537175)
                ·
                  refine ⟨16527657881952691925305763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11018438587968461283537175 16527657881952691925305763)
                  ·
                    refine ⟨24791486822929037887958645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16527657881952691925305763 24791486822929037887958645)
                    ·
                      refine ⟨2324201889649597301996123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24791486822929037887958645 2324201889649597301996123)
                      ·
                        rfl

theorem cell23_4526367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_4526367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526367 prefixEnd_4526367 := by exact prefixLift 4526367
  have htrace : WordTrace (prefixWord ++ tailWord_4526367) baseStart_4526367 baseEnd_4526367 := by
    simpa [prefixWord, tailWord_4526367, baseEnd_4526367] using wordTrace_append hprefix tailTrace_4526367
  have hstable : (prefixWord ++ tailWord_4526367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526367).length < 2 ^ (prefixWord ++ tailWord_4526367).sum := by decide
  have hdescent : baseEnd_4526367 < baseStart_4526367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526404 : List Nat := [2, 3, 4, 1, 2, 2, 9]
def baseStart_4526404 : Nat := 118140960795 + 4526404 * 2 ^ 59
def prefixEnd_4526404 : Nat := 4983230072969 + 3 ^ 40 * 4526404 * 2
def baseEnd_4526404 : Nat := 28694085042392761200413

theorem tailTrace_4526404 : CollatzResearch.WordTrace tailWord_4526404 prefixEnd_4526404 28694085042392761200413 := by
  unfold tailWord_4526404
  simp only [CollatzResearch.WordTrace]
  refine ⟨82545758346809415551397133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110061011129079220735196177 82545758346809415551397133)
  ·
    refine ⟨30954659380053530831773925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82545758346809415551397133 30954659380053530831773925)
    ·
      refine ⟨5803998633760037030957611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30954659380053530831773925 5803998633760037030957611)
      ·
        refine ⟨8705997950640055546436417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5803998633760037030957611 8705997950640055546436417)
        ·
          refine ⟨6529498462980041659827313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8705997950640055546436417 6529498462980041659827313)
          ·
            refine ⟨4897123847235031244870485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6529498462980041659827313 4897123847235031244870485)
            ·
              refine ⟨28694085042392761200413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4897123847235031244870485 28694085042392761200413)
              ·
                rfl

theorem cell23_4526404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 9].length) (baseStart_4526404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526404 prefixEnd_4526404 := by exact prefixLift 4526404
  have htrace : WordTrace (prefixWord ++ tailWord_4526404) baseStart_4526404 baseEnd_4526404 := by
    simpa [prefixWord, tailWord_4526404, baseEnd_4526404] using wordTrace_append hprefix tailTrace_4526404
  have hstable : (prefixWord ++ tailWord_4526404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526404).length < 2 ^ (prefixWord ++ tailWord_4526404).sum := by decide
  have hdescent : baseEnd_4526404 < baseStart_4526404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526431 : List Nat := [1, 1, 2, 3, 1, 2, 6, 1, 2, 1, 3]
def baseStart_4526431 : Nat := 118140960795 + 4526431 * 2 ^ 59
def prefixEnd_4526431 : Nat := 4983230072969 + 3 ^ 40 * 4526431 * 2
def baseEnd_4526431 : Nat := 2324234752411485051595829

theorem tailTrace_4526431 : CollatzResearch.WordTrace tailWord_4526431 prefixEnd_4526431 2324234752411485051595829 := by
  unfold tailWord_4526431
  simp only [CollatzResearch.WordTrace]
  refine ⟨165092501464521014714027147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110061667643014009809351431 165092501464521014714027147)
  ·
    refine ⟨247638752196781522071040721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165092501464521014714027147 247638752196781522071040721)
    ·
      refine ⟨185729064147586141553280541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247638752196781522071040721 185729064147586141553280541)
      ·
        refine ⟨69648399055344803082480203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185729064147586141553280541 69648399055344803082480203)
        ·
          refine ⟨104472598583017204623720305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69648399055344803082480203 104472598583017204623720305)
          ·
            refine ⟨78354448937262903467790229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104472598583017204623720305 78354448937262903467790229)
            ·
              refine ⟨3672864793934198600052667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78354448937262903467790229 3672864793934198600052667)
              ·
                refine ⟨5509297190901297900079001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3672864793934198600052667 5509297190901297900079001)
                ·
                  refine ⟨4131972893175973425059251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5509297190901297900079001 4131972893175973425059251)
                  ·
                    refine ⟨6197959339763960137588877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4131972893175973425059251 6197959339763960137588877)
                    ·
                      refine ⟨2324234752411485051595829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6197959339763960137588877 2324234752411485051595829)
                      ·
                        rfl

theorem cell23_4526431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_4526431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526431 prefixEnd_4526431 := by exact prefixLift 4526431
  have htrace : WordTrace (prefixWord ++ tailWord_4526431) baseStart_4526431 baseEnd_4526431 := by
    simpa [prefixWord, tailWord_4526431, baseEnd_4526431] using wordTrace_append hprefix tailTrace_4526431
  have hstable : (prefixWord ++ tailWord_4526431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526431).length < 2 ^ (prefixWord ++ tailWord_4526431).sum := by decide
  have hdescent : baseEnd_4526431 < baseStart_4526431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526460 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 11]
def baseStart_4526460 : Nat := 118140960795 + 4526460 * 2 ^ 59
def prefixEnd_4526460 : Nat := 4983230072969 + 3 ^ 40 * 4526460 * 2
def baseEnd_4526460 : Nat := 258249960372273937570355

theorem tailTrace_4526460 : CollatzResearch.WordTrace tailWord_4526460 prefixEnd_4526460 258249960372273937570355 := by
  unfold tailWord_4526460
  simp only [CollatzResearch.WordTrace]
  refine ⟨82546779590707976333416417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110062372787610635111221889 82546779590707976333416417)
  ·
    refine ⟨61910084693030982250062313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82546779590707976333416417 61910084693030982250062313)
    ·
      refine ⟨46432563519773236687546735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61910084693030982250062313 46432563519773236687546735)
      ·
        refine ⟨69648845279659855031320103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46432563519773236687546735 69648845279659855031320103)
        ·
          refine ⟨104473267919489782546980155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69648845279659855031320103 104473267919489782546980155)
          ·
            refine ⟨156709901879234673820470233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104473267919489782546980155 156709901879234673820470233)
            ·
              refine ⟨117532426409426005365352675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156709901879234673820470233 117532426409426005365352675)
              ·
                refine ⟨176298639614139008048029013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117532426409426005365352675 176298639614139008048029013)
                ·
                  refine ⟨258249960372273937570355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 176298639614139008048029013 258249960372273937570355)
                  ·
                    rfl

theorem cell23_4526460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 11].length) (baseStart_4526460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526460 prefixEnd_4526460 := by exact prefixLift 4526460
  have htrace : WordTrace (prefixWord ++ tailWord_4526460) baseStart_4526460 baseEnd_4526460 := by
    simpa [prefixWord, tailWord_4526460, baseEnd_4526460] using wordTrace_append hprefix tailTrace_4526460
  have hstable : (prefixWord ++ tailWord_4526460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526460).length < 2 ^ (prefixWord ++ tailWord_4526460).sum := by decide
  have hdescent : baseEnd_4526460 < baseStart_4526460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526466 : List Nat := [3, 4, 2, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_4526466 : Nat := 118140960795 + 4526466 * 2 ^ 59
def prefixEnd_4526466 : Nat := 4983230072969 + 3 ^ 40 * 4526466 * 2
def baseEnd_4526466 : Nat := 2324252724234392414658169

theorem tailTrace_4526466 : CollatzResearch.WordTrace tailWord_4526466 prefixEnd_4526466 2324252724234392414658169 := by
  unfold tailWord_4526466
  simp only [CollatzResearch.WordTrace]
  refine ⟨41273444504848553922887813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110062518679596143794367501 41273444504848553922887813)
  ·
    refine ⟨7738770844659103860541465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41273444504848553922887813 7738770844659103860541465)
    ·
      refine ⟨5804078133494327895406099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7738770844659103860541465 5804078133494327895406099)
      ·
        refine ⟨8706117200241491843109149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5804078133494327895406099 8706117200241491843109149)
        ·
          refine ⟨3264793950090559441165931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8706117200241491843109149 3264793950090559441165931)
          ·
            refine ⟨4897190925135839161748897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264793950090559441165931 4897190925135839161748897)
            ·
              refine ⟨3672893193851879371311673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4897190925135839161748897 3672893193851879371311673)
              ·
                refine ⟨2754669895388909528483755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3672893193851879371311673 2754669895388909528483755)
                ·
                  refine ⟨4132004843083364292725633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2754669895388909528483755 4132004843083364292725633)
                  ·
                    refine ⟨3099003632312523219544225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4132004843083364292725633 3099003632312523219544225)
                    ·
                      refine ⟨2324252724234392414658169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3099003632312523219544225 2324252724234392414658169)
                      ·
                        rfl

theorem cell23_4526466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_4526466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526466 prefixEnd_4526466 := by exact prefixLift 4526466
  have htrace : WordTrace (prefixWord ++ tailWord_4526466) baseStart_4526466 baseEnd_4526466 := by
    simpa [prefixWord, tailWord_4526466, baseEnd_4526466] using wordTrace_append hprefix tailTrace_4526466
  have hstable : (prefixWord ++ tailWord_4526466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526466).length < 2 ^ (prefixWord ++ tailWord_4526466).sum := by decide
  have hdescent : baseEnd_4526466 < baseStart_4526466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526487 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 3]
def baseStart_4526487 : Nat := 118140960795 + 4526487 * 2 ^ 59
def prefixEnd_4526487 : Nat := 4983230072969 + 3 ^ 40 * 4526487 * 2
def baseEnd_4526487 : Nat := 2324263507328136832495571

theorem tailTrace_4526487 : CollatzResearch.WordTrace tailWord_4526487 prefixEnd_4526487 2324263507328136832495571 := by
  unfold tailWord_4526487
  simp only [CollatzResearch.WordTrace]
  refine ⟨165094543952318136278065715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110063029301545424185377143 165094543952318136278065715)
  ·
    refine ⟨247641815928477204417098573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165094543952318136278065715 247641815928477204417098573)
    ·
      refine ⟨92865680973178951656411965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247641815928477204417098573 92865680973178951656411965)
      ·
        refine ⟨34824630364942106871154487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92865680973178951656411965 34824630364942106871154487)
        ·
          refine ⟨52236945547413160306731731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34824630364942106871154487 52236945547413160306731731)
          ·
            refine ⟨78355418321119740460097597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52236945547413160306731731 78355418321119740460097597)
            ·
              refine ⟨29383281870419902672536599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78355418321119740460097597 29383281870419902672536599)
              ·
                refine ⟨44074922805629854008804899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29383281870419902672536599 44074922805629854008804899)
                ·
                  refine ⟨66112384208444781013207349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44074922805629854008804899 66112384208444781013207349)
                  ·
                    refine ⟨6198036019541698219988189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66112384208444781013207349 6198036019541698219988189)
                    ·
                      refine ⟨2324263507328136832495571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6198036019541698219988189 2324263507328136832495571)
                      ·
                        rfl

theorem cell23_4526487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_4526487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526487 prefixEnd_4526487 := by exact prefixLift 4526487
  have htrace : WordTrace (prefixWord ++ tailWord_4526487) baseStart_4526487 baseEnd_4526487 := by
    simpa [prefixWord, tailWord_4526487, baseEnd_4526487] using wordTrace_append hprefix tailTrace_4526487
  have hstable : (prefixWord ++ tailWord_4526487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526487).length < 2 ^ (prefixWord ++ tailWord_4526487).sum := by decide
  have hdescent : baseEnd_4526487 < baseStart_4526487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526488 : List Nat := [2, 1, 2, 5, 1, 1, 2, 3, 2, 2, 2]
def baseStart_4526488 : Nat := 118140960795 + 4526488 * 2 ^ 59
def prefixEnd_4526488 : Nat := 4983230072969 + 3 ^ 40 * 4526488 * 2
def baseEnd_4526488 : Nat := 2324264020808791328583067

theorem tailTrace_4526488 : CollatzResearch.WordTrace tailWord_4526488 prefixEnd_4526488 2324264020808791328583067 := by
  unfold tailWord_4526488
  simp only [CollatzResearch.WordTrace]
  refine ⟨82547290212657256724426059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110063053616876342299234745 82547290212657256724426059)
  ·
    refine ⟨123820935318985885086639089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82547290212657256724426059 123820935318985885086639089)
    ·
      refine ⟨92865701489239413814979317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123820935318985885086639089 92865701489239413814979317)
      ·
        refine ⟨8706159514616195045154311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92865701489239413814979317 8706159514616195045154311)
        ·
          refine ⟨13059239271924292567731467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8706159514616195045154311 13059239271924292567731467)
          ·
            refine ⟨19588858907886438851597201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13059239271924292567731467 19588858907886438851597201)
            ·
              refine ⟨14691644180914829138697901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19588858907886438851597201 14691644180914829138697901)
              ·
                refine ⟨5509366567843060927011713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14691644180914829138697901 5509366567843060927011713)
                ·
                  refine ⟨4132024925882295695258785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5509366567843060927011713 4132024925882295695258785)
                  ·
                    refine ⟨3099018694411721771444089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4132024925882295695258785 3099018694411721771444089)
                    ·
                      refine ⟨2324264020808791328583067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3099018694411721771444089 2324264020808791328583067)
                      ·
                        rfl

theorem cell23_4526488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_4526488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526488 prefixEnd_4526488 := by exact prefixLift 4526488
  have htrace : WordTrace (prefixWord ++ tailWord_4526488) baseStart_4526488 baseEnd_4526488 := by
    simpa [prefixWord, tailWord_4526488, baseEnd_4526488] using wordTrace_append hprefix tailTrace_4526488
  have hstable : (prefixWord ++ tailWord_4526488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526488).length < 2 ^ (prefixWord ++ tailWord_4526488).sum := by decide
  have hdescent : baseEnd_4526488 < baseStart_4526488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526494 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 9]
def baseStart_4526494 : Nat := 118140960795 + 4526494 * 2 ^ 59
def prefixEnd_4526494 : Nat := 4983230072969 + 3 ^ 40 * 4526494 * 2
def baseEnd_4526494 : Nat := 258251900188079811678671

theorem tailTrace_4526494 : CollatzResearch.WordTrace tailWord_4526494 prefixEnd_4526494 258251900188079811678671 := by
  unfold tailWord_4526494
  simp only [CollatzResearch.WordTrace]
  refine ⟨20636849907911597059196317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110063199508861850982380357 20636849907911597059196317)
  ·
    refine ⟨7738818715466848897198619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20636849907911597059196317 7738818715466848897198619)
    ·
      refine ⟨11608228073200273345797929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7738818715466848897198619 11608228073200273345797929)
      ·
        refine ⟨8706171054900205009348447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11608228073200273345797929 8706171054900205009348447)
        ·
          refine ⟨13059256582350307514022671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8706171054900205009348447 13059256582350307514022671)
          ·
            refine ⟨19588884873525461271034007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13059256582350307514022671 19588884873525461271034007)
            ·
              refine ⟨29383327310288191906551011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19588884873525461271034007 29383327310288191906551011)
              ·
                refine ⟨44074990965432287859826517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29383327310288191906551011 44074990965432287859826517)
                ·
                  refine ⟨258251900188079811678671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44074990965432287859826517 258251900188079811678671)
                  ·
                    rfl

theorem cell23_4526494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_4526494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526494 prefixEnd_4526494 := by exact prefixLift 4526494
  have htrace : WordTrace (prefixWord ++ tailWord_4526494) baseStart_4526494 baseEnd_4526494 := by
    simpa [prefixWord, tailWord_4526494, baseEnd_4526494] using wordTrace_append hprefix tailTrace_4526494
  have hstable : (prefixWord ++ tailWord_4526494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526494).length < 2 ^ (prefixWord ++ tailWord_4526494).sum := by decide
  have hdescent : baseEnd_4526494 < baseStart_4526494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526554 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 3, 4]
def baseStart_4526554 : Nat := 118140960795 + 4526554 * 2 ^ 59
def prefixEnd_4526554 : Nat := 4983230072969 + 3 ^ 40 * 4526554 * 2
def baseEnd_4526554 : Nat := 774765970177329356785921

theorem tailTrace_4526554 : CollatzResearch.WordTrace tailWord_4526554 prefixEnd_4526554 774765970177329356785921 := by
  unfold tailWord_4526554
  simp only [CollatzResearch.WordTrace]
  refine ⟨41274246910768851680188679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110064658428716937813836477 41274246910768851680188679)
  ·
    refine ⟨61911370366153277520283019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41274246910768851680188679 61911370366153277520283019)
    ·
      refine ⟨92867055549229916280424529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61911370366153277520283019 92867055549229916280424529)
      ·
        refine ⟨69650291661922437210318397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92867055549229916280424529 69650291661922437210318397)
        ·
          refine ⟨26118859373220913953869399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69650291661922437210318397 26118859373220913953869399)
          ·
            refine ⟨39178289059831370930804099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26118859373220913953869399 39178289059831370930804099)
            ·
              refine ⟨58767433589747056396206149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39178289059831370930804099 58767433589747056396206149)
              ·
                refine ⟨11018893798077573074288653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58767433589747056396206149 11018893798077573074288653)
                ·
                  refine ⟨4132085174279089902858245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11018893798077573074288653 4132085174279089902858245)
                  ·
                    refine ⟨774765970177329356785921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4132085174279089902858245 774765970177329356785921)
                    ·
                      rfl

theorem cell23_4526554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_4526554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526554 prefixEnd_4526554 := by exact prefixLift 4526554
  have htrace : WordTrace (prefixWord ++ tailWord_4526554) baseStart_4526554 baseEnd_4526554 := by
    simpa [prefixWord, tailWord_4526554, baseEnd_4526554] using wordTrace_append hprefix tailTrace_4526554
  have hstable : (prefixWord ++ tailWord_4526554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526554).length < 2 ^ (prefixWord ++ tailWord_4526554).sum := by decide
  have hdescent : baseEnd_4526554 < baseStart_4526554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526562 : List Nat := [3, 3, 3, 2, 2, 1, 1, 3, 5]
def baseStart_4526562 : Nat := 118140960795 + 4526562 * 2 ^ 59
def prefixEnd_4526562 : Nat := 4983230072969 + 3 ^ 40 * 4526562 * 2
def baseEnd_4526562 : Nat := 258255779819691559895303

theorem tailTrace_4526562 : CollatzResearch.WordTrace tailWord_4526562 prefixEnd_4526562 258255779819691559895303 := by
  unfold tailWord_4526562
  simp only [CollatzResearch.WordTrace]
  refine ⟨41274319856761606021761485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110064852951364282724697293 41274319856761606021761485)
  ·
    refine ⟨15477869946285602258160557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41274319856761606021761485 15477869946285602258160557)
    ·
      refine ⟨5804201229857100846810209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15477869946285602258160557 5804201229857100846810209)
      ·
        refine ⟨4353150922392825635107657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5804201229857100846810209 4353150922392825635107657)
        ·
          refine ⟨3264863191794619226330743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4353150922392825635107657 3264863191794619226330743)
          ·
            refine ⟨4897294787691928839496115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264863191794619226330743 4897294787691928839496115)
            ·
              refine ⟨7345942181537893259244173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4897294787691928839496115 7345942181537893259244173)
              ·
                refine ⟨2754728318076709972216565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7345942181537893259244173 2754728318076709972216565)
                ·
                  refine ⟨258255779819691559895303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2754728318076709972216565 258255779819691559895303)
                  ·
                    rfl

theorem cell23_4526562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_4526562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526562 prefixEnd_4526562 := by exact prefixLift 4526562
  have htrace : WordTrace (prefixWord ++ tailWord_4526562) baseStart_4526562 baseEnd_4526562 := by
    simpa [prefixWord, tailWord_4526562, baseEnd_4526562] using wordTrace_append hprefix tailTrace_4526562
  have hstable : (prefixWord ++ tailWord_4526562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526562).length < 2 ^ (prefixWord ++ tailWord_4526562).sum := by decide
  have hdescent : baseEnd_4526562 < baseStart_4526562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526567 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 10]
def baseStart_4526567 : Nat := 118140960795 + 4526567 * 2 ^ 59
def prefixEnd_4526567 : Nat := 4983230072969 + 3 ^ 40 * 4526567 * 2
def baseEnd_4526567 : Nat := 258256065086721835499467

theorem tailTrace_4526567 : CollatzResearch.WordTrace tailWord_4526567 prefixEnd_4526567 258256065086721835499467 := by
  unfold tailWord_4526567
  simp only [CollatzResearch.WordTrace]
  refine ⟨165097461792028309940977955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110064974528018873293985303 165097461792028309940977955)
  ·
    refine ⟨247646192688042464911466933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165097461792028309940977955 247646192688042464911466933)
    ·
      refine ⟨23216830564503981085450025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 247646192688042464911466933 23216830564503981085450025)
      ·
        refine ⟨17412622923377985814087519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23216830564503981085450025 17412622923377985814087519)
        ·
          refine ⟨26118934385066978721131279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17412622923377985814087519 26118934385066978721131279)
          ·
            refine ⟨39178401577600468081696919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26118934385066978721131279 39178401577600468081696919)
            ·
              refine ⟨58767602366400702122545379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39178401577600468081696919 58767602366400702122545379)
              ·
                refine ⟨88151403549601053183818069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58767602366400702122545379 88151403549601053183818069)
                ·
                  refine ⟨258256065086721835499467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 88151403549601053183818069 258256065086721835499467)
                  ·
                    rfl

theorem cell23_4526567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 10].length) (baseStart_4526567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526567 prefixEnd_4526567 := by exact prefixLift 4526567
  have htrace : WordTrace (prefixWord ++ tailWord_4526567) baseStart_4526567 baseEnd_4526567 := by
    simpa [prefixWord, tailWord_4526567, baseEnd_4526567] using wordTrace_append hprefix tailTrace_4526567
  have hstable : (prefixWord ++ tailWord_4526567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526567).length < 2 ^ (prefixWord ++ tailWord_4526567).sum := by decide
  have hdescent : baseEnd_4526567 < baseStart_4526567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526617 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 2, 5, 4]
def baseStart_4526617 : Nat := 118140960795 + 4526617 * 2 ^ 59
def prefixEnd_4526617 : Nat := 4983230072969 + 3 ^ 40 * 4526617 * 2
def baseEnd_4526617 : Nat := 2324330259813221323869973

theorem tailTrace_4526617 : CollatzResearch.WordTrace tailWord_4526617 prefixEnd_4526617 2324330259813221323869973 := by
  unfold tailWord_4526617
  simp only [CollatzResearch.WordTrace]
  refine ⟨165099285441847168480298105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110066190294564778986865403 165099285441847168480298105)
  ·
    refine ⟨123824464081385376360223579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165099285441847168480298105 123824464081385376360223579)
    ·
      refine ⟨185736696122078064540335369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123824464081385376360223579 185736696122078064540335369)
      ·
        refine ⟨139302522091558548405251527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185736696122078064540335369 139302522091558548405251527)
        ·
          refine ⟨208953783137337822607877291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139302522091558548405251527 208953783137337822607877291)
          ·
            refine ⟨313430674706006733911815937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208953783137337822607877291 313430674706006733911815937)
            ·
              refine ⟨235073006029505050433861953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313430674706006733911815937 235073006029505050433861953)
              ·
                refine ⟨176304754522128787825396465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235073006029505050433861953 176304754522128787825396465)
                ·
                  refine ⟨132228565891596590869047349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176304754522128787825396465 132228565891596590869047349)
                  ·
                    refine ⟨12396428052337180393973189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 132228565891596590869047349 12396428052337180393973189)
                    ·
                      refine ⟨2324330259813221323869973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12396428052337180393973189 2324330259813221323869973)
                      ·
                        rfl

theorem cell23_4526617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_4526617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526617 prefixEnd_4526617 := by exact prefixLift 4526617
  have htrace : WordTrace (prefixWord ++ tailWord_4526617) baseStart_4526617 baseEnd_4526617 := by
    simpa [prefixWord, tailWord_4526617, baseEnd_4526617] using wordTrace_append hprefix tailTrace_4526617
  have hstable : (prefixWord ++ tailWord_4526617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526617).length < 2 ^ (prefixWord ++ tailWord_4526617).sum := by decide
  have hdescent : baseEnd_4526617 < baseStart_4526617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526661 : List Nat := [1, 3, 1, 1, 1, 5, 2, 3, 2, 4]
def baseStart_4526661 : Nat := 118140960795 + 4526661 * 2 ^ 59
def prefixEnd_4526661 : Nat := 4983230072969 + 3 ^ 40 * 4526661 * 2
def baseEnd_4526661 : Nat := 774784284320673050573257

theorem tailTrace_4526661 : CollatzResearch.WordTrace tailWord_4526661 prefixEnd_4526661 774784284320673050573257 := by
  unfold tailWord_4526661
  simp only [CollatzResearch.WordTrace]
  refine ⟨165100890253687763994899837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110067260169125175996599891 165100890253687763994899837)
  ·
    refine ⟨61912833845132911498087439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165100890253687763994899837 61912833845132911498087439)
    ·
      refine ⟨92869250767699367247131159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61912833845132911498087439 92869250767699367247131159)
      ·
        refine ⟨139303876151549050870696739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92869250767699367247131159 139303876151549050870696739)
        ·
          refine ⟨208955814227323576306045109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139303876151549050870696739 208955814227323576306045109)
          ·
            refine ⟨19589607583811585278691729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 208955814227323576306045109 19589607583811585278691729)
            ·
              refine ⟨14692205687858688959018797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19589607583811585278691729 14692205687858688959018797)
              ·
                refine ⟨5509577132947008359632049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14692205687858688959018797 5509577132947008359632049)
                ·
                  refine ⟨4132182849710256269724037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5509577132947008359632049 4132182849710256269724037)
                  ·
                    refine ⟨774784284320673050573257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4132182849710256269724037 774784284320673050573257)
                    ·
                      rfl

theorem cell23_4526661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_4526661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526661 prefixEnd_4526661 := by exact prefixLift 4526661
  have htrace : WordTrace (prefixWord ++ tailWord_4526661) baseStart_4526661 baseEnd_4526661 := by
    simpa [prefixWord, tailWord_4526661, baseEnd_4526661] using wordTrace_append hprefix tailTrace_4526661
  have hstable : (prefixWord ++ tailWord_4526661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526661).length < 2 ^ (prefixWord ++ tailWord_4526661).sum := by decide
  have hdescent : baseEnd_4526661 < baseStart_4526661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526668 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 3, 2, 2]
def baseStart_4526668 : Nat := 118140960795 + 4526668 * 2 ^ 59
def prefixEnd_4526668 : Nat := 4983230072969 + 3 ^ 40 * 4526668 * 2
def baseEnd_4526668 : Nat := 2324356447326600624332239

theorem tailTrace_4526668 : CollatzResearch.WordTrace tailWord_4526668 prefixEnd_4526668 2324356447326600624332239 := by
  unfold tailWord_4526668
  simp only [CollatzResearch.WordTrace]
  refine ⟨82550572782331202095202329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110067430376441602793603105 82550572782331202095202329)
  ·
    refine ⟨61912929586748401571401747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82550572782331202095202329 61912929586748401571401747)
    ·
      refine ⟨92869394380122602357102621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61912929586748401571401747 92869394380122602357102621)
      ·
        refine ⟨34826022892545975883913483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92869394380122602357102621 34826022892545975883913483)
        ·
          refine ⟨52239034338818963825870225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34826022892545975883913483 52239034338818963825870225)
          ·
            refine ⟨39179275754114222869402669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52239034338818963825870225 39179275754114222869402669)
            ·
              refine ⟨14692228407792833576026001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39179275754114222869402669 14692228407792833576026001)
              ·
                refine ⟨11019171305844625182019501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14692228407792833576026001 11019171305844625182019501)
                ·
                  refine ⟨4132189239691734443257313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11019171305844625182019501 4132189239691734443257313)
                  ·
                    refine ⟨3099141929768800832442985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4132189239691734443257313 3099141929768800832442985)
                    ·
                      refine ⟨2324356447326600624332239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3099141929768800832442985 2324356447326600624332239)
                      ·
                        rfl

theorem cell23_4526668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_4526668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526668 prefixEnd_4526668 := by exact prefixLift 4526668
  have htrace : WordTrace (prefixWord ++ tailWord_4526668) baseStart_4526668 baseEnd_4526668 := by
    simpa [prefixWord, tailWord_4526668, baseEnd_4526668] using wordTrace_append hprefix tailTrace_4526668
  have hstable : (prefixWord ++ tailWord_4526668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526668).length < 2 ^ (prefixWord ++ tailWord_4526668).sum := by decide
  have hdescent : baseEnd_4526668 < baseStart_4526668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526688 : List Nat := [2, 1, 1, 3, 2, 1, 6, 1, 1, 2, 3]
def baseStart_4526688 : Nat := 118140960795 + 4526688 * 2 ^ 59
def prefixEnd_4526688 : Nat := 4983230072969 + 3 ^ 40 * 4526688 * 2
def baseEnd_4526688 : Nat := 2324366716939690546082147

theorem tailTrace_4526688 : CollatzResearch.WordTrace tailWord_4526688 prefixEnd_4526688 2324366716939690546082147 := by
  unfold tailWord_4526688
  simp only [CollatzResearch.WordTrace]
  refine ⟨82550937512294973803066359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110067916683059965070755145 82550937512294973803066359)
  ·
    refine ⟨123826406268442460704599539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82550937512294973803066359 123826406268442460704599539)
    ·
      refine ⟨185739609402663691056899309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123826406268442460704599539 185739609402663691056899309)
      ·
        refine ⟨69652353525998884146337241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185739609402663691056899309 69652353525998884146337241)
        ·
          refine ⟨52239265144499163109752931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69652353525998884146337241 52239265144499163109752931)
          ·
            refine ⟨78358897716748744664629397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52239265144499163109752931 78358897716748744664629397)
            ·
              refine ⟨3673073330472597406154503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78358897716748744664629397 3673073330472597406154503)
              ·
                refine ⟨5509609995708896109231755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3673073330472597406154503 5509609995708896109231755)
                ·
                  refine ⟨8264414993563344163847633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5509609995708896109231755 8264414993563344163847633)
                  ·
                    refine ⟨6198311245172508122885725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8264414993563344163847633 6198311245172508122885725)
                    ·
                      refine ⟨2324366716939690546082147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6198311245172508122885725 2324366716939690546082147)
                      ·
                        rfl

theorem cell23_4526688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_4526688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526688 prefixEnd_4526688 := by exact prefixLift 4526688
  have htrace : WordTrace (prefixWord ++ tailWord_4526688) baseStart_4526688 baseEnd_4526688 := by
    simpa [prefixWord, tailWord_4526688, baseEnd_4526688] using wordTrace_append hprefix tailTrace_4526688
  have hstable : (prefixWord ++ tailWord_4526688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526688).length < 2 ^ (prefixWord ++ tailWord_4526688).sum := by decide
  have hdescent : baseEnd_4526688 < baseStart_4526688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526702 : List Nat := [4, 1, 2, 2, 2, 1, 2, 4, 1, 2, 2]
def baseStart_4526702 : Nat := 118140960795 + 4526702 * 2 ^ 59
def prefixEnd_4526702 : Nat := 4983230072969 + 3 ^ 40 * 4526702 * 2
def baseEnd_4526702 : Nat := 2324373905668853491307083

theorem tailTrace_4526702 : CollatzResearch.WordTrace tailWord_4526702 prefixEnd_4526702 2324373905668853491307083 := by
  unfold tailWord_4526702
  simp only [CollatzResearch.WordTrace]
  refine ⟨20637798205817403499642795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110068257097692818664761573 20637798205817403499642795)
  ·
    refine ⟨30956697308726105249464193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20637798205817403499642795 30956697308726105249464193)
    ·
      refine ⟨23217522981544578937098145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30956697308726105249464193 23217522981544578937098145)
      ·
        refine ⟨17413142236158434202823609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23217522981544578937098145 17413142236158434202823609)
        ·
          refine ⟨13059856677118825652117707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17413142236158434202823609 13059856677118825652117707)
          ·
            refine ⟨19589785015678238478176561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13059856677118825652117707 19589785015678238478176561)
            ·
              refine ⟨14692338761758678858632421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19589785015678238478176561 14692338761758678858632421)
              ·
                refine ⟨2754813517829752285993579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14692338761758678858632421 2754813517829752285993579)
                ·
                  refine ⟨4132220276744628428990369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2754813517829752285993579 4132220276744628428990369)
                  ·
                    refine ⟨3099165207558471321742777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4132220276744628428990369 3099165207558471321742777)
                    ·
                      refine ⟨2324373905668853491307083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3099165207558471321742777 2324373905668853491307083)
                      ·
                        rfl

theorem cell23_4526702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_4526702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526702 prefixEnd_4526702 := by exact prefixLift 4526702
  have htrace : WordTrace (prefixWord ++ tailWord_4526702) baseStart_4526702 baseEnd_4526702 := by
    simpa [prefixWord, tailWord_4526702, baseEnd_4526702] using wordTrace_append hprefix tailTrace_4526702
  have hstable : (prefixWord ++ tailWord_4526702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526702).length < 2 ^ (prefixWord ++ tailWord_4526702).sum := by decide
  have hdescent : baseEnd_4526702 < baseStart_4526702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526711 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 5, 3, 2]
def baseStart_4526711 : Nat := 118140960795 + 4526711 * 2 ^ 59
def prefixEnd_4526711 : Nat := 4983230072969 + 3 ^ 40 * 4526711 * 2
def baseEnd_4526711 : Nat := 2324378526994743956094541

theorem tailTrace_4526711 : CollatzResearch.WordTrace tailWord_4526711 prefixEnd_4526711 2324378526994743956094541 := by
  unfold tailWord_4526711
  simp only [CollatzResearch.WordTrace]
  refine ⟨165102713903506622534219987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110068475935671081689479991 165102713903506622534219987)
  ·
    refine ⟨247654070855259933801329981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165102713903506622534219987 247654070855259933801329981)
    ·
      refine ⟨92870276570722475175498743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247654070855259933801329981 92870276570722475175498743)
      ·
        refine ⟨139305414856083712763248115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92870276570722475175498743 139305414856083712763248115)
        ·
          refine ⟨208958122284125569144872173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139305414856083712763248115 208958122284125569144872173)
          ·
            refine ⟨78359295856547088429327065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208958122284125569144872173 78359295856547088429327065)
            ·
              refine ⟨58769471892410316321995299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78359295856547088429327065 58769471892410316321995299)
              ·
                refine ⟨88154207838615474482992949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58769471892410316321995299 88154207838615474482992949)
                ·
                  refine ⟨8264456984870200732780589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88154207838615474482992949 8264456984870200732780589)
                  ·
                    refine ⟨3099171369326325274792721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8264456984870200732780589 3099171369326325274792721)
                    ·
                      refine ⟨2324378526994743956094541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3099171369326325274792721 2324378526994743956094541)
                      ·
                        rfl

theorem cell23_4526711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 3, 2].length) (baseStart_4526711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526711 prefixEnd_4526711 := by exact prefixLift 4526711
  have htrace : WordTrace (prefixWord ++ tailWord_4526711) baseStart_4526711 baseEnd_4526711 := by
    simpa [prefixWord, tailWord_4526711, baseEnd_4526711] using wordTrace_append hprefix tailTrace_4526711
  have hstable : (prefixWord ++ tailWord_4526711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526711).length < 2 ^ (prefixWord ++ tailWord_4526711).sum := by decide
  have hdescent : baseEnd_4526711 < baseStart_4526711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526769 : List Nat := [1, 2, 2, 6, 1, 2, 2, 1, 2, 1, 3]
def baseStart_4526769 : Nat := 118140960795 + 4526769 * 2 ^ 59
def prefixEnd_4526769 : Nat := 4983230072969 + 3 ^ 40 * 4526769 * 2
def baseEnd_4526769 : Nat := 2324408308872704729169275

theorem tailTrace_4526769 : CollatzResearch.WordTrace tailWord_4526769 prefixEnd_4526769 2324408308872704729169275 := by
  unfold tailWord_4526769
  simp only [CollatzResearch.WordTrace]
  refine ⟨165104829337296498439831361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110069886224864332293220907 165104829337296498439831361)
  ·
    refine ⟨123828622002972373829873521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165104829337296498439831361 123828622002972373829873521)
    ·
      refine ⟨92871466502229280372405141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123828622002972373829873521 92871466502229280372405141)
      ·
        refine ⟨4353349992291997517456491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 92871466502229280372405141 4353349992291997517456491)
        ·
          refine ⟨6530024988437996276184737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4353349992291997517456491 6530024988437996276184737)
          ·
            refine ⟨4897518741328497207138553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6530024988437996276184737 4897518741328497207138553)
            ·
              refine ⟨3673139055996372905353915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4897518741328497207138553 3673139055996372905353915)
              ·
                refine ⟨5509708583994559358030873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3673139055996372905353915 5509708583994559358030873)
                ·
                  refine ⟨4132281437995919518523155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5509708583994559358030873 4132281437995919518523155)
                  ·
                    refine ⟨6198422156993879277784733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4132281437995919518523155 6198422156993879277784733)
                    ·
                      refine ⟨2324408308872704729169275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6198422156993879277784733 2324408308872704729169275)
                      ·
                        rfl

theorem cell23_4526769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_4526769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526769 prefixEnd_4526769 := by exact prefixLift 4526769
  have htrace : WordTrace (prefixWord ++ tailWord_4526769) baseStart_4526769 baseEnd_4526769 := by
    simpa [prefixWord, tailWord_4526769, baseEnd_4526769] using wordTrace_append hprefix tailTrace_4526769
  have hstable : (prefixWord ++ tailWord_4526769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526769).length < 2 ^ (prefixWord ++ tailWord_4526769).sum := by decide
  have hdescent : baseEnd_4526769 < baseStart_4526769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526815 : List Nat := [1, 1, 2, 3, 2, 5, 2, 2, 5]
def baseStart_4526815 : Nat := 118140960795 + 4526815 * 2 ^ 59
def prefixEnd_4526815 : Nat := 4983230072969 + 3 ^ 40 * 4526815 * 2
def baseEnd_4526815 : Nat := 258270214331423505466007

theorem tailTrace_4526815 : CollatzResearch.WordTrace tailWord_4526815 prefixEnd_4526815 258270214331423505466007 := by
  unfold tailWord_4526815
  simp only [CollatzResearch.WordTrace]
  refine ⟨165106507095129848296005899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110071004730086565530670599 165106507095129848296005899)
  ·
    refine ⟨247659760642694772444008849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165106507095129848296005899 247659760642694772444008849)
    ·
      refine ⟨185744820482021079333006637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247659760642694772444008849 185744820482021079333006637)
      ·
        refine ⟨69654307680757904749877489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185744820482021079333006637 69654307680757904749877489)
        ·
          refine ⟨52240730760568428562408117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69654307680757904749877489 52240730760568428562408117)
          ·
            refine ⟨4897568508803290177725761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52240730760568428562408117 4897568508803290177725761)
            ·
              refine ⟨3673176381602467633294321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4897568508803290177725761 3673176381602467633294321)
              ·
                refine ⟨2754882286201850724970741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3673176381602467633294321 2754882286201850724970741)
                ·
                  refine ⟨258270214331423505466007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2754882286201850724970741 258270214331423505466007)
                  ·
                    rfl

theorem cell23_4526815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 5].length) (baseStart_4526815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526815 prefixEnd_4526815 := by exact prefixLift 4526815
  have htrace : WordTrace (prefixWord ++ tailWord_4526815) baseStart_4526815 baseEnd_4526815 := by
    simpa [prefixWord, tailWord_4526815, baseEnd_4526815] using wordTrace_append hprefix tailTrace_4526815
  have hstable : (prefixWord ++ tailWord_4526815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526815).length < 2 ^ (prefixWord ++ tailWord_4526815).sum := by decide
  have hdescent : baseEnd_4526815 < baseStart_4526815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526821 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 1, 2, 5]
def baseStart_4526821 : Nat := 118140960795 + 4526821 * 2 ^ 59
def prefixEnd_4526821 : Nat := 4983230072969 + 3 ^ 40 * 4526821 * 2
def baseEnd_4526821 : Nat := 2324435009866738525719035

theorem tailTrace_4526821 : CollatzResearch.WordTrace tailWord_4526821 prefixEnd_4526821 2324435009866738525719035 := by
  unfold tailWord_4526821
  simp only [CollatzResearch.WordTrace]
  refine ⟨165106725933108111320724317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110071150622072074213816211 165106725933108111320724317)
  ·
    refine ⟨61915022224915541745271619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165106725933108111320724317 61915022224915541745271619)
    ·
      refine ⟨92872533337373312617907429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61915022224915541745271619 92872533337373312617907429)
      ·
        refine ⟨17413600000757496115857643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92872533337373312617907429 17413600000757496115857643)
        ·
          refine ⟨26120400001136244173786465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17413600000757496115857643 26120400001136244173786465)
          ·
            refine ⟨19590300000852183130339849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26120400001136244173786465 19590300000852183130339849)
            ·
              refine ⟨14692725000639137347754887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19590300000852183130339849 14692725000639137347754887)
              ·
                refine ⟨22039087500958706021632331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14692725000639137347754887 22039087500958706021632331)
                ·
                  refine ⟨33058631251438059032448497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22039087500958706021632331 33058631251438059032448497)
                  ·
                    refine ⟨24793973438578544274336373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33058631251438059032448497 24793973438578544274336373)
                    ·
                      refine ⟨2324435009866738525719035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24793973438578544274336373 2324435009866738525719035)
                      ·
                        rfl

theorem cell23_4526821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_4526821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526821 prefixEnd_4526821 := by exact prefixLift 4526821
  have htrace : WordTrace (prefixWord ++ tailWord_4526821) baseStart_4526821 baseEnd_4526821 := by
    simpa [prefixWord, tailWord_4526821, baseEnd_4526821] using wordTrace_append hprefix tailTrace_4526821
  have hstable : (prefixWord ++ tailWord_4526821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526821).length < 2 ^ (prefixWord ++ tailWord_4526821).sum := by decide
  have hdescent : baseEnd_4526821 < baseStart_4526821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526864 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 7]
def baseStart_4526864 : Nat := 118140960795 + 4526864 * 2 ^ 59
def prefixEnd_4526864 : Nat := 4983230072969 + 3 ^ 40 * 4526864 * 2
def baseEnd_4526864 : Nat := 2324457089534881857481337

theorem tailTrace_4526864 : CollatzResearch.WordTrace tailWord_4526864 prefixEnd_4526864 2324457089534881857481337 := by
  unfold tailWord_4526864
  simp only [CollatzResearch.WordTrace]
  refine ⟨82554147135976164832269823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110072196181301553109693097 82554147135976164832269823)
  ·
    refine ⟨123831220703964247248404735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82554147135976164832269823 123831220703964247248404735)
    ·
      refine ⟨185746831055946370872607103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123831220703964247248404735 185746831055946370872607103)
      ·
        refine ⟨278620246583919556308910655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185746831055946370872607103 278620246583919556308910655)
        ·
          refine ⟨417930369875879334463365983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278620246583919556308910655 417930369875879334463365983)
          ·
            refine ⟨626895554813819001695048975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417930369875879334463365983 626895554813819001695048975)
            ·
              refine ⟨940343332220728502542573463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626895554813819001695048975 940343332220728502542573463)
              ·
                refine ⟨1410514998331092753813860195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940343332220728502542573463 1410514998331092753813860195)
                ·
                  refine ⟨2115772497496639130720790293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1410514998331092753813860195 2115772497496639130720790293)
                  ·
                    refine ⟨99176835820154959252537045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2115772497496639130720790293 99176835820154959252537045)
                    ·
                      refine ⟨2324457089534881857481337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99176835820154959252537045 2324457089534881857481337)
                      ·
                        rfl

theorem cell23_4526864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_4526864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526864 prefixEnd_4526864 := by exact prefixLift 4526864
  have htrace : WordTrace (prefixWord ++ tailWord_4526864) baseStart_4526864 baseEnd_4526864 := by
    simpa [prefixWord, tailWord_4526864, baseEnd_4526864] using wordTrace_append hprefix tailTrace_4526864
  have hstable : (prefixWord ++ tailWord_4526864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526864).length < 2 ^ (prefixWord ++ tailWord_4526864).sum := by decide
  have hdescent : baseEnd_4526864 < baseStart_4526864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526909 : List Nat := [1, 4, 1, 4, 2, 2, 1, 3, 1, 4]
def baseStart_4526909 : Nat := 118140960795 + 4526909 * 2 ^ 59
def prefixEnd_4526909 : Nat := 4983230072969 + 3 ^ 40 * 4526909 * 2
def baseEnd_4526909 : Nat := 774826732054778060472877

theorem tailTrace_4526909 : CollatzResearch.WordTrace tailWord_4526909 prefixEnd_4526909 774826732054778060472877 := by
  unfold tailWord_4526909
  simp only [CollatzResearch.WordTrace]
  refine ⟨165109935556789302349927781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110073290371192868233285187 165109935556789302349927781)
  ·
    refine ⟨30958112916897994190611459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165109935556789302349927781 30958112916897994190611459)
    ·
      refine ⟨46437169375346991285917189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30958112916897994190611459 46437169375346991285917189)
      ·
        refine ⟨8706969257877560866109473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46437169375346991285917189 8706969257877560866109473)
        ·
          refine ⟨6530226943408170649582105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8706969257877560866109473 6530226943408170649582105)
          ·
            refine ⟨4897670207556127987186579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6530226943408170649582105 4897670207556127987186579)
            ·
              refine ⟨7346505311334191980779869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4897670207556127987186579 7346505311334191980779869)
              ·
                refine ⟨2754939491750321992792451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7346505311334191980779869 2754939491750321992792451)
                ·
                  refine ⟨4132409237625482989188677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2754939491750321992792451 4132409237625482989188677)
                  ·
                    refine ⟨774826732054778060472877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4132409237625482989188677 774826732054778060472877)
                    ·
                      rfl

theorem cell23_4526909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_4526909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526909 prefixEnd_4526909 := by exact prefixLift 4526909
  have htrace : WordTrace (prefixWord ++ tailWord_4526909) baseStart_4526909 baseEnd_4526909 := by
    simpa [prefixWord, tailWord_4526909, baseEnd_4526909] using wordTrace_append hprefix tailTrace_4526909
  have hstable : (prefixWord ++ tailWord_4526909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526909).length < 2 ^ (prefixWord ++ tailWord_4526909).sum := by decide
  have hdescent : baseEnd_4526909 < baseStart_4526909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526955 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 3, 2, 2]
def baseStart_4526955 : Nat := 118140960795 + 4526955 * 2 ^ 59
def prefixEnd_4526955 : Nat := 4983230072969 + 3 ^ 40 * 4526955 * 2
def baseEnd_4526955 : Nat := 2324503816274441001443419

theorem tailTrace_4526955 : CollatzResearch.WordTrace tailWord_4526955 prefixEnd_4526955 2324503816274441001443419 := by
  unfold tailWord_4526955
  simp only [CollatzResearch.WordTrace]
  refine ⟨165111613314622652206102319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110074408876415101470734879 165111613314622652206102319)
  ·
    refine ⟨247667419971933978309153479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165111613314622652206102319 247667419971933978309153479)
    ·
      refine ⟨371501129957900967463730219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247667419971933978309153479 371501129957900967463730219)
      ·
        refine ⟨557251694936851451195595329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371501129957900967463730219 557251694936851451195595329)
        ·
          refine ⟨417938771202638588396696497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557251694936851451195595329 417938771202638588396696497)
          ·
            refine ⟨313454078401978941297522373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417938771202638588396696497 313454078401978941297522373)
            ·
              refine ⟨58772639700371051493285445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 313454078401978941297522373 58772639700371051493285445)
              ·
                refine ⟨11019869943819572154991021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58772639700371051493285445 11019869943819572154991021)
                ·
                  refine ⟨4132451228932339558121633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11019869943819572154991021 4132451228932339558121633)
                  ·
                    refine ⟨3099338421699254668591225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4132451228932339558121633 3099338421699254668591225)
                    ·
                      refine ⟨2324503816274441001443419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3099338421699254668591225 2324503816274441001443419)
                      ·
                        rfl

theorem cell23_4526955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 2, 2].length) (baseStart_4526955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526955 prefixEnd_4526955 := by exact prefixLift 4526955
  have htrace : WordTrace (prefixWord ++ tailWord_4526955) baseStart_4526955 baseEnd_4526955 := by
    simpa [prefixWord, tailWord_4526955, baseEnd_4526955] using wordTrace_append hprefix tailTrace_4526955
  have hstable : (prefixWord ++ tailWord_4526955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526955).length < 2 ^ (prefixWord ++ tailWord_4526955).sum := by decide
  have hdescent : baseEnd_4526955 < baseStart_4526955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4526961 : List Nat := [1, 2, 2, 2, 1, 4, 2, 9]
def baseStart_4526961 : Nat := 118140960795 + 4526961 * 2 ^ 59
def prefixEnd_4526961 : Nat := 4983230072969 + 3 ^ 40 * 4526961 * 2
def baseEnd_4526961 : Nat := 86092848042902517702533

theorem tailTrace_4526961 : CollatzResearch.WordTrace tailWord_4526961 prefixEnd_4526961 86092848042902517702533 := by
  unfold tailWord_4526961
  simp only [CollatzResearch.WordTrace]
  refine ⟨165111832152600915230820737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110074554768400610153880491 165111832152600915230820737)
  ·
    refine ⟨123833874114450686423115553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165111832152600915230820737 123833874114450686423115553)
    ·
      refine ⟨92875405585838014817336665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123833874114450686423115553 92875405585838014817336665)
      ·
        refine ⟨69656554189378511113002499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92875405585838014817336665 69656554189378511113002499)
        ·
          refine ⟨104484831284067766669503749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69656554189378511113002499 104484831284067766669503749)
          ·
            refine ⟨19590905865762706250531953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104484831284067766669503749 19590905865762706250531953)
            ·
              refine ⟨14693179399322029687898965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19590905865762706250531953 14693179399322029687898965)
              ·
                refine ⟨86092848042902517702533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14693179399322029687898965 86092848042902517702533)
                ·
                  rfl

theorem cell23_4526961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 9].length) (baseStart_4526961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4526961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4526961 prefixEnd_4526961 := by exact prefixLift 4526961
  have htrace : WordTrace (prefixWord ++ tailWord_4526961) baseStart_4526961 baseEnd_4526961 := by
    simpa [prefixWord, tailWord_4526961, baseEnd_4526961] using wordTrace_append hprefix tailTrace_4526961
  have hstable : (prefixWord ++ tailWord_4526961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4526961).length < 2 ^ (prefixWord ++ tailWord_4526961).sum := by decide
  have hdescent : baseEnd_4526961 < baseStart_4526961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4526961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527001 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 1, 4, 5]
def baseStart_4527001 : Nat := 118140960795 + 4527001 * 2 ^ 59
def prefixEnd_4527001 : Nat := 4983230072969 + 3 ^ 40 * 4527001 * 2
def baseEnd_4527001 : Nat := 2324527436384547821468207

theorem tailTrace_4527001 : CollatzResearch.WordTrace tailWord_4527001 prefixEnd_4527001 2324527436384547821468207 := by
  unfold tailWord_4527001
  simp only [CollatzResearch.WordTrace]
  refine ⟨165113291072456002062276857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110075527381637334708184571 165113291072456002062276857)
  ·
    refine ⟨123834968304342001546707643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165113291072456002062276857 123834968304342001546707643)
    ·
      refine ⟨185752452456513002320061465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123834968304342001546707643 185752452456513002320061465)
      ·
        refine ⟨139314339342384751740046099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185752452456513002320061465 139314339342384751740046099)
        ·
          refine ⟨208971509013577127610069149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139314339342384751740046099 208971509013577127610069149)
          ·
            refine ⟨78364315880091422853775931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208971509013577127610069149 78364315880091422853775931)
            ·
              refine ⟨117546473820137134280663897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78364315880091422853775931 117546473820137134280663897)
              ·
                refine ⟨88159855365102850710497923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117546473820137134280663897 88159855365102850710497923)
                ·
                  refine ⟨132239783047654276065746885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88159855365102850710497923 132239783047654276065746885)
                  ·
                    refine ⟨24794959321435176762327541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 132239783047654276065746885 24794959321435176762327541)
                    ·
                      refine ⟨2324527436384547821468207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24794959321435176762327541 2324527436384547821468207)
                      ·
                        rfl

theorem cell23_4527001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_4527001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527001 prefixEnd_4527001 := by exact prefixLift 4527001
  have htrace : WordTrace (prefixWord ++ tailWord_4527001) baseStart_4527001 baseEnd_4527001 := by
    simpa [prefixWord, tailWord_4527001, baseEnd_4527001] using wordTrace_append hprefix tailTrace_4527001
  have hstable : (prefixWord ++ tailWord_4527001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527001).length < 2 ^ (prefixWord ++ tailWord_4527001).sum := by decide
  have hdescent : baseEnd_4527001 < baseStart_4527001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527005 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_4527005 : Nat := 118140960795 + 4527005 * 2 ^ 59
def prefixEnd_4527005 : Nat := 4983230072969 + 3 ^ 40 * 4527005 * 2
def baseEnd_4527005 : Nat := 2324529490307165805818189

theorem tailTrace_4527005 : CollatzResearch.WordTrace tailWord_4527005 prefixEnd_4527005 2324529490307165805818189 := by
  unfold tailWord_4527005
  simp only [CollatzResearch.WordTrace]
  refine ⟨165113436964441510745422469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110075624642961007163614979 165113436964441510745422469)
  ·
    refine ⟨30958769430832783264766713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165113436964441510745422469 30958769430832783264766713)
    ·
      refine ⟨23219077073124587448575035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30958769430832783264766713 23219077073124587448575035)
      ·
        refine ⟨34828615609686881172862553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23219077073124587448575035 34828615609686881172862553)
        ·
          refine ⟨26121461707265160879646915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34828615609686881172862553 26121461707265160879646915)
          ·
            refine ⟨39182192560897741319470373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26121461707265160879646915 39182192560897741319470373)
            ·
              refine ⟨7346661105168326497400695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39182192560897741319470373 7346661105168326497400695)
              ·
                refine ⟨11019991657752489746101043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7346661105168326497400695 11019991657752489746101043)
                ·
                  refine ⟨16529987486628734619151565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11019991657752489746101043 16529987486628734619151565)
                  ·
                    refine ⟨6198745307485775482181837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16529987486628734619151565 6198745307485775482181837)
                    ·
                      refine ⟨2324529490307165805818189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6198745307485775482181837 2324529490307165805818189)
                      ·
                        rfl

theorem cell23_4527005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_4527005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527005 prefixEnd_4527005 := by exact prefixLift 4527005
  have htrace : WordTrace (prefixWord ++ tailWord_4527005) baseStart_4527005 baseEnd_4527005 := by
    simpa [prefixWord, tailWord_4527005, baseEnd_4527005] using wordTrace_append hprefix tailTrace_4527005
  have hstable : (prefixWord ++ tailWord_4527005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527005).length < 2 ^ (prefixWord ++ tailWord_4527005).sum := by decide
  have hdescent : baseEnd_4527005 < baseStart_4527005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527032 : List Nat := [2, 1, 2, 1, 2, 5, 1, 3, 1, 3, 2]
def baseStart_4527032 : Nat := 118140960795 + 4527032 * 2 ^ 59
def prefixEnd_4527032 : Nat := 4983230072969 + 3 ^ 40 * 4527032 * 2
def baseEnd_4527032 : Nat := 2324543354284837200180565

theorem tailTrace_4527032 : CollatzResearch.WordTrace tailWord_4527032 prefixEnd_4527032 2324543354284837200180565 := by
  unfold tailWord_4527032
  simp only [CollatzResearch.WordTrace]
  refine ⟨82557210867671847178327675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110076281156895796237770233 82557210867671847178327675)
  ·
    refine ⟨123835816301507770767491513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82557210867671847178327675 123835816301507770767491513)
    ·
      refine ⟨92876862226130828075618635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123835816301507770767491513 92876862226130828075618635)
      ·
        refine ⟨139315293339196242113427953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92876862226130828075618635 139315293339196242113427953)
        ·
          refine ⟨104486470004397181585070965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139315293339196242113427953 104486470004397181585070965)
          ·
            refine ⟨9795606562912235773600403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104486470004397181585070965 9795606562912235773600403)
            ·
              refine ⟨14693409844368353660400605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9795606562912235773600403 14693409844368353660400605)
              ·
                refine ⟨5510028691638132622650227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14693409844368353660400605 5510028691638132622650227)
                ·
                  refine ⟨8265043037457198933975341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5510028691638132622650227 8265043037457198933975341)
                  ·
                    refine ⟨3099391139046449600240753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8265043037457198933975341 3099391139046449600240753)
                    ·
                      refine ⟨2324543354284837200180565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3099391139046449600240753 2324543354284837200180565)
                      ·
                        rfl

theorem cell23_4527032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 1, 3, 2].length) (baseStart_4527032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527032 prefixEnd_4527032 := by exact prefixLift 4527032
  have htrace : WordTrace (prefixWord ++ tailWord_4527032) baseStart_4527032 baseEnd_4527032 := by
    simpa [prefixWord, tailWord_4527032, baseEnd_4527032] using wordTrace_append hprefix tailTrace_4527032
  have hstable : (prefixWord ++ tailWord_4527032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527032).length < 2 ^ (prefixWord ++ tailWord_4527032).sum := by decide
  have hdescent : baseEnd_4527032 < baseStart_4527032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527038 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_4527038 : Nat := 118140960795 + 4527038 * 2 ^ 59
def prefixEnd_4527038 : Nat := 4983230072969 + 3 ^ 40 * 4527038 * 2
def baseEnd_4527038 : Nat := 774848811722921392235179

theorem tailTrace_4527038 : CollatzResearch.WordTrace tailWord_4527038 prefixEnd_4527038 774848811722921392235179 := by
  unfold tailWord_4527038
  simp only [CollatzResearch.WordTrace]
  refine ⟨20639330071665244672671721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110076427048881304920915845 20639330071665244672671721)
  ·
    refine ⟨15479497553748933504503791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20639330071665244672671721 15479497553748933504503791)
    ·
      refine ⟨23219246330623400256755687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15479497553748933504503791 23219246330623400256755687)
      ·
        refine ⟨34828869495935100385133531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23219246330623400256755687 34828869495935100385133531)
        ·
          refine ⟨52243304243902650577700297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34828869495935100385133531 52243304243902650577700297)
          ·
            refine ⟨39182478182926987933275223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52243304243902650577700297 39182478182926987933275223)
            ·
              refine ⟨58773717274390481899912835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39182478182926987933275223 58773717274390481899912835)
              ·
                refine ⟨88160575911585722849869253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58773717274390481899912835 88160575911585722849869253)
                ·
                  refine ⟨16530107983422323034350485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88160575911585722849869253 16530107983422323034350485)
                  ·
                    refine ⟨774848811722921392235179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16530107983422323034350485 774848811722921392235179)
                    ·
                      rfl

theorem cell23_4527038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_4527038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527038 prefixEnd_4527038 := by exact prefixLift 4527038
  have htrace : WordTrace (prefixWord ++ tailWord_4527038) baseStart_4527038 baseEnd_4527038 := by
    simpa [prefixWord, tailWord_4527038, baseEnd_4527038] using wordTrace_append hprefix tailTrace_4527038
  have hstable : (prefixWord ++ tailWord_4527038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527038).length < 2 ^ (prefixWord ++ tailWord_4527038).sum := by decide
  have hdescent : baseEnd_4527038 < baseStart_4527038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527053 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_4527053 : Nat := 118140960795 + 4527053 * 2 ^ 59
def prefixEnd_4527053 : Nat := 4983230072969 + 3 ^ 40 * 4527053 * 2
def baseEnd_4527053 : Nat := 2324554137378581618017969

theorem tailTrace_4527053 : CollatzResearch.WordTrace tailWord_4527053 prefixEnd_4527053 2324554137378581618017969 := by
  unfold tailWord_4527053
  simp only [CollatzResearch.WordTrace]
  refine ⟨165115187668267614943169813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110076791778845076628779875 165115187668267614943169813)
  ·
    refine ⟨7739774421950044450461085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 165115187668267614943169813 7739774421950044450461085)
    ·
      refine ⟨2902415408231266668922907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7739774421950044450461085 2902415408231266668922907)
      ·
        refine ⟨4353623112346900003384361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2902415408231266668922907 4353623112346900003384361)
        ·
          refine ⟨3265217334260175002538271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4353623112346900003384361 3265217334260175002538271)
          ·
            refine ⟨4897826001390262503807407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3265217334260175002538271 4897826001390262503807407)
            ·
              refine ⟨7346739002085393755711111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4897826001390262503807407 7346739002085393755711111)
              ·
                refine ⟨11020108503128090633566667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7346739002085393755711111 11020108503128090633566667)
                ·
                  refine ⟨16530162754692135950350001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11020108503128090633566667 16530162754692135950350001)
                  ·
                    refine ⟨12397622066019101962762501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16530162754692135950350001 12397622066019101962762501)
                    ·
                      refine ⟨2324554137378581618017969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12397622066019101962762501 2324554137378581618017969)
                      ·
                        rfl

theorem cell23_4527053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_4527053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527053 prefixEnd_4527053 := by exact prefixLift 4527053
  have htrace : WordTrace (prefixWord ++ tailWord_4527053) baseStart_4527053 baseEnd_4527053 := by
    simpa [prefixWord, tailWord_4527053, baseEnd_4527053] using wordTrace_append hprefix tailTrace_4527053
  have hstable : (prefixWord ++ tailWord_4527053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527053).length < 2 ^ (prefixWord ++ tailWord_4527053).sum := by decide
  have hdescent : baseEnd_4527053 < baseStart_4527053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527132 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 2, 5]
def baseStart_4527132 : Nat := 118140960795 + 4527132 * 2 ^ 59
def prefixEnd_4527132 : Nat := 4983230072969 + 3 ^ 40 * 4527132 * 2
def baseEnd_4527132 : Nat := 774864900783428936310035

theorem tailTrace_4527132 : CollatzResearch.WordTrace tailWord_4527132 prefixEnd_4527132 774864900783428936310035 := by
  unfold tailWord_4527132
  simp only [CollatzResearch.WordTrace]
  refine ⟨82559034517490705717647825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110078712689987607623530433 82559034517490705717647825)
  ·
    refine ⟨61919275888118029288235869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82559034517490705717647825 61919275888118029288235869)
    ·
      refine ⟨23219728458044260983088451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61919275888118029288235869 23219728458044260983088451)
      ·
        refine ⟨34829592687066391474632677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23219728458044260983088451 34829592687066391474632677)
        ·
          refine ⟨6530548628824948401493627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34829592687066391474632677 6530548628824948401493627)
          ·
            refine ⟨9795822943237422602240441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6530548628824948401493627 9795822943237422602240441)
            ·
              refine ⟨7346867207428066951680331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9795822943237422602240441 7346867207428066951680331)
              ·
                refine ⟨11020300811142100427520497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7346867207428066951680331 11020300811142100427520497)
                ·
                  refine ⟨8265225608356575320640373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11020300811142100427520497 8265225608356575320640373)
                  ·
                    refine ⟨774864900783428936310035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8265225608356575320640373 774864900783428936310035)
                    ·
                      rfl

theorem cell23_4527132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_4527132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527132 prefixEnd_4527132 := by exact prefixLift 4527132
  have htrace : WordTrace (prefixWord ++ tailWord_4527132) baseStart_4527132 baseEnd_4527132 := by
    simpa [prefixWord, tailWord_4527132, baseEnd_4527132] using wordTrace_append hprefix tailTrace_4527132
  have hstable : (prefixWord ++ tailWord_4527132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527132).length < 2 ^ (prefixWord ++ tailWord_4527132).sum := by decide
  have hdescent : baseEnd_4527132 < baseStart_4527132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527135 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 4]
def baseStart_4527135 : Nat := 118140960795 + 4527135 * 2 ^ 59
def prefixEnd_4527135 : Nat := 4983230072969 + 3 ^ 40 * 4527135 * 2
def baseEnd_4527135 : Nat := 2324596242792250297192591

theorem tailTrace_4527135 : CollatzResearch.WordTrace tailWord_4527135 prefixEnd_4527135 2324596242792250297192591 := by
  unfold tailWord_4527135
  simp only [CollatzResearch.WordTrace]
  refine ⟨165118178453970542947654859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110078785635980361965103239 165118178453970542947654859)
  ·
    refine ⟨247677267680955814421482289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165118178453970542947654859 247677267680955814421482289)
    ·
      refine ⟨185757950760716860816111717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247677267680955814421482289 185757950760716860816111717)
      ·
        refine ⟨34829615767634411403020947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185757950760716860816111717 34829615767634411403020947)
        ·
          refine ⟨52244423651451617104531421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34829615767634411403020947 52244423651451617104531421)
          ·
            refine ⟨19591658869294356414199283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52244423651451617104531421 19591658869294356414199283)
            ·
              refine ⟨29387488303941534621298925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19591658869294356414199283 29387488303941534621298925)
              ·
                refine ⟨11020308113978075482987097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29387488303941534621298925 11020308113978075482987097)
                ·
                  refine ⟨8265231085483556612240323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11020308113978075482987097 8265231085483556612240323)
                  ·
                    refine ⟨12397846628225334918360485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8265231085483556612240323 12397846628225334918360485)
                    ·
                      refine ⟨2324596242792250297192591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12397846628225334918360485 2324596242792250297192591)
                      ·
                        rfl

theorem cell23_4527135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_4527135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527135 prefixEnd_4527135 := by exact prefixLift 4527135
  have htrace : WordTrace (prefixWord ++ tailWord_4527135) baseStart_4527135 baseEnd_4527135 := by
    simpa [prefixWord, tailWord_4527135, baseEnd_4527135] using wordTrace_append hprefix tailTrace_4527135
  have hstable : (prefixWord ++ tailWord_4527135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527135).length < 2 ^ (prefixWord ++ tailWord_4527135).sum := by decide
  have hdescent : baseEnd_4527135 < baseStart_4527135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527148 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 6]
def baseStart_4527148 : Nat := 118140960795 + 4527148 * 2 ^ 59
def prefixEnd_4527148 : Nat := 4983230072969 + 3 ^ 40 * 4527148 * 2
def baseEnd_4527148 : Nat := 2324602918040758746330031

theorem tailTrace_4527148 : CollatzResearch.WordTrace tailWord_4527148 prefixEnd_4527148 2324602918040758746330031 := by
  unfold tailWord_4527148
  simp only [CollatzResearch.WordTrace]
  refine ⟨82559326301461723083939049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110079101735282297445252065 82559326301461723083939049)
  ·
    refine ⟨61919494726096292312954287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82559326301461723083939049 61919494726096292312954287)
    ·
      refine ⟨92879242089144438469431431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61919494726096292312954287 92879242089144438469431431)
      ·
        refine ⟨139318863133716657704147147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92879242089144438469431431 139318863133716657704147147)
        ·
          refine ⟨208978294700574986556220721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139318863133716657704147147 208978294700574986556220721)
          ·
            refine ⟨156733721025431239917165541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208978294700574986556220721 156733721025431239917165541)
            ·
              refine ⟨29387572692268357484468539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156733721025431239917165541 29387572692268357484468539)
              ·
                refine ⟨44081359038402536226702809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29387572692268357484468539 44081359038402536226702809)
                ·
                  refine ⟨33061019278801902170027107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44081359038402536226702809 33061019278801902170027107)
                  ·
                    refine ⟨49591528918202853255040661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33061019278801902170027107 49591528918202853255040661)
                    ·
                      refine ⟨2324602918040758746330031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49591528918202853255040661 2324602918040758746330031)
                      ·
                        rfl

theorem cell23_4527148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_4527148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527148 prefixEnd_4527148 := by exact prefixLift 4527148
  have htrace : WordTrace (prefixWord ++ tailWord_4527148) baseStart_4527148 baseEnd_4527148 := by
    simpa [prefixWord, tailWord_4527148, baseEnd_4527148] using wordTrace_append hprefix tailTrace_4527148
  have hstable : (prefixWord ++ tailWord_4527148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527148).length < 2 ^ (prefixWord ++ tailWord_4527148).sum := by decide
  have hdescent : baseEnd_4527148 < baseStart_4527148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527169 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_4527169 : Nat := 118140960795 + 4527169 * 2 ^ 59
def prefixEnd_4527169 : Nat := 4983230072969 + 3 ^ 40 * 4527169 * 2
def baseEnd_4527169 : Nat := 2324613701134503164167435

theorem tailTrace_4527169 : CollatzResearch.WordTrace tailWord_4527169 prefixEnd_4527169 2324613701134503164167435 := by
  unfold tailWord_4527169
  simp only [CollatzResearch.WordTrace]
  refine ⟨165119418535847366754392561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110079612357231577836261707 165119418535847366754392561)
  ·
    refine ⟨123839563901885525065794421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165119418535847366754392561 123839563901885525065794421)
    ·
      refine ⟨11609959115801767974918227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123839563901885525065794421 11609959115801767974918227)
      ·
        refine ⟨17414938673702651962377341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11609959115801767974918227 17414938673702651962377341)
        ·
          refine ⟨6530602002638494485891503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17414938673702651962377341 6530602002638494485891503)
          ·
            refine ⟨9795903003957741728837255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6530602002638494485891503 9795903003957741728837255)
            ·
              refine ⟨14693854505936612593255883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9795903003957741728837255 14693854505936612593255883)
              ·
                refine ⟨22040781758904918889883825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14693854505936612593255883 22040781758904918889883825)
                ·
                  refine ⟨16530586319178689167412869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22040781758904918889883825 16530586319178689167412869)
                  ·
                    refine ⟨3099484934846004218889913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16530586319178689167412869 3099484934846004218889913)
                    ·
                      refine ⟨2324613701134503164167435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3099484934846004218889913 2324613701134503164167435)
                      ·
                        rfl

theorem cell23_4527169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_4527169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527169 prefixEnd_4527169 := by exact prefixLift 4527169
  have htrace : WordTrace (prefixWord ++ tailWord_4527169) baseStart_4527169 baseEnd_4527169 := by
    simpa [prefixWord, tailWord_4527169, baseEnd_4527169] using wordTrace_append hprefix tailTrace_4527169
  have hstable : (prefixWord ++ tailWord_4527169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527169).length < 2 ^ (prefixWord ++ tailWord_4527169).sum := by decide
  have hdescent : baseEnd_4527169 < baseStart_4527169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527175 : List Nat := [1, 1, 4, 1, 3, 2, 2, 3, 6]
def baseStart_4527175 : Nat := 118140960795 + 4527175 * 2 ^ 59
def prefixEnd_4527175 : Nat := 4983230072969 + 3 ^ 40 * 4527175 * 2
def baseEnd_4527175 : Nat := 258290753557603348965823

theorem tailTrace_4527175 : CollatzResearch.WordTrace tailWord_4527175 prefixEnd_4527175 258290753557603348965823 := by
  unfold tailWord_4527175
  simp only [CollatzResearch.WordTrace]
  refine ⟨165119637373825629779110979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110079758249217086519407319 165119637373825629779110979)
  ·
    refine ⟨247679456060738444668666469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165119637373825629779110979 247679456060738444668666469)
    ·
      refine ⟨46439898011388458375374963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 247679456060738444668666469 46439898011388458375374963)
      ·
        refine ⟨69659847017082687563062445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46439898011388458375374963 69659847017082687563062445)
        ·
          refine ⟨26122442631406007836148417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69659847017082687563062445 26122442631406007836148417)
          ·
            refine ⟨19591831973554505877111313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26122442631406007836148417 19591831973554505877111313)
            ·
              refine ⟨14693873980165879407833485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19591831973554505877111313 14693873980165879407833485)
              ·
                refine ⟨5510202742562204777937557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14693873980165879407833485 5510202742562204777937557)
                ·
                  refine ⟨258290753557603348965823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5510202742562204777937557 258290753557603348965823)
                  ·
                    rfl

theorem cell23_4527175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 6].length) (baseStart_4527175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527175 prefixEnd_4527175 := by exact prefixLift 4527175
  have htrace : WordTrace (prefixWord ++ tailWord_4527175) baseStart_4527175 baseEnd_4527175 := by
    simpa [prefixWord, tailWord_4527175, baseEnd_4527175] using wordTrace_append hprefix tailTrace_4527175
  have hstable : (prefixWord ++ tailWord_4527175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527175).length < 2 ^ (prefixWord ++ tailWord_4527175).sum := by decide
  have hdescent : baseEnd_4527175 < baseStart_4527175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527212 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 4, 3, 2]
def baseStart_4527212 : Nat := 118140960795 + 4527212 * 2 ^ 59
def prefixEnd_4527212 : Nat := 4983230072969 + 3 ^ 40 * 4527212 * 2
def baseEnd_4527212 : Nat := 2324635780802646495929737

theorem tailTrace_4527212 : CollatzResearch.WordTrace tailWord_4527212 prefixEnd_4527212 2324635780802646495929737 := by
  unfold tailWord_4527212
  simp only [CollatzResearch.WordTrace]
  refine ⟨82560493437345792549103945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110080657916461056732138593 82560493437345792549103945)
  ·
    refine ⟨61920370078009344411827959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82560493437345792549103945 61920370078009344411827959)
    ·
      refine ⟨92880555117014016617741939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61920370078009344411827959 92880555117014016617741939)
      ·
        refine ⟨139320832675521024926612909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92880555117014016617741939 139320832675521024926612909)
        ·
          refine ⟨52245312253320384347479841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139320832675521024926612909 52245312253320384347479841)
          ·
            refine ⟨39183984189990288260609881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52245312253320384347479841 39183984189990288260609881)
            ·
              refine ⟨29387988142492716195457411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39183984189990288260609881 29387988142492716195457411)
              ·
                refine ⟨44081982213739074293186117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29387988142492716195457411 44081982213739074293186117)
                ·
                  refine ⟨8265371665076076429972397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44081982213739074293186117 8265371665076076429972397)
                  ·
                    refine ⟨3099514374403528661239649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8265371665076076429972397 3099514374403528661239649)
                    ·
                      refine ⟨2324635780802646495929737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3099514374403528661239649 2324635780802646495929737)
                      ·
                        rfl

theorem cell23_4527212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 3, 2].length) (baseStart_4527212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527212 prefixEnd_4527212 := by exact prefixLift 4527212
  have htrace : WordTrace (prefixWord ++ tailWord_4527212) baseStart_4527212 baseEnd_4527212 := by
    simpa [prefixWord, tailWord_4527212, baseEnd_4527212] using wordTrace_append hprefix tailTrace_4527212
  have hstable : (prefixWord ++ tailWord_4527212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527212).length < 2 ^ (prefixWord ++ tailWord_4527212).sum := by decide
  have hdescent : baseEnd_4527212 < baseStart_4527212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527242 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 2, 6, 2]
def baseStart_4527242 : Nat := 118140960795 + 4527242 * 2 ^ 59
def prefixEnd_4527242 : Nat := 4983230072969 + 3 ^ 40 * 4527242 * 2
def baseEnd_4527242 : Nat := 2324651185222281378554599

theorem tailTrace_4527242 : CollatzResearch.WordTrace tailWord_4527242 prefixEnd_4527242 2324651185222281378554599 := by
  unfold tailWord_4527242
  simp only [CollatzResearch.WordTrace]
  refine ⟨41280520266145725055449995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110081387376388600147866653 41280520266145725055449995)
  ·
    refine ⟨61920780399218587583174993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41280520266145725055449995 61920780399218587583174993)
    ·
      refine ⟨46440585299413940687381245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61920780399218587583174993 46440585299413940687381245)
      ·
        refine ⟨17415219487280227757767967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46440585299413940687381245 17415219487280227757767967)
        ·
          refine ⟨26122829230920341636651951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17415219487280227757767967 26122829230920341636651951)
          ·
            refine ⟨39184243846380512454977927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26122829230920341636651951 39184243846380512454977927)
            ·
              refine ⟨58776365769570768682466891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39184243846380512454977927 58776365769570768682466891)
              ·
                refine ⟨88164548654356153023700337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58776365769570768682466891 88164548654356153023700337)
                ·
                  refine ⟨66123411490767114767775253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88164548654356153023700337 66123411490767114767775253)
                  ·
                    refine ⟨3099534913629708504739465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66123411490767114767775253 3099534913629708504739465)
                    ·
                      refine ⟨2324651185222281378554599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3099534913629708504739465 2324651185222281378554599)
                      ·
                        rfl

theorem cell23_4527242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_4527242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527242 prefixEnd_4527242 := by exact prefixLift 4527242
  have htrace : WordTrace (prefixWord ++ tailWord_4527242) baseStart_4527242 baseEnd_4527242 := by
    simpa [prefixWord, tailWord_4527242, baseEnd_4527242] using wordTrace_append hprefix tailTrace_4527242
  have hstable : (prefixWord ++ tailWord_4527242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527242).length < 2 ^ (prefixWord ++ tailWord_4527242).sum := by decide
  have hdescent : baseEnd_4527242 < baseStart_4527242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527296 : List Nat := [2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 3]
def baseStart_4527296 : Nat := 118140960795 + 4527296 * 2 ^ 59
def prefixEnd_4527296 : Nat := 4983230072969 + 3 ^ 40 * 4527296 * 2
def baseEnd_4527296 : Nat := 2324678913177624167279351

theorem tailTrace_4527296 : CollatzResearch.WordTrace tailWord_4527296 prefixEnd_4527296 2324678913177624167279351 := by
  unfold tailWord_4527296
  simp only [CollatzResearch.WordTrace]
  refine ⟨82562025303193633722132871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110082700404258178296177161 82562025303193633722132871)
  ·
    refine ⟨123843037954790450583199307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82562025303193633722132871 123843037954790450583199307)
    ·
      refine ⟨185764556932185675874798961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123843037954790450583199307 185764556932185675874798961)
      ·
        refine ⟨139323417699139256906099221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185764556932185675874798961 139323417699139256906099221)
        ·
          refine ⟨6530785204647152667473401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 139323417699139256906099221 6530785204647152667473401)
          ·
            refine ⟨4898088903485364500605051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6530785204647152667473401 4898088903485364500605051)
            ·
              refine ⟨7347133355228046750907577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4898088903485364500605051 7347133355228046750907577)
              ·
                refine ⟨5510350016421035063180683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7347133355228046750907577 5510350016421035063180683)
                ·
                  refine ⟨8265525024631552594771025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5510350016421035063180683 8265525024631552594771025)
                  ·
                    refine ⟨6199143768473664446078269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8265525024631552594771025 6199143768473664446078269)
                    ·
                      refine ⟨2324678913177624167279351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6199143768473664446078269 2324678913177624167279351)
                      ·
                        rfl

theorem cell23_4527296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_4527296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527296 prefixEnd_4527296 := by exact prefixLift 4527296
  have htrace : WordTrace (prefixWord ++ tailWord_4527296) baseStart_4527296 baseEnd_4527296 := by
    simpa [prefixWord, tailWord_4527296, baseEnd_4527296] using wordTrace_append hprefix tailTrace_4527296
  have hstable : (prefixWord ++ tailWord_4527296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527296).length < 2 ^ (prefixWord ++ tailWord_4527296).sum := by decide
  have hdescent : baseEnd_4527296 < baseStart_4527296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527319 : List Nat := [1, 1, 3, 2, 1, 2, 2, 5, 1, 3, 2]
def baseStart_4527319 : Nat := 118140960795 + 4527319 * 2 ^ 59
def prefixEnd_4527319 : Nat := 4983230072969 + 3 ^ 40 * 4527319 * 2
def baseEnd_4527319 : Nat := 2324690723232677577291745

theorem tailTrace_4527319 : CollatzResearch.WordTrace tailWord_4527319 prefixEnd_4527319 2324690723232677577291745 := by
  unfold tailWord_4527319
  simp only [CollatzResearch.WordTrace]
  refine ⟨165124889485303942372353011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110083259656869294914902007 165124889485303942372353011)
  ·
    refine ⟨247687334227955913558529517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165124889485303942372353011 247687334227955913558529517)
    ·
      refine ⟨92882750335483467584448569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247687334227955913558529517 92882750335483467584448569)
      ·
        refine ⟨69662062751612600688336427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92882750335483467584448569 69662062751612600688336427)
        ·
          refine ⟨104493094127418901032504641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69662062751612600688336427 104493094127418901032504641)
          ·
            refine ⟨78369820595564175774378481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104493094127418901032504641 78369820595564175774378481)
            ·
              refine ⟨58777365446673131830783861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78369820595564175774378481 58777365446673131830783861)
              ·
                refine ⟨5510378010625606109135987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58777365446673131830783861 5510378010625606109135987)
                ·
                  refine ⟨8265567015938409163703981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5510378010625606109135987 8265567015938409163703981)
                  ·
                    refine ⟨3099587630976903436388993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8265567015938409163703981 3099587630976903436388993)
                    ·
                      refine ⟨2324690723232677577291745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3099587630976903436388993 2324690723232677577291745)
                      ·
                        rfl

theorem cell23_4527319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_4527319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527319 prefixEnd_4527319 := by exact prefixLift 4527319
  have htrace : WordTrace (prefixWord ++ tailWord_4527319) baseStart_4527319 baseEnd_4527319 := by
    simpa [prefixWord, tailWord_4527319, baseEnd_4527319] using wordTrace_append hprefix tailTrace_4527319
  have hstable : (prefixWord ++ tailWord_4527319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527319).length < 2 ^ (prefixWord ++ tailWord_4527319).sum := by decide
  have hdescent : baseEnd_4527319 < baseStart_4527319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527389 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 7]
def baseStart_4527389 : Nat := 118140960795 + 4527389 * 2 ^ 59
def prefixEnd_4527389 : Nat := 4983230072969 + 3 ^ 40 * 4527389 * 2
def baseEnd_4527389 : Nat := 258302962986499144824047

theorem tailTrace_4527389 : CollatzResearch.WordTrace tailWord_4527389 prefixEnd_4527389 258302962986499144824047 := by
  unfold tailWord_4527389
  simp only [CollatzResearch.WordTrace]
  refine ⟨165127442595050344327401221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110084961730033562884934147 165127442595050344327401221)
  ·
    refine ⟨30961395486571939561387729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165127442595050344327401221 30961395486571939561387729)
    ·
      refine ⟨23221046614928954671040797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30961395486571939561387729 23221046614928954671040797)
      ·
        refine ⟨8707892480598358001640299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23221046614928954671040797 8707892480598358001640299)
        ·
          refine ⟨13061838720897537002460449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8707892480598358001640299 13061838720897537002460449)
          ·
            refine ⟨9796379040673152751845337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13061838720897537002460449 9796379040673152751845337)
            ·
              refine ⟨7347284280504864563884003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9796379040673152751845337 7347284280504864563884003)
              ·
                refine ⟨11020926420757296845826005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7347284280504864563884003 11020926420757296845826005)
                ·
                  refine ⟨258302962986499144824047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11020926420757296845826005 258302962986499144824047)
                  ·
                    rfl

theorem cell23_4527389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_4527389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527389 prefixEnd_4527389 := by exact prefixLift 4527389
  have htrace : WordTrace (prefixWord ++ tailWord_4527389) baseStart_4527389 baseEnd_4527389 := by
    simpa [prefixWord, tailWord_4527389, baseEnd_4527389] using wordTrace_append hprefix tailTrace_4527389
  have hstable : (prefixWord ++ tailWord_4527389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527389).length < 2 ^ (prefixWord ++ tailWord_4527389).sum := by decide
  have hdescent : baseEnd_4527389 < baseStart_4527389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527400 : List Nat := [2, 1, 5, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_4527400 : Nat := 118140960795 + 4527400 * 2 ^ 59
def prefixEnd_4527400 : Nat := 4983230072969 + 3 ^ 40 * 4527400 * 2
def baseEnd_4527400 : Nat := 2324732315165691760378873

theorem tailTrace_4527400 : CollatzResearch.WordTrace tailWord_4527400 prefixEnd_4527400 2324732315165691760378873 := by
  unfold tailWord_4527400
  simp only [CollatzResearch.WordTrace]
  refine ⟨82563921899005246603025827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110085229198673662137367769 82563921899005246603025827)
  ·
    refine ⟨123845882848507869904538741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82563921899005246603025827 123845882848507869904538741)
    ·
      refine ⟨11610551517047612803550507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123845882848507869904538741 11610551517047612803550507)
      ·
        refine ⟨17415827275571419205325761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11610551517047612803550507 17415827275571419205325761)
        ·
          refine ⟨13061870456678564403994321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17415827275571419205325761 13061870456678564403994321)
          ·
            refine ⟨9796402842508923302995741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13061870456678564403994321 9796402842508923302995741)
            ·
              refine ⟨3673651065940846238623403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9796402842508923302995741 3673651065940846238623403)
              ·
                refine ⟨5510476598911269357935105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3673651065940846238623403 5510476598911269357935105)
                ·
                  refine ⟨4132857449183452018451329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5510476598911269357935105 4132857449183452018451329)
                  ·
                    refine ⟨3099643086887589013838497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4132857449183452018451329 3099643086887589013838497)
                    ·
                      refine ⟨2324732315165691760378873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3099643086887589013838497 2324732315165691760378873)
                      ·
                        rfl

theorem cell23_4527400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_4527400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527400 prefixEnd_4527400 := by exact prefixLift 4527400
  have htrace : WordTrace (prefixWord ++ tailWord_4527400) baseStart_4527400 baseEnd_4527400 := by
    simpa [prefixWord, tailWord_4527400, baseEnd_4527400] using wordTrace_append hprefix tailTrace_4527400
  have hstable : (prefixWord ++ tailWord_4527400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527400).length < 2 ^ (prefixWord ++ tailWord_4527400).sum := by decide
  have hdescent : baseEnd_4527400 < baseStart_4527400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527449 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 3, 4]
def baseStart_4527449 : Nat := 118140960795 + 4527449 * 2 ^ 59
def prefixEnd_4527449 : Nat := 4983230072969 + 3 ^ 40 * 4527449 * 2
def baseEnd_4527449 : Nat := 774919158572587356222049

theorem tailTrace_4527449 : CollatzResearch.WordTrace tailWord_4527449 prefixEnd_4527449 774919158572587356222049 := by
  unfold tailWord_4527449
  simp only [CollatzResearch.WordTrace]
  refine ⟨165129630974832974574585401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110086420649888649716390267 165129630974832974574585401)
  ·
    refine ⟨123847223231124730930939051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165129630974832974574585401 123847223231124730930939051)
    ·
      refine ⟨185770834846687096396408577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123847223231124730930939051 185770834846687096396408577)
      ·
        refine ⟨139328126135015322297306433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185770834846687096396408577 139328126135015322297306433)
        ·
          refine ⟨104496094601261491722979825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139328126135015322297306433 104496094601261491722979825)
          ·
            refine ⟨78372070950946118792234869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104496094601261491722979825 78372070950946118792234869)
            ·
              refine ⟨7347381651651198636772019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78372070950946118792234869 7347381651651198636772019)
              ·
                refine ⟨11021072477476797955158029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7347381651651198636772019 11021072477476797955158029)
                ·
                  refine ⟨4132902179053799233184261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11021072477476797955158029 4132902179053799233184261)
                  ·
                    refine ⟨774919158572587356222049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4132902179053799233184261 774919158572587356222049)
                    ·
                      rfl

theorem cell23_4527449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 4].length) (baseStart_4527449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527449 prefixEnd_4527449 := by exact prefixLift 4527449
  have htrace : WordTrace (prefixWord ++ tailWord_4527449) baseStart_4527449 baseEnd_4527449 := by
    simpa [prefixWord, tailWord_4527449, baseEnd_4527449] using wordTrace_append hprefix tailTrace_4527449
  have hstable : (prefixWord ++ tailWord_4527449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527449).length < 2 ^ (prefixWord ++ tailWord_4527449).sum := by decide
  have hdescent : baseEnd_4527449 < baseStart_4527449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527533 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_4527533 : Nat := 118140960795 + 4527533 * 2 ^ 59
def prefixEnd_4527533 : Nat := 4983230072969 + 3 ^ 40 * 4527533 * 2
def baseEnd_4527533 : Nat := 2324800608092739740015761

theorem tailTrace_4527533 : CollatzResearch.WordTrace tailWord_4527533 prefixEnd_4527533 2324800608092739740015761 := by
  unfold tailWord_4527533
  simp only [CollatzResearch.WordTrace]
  refine ⟨165132694706528656920643253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110088463137685771280428835 165132694706528656920643253)
  ·
    refine ⟨15481190128737061586310305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165132694706528656920643253 15481190128737061586310305)
    ·
      refine ⟨11610892596552796189732729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15481190128737061586310305 11610892596552796189732729)
      ·
        refine ⟨8708169447414597142299547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11610892596552796189732729 8708169447414597142299547)
        ·
          refine ⟨13062254171121895713449321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8708169447414597142299547 13062254171121895713449321)
          ·
            refine ⟨9796690628341421785086991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13062254171121895713449321 9796690628341421785086991)
            ·
              refine ⟨14695035942512132677630487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9796690628341421785086991 14695035942512132677630487)
              ·
                refine ⟨22042553913768199016445731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14695035942512132677630487 22042553913768199016445731)
                ·
                  refine ⟨33063830870652298524668597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22042553913768199016445731 33063830870652298524668597)
                  ·
                    refine ⟨3099734144123652986687681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33063830870652298524668597 3099734144123652986687681)
                    ·
                      refine ⟨2324800608092739740015761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3099734144123652986687681 2324800608092739740015761)
                      ·
                        rfl

theorem cell23_4527533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_4527533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527533 prefixEnd_4527533 := by exact prefixLift 4527533
  have htrace : WordTrace (prefixWord ++ tailWord_4527533) baseStart_4527533 baseEnd_4527533 := by
    simpa [prefixWord, tailWord_4527533, baseEnd_4527533] using wordTrace_append hprefix tailTrace_4527533
  have hstable : (prefixWord ++ tailWord_4527533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527533).length < 2 ^ (prefixWord ++ tailWord_4527533).sum := by decide
  have hdescent : baseEnd_4527533 < baseStart_4527533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527549 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_4527549 : Nat := 118140960795 + 4527549 * 2 ^ 59
def prefixEnd_4527549 : Nat := 4983230072969 + 3 ^ 40 * 4527549 * 2
def baseEnd_4527549 : Nat := 2324808823783211677415687

theorem tailTrace_4527549 : CollatzResearch.WordTrace tailWord_4527549 prefixEnd_4527549 2324808823783211677415687 := by
  unfold tailWord_4527549
  simp only [CollatzResearch.WordTrace]
  refine ⟨165133278274470691653225701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110088852182980461102150467 165133278274470691653225701)
  ·
    refine ⟨30962489676463254684979819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165133278274470691653225701 30962489676463254684979819)
    ·
      refine ⟨46443734514694882027469729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30962489676463254684979819 46443734514694882027469729)
      ·
        refine ⟨34832800886021161520602297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46443734514694882027469729 34832800886021161520602297)
        ·
          refine ⟨26124600664515871140451723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34832800886021161520602297 26124600664515871140451723)
          ·
            refine ⟨39186900996773806710677585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26124600664515871140451723 39186900996773806710677585)
            ·
              refine ⟨29390175747580355033008189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39186900996773806710677585 29390175747580355033008189)
              ·
                refine ⟨11021315905342633137378071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29390175747580355033008189 11021315905342633137378071)
                ·
                  refine ⟨16531973858013949706067107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11021315905342633137378071 16531973858013949706067107)
                  ·
                    refine ⟨24797960787020924559100661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16531973858013949706067107 24797960787020924559100661)
                    ·
                      refine ⟨2324808823783211677415687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24797960787020924559100661 2324808823783211677415687)
                      ·
                        rfl

theorem cell23_4527549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_4527549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527549 prefixEnd_4527549 := by exact prefixLift 4527549
  have htrace : WordTrace (prefixWord ++ tailWord_4527549) baseStart_4527549 baseEnd_4527549 := by
    simpa [prefixWord, tailWord_4527549, baseEnd_4527549] using wordTrace_append hprefix tailTrace_4527549
  have hstable : (prefixWord ++ tailWord_4527549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527549).length < 2 ^ (prefixWord ++ tailWord_4527549).sum := by decide
  have hdescent : baseEnd_4527549 < baseStart_4527549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527573 : List Nat := [1, 3, 2, 3, 1, 1, 5, 1, 2, 4]
def baseStart_4527573 : Nat := 118140960795 + 4527573 * 2 ^ 59
def prefixEnd_4527573 : Nat := 4983230072969 + 3 ^ 40 * 4527573 * 2
def baseEnd_4527573 : Nat := 774940382439639861171859

theorem tailTrace_4527573 : CollatzResearch.WordTrace tailWord_4527573 prefixEnd_4527573 774940382439639861171859 := by
  unfold tailWord_4527573
  simp only [CollatzResearch.WordTrace]
  refine ⟨165134153626383743752099373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110089435750922495834732915 165134153626383743752099373)
  ·
    refine ⟨61925307609893903907037265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165134153626383743752099373 61925307609893903907037265)
    ·
      refine ⟨46443980707420427930277949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61925307609893903907037265 46443980707420427930277949)
      ·
        refine ⟨17416492765282660473854231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46443980707420427930277949 17416492765282660473854231)
        ·
          refine ⟨26124739147923990710781347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17416492765282660473854231 26124739147923990710781347)
          ·
            refine ⟨39187108721885986066172021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26124739147923990710781347 39187108721885986066172021)
            ·
              refine ⟨3673791442676811193703627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39187108721885986066172021 3673791442676811193703627)
              ·
                refine ⟨5510687164015216790555441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3673791442676811193703627 5510687164015216790555441)
                ·
                  refine ⟨4133015373011412592916581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5510687164015216790555441 4133015373011412592916581)
                  ·
                    refine ⟨774940382439639861171859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4133015373011412592916581 774940382439639861171859)
                    ·
                      rfl

theorem cell23_4527573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_4527573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527573 prefixEnd_4527573 := by exact prefixLift 4527573
  have htrace : WordTrace (prefixWord ++ tailWord_4527573) baseStart_4527573 baseEnd_4527573 := by
    simpa [prefixWord, tailWord_4527573, baseEnd_4527573] using wordTrace_append hprefix tailTrace_4527573
  have hstable : (prefixWord ++ tailWord_4527573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527573).length < 2 ^ (prefixWord ++ tailWord_4527573).sum := by decide
  have hdescent : baseEnd_4527573 < baseStart_4527573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527614 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_4527614 : Nat := 118140960795 + 4527614 * 2 ^ 59
def prefixEnd_4527614 : Nat := 4983230072969 + 3 ^ 40 * 4527614 * 2
def baseEnd_4527614 : Nat := 2324842200025753923102889

theorem tailTrace_4527614 : CollatzResearch.WordTrace tailWord_4527614 prefixEnd_4527614 2324842200025753923102889 := by
  unfold tailWord_4527614
  simp only [CollatzResearch.WordTrace]
  refine ⟨20641956127404400969292737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110090432679490138502894597 20641956127404400969292737)
  ·
    refine ⟨15481467095553300726969553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20641956127404400969292737 15481467095553300726969553)
    ·
      refine ⟨11611100321664975545227165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15481467095553300726969553 11611100321664975545227165)
      ·
        refine ⟨4354162620624365829460187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11611100321664975545227165 4354162620624365829460187)
        ·
          refine ⟨6531243930936548744190281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4354162620624365829460187 6531243930936548744190281)
          ·
            refine ⟨4898432948202411558142711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6531243930936548744190281 4898432948202411558142711)
            ·
              refine ⟨7347649422303617337214067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4898432948202411558142711 7347649422303617337214067)
              ·
                refine ⟨11021474133455426005821101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7347649422303617337214067 11021474133455426005821101)
                ·
                  refine ⟨4133052800045784752182913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11021474133455426005821101 4133052800045784752182913)
                  ·
                    refine ⟨3099789600034338564137185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4133052800045784752182913 3099789600034338564137185)
                    ·
                      refine ⟨2324842200025753923102889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3099789600034338564137185 2324842200025753923102889)
                      ·
                        rfl

theorem cell23_4527614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_4527614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527614 prefixEnd_4527614 := by exact prefixLift 4527614
  have htrace : WordTrace (prefixWord ++ tailWord_4527614) baseStart_4527614 baseEnd_4527614 := by
    simpa [prefixWord, tailWord_4527614, baseEnd_4527614] using wordTrace_append hprefix tailTrace_4527614
  have hstable : (prefixWord ++ tailWord_4527614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527614).length < 2 ^ (prefixWord ++ tailWord_4527614).sum := by decide
  have hdescent : baseEnd_4527614 < baseStart_4527614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527630 : List Nat := [4, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3]
def baseStart_4527630 : Nat := 118140960795 + 4527630 * 2 ^ 59
def prefixEnd_4527630 : Nat := 4983230072969 + 3 ^ 40 * 4527630 * 2
def baseEnd_4527630 : Nat := 2324850415716225860502815

theorem tailTrace_4527630 : CollatzResearch.WordTrace tailWord_4527630 prefixEnd_4527630 2324850415716225860502815 := by
  unfold tailWord_4527630
  simp only [CollatzResearch.WordTrace]
  refine ⟨20642029073397155310865543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110090821724784828324616229 20642029073397155310865543)
  ·
    refine ⟨30963043610095732966298315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20642029073397155310865543 30963043610095732966298315)
    ·
      refine ⟨46444565415143599449447473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30963043610095732966298315 46444565415143599449447473)
      ·
        refine ⟨34833424061357699587085605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46444565415143599449447473 34833424061357699587085605)
        ·
          refine ⟨6531267011504568672578551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34833424061357699587085605 6531267011504568672578551)
          ·
            refine ⟨9796900517256853008867827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6531267011504568672578551 9796900517256853008867827)
            ·
              refine ⟨14695350775885279513301741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9796900517256853008867827 14695350775885279513301741)
              ·
                refine ⟨5510756540956979817488153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14695350775885279513301741 5510756540956979817488153)
                ·
                  refine ⟨4133067405717734863116115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5510756540956979817488153 4133067405717734863116115)
                  ·
                    refine ⟨6199601108576602294674173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4133067405717734863116115 6199601108576602294674173)
                    ·
                      refine ⟨2324850415716225860502815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6199601108576602294674173 2324850415716225860502815)
                      ·
                        rfl

theorem cell23_4527630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_4527630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527630 prefixEnd_4527630 := by exact prefixLift 4527630
  have htrace : WordTrace (prefixWord ++ tailWord_4527630) baseStart_4527630 baseEnd_4527630 := by
    simpa [prefixWord, tailWord_4527630, baseEnd_4527630] using wordTrace_append hprefix tailTrace_4527630
  have hstable : (prefixWord ++ tailWord_4527630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527630).length < 2 ^ (prefixWord ++ tailWord_4527630).sum := by decide
  have hdescent : baseEnd_4527630 < baseStart_4527630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527689 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 4, 5]
def baseStart_4527689 : Nat := 118140960795 + 4527689 * 2 ^ 59
def prefixEnd_4527689 : Nat := 4983230072969 + 3 ^ 40 * 4527689 * 2
def baseEnd_4527689 : Nat := 774960237024947043221681

theorem tailTrace_4527689 : CollatzResearch.WordTrace tailWord_4527689 prefixEnd_4527689 774960237024947043221681 := by
  unfold tailWord_4527689
  simp only [CollatzResearch.WordTrace]
  refine ⟨165138384493963495563322121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110092256329308997042214747 165138384493963495563322121)
  ·
    refine ⟨123853788370472621672491591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165138384493963495563322121 123853788370472621672491591)
    ·
      refine ⟨185780682555708932508737387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123853788370472621672491591 185780682555708932508737387)
      ·
        refine ⟨278671023833563398763106081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185780682555708932508737387 278671023833563398763106081)
        ·
          refine ⟨209003267875172549072329561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278671023833563398763106081 209003267875172549072329561)
          ·
            refine ⟨156752450906379411804247171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209003267875172549072329561 156752450906379411804247171)
            ·
              refine ⟨235128676359569117706370757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156752450906379411804247171 235128676359569117706370757)
              ·
                refine ⟨44086626817419209569944517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 235128676359569117706370757 44086626817419209569944517)
                ·
                  refine ⟨8266242528266101794364597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44086626817419209569944517 8266242528266101794364597)
                  ·
                    refine ⟨774960237024947043221681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8266242528266101794364597 774960237024947043221681)
                    ·
                      rfl

theorem cell23_4527689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 5].length) (baseStart_4527689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527689 prefixEnd_4527689 := by exact prefixLift 4527689
  have htrace : WordTrace (prefixWord ++ tailWord_4527689) baseStart_4527689 baseEnd_4527689 := by
    simpa [prefixWord, tailWord_4527689, baseEnd_4527689] using wordTrace_append hprefix tailTrace_4527689
  have hstable : (prefixWord ++ tailWord_4527689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527689).length < 2 ^ (prefixWord ++ tailWord_4527689).sum := by decide
  have hdescent : baseEnd_4527689 < baseStart_4527689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527693 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 7]
def baseStart_4527693 : Nat := 118140960795 + 4527693 * 2 ^ 59
def prefixEnd_4527693 : Nat := 4983230072969 + 3 ^ 40 * 4527693 * 2
def baseEnd_4527693 : Nat := 258320307221939901557225

theorem tailTrace_4527693 : CollatzResearch.WordTrace tailWord_4527693 prefixEnd_4527693 258320307221939901557225 := by
  unfold tailWord_4527693
  simp only [CollatzResearch.WordTrace]
  refine ⟨165138530385949004246467733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110092353590632669497645155 165138530385949004246467733)
  ·
    refine ⟨7740868611841359574053175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 165138530385949004246467733 7740868611841359574053175)
    ·
      refine ⟨11611302917762039361079763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7740868611841359574053175 11611302917762039361079763)
      ·
        refine ⟨17416954376643059041619645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11611302917762039361079763 17416954376643059041619645)
        ·
          refine ⟨6531357891241147140607367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17416954376643059041619645 6531357891241147140607367)
          ·
            refine ⟨9797036836861720710911051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6531357891241147140607367 9797036836861720710911051)
            ·
              refine ⟨14695555255292581066366577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9797036836861720710911051 14695555255292581066366577)
              ·
                refine ⟨11021666441469435799774933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14695555255292581066366577 11021666441469435799774933)
                ·
                  refine ⟨258320307221939901557225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11021666441469435799774933 258320307221939901557225)
                  ·
                    rfl

theorem cell23_4527693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_4527693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527693 prefixEnd_4527693 := by exact prefixLift 4527693
  have htrace : WordTrace (prefixWord ++ tailWord_4527693) baseStart_4527693 baseEnd_4527693 := by
    simpa [prefixWord, tailWord_4527693, baseEnd_4527693] using wordTrace_append hprefix tailTrace_4527693
  have hstable : (prefixWord ++ tailWord_4527693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527693).length < 2 ^ (prefixWord ++ tailWord_4527693).sum := by decide
  have hdescent : baseEnd_4527693 < baseStart_4527693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527696 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 2, 5, 2]
def baseStart_4527696 : Nat := 118140960795 + 4527696 * 2 ^ 59
def prefixEnd_4527696 : Nat := 4983230072969 + 3 ^ 40 * 4527696 * 2
def baseEnd_4527696 : Nat := 2324884305439422602277511

theorem tailTrace_4527696 : CollatzResearch.WordTrace tailWord_4527696 prefixEnd_4527696 2324884305439422602277511 := by
  unfold tailWord_4527696
  simp only [CollatzResearch.WordTrace]
  refine ⟨82569319902469067879413471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110092426536625423839217961 82569319902469067879413471)
  ·
    refine ⟨123853979853703601819120207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82569319902469067879413471 123853979853703601819120207)
    ·
      refine ⟨185780969780555402728680311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123853979853703601819120207 185780969780555402728680311)
      ·
        refine ⟨278671454670833104093020467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185780969780555402728680311 278671454670833104093020467)
        ·
          refine ⟨418007182006249656139530701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278671454670833104093020467 418007182006249656139530701)
          ·
            refine ⟨156752693252343621052324013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 418007182006249656139530701 156752693252343621052324013)
            ·
              refine ⟨58782259969628857894621505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156752693252343621052324013 58782259969628857894621505)
              ·
                refine ⟨44086694977221643420966129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58782259969628857894621505 44086694977221643420966129)
                ·
                  refine ⟨33065021232916232565724597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44086694977221643420966129 33065021232916232565724597)
                  ·
                    refine ⟨3099845740585896803036681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33065021232916232565724597 3099845740585896803036681)
                    ·
                      refine ⟨2324884305439422602277511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3099845740585896803036681 2324884305439422602277511)
                      ·
                        rfl

theorem cell23_4527696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 2, 5, 2].length) (baseStart_4527696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527696 prefixEnd_4527696 := by exact prefixLift 4527696
  have htrace : WordTrace (prefixWord ++ tailWord_4527696) baseStart_4527696 baseEnd_4527696 := by
    simpa [prefixWord, tailWord_4527696, baseEnd_4527696] using wordTrace_append hprefix tailTrace_4527696
  have hstable : (prefixWord ++ tailWord_4527696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527696).length < 2 ^ (prefixWord ++ tailWord_4527696).sum := by decide
  have hdescent : baseEnd_4527696 < baseStart_4527696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527729 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 2, 3, 5]
def baseStart_4527729 : Nat := 118140960795 + 4527729 * 2 ^ 59
def prefixEnd_4527729 : Nat := 4983230072969 + 3 ^ 40 * 4527729 * 2
def baseEnd_4527729 : Nat := 2324901250301020973164859

theorem tailTrace_4527729 : CollatzResearch.WordTrace tailWord_4527729 prefixEnd_4527729 2324901250301020973164859 := by
  unfold tailWord_4527729
  simp only [CollatzResearch.WordTrace]
  refine ⟨165139843413818582394778241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110093228942545721596518827 165139843413818582394778241)
  ·
    refine ⟨123854882560363936796083681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165139843413818582394778241 123854882560363936796083681)
    ·
      refine ⟨92891161920272952597062761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123854882560363936796083681 92891161920272952597062761)
      ·
        refine ⟨69668371440204714447797071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92891161920272952597062761 69668371440204714447797071)
        ·
          refine ⟨104502557160307071671695607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69668371440204714447797071 104502557160307071671695607)
          ·
            refine ⟨156753835740460607507543411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104502557160307071671695607 156753835740460607507543411)
            ·
              refine ⟨235130753610690911261315117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156753835740460607507543411 235130753610690911261315117)
              ·
                refine ⟨88174032604009091722993169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235130753610690911261315117 88174032604009091722993169)
                ·
                  refine ⟨66130524453006818792244877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88174032604009091722993169 66130524453006818792244877)
                  ·
                    refine ⟨24798946669877557047091829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66130524453006818792244877 24798946669877557047091829)
                    ·
                      refine ⟨2324901250301020973164859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24798946669877557047091829 2324901250301020973164859)
                      ·
                        rfl

theorem cell23_4527729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_4527729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527729 prefixEnd_4527729 := by exact prefixLift 4527729
  have htrace : WordTrace (prefixWord ++ tailWord_4527729) baseStart_4527729 baseEnd_4527729 := by
    simpa [prefixWord, tailWord_4527729, baseEnd_4527729] using wordTrace_append hprefix tailTrace_4527729
  have hstable : (prefixWord ++ tailWord_4527729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527729).length < 2 ^ (prefixWord ++ tailWord_4527729).sum := by decide
  have hdescent : baseEnd_4527729 < baseStart_4527729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527739 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 6]
def baseStart_4527739 : Nat := 118140960795 + 4527739 * 2 ^ 59
def prefixEnd_4527739 : Nat := 4983230072969 + 3 ^ 40 * 4527739 * 2
def baseEnd_4527739 : Nat := 2324906385107565934039813

theorem tailTrace_4527739 : CollatzResearch.WordTrace tailWord_4527739 prefixEnd_4527739 2324906385107565934039813 := by
  unfold tailWord_4527739
  simp only [CollatzResearch.WordTrace]
  refine ⟨165140208143782354102642271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110093472095854902735094847 165140208143782354102642271)
  ·
    refine ⟨247710312215673531153963407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165140208143782354102642271 247710312215673531153963407)
    ·
      refine ⟨371565468323510296730945111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247710312215673531153963407 371565468323510296730945111)
      ·
        refine ⟨557348202485265445096417667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371565468323510296730945111 557348202485265445096417667)
        ·
          refine ⟨836022303727898167644626501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557348202485265445096417667 836022303727898167644626501)
          ·
            refine ⟨156754181948980906433367469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 836022303727898167644626501 156754181948980906433367469)
            ·
              refine ⟨58782818230867839912512801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156754181948980906433367469 58782818230867839912512801)
              ·
                refine ⟨44087113673150879934384601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58782818230867839912512801 44087113673150879934384601)
                ·
                  refine ⟨33065335254863159950788451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44087113673150879934384601 33065335254863159950788451)
                  ·
                    refine ⟨49598002882294739926182677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33065335254863159950788451 49598002882294739926182677)
                    ·
                      refine ⟨2324906385107565934039813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49598002882294739926182677 2324906385107565934039813)
                      ·
                        rfl

theorem cell23_4527739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 6].length) (baseStart_4527739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527739 prefixEnd_4527739 := by exact prefixLift 4527739
  have htrace : WordTrace (prefixWord ++ tailWord_4527739) baseStart_4527739 baseEnd_4527739 := by
    simpa [prefixWord, tailWord_4527739, baseEnd_4527739] using wordTrace_append hprefix tailTrace_4527739
  have hstable : (prefixWord ++ tailWord_4527739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527739).length < 2 ^ (prefixWord ++ tailWord_4527739).sum := by decide
  have hdescent : baseEnd_4527739 < baseStart_4527739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527769 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 8]
def baseStart_4527769 : Nat := 118140960795 + 4527769 * 2 ^ 59
def prefixEnd_4527769 : Nat := 4983230072969 + 3 ^ 40 * 4527769 * 2
def baseEnd_4527769 : Nat := 2324921789527200816664675

theorem tailTrace_4527769 : CollatzResearch.WordTrace tailWord_4527769 prefixEnd_4527769 2324921789527200816664675 := by
  unfold tailWord_4527769
  simp only [CollatzResearch.WordTrace]
  refine ⟨165141302333673669226234361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110094201555782446150822907 165141302333673669226234361)
  ·
    refine ⟨123855976750255251919675771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165141302333673669226234361 123855976750255251919675771)
    ·
      refine ⟨185783965125382877879513657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123855976750255251919675771 185783965125382877879513657)
      ·
        refine ⟨139337973844037158409635243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185783965125382877879513657 139337973844037158409635243)
        ·
          refine ⟨209006960766055737614452865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139337973844037158409635243 209006960766055737614452865)
          ·
            refine ⟨156755220574541803210839649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209006960766055737614452865 156755220574541803210839649)
            ·
              refine ⟨117566415430906352408129737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156755220574541803210839649 117566415430906352408129737)
              ·
                refine ⟨88174811573179764306097303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117566415430906352408129737 88174811573179764306097303)
                ·
                  refine ⟨132262217359769646459145955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88174811573179764306097303 132262217359769646459145955)
                  ·
                    refine ⟨198393326039654469688718933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 132262217359769646459145955 198393326039654469688718933)
                    ·
                      refine ⟨2324921789527200816664675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 198393326039654469688718933 2324921789527200816664675)
                      ·
                        rfl

theorem cell23_4527769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_4527769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527769 prefixEnd_4527769 := by exact prefixLift 4527769
  have htrace : WordTrace (prefixWord ++ tailWord_4527769) baseStart_4527769 baseEnd_4527769 := by
    simpa [prefixWord, tailWord_4527769, baseEnd_4527769] using wordTrace_append hprefix tailTrace_4527769
  have hstable : (prefixWord ++ tailWord_4527769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527769).length < 2 ^ (prefixWord ++ tailWord_4527769).sum := by decide
  have hdescent : baseEnd_4527769 < baseStart_4527769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527814 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_4527814 : Nat := 118140960795 + 4527814 * 2 ^ 59
def prefixEnd_4527814 : Nat := 4983230072969 + 3 ^ 40 * 4527814 * 2
def baseEnd_4527814 : Nat := 2324944896156653140601969

theorem tailTrace_4527814 : CollatzResearch.WordTrace tailWord_4527814 prefixEnd_4527814 2324944896156653140601969 := by
  unfold tailWord_4527814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5160716988078457559738203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 110095295745673761274414997 5160716988078457559738203)
  ·
    refine ⟨7741075482117686339607305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5160716988078457559738203 7741075482117686339607305)
    ·
      refine ⟨5805806611588264754705479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7741075482117686339607305 5805806611588264754705479)
      ·
        refine ⟨8708709917382397132058219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5805806611588264754705479 8708709917382397132058219)
        ·
          refine ⟨13063064876073595698087329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8708709917382397132058219 13063064876073595698087329)
          ·
            refine ⟨9797298657055196773565497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13063064876073595698087329 9797298657055196773565497)
            ·
              refine ⟨7347973992791397580174123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9797298657055196773565497 7347973992791397580174123)
              ·
                refine ⟨11021960989187096370261185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7347973992791397580174123 11021960989187096370261185)
                ·
                  refine ⟨8266470741890322277695889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11021960989187096370261185 8266470741890322277695889)
                  ·
                    refine ⟨6199853056417741708271917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8266470741890322277695889 6199853056417741708271917)
                    ·
                      refine ⟨2324944896156653140601969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6199853056417741708271917 2324944896156653140601969)
                      ·
                        rfl

theorem cell23_4527814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_4527814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527814 prefixEnd_4527814 := by exact prefixLift 4527814
  have htrace : WordTrace (prefixWord ++ tailWord_4527814) baseStart_4527814 baseEnd_4527814 := by
    simpa [prefixWord, tailWord_4527814, baseEnd_4527814] using wordTrace_append hprefix tailTrace_4527814
  have hstable : (prefixWord ++ tailWord_4527814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527814).length < 2 ^ (prefixWord ++ tailWord_4527814).sum := by decide
  have hdescent : baseEnd_4527814 < baseStart_4527814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527883 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 3]
def baseStart_4527883 : Nat := 118140960795 + 4527883 * 2 ^ 59
def prefixEnd_4527883 : Nat := 4983230072969 + 3 ^ 40 * 4527883 * 2
def baseEnd_4527883 : Nat := 2324980326321813370639151

theorem tailTrace_4527883 : CollatzResearch.WordTrace tailWord_4527883 prefixEnd_4527883 2324980326321813370639151 := by
  unfold tailWord_4527883
  simp only [CollatzResearch.WordTrace]
  refine ⟨165145460255260666695884303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110096973503507111130589535 165145460255260666695884303)
  ·
    refine ⟨247718190382891000043826455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165145460255260666695884303 247718190382891000043826455)
    ·
      refine ⟨371577285574336500065739683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247718190382891000043826455 371577285574336500065739683)
      ·
        refine ⟨557365928361504750098609525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371577285574336500065739683 557365928361504750098609525)
        ·
          refine ⟨52253055783891070321744643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 557365928361504750098609525 52253055783891070321744643)
          ·
            refine ⟨78379583675836605482616965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52253055783891070321744643 78379583675836605482616965)
            ·
              refine ⟨14696171939219363527990681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78379583675836605482616965 14696171939219363527990681)
              ·
                refine ⟨11022128954414522645993011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14696171939219363527990681 11022128954414522645993011)
                ·
                  refine ⟨16533193431621783968989517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11022128954414522645993011 16533193431621783968989517)
                  ·
                    refine ⟨6199947536858168988371069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16533193431621783968989517 6199947536858168988371069)
                    ·
                      refine ⟨2324980326321813370639151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6199947536858168988371069 2324980326321813370639151)
                      ·
                        rfl

theorem cell23_4527883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 3].length) (baseStart_4527883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527883 prefixEnd_4527883 := by exact prefixLift 4527883
  have htrace : WordTrace (prefixWord ++ tailWord_4527883) baseStart_4527883 baseEnd_4527883 := by
    simpa [prefixWord, tailWord_4527883, baseEnd_4527883] using wordTrace_append hprefix tailTrace_4527883
  have hstable : (prefixWord ++ tailWord_4527883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527883).length < 2 ^ (prefixWord ++ tailWord_4527883).sum := by decide
  have hdescent : baseEnd_4527883 < baseStart_4527883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527900 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_4527900 : Nat := 118140960795 + 4527900 * 2 ^ 59
def prefixEnd_4527900 : Nat := 4983230072969 + 3 ^ 40 * 4527900 * 2
def baseEnd_4527900 : Nat := 2324989055492939804126573

theorem tailTrace_4527900 : CollatzResearch.WordTrace tailWord_4527900 prefixEnd_4527900 2324989055492939804126573 := by
  unfold tailWord_4527900
  simp only [CollatzResearch.WordTrace]
  refine ⟨82573040148099539299626577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110097386864132719066168769 82573040148099539299626577)
  ·
    refine ⟨61929780111074654474719933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82573040148099539299626577 61929780111074654474719933)
    ·
      refine ⟨23223667541652995428019975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61929780111074654474719933 23223667541652995428019975)
      ·
        refine ⟨34835501312479493142029963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23223667541652995428019975 34835501312479493142029963)
        ·
          refine ⟨52253251968719239713044945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34835501312479493142029963 52253251968719239713044945)
          ·
            refine ⟨39189938976539429784783709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52253251968719239713044945 39189938976539429784783709)
            ·
              refine ⟨14696227116202286169293891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39189938976539429784783709 14696227116202286169293891)
              ·
                refine ⟨22044340674303429253940837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14696227116202286169293891 22044340674303429253940837)
                ·
                  refine ⟨4133313876431892985113907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22044340674303429253940837 4133313876431892985113907)
                  ·
                    refine ⟨6199970814647839477670861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4133313876431892985113907 6199970814647839477670861)
                    ·
                      refine ⟨2324989055492939804126573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6199970814647839477670861 2324989055492939804126573)
                      ·
                        rfl

theorem cell23_4527900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_4527900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527900 prefixEnd_4527900 := by exact prefixLift 4527900
  have htrace : WordTrace (prefixWord ++ tailWord_4527900) baseStart_4527900 baseEnd_4527900 := by
    simpa [prefixWord, tailWord_4527900, baseEnd_4527900] using wordTrace_append hprefix tailTrace_4527900
  have hstable : (prefixWord ++ tailWord_4527900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527900).length < 2 ^ (prefixWord ++ tailWord_4527900).sum := by decide
  have hdescent : baseEnd_4527900 < baseStart_4527900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527957 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 4, 2, 2]
def baseStart_4527957 : Nat := 118140960795 + 4527957 * 2 ^ 59
def prefixEnd_4527957 : Nat := 4983230072969 + 3 ^ 40 * 4527957 * 2
def baseEnd_4527957 : Nat := 2325018323890246081113811

theorem tailTrace_4527957 : CollatzResearch.WordTrace tailWord_4527957 prefixEnd_4527957 2325018323890246081113811 := by
  unfold tailWord_4527957
  simp only [CollatzResearch.WordTrace]
  refine ⟨165148159256992577334078125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110098772837995051556052083 165148159256992577334078125)
  ·
    refine ⟨61930559721372216500279297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165148159256992577334078125 61930559721372216500279297)
    ·
      refine ⟨46447919791029162375209473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61930559721372216500279297 46447919791029162375209473)
      ·
        refine ⟨34835939843271871781407105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46447919791029162375209473 34835939843271871781407105)
        ·
          refine ⟨26126954882453903836055329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34835939843271871781407105 26126954882453903836055329)
          ·
            refine ⟨19595216161840427877041497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26126954882453903836055329 19595216161840427877041497)
            ·
              refine ⟨14696412121380320907781123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19595216161840427877041497 14696412121380320907781123)
              ·
                refine ⟨22044618182070481361671685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14696412121380320907781123 22044618182070481361671685)
                ·
                  refine ⟨4133365909138215255313441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22044618182070481361671685 4133365909138215255313441)
                  ·
                    refine ⟨3100024431853661441485081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4133365909138215255313441 3100024431853661441485081)
                    ·
                      refine ⟨2325018323890246081113811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3100024431853661441485081 2325018323890246081113811)
                      ·
                        rfl

theorem cell23_4527957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_4527957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527957 prefixEnd_4527957 := by exact prefixLift 4527957
  have htrace : WordTrace (prefixWord ++ tailWord_4527957) baseStart_4527957 baseEnd_4527957 := by
    simpa [prefixWord, tailWord_4527957, baseEnd_4527957] using wordTrace_append hprefix tailTrace_4527957
  have hstable : (prefixWord ++ tailWord_4527957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527957).length < 2 ^ (prefixWord ++ tailWord_4527957).sum := by decide
  have hdescent : baseEnd_4527957 < baseStart_4527957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527973 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 1, 5, 3]
def baseStart_4527973 : Nat := 118140960795 + 4527973 * 2 ^ 59
def prefixEnd_4527973 : Nat := 4983230072969 + 3 ^ 40 * 4527973 * 2
def baseEnd_4527973 : Nat := 2325026539580718018513737

theorem tailTrace_4527973 : CollatzResearch.WordTrace tailWord_4527973 prefixEnd_4527973 2325026539580718018513737 := by
  unfold tailWord_4527973
  simp only [CollatzResearch.WordTrace]
  refine ⟨165148742824934612066660573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110099161883289741377773715 165148742824934612066660573)
  ·
    refine ⟨61930778559350479524997715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165148742824934612066660573 61930778559350479524997715)
    ·
      refine ⟨92896167839025719287496573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61930778559350479524997715 92896167839025719287496573)
      ·
        refine ⟨34836062939634644732811215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92896167839025719287496573 34836062939634644732811215)
        ·
          refine ⟨52254094409451967099216823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34836062939634644732811215 52254094409451967099216823)
          ·
            refine ⟨78381141614177950648825235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52254094409451967099216823 78381141614177950648825235)
            ·
              refine ⟨117571712421266925973237853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78381141614177950648825235 117571712421266925973237853)
              ·
                refine ⟨44089392157975097239964195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117571712421266925973237853 44089392157975097239964195)
                ·
                  refine ⟨66134088236962645859946293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44089392157975097239964195 66134088236962645859946293)
                  ·
                    refine ⟨6200070772215248049369965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66134088236962645859946293 6200070772215248049369965)
                    ·
                      refine ⟨2325026539580718018513737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6200070772215248049369965 2325026539580718018513737)
                      ·
                        rfl

theorem cell23_4527973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_4527973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527973 prefixEnd_4527973 := by exact prefixLift 4527973
  have htrace : WordTrace (prefixWord ++ tailWord_4527973) baseStart_4527973 baseEnd_4527973 := by
    simpa [prefixWord, tailWord_4527973, baseEnd_4527973] using wordTrace_append hprefix tailTrace_4527973
  have hstable : (prefixWord ++ tailWord_4527973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527973).length < 2 ^ (prefixWord ++ tailWord_4527973).sum := by decide
  have hdescent : baseEnd_4527973 < baseStart_4527973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4527978 : List Nat := [3, 1, 3, 4, 2, 1, 1, 2, 1, 3, 2]
def baseStart_4527978 : Nat := 118140960795 + 4527978 * 2 ^ 59
def prefixEnd_4527978 : Nat := 4983230072969 + 3 ^ 40 * 4527978 * 2
def baseEnd_4527978 : Nat := 2325029106983990498951215

theorem tailTrace_4527978 : CollatzResearch.WordTrace tailWord_4527978 prefixEnd_4527978 2325029106983990498951215 := by
  unfold tailWord_4527978
  simp only [CollatzResearch.WordTrace]
  refine ⟨41287231297479124480148147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110099283459944331947061725 41287231297479124480148147)
  ·
    refine ⟨61930846946218686720222221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41287231297479124480148147 61930846946218686720222221)
    ·
      refine ⟨23224067604832007520083333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61930846946218686720222221 23224067604832007520083333)
      ·
        refine ⟨4354512675906001410015625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23224067604832007520083333 4354512675906001410015625)
        ·
          refine ⟨3265884506929501057511719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4354512675906001410015625 3265884506929501057511719)
          ·
            refine ⟨4898826760394251586267579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3265884506929501057511719 4898826760394251586267579)
            ·
              refine ⟨7348240140591377379401369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4898826760394251586267579 7348240140591377379401369)
              ·
                refine ⟨5511180105443533034551027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7348240140591377379401369 5511180105443533034551027)
                ·
                  refine ⟨8266770158165299551826541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5511180105443533034551027 8266770158165299551826541)
                  ·
                    refine ⟨3100038809311987331934953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8266770158165299551826541 3100038809311987331934953)
                    ·
                      refine ⟨2325029106983990498951215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3100038809311987331934953 2325029106983990498951215)
                      ·
                        rfl

theorem cell23_4527978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_4527978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4527978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4527978 prefixEnd_4527978 := by exact prefixLift 4527978
  have htrace : WordTrace (prefixWord ++ tailWord_4527978) baseStart_4527978 baseEnd_4527978 := by
    simpa [prefixWord, tailWord_4527978, baseEnd_4527978] using wordTrace_append hprefix tailTrace_4527978
  have hstable : (prefixWord ++ tailWord_4527978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4527978).length < 2 ^ (prefixWord ++ tailWord_4527978).sum := by decide
  have hdescent : baseEnd_4527978 < baseStart_4527978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4527978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528003 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 5]
def baseStart_4528003 : Nat := 118140960795 + 4528003 * 2 ^ 59
def prefixEnd_4528003 : Nat := 4983230072969 + 3 ^ 40 * 4528003 * 2
def baseEnd_4528003 : Nat := 2325041944000352901138599

theorem tailTrace_4528003 : CollatzResearch.WordTrace tailWord_4528003 prefixEnd_4528003 2325041944000352901138599 := by
  unfold tailWord_4528003
  simp only [CollatzResearch.WordTrace]
  refine ⟨165149837014825927190252663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110099891343217284793501775 165149837014825927190252663)
  ·
    refine ⟨247724755522238890785378995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165149837014825927190252663 247724755522238890785378995)
    ·
      refine ⟨371587133283358336178068493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247724755522238890785378995 371587133283358336178068493)
      ·
        refine ⟨139345174981259376066775685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 371587133283358336178068493 139345174981259376066775685)
        ·
          refine ⟨26127220308986133012520441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139345174981259376066775685 26127220308986133012520441)
          ·
            refine ⟨19595415231739599759390331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26127220308986133012520441 19595415231739599759390331)
            ·
              refine ⟨29393122847609399639085497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19595415231739599759390331 29393122847609399639085497)
              ·
                refine ⟨22044842135707049729314123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29393122847609399639085497 22044842135707049729314123)
                ·
                  refine ⟨33067263203560574593971185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22044842135707049729314123 33067263203560574593971185)
                  ·
                    refine ⟨24800447402670430945478389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33067263203560574593971185 24800447402670430945478389)
                    ·
                      refine ⟨2325041944000352901138599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24800447402670430945478389 2325041944000352901138599)
                      ·
                        rfl

theorem cell23_4528003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_4528003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528003 prefixEnd_4528003 := by exact prefixLift 4528003
  have htrace : WordTrace (prefixWord ++ tailWord_4528003) baseStart_4528003 baseEnd_4528003 := by
    simpa [prefixWord, tailWord_4528003, baseEnd_4528003] using wordTrace_append hprefix tailTrace_4528003
  have hstable : (prefixWord ++ tailWord_4528003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528003).length < 2 ^ (prefixWord ++ tailWord_4528003).sum := by decide
  have hdescent : baseEnd_4528003 < baseStart_4528003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528014 : List Nat := [4, 1, 1, 5, 1, 1, 1, 4, 5]
def baseStart_4528014 : Nat := 118140960795 + 4528014 * 2 ^ 59
def prefixEnd_4528014 : Nat := 4983230072969 + 3 ^ 40 * 4528014 * 2
def baseEnd_4528014 : Nat := 258338621365283595344561

theorem tailTrace_4528014 : CollatzResearch.WordTrace tailWord_4528014 prefixEnd_4528014 258338621365283595344561 := by
  unfold tailWord_4528014
  simp only [CollatzResearch.WordTrace]
  refine ⟨20643779777223259508612887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110100158811857384045935397 20643779777223259508612887)
  ·
    refine ⟨30965669665834889262919331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20643779777223259508612887 30965669665834889262919331)
    ·
      refine ⟨46448504498752333894378997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30965669665834889262919331 46448504498752333894378997)
      ·
        refine ⟨4354547296758031302598031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46448504498752333894378997 4354547296758031302598031)
        ·
          refine ⟨6531820945137046953897047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4354547296758031302598031 6531820945137046953897047)
          ·
            refine ⟨9797731417705570430845571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6531820945137046953897047 9797731417705570430845571)
            ·
              refine ⟨14696597126558355646268357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9797731417705570430845571 14696597126558355646268357)
              ·
                refine ⟨2755611961229691683675317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14696597126558355646268357 2755611961229691683675317)
                ·
                  refine ⟨258338621365283595344561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2755611961229691683675317 258338621365283595344561)
                  ·
                    rfl

theorem cell23_4528014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_4528014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528014 prefixEnd_4528014 := by exact prefixLift 4528014
  have htrace : WordTrace (prefixWord ++ tailWord_4528014) baseStart_4528014 baseEnd_4528014 := by
    simpa [prefixWord, tailWord_4528014, baseEnd_4528014] using wordTrace_append hprefix tailTrace_4528014
  have hstable : (prefixWord ++ tailWord_4528014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528014).length < 2 ^ (prefixWord ++ tailWord_4528014).sum := by decide
  have hdescent : baseEnd_4528014 < baseStart_4528014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528020 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_4528020 : Nat := 118140960795 + 4528020 * 2 ^ 59
def prefixEnd_4528020 : Nat := 4983230072969 + 3 ^ 40 * 4528020 * 2
def baseEnd_4528020 : Nat := 2325050673171479334626021

theorem tailTrace_4528020 : CollatzResearch.WordTrace tailWord_4528020 prefixEnd_4528020 2325050673171479334626021 := by
  unfold tailWord_4528020
  simp only [CollatzResearch.WordTrace]
  refine ⟨82575228527882169546810757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110100304703842892729081009 82575228527882169546810757)
  ·
    refine ⟨15482855348977906790027017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82575228527882169546810757 15482855348977906790027017)
    ·
      refine ⟨11612141511733430092520263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15482855348977906790027017 11612141511733430092520263)
      ·
        refine ⟨17418212267600145138780395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11612141511733430092520263 17418212267600145138780395)
        ·
          refine ⟨26127318401400217708170593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17418212267600145138780395 26127318401400217708170593)
          ·
            refine ⟨19595488801050163281127945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26127318401400217708170593 19595488801050163281127945)
            ·
              refine ⟨14696616600787622460845959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19595488801050163281127945 14696616600787622460845959)
              ·
                refine ⟨22044924901181433691268939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14696616600787622460845959 22044924901181433691268939)
                ·
                  refine ⟨33067387351772150536903409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22044924901181433691268939 33067387351772150536903409)
                  ·
                    refine ⟨24800540513829112902677557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33067387351772150536903409 24800540513829112902677557)
                    ·
                      refine ⟨2325050673171479334626021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24800540513829112902677557 2325050673171479334626021)
                      ·
                        rfl

theorem cell23_4528020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_4528020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528020 prefixEnd_4528020 := by exact prefixLift 4528020
  have htrace : WordTrace (prefixWord ++ tailWord_4528020) baseStart_4528020 baseEnd_4528020 := by
    simpa [prefixWord, tailWord_4528020, baseEnd_4528020] using wordTrace_append hprefix tailTrace_4528020
  have hstable : (prefixWord ++ tailWord_4528020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528020).length < 2 ^ (prefixWord ++ tailWord_4528020).sum := by decide
  have hdescent : baseEnd_4528020 < baseStart_4528020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528097 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 3, 1, 3]
def baseStart_4528097 : Nat := 118140960795 + 4528097 * 2 ^ 59
def prefixEnd_4528097 : Nat := 4983230072969 + 3 ^ 40 * 4528097 * 2
def baseEnd_4528097 : Nat := 2325090211181875533363167

theorem tailTrace_4528097 : CollatzResearch.WordTrace tailWord_4528097 prefixEnd_4528097 2325090211181875533363167 := by
  unfold tailWord_4528097
  simp only [CollatzResearch.WordTrace]
  refine ⟨165153265476485381244174545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110102176984323587496116363 165153265476485381244174545)
  ·
    refine ⟨123864949107364035933130909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165153265476485381244174545 123864949107364035933130909)
    ·
      refine ⟨46449355915261513474924091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123864949107364035933130909 46449355915261513474924091)
      ·
        refine ⟨69674033872892270212386137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46449355915261513474924091 69674033872892270212386137)
        ·
          refine ⟨52255525404669202659289603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69674033872892270212386137 52255525404669202659289603)
          ·
            refine ⟨78383288107003803988934405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52255525404669202659289603 78383288107003803988934405)
            ·
              refine ⟨14696866520063213247925201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78383288107003803988934405 14696866520063213247925201)
              ·
                refine ⟨11022649890047409935943901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14696866520063213247925201 11022649890047409935943901)
                ·
                  refine ⟨4133493708767778725978963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11022649890047409935943901 4133493708767778725978963)
                  ·
                    refine ⟨6200240563151668088968445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4133493708767778725978963 6200240563151668088968445)
                    ·
                      refine ⟨2325090211181875533363167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6200240563151668088968445 2325090211181875533363167)
                      ·
                        rfl

theorem cell23_4528097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_4528097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528097 prefixEnd_4528097 := by exact prefixLift 4528097
  have htrace : WordTrace (prefixWord ++ tailWord_4528097) baseStart_4528097 baseEnd_4528097 := by
    simpa [prefixWord, tailWord_4528097, baseEnd_4528097] using wordTrace_append hprefix tailTrace_4528097
  have hstable : (prefixWord ++ tailWord_4528097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528097).length < 2 ^ (prefixWord ++ tailWord_4528097).sum := by decide
  have hdescent : baseEnd_4528097 < baseStart_4528097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528140 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 1, 1, 5]
def baseStart_4528140 : Nat := 118140960795 + 4528140 * 2 ^ 59
def prefixEnd_4528140 : Nat := 4983230072969 + 3 ^ 40 * 4528140 * 2
def baseEnd_4528140 : Nat := 2325112290850018865125469

theorem tailTrace_4528140 : CollatzResearch.WordTrace tailWord_4528140 prefixEnd_4528140 2325112290850018865125469 := by
  unfold tailWord_4528140
  simp only [CollatzResearch.WordTrace]
  refine ⟨82577416907664799793994937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110103222543553066391993249 82577416907664799793994937)
  ·
    refine ⟨61933062680748599845496203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82577416907664799793994937 61933062680748599845496203)
    ·
      refine ⟨92899594021122899768244305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61933062680748599845496203 92899594021122899768244305)
      ·
        refine ⟨69674695515842174826183229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92899594021122899768244305 69674695515842174826183229)
        ·
          refine ⟨26128010818440815559818711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69674695515842174826183229 26128010818440815559818711)
          ·
            refine ⟨39192016227661223339728067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26128010818440815559818711 39192016227661223339728067)
            ·
              refine ⟨58788024341491835009592101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39192016227661223339728067 58788024341491835009592101)
              ·
                refine ⟨11022754564029719064298519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58788024341491835009592101 11022754564029719064298519)
                ·
                  refine ⟨16534131846044578596447779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11022754564029719064298519 16534131846044578596447779)
                  ·
                    refine ⟨24801197769066867894671669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16534131846044578596447779 24801197769066867894671669)
                    ·
                      refine ⟨2325112290850018865125469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24801197769066867894671669 2325112290850018865125469)
                      ·
                        rfl

theorem cell23_4528140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_4528140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528140 prefixEnd_4528140 := by exact prefixLift 4528140
  have htrace : WordTrace (prefixWord ++ tailWord_4528140) baseStart_4528140 baseEnd_4528140 := by
    simpa [prefixWord, tailWord_4528140, baseEnd_4528140] using wordTrace_append hprefix tailTrace_4528140
  have hstable : (prefixWord ++ tailWord_4528140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528140).length < 2 ^ (prefixWord ++ tailWord_4528140).sum := by decide
  have hdescent : baseEnd_4528140 < baseStart_4528140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528151 : List Nat := [1, 1, 3, 5, 3, 1, 1, 2, 1, 5]
def baseStart_4528151 : Nat := 118140960795 + 4528151 * 2 ^ 59
def prefixEnd_4528151 : Nat := 4983230072969 + 3 ^ 40 * 4528151 * 2
def baseEnd_4528151 : Nat := 775039313045739440695973

theorem tailTrace_4528151 : CollatzResearch.WordTrace tailWord_4528151 prefixEnd_4528151 775039313045739440695973 := by
  unfold tailWord_4528151
  simp only [CollatzResearch.WordTrace]
  refine ⟨165155235018289748466640307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110103490012193165644426871 165155235018289748466640307)
  ·
    refine ⟨247732852527434622699960461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165155235018289748466640307 247732852527434622699960461)
    ·
      refine ⟨92899819697787983512485173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247732852527434622699960461 92899819697787983512485173)
      ·
        refine ⟨8709358096667623454295485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92899819697787983512485173 8709358096667623454295485)
        ·
          refine ⟨3266009286250358795360807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8709358096667623454295485 3266009286250358795360807)
          ·
            refine ⟨4899013929375538193041211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3266009286250358795360807 4899013929375538193041211)
            ·
              refine ⟨7348520894063307289561817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4899013929375538193041211 7348520894063307289561817)
              ·
                refine ⟨5511390670547480467171363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7348520894063307289561817 5511390670547480467171363)
                ·
                  refine ⟨8267086005821220700757045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5511390670547480467171363 8267086005821220700757045)
                  ·
                    refine ⟨775039313045739440695973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8267086005821220700757045 775039313045739440695973)
                    ·
                      rfl

theorem cell23_4528151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 1, 5].length) (baseStart_4528151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528151 prefixEnd_4528151 := by exact prefixLift 4528151
  have htrace : WordTrace (prefixWord ++ tailWord_4528151) baseStart_4528151 baseEnd_4528151 := by
    simpa [prefixWord, tailWord_4528151, baseEnd_4528151] using wordTrace_append hprefix tailTrace_4528151
  have hstable : (prefixWord ++ tailWord_4528151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528151).length < 2 ^ (prefixWord ++ tailWord_4528151).sum := by decide
  have hdescent : baseEnd_4528151 < baseStart_4528151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528154 : List Nat := [3, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4]
def baseStart_4528154 : Nat := 118140960795 + 4528154 * 2 ^ 59
def prefixEnd_4528154 : Nat := 4983230072969 + 3 ^ 40 * 4528154 * 2
def baseEnd_4528154 : Nat := 2325119479579181810350405

theorem tailTrace_4528154 : CollatzResearch.WordTrace tailWord_4528154 prefixEnd_4528154 2325119479579181810350405 := by
  unfold tailWord_4528154
  simp only [CollatzResearch.WordTrace]
  refine ⟨41288836109319719994749879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110103562958185919985999677 41288836109319719994749879)
  ·
    refine ⟨61933254163979579992124819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41288836109319719994749879 61933254163979579992124819)
    ·
      refine ⟨92899881245969369988187229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61933254163979579992124819 92899881245969369988187229)
      ·
        refine ⟨34837455467238513745570211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92899881245969369988187229 34837455467238513745570211)
        ·
          refine ⟨52256183200857770618355317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34837455467238513745570211 52256183200857770618355317)
          ·
            refine ⟨4899017175080415995470811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52256183200857770618355317 4899017175080415995470811)
            ·
              refine ⟨7348525762620623993206217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4899017175080415995470811 7348525762620623993206217)
              ·
                refine ⟨5511394321965467994904663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7348525762620623993206217 5511394321965467994904663)
                ·
                  refine ⟨8267091482948201992356995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5511394321965467994904663 8267091482948201992356995)
                  ·
                    refine ⟨12400637224422302988535493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8267091482948201992356995 12400637224422302988535493)
                    ·
                      refine ⟨2325119479579181810350405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12400637224422302988535493 2325119479579181810350405)
                      ·
                        rfl

theorem cell23_4528154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_4528154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528154 prefixEnd_4528154 := by exact prefixLift 4528154
  have htrace : WordTrace (prefixWord ++ tailWord_4528154) baseStart_4528154 baseEnd_4528154 := by
    simpa [prefixWord, tailWord_4528154, baseEnd_4528154] using wordTrace_append hprefix tailTrace_4528154
  have hstable : (prefixWord ++ tailWord_4528154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528154).length < 2 ^ (prefixWord ++ tailWord_4528154).sum := by decide
  have hdescent : baseEnd_4528154 < baseStart_4528154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528174 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_4528174 : Nat := 118140960795 + 4528174 * 2 ^ 59
def prefixEnd_4528174 : Nat := 4983230072969 + 3 ^ 40 * 4528174 * 2
def baseEnd_4528174 : Nat := 2325129749192271732100313

theorem tailTrace_4528174 : CollatzResearch.WordTrace tailWord_4528174 prefixEnd_4528174 2325129749192271732100313 := by
  unfold tailWord_4528174
  simp only [CollatzResearch.WordTrace]
  refine ⟨20644509237150802924340947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110104049264804282263151717 20644509237150802924340947)
  ·
    refine ⟨30966763855726204386511421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20644509237150802924340947 30966763855726204386511421)
    ·
      refine ⟨11612536445897326644941783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30966763855726204386511421 11612536445897326644941783)
      ·
        refine ⟨17418804668845989967412675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11612536445897326644941783 17418804668845989967412675)
        ·
          refine ⟨26128207003268984951119013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17418804668845989967412675 26128207003268984951119013)
          ·
            refine ⟨4899038813112934678334815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26128207003268984951119013 4899038813112934678334815)
            ·
              refine ⟨7348558219669402017502223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4899038813112934678334815 7348558219669402017502223)
              ·
                refine ⟨11022837329504103026253335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7348558219669402017502223 11022837329504103026253335)
                ·
                  refine ⟨16534255994256154539380003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11022837329504103026253335 16534255994256154539380003)
                  ·
                    refine ⟨24801383991384231809070005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16534255994256154539380003 24801383991384231809070005)
                    ·
                      refine ⟨2325129749192271732100313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24801383991384231809070005 2325129749192271732100313)
                      ·
                        rfl

theorem cell23_4528174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_4528174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528174 prefixEnd_4528174 := by exact prefixLift 4528174
  have htrace : WordTrace (prefixWord ++ tailWord_4528174) baseStart_4528174 baseEnd_4528174 := by
    simpa [prefixWord, tailWord_4528174, baseEnd_4528174] using wordTrace_append hprefix tailTrace_4528174
  have hstable : (prefixWord ++ tailWord_4528174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528174).length < 2 ^ (prefixWord ++ tailWord_4528174).sum := by decide
  have hdescent : baseEnd_4528174 < baseStart_4528174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528204 : List Nat := [2, 2, 1, 3, 1, 1, 4, 3, 2, 1, 3]
def baseStart_4528204 : Nat := 118140960795 + 4528204 * 2 ^ 59
def prefixEnd_4528204 : Nat := 4983230072969 + 3 ^ 40 * 4528204 * 2
def baseEnd_4528204 : Nat := 2325145153611906614725175

theorem tailTrace_4528204 : CollatzResearch.WordTrace tailWord_4528204 prefixEnd_4528204 2325145153611906614725175 := by
  unfold tailWord_4528204
  simp only [CollatzResearch.WordTrace]
  refine ⟨82578584043548869259159833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110104778724731825678879777 82578584043548869259159833)
  ·
    refine ⟨61933938032661651944369875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82578584043548869259159833 61933938032661651944369875)
    ·
      refine ⟨92900907048992477916554813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61933938032661651944369875 92900907048992477916554813)
      ·
        refine ⟨34837840143372179218708055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92900907048992477916554813 34837840143372179218708055)
        ·
          refine ⟨52256760215058268828062083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34837840143372179218708055 52256760215058268828062083)
          ·
            refine ⟨78385140322587403242093125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52256760215058268828062083 78385140322587403242093125)
            ·
              refine ⟨14697213810485138107892461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78385140322587403242093125 14697213810485138107892461)
              ·
                refine ⟨5511455178931926790459673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14697213810485138107892461 5511455178931926790459673)
                ·
                  refine ⟨4133591384198945092844755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5511455178931926790459673 4133591384198945092844755)
                  ·
                    refine ⟨6200387076298417639267133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4133591384198945092844755 6200387076298417639267133)
                    ·
                      refine ⟨2325145153611906614725175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6200387076298417639267133 2325145153611906614725175)
                      ·
                        rfl

theorem cell23_4528204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_4528204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528204 prefixEnd_4528204 := by exact prefixLift 4528204
  have htrace : WordTrace (prefixWord ++ tailWord_4528204) baseStart_4528204 baseEnd_4528204 := by
    simpa [prefixWord, tailWord_4528204, baseEnd_4528204] using wordTrace_append hprefix tailTrace_4528204
  have hstable : (prefixWord ++ tailWord_4528204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528204).length < 2 ^ (prefixWord ++ tailWord_4528204).sum := by decide
  have hdescent : baseEnd_4528204 < baseStart_4528204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528222 : List Nat := [4, 4, 1, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_4528222 : Nat := 118140960795 + 4528222 * 2 ^ 59
def prefixEnd_4528222 : Nat := 4983230072969 + 3 ^ 40 * 4528222 * 2
def baseEnd_4528222 : Nat := 2325154396263687544300093

theorem tailTrace_4528222 : CollatzResearch.WordTrace tailWord_4528222 prefixEnd_4528222 2325154396263687544300093 := by
  unfold tailWord_4528222
  simp only [CollatzResearch.WordTrace]
  refine ⟨20644728075129065949059365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110105216400688351728316613 20644728075129065949059365)
  ·
    refine ⟨3870886514086699865448631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20644728075129065949059365 3870886514086699865448631)
    ·
      refine ⟨5806329771130049798172947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3870886514086699865448631 5806329771130049798172947)
      ·
        refine ⟨8709494656695074697259421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5806329771130049798172947 8709494656695074697259421)
        ·
          refine ⟨3266060496260653011472283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8709494656695074697259421 3266060496260653011472283)
          ·
            refine ⟨4899090744390979517208425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3266060496260653011472283 4899090744390979517208425)
            ·
              refine ⟨3674318058293234637906319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4899090744390979517208425 3674318058293234637906319)
              ·
                refine ⟨5511477087439851956859479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3674318058293234637906319 5511477087439851956859479)
                ·
                  refine ⟨8267215631159777935289219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5511477087439851956859479 8267215631159777935289219)
                  ·
                    refine ⟨12400823446739666902933829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8267215631159777935289219 12400823446739666902933829)
                    ·
                      refine ⟨2325154396263687544300093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12400823446739666902933829 2325154396263687544300093)
                      ·
                        rfl

theorem cell23_4528222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_4528222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528222 prefixEnd_4528222 := by exact prefixLift 4528222
  have htrace : WordTrace (prefixWord ++ tailWord_4528222) baseStart_4528222 baseEnd_4528222 := by
    simpa [prefixWord, tailWord_4528222, baseEnd_4528222] using wordTrace_append hprefix tailTrace_4528222
  have hstable : (prefixWord ++ tailWord_4528222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528222).length < 2 ^ (prefixWord ++ tailWord_4528222).sum := by decide
  have hdescent : baseEnd_4528222 < baseStart_4528222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528261 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 1, 4, 2]
def baseStart_4528261 : Nat := 118140960795 + 4528261 * 2 ^ 59
def prefixEnd_4528261 : Nat := 4983230072969 + 3 ^ 40 * 4528261 * 2
def baseEnd_4528261 : Nat := 2325174422009212891712413

theorem tailTrace_4528261 : CollatzResearch.WordTrace tailWord_4528261 prefixEnd_4528261 2325174422009212891712413 := by
  unfold tailWord_4528261
  simp only [CollatzResearch.WordTrace]
  refine ⟨165159247047891237253144637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110106164698594158168763091 165159247047891237253144637)
  ·
    refine ⟨61934717642959213969929239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165159247047891237253144637 61934717642959213969929239)
    ·
      refine ⟨92902076464438820954893859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61934717642959213969929239 92902076464438820954893859)
      ·
        refine ⟨139353114696658231432340789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92902076464438820954893859 139353114696658231432340789)
        ·
          refine ⟨13064354502811709196781949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139353114696658231432340789 13064354502811709196781949)
          ·
            refine ⟨4899132938554390948793231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13064354502811709196781949 4899132938554390948793231)
            ·
              refine ⟨7348699407831586423189847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4899132938554390948793231 7348699407831586423189847)
              ·
                refine ⟨11023049111747379634784771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7348699407831586423189847 11023049111747379634784771)
                ·
                  refine ⟨16534573667621069452177157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11023049111747379634784771 16534573667621069452177157)
                  ·
                    refine ⟨3100232562678950522283217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16534573667621069452177157 3100232562678950522283217)
                    ·
                      refine ⟨2325174422009212891712413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3100232562678950522283217 2325174422009212891712413)
                      ·
                        rfl

theorem cell23_4528261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 4, 2].length) (baseStart_4528261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528261 prefixEnd_4528261 := by exact prefixLift 4528261
  have htrace : WordTrace (prefixWord ++ tailWord_4528261) baseStart_4528261 baseEnd_4528261 := by
    simpa [prefixWord, tailWord_4528261, baseEnd_4528261] using wordTrace_append hprefix tailTrace_4528261
  have hstable : (prefixWord ++ tailWord_4528261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528261).length < 2 ^ (prefixWord ++ tailWord_4528261).sum := by decide
  have hdescent : baseEnd_4528261 < baseStart_4528261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528317 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_4528317 : Nat := 118140960795 + 4528317 * 2 ^ 59
def prefixEnd_4528317 : Nat := 4983230072969 + 3 ^ 40 * 4528317 * 2
def baseEnd_4528317 : Nat := 2325203176925864672612155

theorem tailTrace_4528317 : CollatzResearch.WordTrace tailWord_4528317 prefixEnd_4528317 2325203176925864672612155 := by
  unfold tailWord_4528317
  simp only [CollatzResearch.WordTrace]
  refine ⟨165161289535688358817183205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110107526357125572544788803 165161289535688358817183205)
  ·
    refine ⟨30967741787941567278221851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165161289535688358817183205 30967741787941567278221851)
    ·
      refine ⟨46451612681912350917332777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30967741787941567278221851 46451612681912350917332777)
      ·
        refine ⟨34838709511434263187999583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46451612681912350917332777 34838709511434263187999583)
        ·
          refine ⟨52258064267151394781999375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34838709511434263187999583 52258064267151394781999375)
          ·
            refine ⟨78387096400727092172999063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52258064267151394781999375 78387096400727092172999063)
            ·
              refine ⟨117580644601090638259498595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78387096400727092172999063 117580644601090638259498595)
              ·
                refine ⟨176370966901635957389247893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117580644601090638259498595 176370966901635957389247893)
                ·
                  refine ⟨8267389073514185502620995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 176370966901635957389247893 8267389073514185502620995)
                  ·
                    refine ⟨12401083610271278253931493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8267389073514185502620995 12401083610271278253931493)
                    ·
                      refine ⟨2325203176925864672612155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12401083610271278253931493 2325203176925864672612155)
                      ·
                        rfl

theorem cell23_4528317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_4528317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528317 prefixEnd_4528317 := by exact prefixLift 4528317
  have htrace : WordTrace (prefixWord ++ tailWord_4528317) baseStart_4528317 baseEnd_4528317 := by
    simpa [prefixWord, tailWord_4528317, baseEnd_4528317] using wordTrace_append hprefix tailTrace_4528317
  have hstable : (prefixWord ++ tailWord_4528317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528317).length < 2 ^ (prefixWord ++ tailWord_4528317).sum := by decide
  have hdescent : baseEnd_4528317 < baseStart_4528317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528334 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_4528334 : Nat := 118140960795 + 4528334 * 2 ^ 59
def prefixEnd_4528334 : Nat := 4983230072969 + 3 ^ 40 * 4528334 * 2
def baseEnd_4528334 : Nat := 2325211906096991106099577

theorem tailTrace_4528334 : CollatzResearch.WordTrace tailWord_4528334 prefixEnd_4528334 2325211906096991106099577 := by
  unfold tailWord_4528334
  simp only [CollatzResearch.WordTrace]
  refine ⟨20645238697078346340069007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110107939717751180480368037 20645238697078346340069007)
  ·
    refine ⟨30967858045617519510103511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20645238697078346340069007 30967858045617519510103511)
    ·
      refine ⟨46451787068426279265155267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30967858045617519510103511 46451787068426279265155267)
      ·
        refine ⟨69677680602639418897732901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46451787068426279265155267 69677680602639418897732901)
        ·
          refine ⟨13064565112994891043324919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69677680602639418897732901 13064565112994891043324919)
          ·
            refine ⟨19596847669492336564987379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13064565112994891043324919 19596847669492336564987379)
            ·
              refine ⟨29395271504238504847481069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19596847669492336564987379 29395271504238504847481069)
              ·
                refine ⟨11023226814089439317805401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29395271504238504847481069 11023226814089439317805401)
                ·
                  refine ⟨8267420110567079488354051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11023226814089439317805401 8267420110567079488354051)
                  ·
                    refine ⟨12401130165850619232531077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8267420110567079488354051 12401130165850619232531077)
                    ·
                      refine ⟨2325211906096991106099577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12401130165850619232531077 2325211906096991106099577)
                      ·
                        rfl

theorem cell23_4528334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_4528334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528334 prefixEnd_4528334 := by exact prefixLift 4528334
  have htrace : WordTrace (prefixWord ++ tailWord_4528334) baseStart_4528334 baseEnd_4528334 := by
    simpa [prefixWord, tailWord_4528334, baseEnd_4528334] using wordTrace_append hprefix tailTrace_4528334
  have hstable : (prefixWord ++ tailWord_4528334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528334).length < 2 ^ (prefixWord ++ tailWord_4528334).sum := by decide
  have hdescent : baseEnd_4528334 < baseStart_4528334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528337 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 1, 4, 3]
def baseStart_4528337 : Nat := 118140960795 + 4528337 * 2 ^ 59
def prefixEnd_4528337 : Nat := 4983230072969 + 3 ^ 40 * 4528337 * 2
def baseEnd_4528337 : Nat := 2325213446538954594362063

theorem tailTrace_4528337 : CollatzResearch.WordTrace tailWord_4528337 prefixEnd_4528337 2325213446538954594362063 := by
  unfold tailWord_4528337
  simp only [CollatzResearch.WordTrace]
  refine ⟨165162018995615902232911265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110108012663743934821940843 165162018995615902232911265)
  ·
    refine ⟨123871514246711926674683449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165162018995615902232911265 123871514246711926674683449)
    ·
      refine ⟨92903635685033945006012587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123871514246711926674683449 92903635685033945006012587)
      ·
        refine ⟨139355453527550917509018881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92903635685033945006012587 139355453527550917509018881)
        ·
          refine ⟨104516590145663188131764161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139355453527550917509018881 104516590145663188131764161)
          ·
            refine ⟨78387442609247391098823121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104516590145663188131764161 78387442609247391098823121)
            ·
              refine ⟨58790581956935543324117341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78387442609247391098823121 58790581956935543324117341)
              ·
                refine ⟨22046468233850828746544003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58790581956935543324117341 22046468233850828746544003)
                ·
                  refine ⟨33069702350776243119816005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22046468233850828746544003 33069702350776243119816005)
                  ·
                    refine ⟨6200569190770545584965501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33069702350776243119816005 6200569190770545584965501)
                    ·
                      refine ⟨2325213446538954594362063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6200569190770545584965501 2325213446538954594362063)
                      ·
                        rfl

theorem cell23_4528337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_4528337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528337 prefixEnd_4528337 := by exact prefixLift 4528337
  have htrace : WordTrace (prefixWord ++ tailWord_4528337) baseStart_4528337 baseEnd_4528337 := by
    simpa [prefixWord, tailWord_4528337, baseEnd_4528337] using wordTrace_append hprefix tailTrace_4528337
  have hstable : (prefixWord ++ tailWord_4528337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528337).length < 2 ^ (prefixWord ++ tailWord_4528337).sum := by decide
  have hdescent : baseEnd_4528337 < baseStart_4528337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528374 : List Nat := [5, 1, 1, 1, 1, 1, 4, 3, 6]
def baseStart_4528374 : Nat := 118140960795 + 4528374 * 2 ^ 59
def prefixEnd_4528374 : Nat := 4983230072969 + 3 ^ 40 * 4528374 * 2
def baseEnd_4528374 : Nat := 258359160591463438844377

theorem tailTrace_4528374 : CollatzResearch.WordTrace tailWord_4528374 prefixEnd_4528374 258359160591463438844377 := by
  unfold tailWord_4528374
  simp only [CollatzResearch.WordTrace]
  refine ⟨10322710531030116097000511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110108912330987905034672117 10322710531030116097000511)
  ·
    refine ⟨15484065796545174145500767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10322710531030116097000511 15484065796545174145500767)
    ·
      refine ⟨23226098694817761218251151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15484065796545174145500767 23226098694817761218251151)
      ·
        refine ⟨34839148042226641827376727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23226098694817761218251151 34839148042226641827376727)
        ·
          refine ⟨52258722063339962741065091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34839148042226641827376727 52258722063339962741065091)
          ·
            refine ⟨78388083095009944111597637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52258722063339962741065091 78388083095009944111597637)
            ·
              refine ⟨14697765580314364520924557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78388083095009944111597637 14697765580314364520924557)
              ·
                refine ⟨5511662092617886695346709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14697765580314364520924557 5511662092617886695346709)
                ·
                  refine ⟨258359160591463438844377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5511662092617886695346709 258359160591463438844377)
                  ·
                    rfl

theorem cell23_4528374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_4528374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528374 prefixEnd_4528374 := by exact prefixLift 4528374
  have htrace : WordTrace (prefixWord ++ tailWord_4528374) baseStart_4528374 baseEnd_4528374 := by
    simpa [prefixWord, tailWord_4528374, baseEnd_4528374] using wordTrace_append hprefix tailTrace_4528374
  have hstable : (prefixWord ++ tailWord_4528374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528374).length < 2 ^ (prefixWord ++ tailWord_4528374).sum := by decide
  have hdescent : baseEnd_4528374 < baseStart_4528374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528384 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 5, 1, 3]
def baseStart_4528384 : Nat := 118140960795 + 4528384 * 2 ^ 59
def prefixEnd_4528384 : Nat := 4983230072969 + 3 ^ 40 * 4528384 * 2
def baseEnd_4528384 : Nat := 2325237580129715910474347

theorem tailTrace_4528384 : CollatzResearch.WordTrace tailWord_4528384 prefixEnd_4528384 2325237580129715910474347 := by
  unfold tailWord_4528384
  simp only [CollatzResearch.WordTrace]
  refine ⟨82581866613222814629936103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110109155484297086173248137 82581866613222814629936103)
  ·
    refine ⟨123872799919834221944904155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82581866613222814629936103 123872799919834221944904155)
    ·
      refine ⟨185809199879751332917356233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123872799919834221944904155 185809199879751332917356233)
      ·
        refine ⟨139356899909813499688017175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185809199879751332917356233 139356899909813499688017175)
        ·
          refine ⟨209035349864720249532025763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139356899909813499688017175 209035349864720249532025763)
          ·
            refine ⟨313553024797080374298038645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209035349864720249532025763 313553024797080374298038645)
            ·
              refine ⟨29395596074726285090441123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 313553024797080374298038645 29395596074726285090441123)
              ·
                refine ⟨44093394112089427635661685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29395596074726285090441123 44093394112089427635661685)
                ·
                  refine ⟨4133755698008383840843283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44093394112089427635661685 4133755698008383840843283)
                  ·
                    refine ⟨6200633547012575761264925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4133755698008383840843283 6200633547012575761264925)
                    ·
                      refine ⟨2325237580129715910474347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6200633547012575761264925 2325237580129715910474347)
                      ·
                        rfl

theorem cell23_4528384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 5, 1, 3].length) (baseStart_4528384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528384 prefixEnd_4528384 := by exact prefixLift 4528384
  have htrace : WordTrace (prefixWord ++ tailWord_4528384) baseStart_4528384 baseEnd_4528384 := by
    simpa [prefixWord, tailWord_4528384, baseEnd_4528384] using wordTrace_append hprefix tailTrace_4528384
  have hstable : (prefixWord ++ tailWord_4528384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528384).length < 2 ^ (prefixWord ++ tailWord_4528384).sum := by decide
  have hdescent : baseEnd_4528384 < baseStart_4528384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528387 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 3, 5]
def baseStart_4528387 : Nat := 118140960795 + 4528387 * 2 ^ 59
def prefixEnd_4528387 : Nat := 4983230072969 + 3 ^ 40 * 4528387 * 2
def baseEnd_4528387 : Nat := 775079706857226466245611

theorem tailTrace_4528387 : CollatzResearch.WordTrace tailWord_4528387 prefixEnd_4528387 775079706857226466245611 := by
  unfold tailWord_4528387
  simp only [CollatzResearch.WordTrace]
  refine ⟨165163842645434760772231415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110109228430289840514820943 165163842645434760772231415)
  ·
    refine ⟨247745763968152141158347123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165163842645434760772231415 247745763968152141158347123)
    ·
      refine ⟨371618645952228211737520685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247745763968152141158347123 371618645952228211737520685)
      ·
        refine ⟨139356992232085579401570257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 371618645952228211737520685 139356992232085579401570257)
        ·
          refine ⟨104517744174064184551177693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139356992232085579401570257 104517744174064184551177693)
          ·
            refine ⟨39194154065274069206691635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104517744174064184551177693 39194154065274069206691635)
            ·
              refine ⟨58791231097911103810037453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39194154065274069206691635 58791231097911103810037453)
              ·
                refine ⟨22046711661716663928764045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58791231097911103810037453 22046711661716663928764045)
                ·
                  refine ⟨8267516873143748973286517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22046711661716663928764045 8267516873143748973286517)
                  ·
                    refine ⟨775079706857226466245611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8267516873143748973286517 775079706857226466245611)
                    ·
                      rfl

theorem cell23_4528387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 5].length) (baseStart_4528387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528387 prefixEnd_4528387 := by exact prefixLift 4528387
  have htrace : WordTrace (prefixWord ++ tailWord_4528387) baseStart_4528387 baseEnd_4528387 := by
    simpa [prefixWord, tailWord_4528387, baseEnd_4528387] using wordTrace_append hprefix tailTrace_4528387
  have hstable : (prefixWord ++ tailWord_4528387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528387).length < 2 ^ (prefixWord ++ tailWord_4528387).sum := by decide
  have hdescent : baseEnd_4528387 < baseStart_4528387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528388 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_4528388 : Nat := 118140960795 + 4528388 * 2 ^ 59
def prefixEnd_4528388 : Nat := 4983230072969 + 3 ^ 40 * 4528388 * 2
def baseEnd_4528388 : Nat := 2325239634052333894824329

theorem tailTrace_4528388 : CollatzResearch.WordTrace tailWord_4528388 prefixEnd_4528388 2325239634052333894824329 := by
  unfold tailWord_4528388
  simp only [CollatzResearch.WordTrace]
  refine ⟨82581939559215568971508909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110109252745620758628678545 82581939559215568971508909)
  ·
    refine ⟨30968227334705838364315841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82581939559215568971508909 30968227334705838364315841)
    ·
      refine ⟨23226170501029378773236881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30968227334705838364315841 23226170501029378773236881)
      ·
        refine ⟨17419627875772034079927661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23226170501029378773236881 17419627875772034079927661)
        ·
          refine ⟨6532360453414512779972873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17419627875772034079927661 6532360453414512779972873)
          ·
            refine ⟨4899270340060884584979655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6532360453414512779972873 4899270340060884584979655)
            ·
              refine ⟨7348905510091326877469483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4899270340060884584979655 7348905510091326877469483)
              ·
                refine ⟨11023358265136990316204225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7348905510091326877469483 11023358265136990316204225)
                ·
                  refine ⟨8267518698852742737153169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11023358265136990316204225 8267518698852742737153169)
                  ·
                    refine ⟨6200639024139557052864877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8267518698852742737153169 6200639024139557052864877)
                    ·
                      refine ⟨2325239634052333894824329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6200639024139557052864877 2325239634052333894824329)
                      ·
                        rfl

theorem cell23_4528388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_4528388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528388 prefixEnd_4528388 := by exact prefixLift 4528388
  have htrace : WordTrace (prefixWord ++ tailWord_4528388) baseStart_4528388 baseEnd_4528388 := by
    simpa [prefixWord, tailWord_4528388, baseEnd_4528388] using wordTrace_append hprefix tailTrace_4528388
  have hstable : (prefixWord ++ tailWord_4528388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528388).length < 2 ^ (prefixWord ++ tailWord_4528388).sum := by decide
  have hdescent : baseEnd_4528388 < baseStart_4528388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528417 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 3, 6]
def baseStart_4528417 : Nat := 118140960795 + 4528417 * 2 ^ 59
def prefixEnd_4528417 : Nat := 4983230072969 + 3 ^ 40 * 4528417 * 2
def baseEnd_4528417 : Nat := 775084841663771427120565

theorem tailTrace_4528417 : CollatzResearch.WordTrace tailWord_4528417 prefixEnd_4528417 775084841663771427120565 := by
  unfold tailWord_4528417
  simp only [CollatzResearch.WordTrace]
  refine ⟨165164936835326075895823505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110109957890217383930549003 165164936835326075895823505)
  ·
    refine ⟨123873702626494556921867629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165164936835326075895823505 123873702626494556921867629)
    ·
      refine ⟨46452638484935458845700361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123873702626494556921867629 46452638484935458845700361)
      ·
        refine ⟨34839478863701594134275271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46452638484935458845700361 34839478863701594134275271)
        ·
          refine ⟨52259218295552391201412907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34839478863701594134275271 52259218295552391201412907)
          ·
            refine ⟨78388827443328586802119361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52259218295552391201412907 78388827443328586802119361)
            ·
              refine ⟨58791620582496440101589521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78388827443328586802119361 58791620582496440101589521)
              ·
                refine ⟨44093715436872330076192141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58791620582496440101589521 44093715436872330076192141)
                ·
                  refine ⟨16535143288827123778572053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44093715436872330076192141 16535143288827123778572053)
                  ·
                    refine ⟨775084841663771427120565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16535143288827123778572053 775084841663771427120565)
                    ·
                      rfl

theorem cell23_4528417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_4528417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528417 prefixEnd_4528417 := by exact prefixLift 4528417
  have htrace : WordTrace (prefixWord ++ tailWord_4528417) baseStart_4528417 baseEnd_4528417 := by
    simpa [prefixWord, tailWord_4528417, baseEnd_4528417] using wordTrace_append hprefix tailTrace_4528417
  have hstable : (prefixWord ++ tailWord_4528417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528417).length < 2 ^ (prefixWord ++ tailWord_4528417).sum := by decide
  have hdescent : baseEnd_4528417 < baseStart_4528417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528418 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_4528418 : Nat := 118140960795 + 4528418 * 2 ^ 59
def prefixEnd_4528418 : Nat := 4983230072969 + 3 ^ 40 * 4528418 * 2
def baseEnd_4528418 : Nat := 2325255038471968777449191

theorem tailTrace_4528418 : CollatzResearch.WordTrace tailWord_4528418 prefixEnd_4528418 2325255038471968777449191 := by
  unfold tailWord_4528418
  simp only [CollatzResearch.WordTrace]
  refine ⟨41291243327080613266652477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110109982205548302044406605 41291243327080613266652477)
  ·
    refine ⟨15484216247655229974994679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41291243327080613266652477 15484216247655229974994679)
    ·
      refine ⟨23226324371482844962492019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15484216247655229974994679 23226324371482844962492019)
      ·
        refine ⟨34839486557224267443738029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23226324371482844962492019 34839486557224267443738029)
        ·
          refine ⟨13064807458959100291401761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34839486557224267443738029 13064807458959100291401761)
          ·
            refine ⟨9798605594219325218551321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13064807458959100291401761 9798605594219325218551321)
            ·
              refine ⟨7348954195664493913913491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9798605594219325218551321 7348954195664493913913491)
              ·
                refine ⟨11023431293496740870870237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7348954195664493913913491 11023431293496740870870237)
                ·
                  refine ⟨4133786735061277826576339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11023431293496740870870237 4133786735061277826576339)
                  ·
                    refine ⟨6200680102591916739864509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4133786735061277826576339 6200680102591916739864509)
                    ·
                      refine ⟨2325255038471968777449191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6200680102591916739864509 2325255038471968777449191)
                      ·
                        rfl

theorem cell23_4528418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_4528418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528418 prefixEnd_4528418 := by exact prefixLift 4528418
  have htrace : WordTrace (prefixWord ++ tailWord_4528418) baseStart_4528418 baseEnd_4528418 := by
    simpa [prefixWord, tailWord_4528418, baseEnd_4528418] using wordTrace_append hprefix tailTrace_4528418
  have hstable : (prefixWord ++ tailWord_4528418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528418).length < 2 ^ (prefixWord ++ tailWord_4528418).sum := by decide
  have hdescent : baseEnd_4528418 < baseStart_4528418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528441 : List Nat := [1, 2, 1, 6, 1, 1, 1, 4, 1, 1, 4]
def baseStart_4528441 : Nat := 118140960795 + 4528441 * 2 ^ 59
def prefixEnd_4528441 : Nat := 4983230072969 + 3 ^ 40 * 4528441 * 2
def baseEnd_4528441 : Nat := 2325266848527022187461585

theorem tailTrace_4528441 : CollatzResearch.WordTrace tailWord_4528441 prefixEnd_4528441 2325266848527022187461585 := by
  unfold tailWord_4528441
  simp only [CollatzResearch.WordTrace]
  refine ⟨165165812187239127994697177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110110541458159418663131451 165165812187239127994697177)
  ·
    refine ⟨123874359140429345996022883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165165812187239127994697177 123874359140429345996022883)
    ·
      refine ⟨185811538710644018994034325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123874359140429345996022883 185811538710644018994034325)
      ·
        refine ⟨8709915877061438390345359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 185811538710644018994034325 8709915877061438390345359)
        ·
          refine ⟨13064873815592157585518039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8709915877061438390345359 13064873815592157585518039)
          ·
            refine ⟨19597310723388236378277059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13064873815592157585518039 19597310723388236378277059)
            ·
              refine ⟨29395966085082354567415589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19597310723388236378277059 29395966085082354567415589)
              ·
                refine ⟨5511743640952941481390423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29395966085082354567415589 5511743640952941481390423)
                ·
                  refine ⟨8267615461429412222085635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5511743640952941481390423 8267615461429412222085635)
                  ·
                    refine ⟨12401423192144118333128453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8267615461429412222085635 12401423192144118333128453)
                    ·
                      refine ⟨2325266848527022187461585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12401423192144118333128453 2325266848527022187461585)
                      ·
                        rfl

theorem cell23_4528441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_4528441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528441 prefixEnd_4528441 := by exact prefixLift 4528441
  have htrace : WordTrace (prefixWord ++ tailWord_4528441) baseStart_4528441 baseEnd_4528441 := by
    simpa [prefixWord, tailWord_4528441, baseEnd_4528441] using wordTrace_append hprefix tailTrace_4528441
  have hstable : (prefixWord ++ tailWord_4528441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528441).length < 2 ^ (prefixWord ++ tailWord_4528441).sum := by decide
  have hdescent : baseEnd_4528441 < baseStart_4528441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528447 : List Nat := [1, 1, 2, 2, 4, 1, 3, 9]
def baseStart_4528447 : Nat := 118140960795 + 4528447 * 2 ^ 59
def prefixEnd_4528447 : Nat := 4983230072969 + 3 ^ 40 * 4528447 * 2
def baseEnd_4528447 : Nat := 86121108496701820888391

theorem tailTrace_4528447 : CollatzResearch.WordTrace tailWord_4528447 prefixEnd_4528447 86121108496701820888391 := by
  unfold tailWord_4528447
  simp only [CollatzResearch.WordTrace]
  refine ⟨165166031025217391019415595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110110687350144927346277063 165166031025217391019415595)
  ·
    refine ⟨247749046537826086529123393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165166031025217391019415595 247749046537826086529123393)
    ·
      refine ⟨185811784903369564896842545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247749046537826086529123393 185811784903369564896842545)
      ·
        refine ⟨139358838677527173672631909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185811784903369564896842545 139358838677527173672631909)
        ·
          refine ⟨26129782252036345063618483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139358838677527173672631909 26129782252036345063618483)
          ·
            refine ⟨39194673378054517595427725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26129782252036345063618483 39194673378054517595427725)
            ·
              refine ⟨14698002516770444098285397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39194673378054517595427725 14698002516770444098285397)
              ·
                refine ⟨86121108496701820888391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14698002516770444098285397 86121108496701820888391)
                ·
                  rfl

theorem cell23_4528447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 9].length) (baseStart_4528447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528447 prefixEnd_4528447 := by exact prefixLift 4528447
  have htrace : WordTrace (prefixWord ++ tailWord_4528447) baseStart_4528447 baseEnd_4528447 := by
    simpa [prefixWord, tailWord_4528447, baseEnd_4528447] using wordTrace_append hprefix tailTrace_4528447
  have hstable : (prefixWord ++ tailWord_4528447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528447).length < 2 ^ (prefixWord ++ tailWord_4528447).sum := by decide
  have hdescent : baseEnd_4528447 < baseStart_4528447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528491 : List Nat := [1, 1, 1, 1, 2, 2, 2, 7, 2, 1, 3]
def baseStart_4528491 : Nat := 118140960795 + 4528491 * 2 ^ 59
def prefixEnd_4528491 : Nat := 4983230072969 + 3 ^ 40 * 4528491 * 2
def baseEnd_4528491 : Nat := 2325292522559746991836355

theorem tailTrace_4528491 : CollatzResearch.WordTrace tailWord_4528491 prefixEnd_4528491 2325292522559746991836355 := by
  unfold tailWord_4528491
  simp only [CollatzResearch.WordTrace]
  refine ⟨165167635837057986534017327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110111757224705324356011551 165167635837057986534017327)
  ·
    refine ⟨247751453755586979801025991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165167635837057986534017327 247751453755586979801025991)
    ·
      refine ⟨371627180633380469701538987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247751453755586979801025991 371627180633380469701538987)
      ·
        refine ⟨557440770950070704552308481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371627180633380469701538987 557440770950070704552308481)
        ·
          refine ⟨418080578212553028414231361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557440770950070704552308481 418080578212553028414231361)
          ·
            refine ⟨313560433659414771310673521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418080578212553028414231361 313560433659414771310673521)
            ·
              refine ⟨235170325244561078483005141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313560433659414771310673521 235170325244561078483005141)
              ·
                refine ⟨5511804497919400276945433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 235170325244561078483005141 5511804497919400276945433)
                ·
                  refine ⟨4133853373439550207709075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5511804497919400276945433 4133853373439550207709075)
                  ·
                    refine ⟨6200780060159325311563613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4133853373439550207709075 6200780060159325311563613)
                    ·
                      refine ⟨2325292522559746991836355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6200780060159325311563613 2325292522559746991836355)
                      ·
                        rfl

theorem cell23_4528491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 1, 3].length) (baseStart_4528491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528491 prefixEnd_4528491 := by exact prefixLift 4528491
  have htrace : WordTrace (prefixWord ++ tailWord_4528491) baseStart_4528491 baseEnd_4528491 := by
    simpa [prefixWord, tailWord_4528491, baseEnd_4528491] using wordTrace_append hprefix tailTrace_4528491
  have hstable : (prefixWord ++ tailWord_4528491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528491).length < 2 ^ (prefixWord ++ tailWord_4528491).sum := by decide
  have hdescent : baseEnd_4528491 < baseStart_4528491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528497 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 8]
def baseStart_4528497 : Nat := 118140960795 + 4528497 * 2 ^ 59
def prefixEnd_4528497 : Nat := 4983230072969 + 3 ^ 40 * 4528497 * 2
def baseEnd_4528497 : Nat := 2325295603443673968361327

theorem tailTrace_4528497 : CollatzResearch.WordTrace tailWord_4528497 prefixEnd_4528497 2325295603443673968361327 := by
  unfold tailWord_4528497
  simp only [CollatzResearch.WordTrace]
  refine ⟨165167854675036249558735745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110111903116690833039157163 165167854675036249558735745)
  ·
    refine ⟨123875891006277187169051809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165167854675036249558735745 123875891006277187169051809)
    ·
      refine ⟨92906918254707890376788857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123875891006277187169051809 92906918254707890376788857)
      ·
        refine ⟨69680188691030917782591643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92906918254707890376788857 69680188691030917782591643)
        ·
          refine ⟨104520283036546376673887465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69680188691030917782591643 104520283036546376673887465)
          ·
            refine ⟨78390212277409782505415599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104520283036546376673887465 78390212277409782505415599)
            ·
              refine ⟨117585318416114673758123399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78390212277409782505415599 117585318416114673758123399)
              ·
                refine ⟨176377977624172010637185099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117585318416114673758123399 176377977624172010637185099)
                ·
                  refine ⟨264566966436258015955777649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176377977624172010637185099 264566966436258015955777649)
                  ·
                    refine ⟨198425224827193511966833237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 264566966436258015955777649 198425224827193511966833237)
                    ·
                      refine ⟨2325295603443673968361327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 198425224827193511966833237 2325295603443673968361327)
                      ·
                        rfl

theorem cell23_4528497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_4528497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528497 prefixEnd_4528497 := by exact prefixLift 4528497
  have htrace : WordTrace (prefixWord ++ tailWord_4528497) baseStart_4528497 baseEnd_4528497 := by
    simpa [prefixWord, tailWord_4528497, baseEnd_4528497] using wordTrace_append hprefix tailTrace_4528497
  have hstable : (prefixWord ++ tailWord_4528497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528497).length < 2 ^ (prefixWord ++ tailWord_4528497).sum := by decide
  have hdescent : baseEnd_4528497 < baseStart_4528497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528541 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 2, 6]
def baseStart_4528541 : Nat := 118140960795 + 4528541 * 2 ^ 59
def prefixEnd_4528541 : Nat := 4983230072969 + 3 ^ 40 * 4528541 * 2
def baseEnd_4528541 : Nat := 775106065530823932070375

theorem tailTrace_4528541 : CollatzResearch.WordTrace tailWord_4528541 prefixEnd_4528541 775106065530823932070375 := by
  unfold tailWord_4528541
  simp only [CollatzResearch.WordTrace]
  refine ⟨165169459486876845073337477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110112972991251230048891651 165169459486876845073337477)
  ·
    refine ⟨30969273653789408451250777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165169459486876845073337477 30969273653789408451250777)
    ·
      refine ⟨23226955240342056338438083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30969273653789408451250777 23226955240342056338438083)
      ·
        refine ⟨34840432860513084507657125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23226955240342056338438083 34840432860513084507657125)
        ·
          refine ⟨6532581161346203345185711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34840432860513084507657125 6532581161346203345185711)
          ·
            refine ⟨9798871742019305017778567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6532581161346203345185711 9798871742019305017778567)
            ·
              refine ⟨14698307613028957526667851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9798871742019305017778567 14698307613028957526667851)
              ·
                refine ⟨22047461419543436290001777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14698307613028957526667851 22047461419543436290001777)
                ·
                  refine ⟨16535596064657577217501333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22047461419543436290001777 16535596064657577217501333)
                  ·
                    refine ⟨775106065530823932070375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16535596064657577217501333 775106065530823932070375)
                    ·
                      rfl

theorem cell23_4528541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_4528541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528541 prefixEnd_4528541 := by exact prefixLift 4528541
  have htrace : WordTrace (prefixWord ++ tailWord_4528541) baseStart_4528541 baseEnd_4528541 := by
    simpa [prefixWord, tailWord_4528541, baseEnd_4528541] using wordTrace_append hprefix tailTrace_4528541
  have hstable : (prefixWord ++ tailWord_4528541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528541).length < 2 ^ (prefixWord ++ tailWord_4528541).sum := by decide
  have hdescent : baseEnd_4528541 < baseStart_4528541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528544 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 4]
def baseStart_4528544 : Nat := 118140960795 + 4528544 * 2 ^ 59
def prefixEnd_4528544 : Nat := 4983230072969 + 3 ^ 40 * 4528544 * 2
def baseEnd_4528544 : Nat := 2325319737034435284473611

theorem tailTrace_4528544 : CollatzResearch.WordTrace tailWord_4528544 prefixEnd_4528544 2325319737034435284473611 := by
  unfold tailWord_4528544
  simp only [CollatzResearch.WordTrace]
  refine ⟨82584784452932988292848343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110113045937243984390464457 82584784452932988292848343)
  ·
    refine ⟨123877176679399482439272515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82584784452932988292848343 123877176679399482439272515)
    ·
      refine ⟨185815765019099223658908773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123877176679399482439272515 185815765019099223658908773)
      ·
        refine ⟨34840455941081104436045395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185815765019099223658908773 34840455941081104436045395)
        ·
          refine ⟨52260683911621656654068093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34840455941081104436045395 52260683911621656654068093)
          ·
            refine ⟨19597756466858121245275535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52260683911621656654068093 19597756466858121245275535)
            ·
              refine ⟨29396634700287181867913303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19597756466858121245275535 29396634700287181867913303)
              ·
                refine ⟨44094952050430772801869955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29396634700287181867913303 44094952050430772801869955)
                ·
                  refine ⟨66142428075646159202804933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44094952050430772801869955 66142428075646159202804933)
                  ·
                    refine ⟨12401705264183654850525925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66142428075646159202804933 12401705264183654850525925)
                    ·
                      refine ⟨2325319737034435284473611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12401705264183654850525925 2325319737034435284473611)
                      ·
                        rfl

theorem cell23_4528544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_4528544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528544 prefixEnd_4528544 := by exact prefixLift 4528544
  have htrace : WordTrace (prefixWord ++ tailWord_4528544) baseStart_4528544 baseEnd_4528544 := by
    simpa [prefixWord, tailWord_4528544, baseEnd_4528544] using wordTrace_append hprefix tailTrace_4528544
  have hstable : (prefixWord ++ tailWord_4528544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528544).length < 2 ^ (prefixWord ++ tailWord_4528544).sum := by decide
  have hdescent : baseEnd_4528544 < baseStart_4528544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528598 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_4528598 : Nat := 118140960795 + 4528598 * 2 ^ 59
def prefixEnd_4528598 : Nat := 4983230072969 + 3 ^ 40 * 4528598 * 2
def baseEnd_4528598 : Nat := 2325347464989778073198363

theorem tailTrace_4528598 : CollatzResearch.WordTrace tailWord_4528598 prefixEnd_4528598 2325347464989778073198363 := by
  unfold tailWord_4528598
  simp only [CollatzResearch.WordTrace]
  refine ⟨10323221152979396488010153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110114358965113562538774965 10323221152979396488010153)
  ·
    refine ⟨7742415864734547366007615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10323221152979396488010153 7742415864734547366007615)
    ·
      refine ⟨11613623797101821049011423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7742415864734547366007615 11613623797101821049011423)
      ·
        refine ⟨17420435695652731573517135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11613623797101821049011423 17420435695652731573517135)
        ·
          refine ⟨26130653543479097360275703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17420435695652731573517135 26130653543479097360275703)
          ·
            refine ⟨39195980315218646040413555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26130653543479097360275703 39195980315218646040413555)
            ·
              refine ⟨58793970472827969060620333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39195980315218646040413555 58793970472827969060620333)
              ·
                refine ⟨22047738927310488397732625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58793970472827969060620333 22047738927310488397732625)
                ·
                  refine ⟨16535804195482866298299469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22047738927310488397732625 16535804195482866298299469)
                  ·
                    refine ⟨6200926573306074861862301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16535804195482866298299469 6200926573306074861862301)
                    ·
                      refine ⟨2325347464989778073198363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6200926573306074861862301 2325347464989778073198363)
                      ·
                        rfl

theorem cell23_4528598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_4528598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528598 prefixEnd_4528598 := by exact prefixLift 4528598
  have htrace : WordTrace (prefixWord ++ tailWord_4528598) baseStart_4528598 baseEnd_4528598 := by
    simpa [prefixWord, tailWord_4528598, baseEnd_4528598] using wordTrace_append hprefix tailTrace_4528598
  have hstable : (prefixWord ++ tailWord_4528598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528598).length < 2 ^ (prefixWord ++ tailWord_4528598).sum := by decide
  have hdescent : baseEnd_4528598 < baseStart_4528598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528634 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6]
def baseStart_4528634 : Nat := 118140960795 + 4528634 * 2 ^ 59
def prefixEnd_4528634 : Nat := 4983230072969 + 3 ^ 40 * 4528634 * 2
def baseEnd_4528634 : Nat := 2325365950293339932348197

theorem tailTrace_4528634 : CollatzResearch.WordTrace tailWord_4528634 prefixEnd_4528634 2325365950293339932348197 := by
  unfold tailWord_4528634
  simp only [CollatzResearch.WordTrace]
  refine ⟨41293212868884980489118239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110115234317026614637648637 41293212868884980489118239)
  ·
    refine ⟨61939819303327470733677359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41293212868884980489118239 61939819303327470733677359)
    ·
      refine ⟨92909728954991206100516039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61939819303327470733677359 92909728954991206100516039)
      ·
        refine ⟨139364593432486809150774059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92909728954991206100516039 139364593432486809150774059)
        ·
          refine ⟨209046890148730213726161089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139364593432486809150774059 209046890148730213726161089)
          ·
            refine ⟨156785167611547660294620817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209046890148730213726161089 156785167611547660294620817)
            ·
              refine ⟨117588875708660745220965613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156785167611547660294620817 117588875708660745220965613)
              ·
                refine ⟨44095828390747779457862105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117588875708660745220965613 44095828390747779457862105)
                ·
                  refine ⟨33071871293060834593396579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44095828390747779457862105 33071871293060834593396579)
                  ·
                    refine ⟨49607806939591251890094869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33071871293060834593396579 49607806939591251890094869)
                    ·
                      refine ⟨2325365950293339932348197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49607806939591251890094869 2325365950293339932348197)
                      ·
                        rfl

theorem cell23_4528634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_4528634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528634 prefixEnd_4528634 := by exact prefixLift 4528634
  have htrace : WordTrace (prefixWord ++ tailWord_4528634) baseStart_4528634 baseEnd_4528634 := by
    simpa [prefixWord, tailWord_4528634, baseEnd_4528634] using wordTrace_append hprefix tailTrace_4528634
  have hstable : (prefixWord ++ tailWord_4528634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528634).length < 2 ^ (prefixWord ++ tailWord_4528634).sum := by decide
  have hdescent : baseEnd_4528634 < baseStart_4528634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528661 : List Nat := [1, 3, 2, 1, 3, 1, 3, 3, 6]
def baseStart_4528661 : Nat := 118140960795 + 4528661 * 2 ^ 59
def prefixEnd_4528661 : Nat := 4983230072969 + 3 ^ 40 * 4528661 * 2
def baseEnd_4528661 : Nat := 258375534919001258523397

theorem tailTrace_4528661 : CollatzResearch.WordTrace tailWord_4528661 prefixEnd_4528661 258375534919001258523397 := by
  unfold tailWord_4528661
  simp only [CollatzResearch.WordTrace]
  refine ⟨165173836246442105567705837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110115890830961403711803891 165173836246442105567705837)
  ·
    refine ⟨61940188592415789587889689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165173836246442105567705837 61940188592415789587889689)
    ·
      refine ⟨46455141444311842190917267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61940188592415789587889689 46455141444311842190917267)
      ·
        refine ⟨69682712166467763286375901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46455141444311842190917267 69682712166467763286375901)
        ·
          refine ⟨26131017062425411232390963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69682712166467763286375901 26131017062425411232390963)
          ·
            refine ⟨39196525593638116848586445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26131017062425411232390963 39196525593638116848586445)
            ·
              refine ⟨14698697097614293818219917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39196525593638116848586445 14698697097614293818219917)
              ·
                refine ⟨5512011411605360181832469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14698697097614293818219917 5512011411605360181832469)
                ·
                  refine ⟨258375534919001258523397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5512011411605360181832469 258375534919001258523397)
                  ·
                    rfl

theorem cell23_4528661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 6].length) (baseStart_4528661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528661 prefixEnd_4528661 := by exact prefixLift 4528661
  have htrace : WordTrace (prefixWord ++ tailWord_4528661) baseStart_4528661 baseEnd_4528661 := by
    simpa [prefixWord, tailWord_4528661, baseEnd_4528661] using wordTrace_append hprefix tailTrace_4528661
  have hstable : (prefixWord ++ tailWord_4528661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528661).length < 2 ^ (prefixWord ++ tailWord_4528661).sum := by decide
  have hdescent : baseEnd_4528661 < baseStart_4528661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528684 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 7]
def baseStart_4528684 : Nat := 118140960795 + 4528684 * 2 ^ 59
def prefixEnd_4528684 : Nat := 4983230072969 + 3 ^ 40 * 4528684 * 2
def baseEnd_4528684 : Nat := 2325391624326064736722967

theorem tailTrace_4528684 : CollatzResearch.WordTrace tailWord_4528684 prefixEnd_4528684 2325391624326064736722967 := by
  unfold tailWord_4528684
  simp only [CollatzResearch.WordTrace]
  refine ⟨82587337562679390247896553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110116450083572520330528737 82587337562679390247896553)
  ·
    refine ⟨61940503172009542685922415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82587337562679390247896553 61940503172009542685922415)
    ·
      refine ⟨92910754758014314028883623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61940503172009542685922415 92910754758014314028883623)
      ·
        refine ⟨139366132137021471043325435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92910754758014314028883623 139366132137021471043325435)
        ·
          refine ⟨209049198205532206564988153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139366132137021471043325435 209049198205532206564988153)
          ·
            refine ⟨156786898654149154923741115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209049198205532206564988153 156786898654149154923741115)
            ·
              refine ⟨235180347981223732385611673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156786898654149154923741115 235180347981223732385611673)
              ·
                refine ⟨176385260985917799289208755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235180347981223732385611673 176385260985917799289208755)
                ·
                  refine ⟨264577891478876698933813133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176385260985917799289208755 264577891478876698933813133)
                  ·
                    refine ⟨99216709304578762100179925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 264577891478876698933813133 99216709304578762100179925)
                    ·
                      refine ⟨2325391624326064736722967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99216709304578762100179925 2325391624326064736722967)
                      ·
                        rfl

theorem cell23_4528684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_4528684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528684 prefixEnd_4528684 := by exact prefixLift 4528684
  have htrace : WordTrace (prefixWord ++ tailWord_4528684) baseStart_4528684 baseEnd_4528684 := by
    simpa [prefixWord, tailWord_4528684, baseEnd_4528684] using wordTrace_append hprefix tailTrace_4528684
  have hstable : (prefixWord ++ tailWord_4528684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528684).length < 2 ^ (prefixWord ++ tailWord_4528684).sum := by decide
  have hdescent : baseEnd_4528684 < baseStart_4528684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528721 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 1, 6]
def baseStart_4528721 : Nat := 118140960795 + 4528721 * 2 ^ 59
def prefixEnd_4528721 : Nat := 4983230072969 + 3 ^ 40 * 4528721 * 2
def baseEnd_4528721 : Nat := 775136874370093697320099

theorem tailTrace_4528721 : CollatzResearch.WordTrace tailWord_4528721 prefixEnd_4528721 775136874370093697320099 := by
  unfold tailWord_4528721
  simp only [CollatzResearch.WordTrace]
  refine ⟨165176024626224735814890017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110117349750816490543260011 165176024626224735814890017)
  ·
    refine ⟨123882018469668551861167513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165176024626224735814890017 123882018469668551861167513)
    ·
      refine ⟨92911513852251413895875635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123882018469668551861167513 92911513852251413895875635)
      ·
        refine ⟨139367270778377120843813453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92911513852251413895875635 139367270778377120843813453)
        ·
          refine ⟨52262726541891420316430045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139367270778377120843813453 52262726541891420316430045)
          ·
            refine ⟨19598522453209282618661267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52262726541891420316430045 19598522453209282618661267)
            ·
              refine ⟨29397783679813923927991901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19598522453209282618661267 29397783679813923927991901)
              ·
                refine ⟨11024168879930221472996963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29397783679813923927991901 11024168879930221472996963)
                ·
                  refine ⟨16536253319895332209495445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11024168879930221472996963 16536253319895332209495445)
                  ·
                    refine ⟨775136874370093697320099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16536253319895332209495445 775136874370093697320099)
                    ·
                      rfl

theorem cell23_4528721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_4528721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528721 prefixEnd_4528721 := by exact prefixLift 4528721
  have htrace : WordTrace (prefixWord ++ tailWord_4528721) baseStart_4528721 baseEnd_4528721 := by
    simpa [prefixWord, tailWord_4528721, baseEnd_4528721] using wordTrace_append hprefix tailTrace_4528721
  have hstable : (prefixWord ++ tailWord_4528721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528721).length < 2 ^ (prefixWord ++ tailWord_4528721).sum := by decide
  have hdescent : baseEnd_4528721 < baseStart_4528721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528772 : List Nat := [2, 3, 2, 1, 3, 2, 3, 1, 2, 4]
def baseStart_4528772 : Nat := 118140960795 + 4528772 * 2 ^ 59
def prefixEnd_4528772 : Nat := 4983230072969 + 3 ^ 40 * 4528772 * 2
def baseEnd_4528772 : Nat := 775145603541220130807521

theorem tailTrace_4528772 : CollatzResearch.WordTrace tailWord_4528772 prefixEnd_4528772 775145603541220130807521 := by
  unfold tailWord_4528772
  simp only [CollatzResearch.WordTrace]
  refine ⟨82588942374519985762498285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110118589832693314349997713 82588942374519985762498285)
  ·
    refine ⟨30970853390444994660936857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82588942374519985762498285 30970853390444994660936857)
    ·
      refine ⟨23228140042833745995702643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30970853390444994660936857 23228140042833745995702643)
      ·
        refine ⟨34842210064250618993553965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23228140042833745995702643 34842210064250618993553965)
        ·
          refine ⟨13065828774093982122582737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34842210064250618993553965 13065828774093982122582737)
          ·
            refine ⟨9799371580570486591937053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13065828774093982122582737 9799371580570486591937053)
            ·
              refine ⟨3674764342713932471976395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9799371580570486591937053 3674764342713932471976395)
              ·
                refine ⟨5512146514070898707964593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3674764342713932471976395 5512146514070898707964593)
                ·
                  refine ⟨4134109885553174030973445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5512146514070898707964593 4134109885553174030973445)
                  ·
                    refine ⟨775145603541220130807521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4134109885553174030973445 775145603541220130807521)
                    ·
                      rfl

theorem cell23_4528772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_4528772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528772 prefixEnd_4528772 := by exact prefixLift 4528772
  have htrace : WordTrace (prefixWord ++ tailWord_4528772) baseStart_4528772 baseEnd_4528772 := by
    simpa [prefixWord, tailWord_4528772, baseEnd_4528772] using wordTrace_append hprefix tailTrace_4528772
  have hstable : (prefixWord ++ tailWord_4528772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528772).length < 2 ^ (prefixWord ++ tailWord_4528772).sum := by decide
  have hdescent : baseEnd_4528772 < baseStart_4528772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528791 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 5]
def baseStart_4528791 : Nat := 118140960795 + 4528791 * 2 ^ 59
def prefixEnd_4528791 : Nat := 4983230072969 + 3 ^ 40 * 4528791 * 2
def baseEnd_4528791 : Nat := 2325446566756095818084975

theorem tailTrace_4528791 : CollatzResearch.WordTrace tailWord_4528791 prefixEnd_4528791 2325446566756095818084975 := by
  unfold tailWord_4528791
  simp only [CollatzResearch.WordTrace]
  refine ⟨165178577735971137769938227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110119051823980758513292151 165178577735971137769938227)
  ·
    refine ⟨247767866603956706654907341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165178577735971137769938227 247767866603956706654907341)
    ·
      refine ⟨92912949976483764995590253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247767866603956706654907341 92912949976483764995590253)
      ·
        refine ⟨34842356241181411873346345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92912949976483764995590253 34842356241181411873346345)
        ·
          refine ⟨26131767180886058905009759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34842356241181411873346345 26131767180886058905009759)
          ·
            refine ⟨39197650771329088357514639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26131767180886058905009759 39197650771329088357514639)
            ·
              refine ⟨58796476156993632536271959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39197650771329088357514639 58796476156993632536271959)
              ·
                refine ⟨88194714235490448804407939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58796476156993632536271959 88194714235490448804407939)
                ·
                  refine ⟨132292071353235673206611909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88194714235490448804407939 132292071353235673206611909)
                  ·
                    refine ⟨24804763378731688726239733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 132292071353235673206611909 24804763378731688726239733)
                    ·
                      refine ⟨2325446566756095818084975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24804763378731688726239733 2325446566756095818084975)
                      ·
                        rfl

theorem cell23_4528791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_4528791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528791 prefixEnd_4528791 := by exact prefixLift 4528791
  have htrace : WordTrace (prefixWord ++ tailWord_4528791) baseStart_4528791 baseEnd_4528791 := by
    simpa [prefixWord, tailWord_4528791, baseEnd_4528791] using wordTrace_append hprefix tailTrace_4528791
  have hstable : (prefixWord ++ tailWord_4528791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528791).length < 2 ^ (prefixWord ++ tailWord_4528791).sum := by decide
  have hdescent : baseEnd_4528791 < baseStart_4528791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528796 : List Nat := [2, 2, 3, 2, 2, 3, 1, 3, 1, 2, 2]
def baseStart_4528796 : Nat := 118140960795 + 4528796 * 2 ^ 59
def prefixEnd_4528796 : Nat := 4983230072969 + 3 ^ 40 * 4528796 * 2
def baseEnd_4528796 : Nat := 2325449134159368298522453

theorem tailTrace_4528796 : CollatzResearch.WordTrace tailWord_4528796 prefixEnd_4528796 2325449134159368298522453 := by
  unfold tailWord_4528796
  simp only [CollatzResearch.WordTrace]
  refine ⟨82589380050476511811935121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110119173400635349082580161 82589380050476511811935121)
  ·
    refine ⟨61942035037857383858951341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82589380050476511811935121 61942035037857383858951341)
    ·
      refine ⟨23228263139196518947106753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61942035037857383858951341 23228263139196518947106753)
      ·
        refine ⟨17421197354397389210330065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23228263139196518947106753 17421197354397389210330065)
        ·
          refine ⟨13065898015798041907747549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17421197354397389210330065 13065898015798041907747549)
          ·
            refine ⟨4899711755924265715405331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13065898015798041907747549 4899711755924265715405331)
            ·
              refine ⟨7349567633886398573107997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4899711755924265715405331 7349567633886398573107997)
              ·
                refine ⟨2756087862707399464915499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7349567633886398573107997 2756087862707399464915499)
                ·
                  refine ⟨4134131794061099197373249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756087862707399464915499 4134131794061099197373249)
                  ·
                    refine ⟨3100598845545824398029937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4134131794061099197373249 3100598845545824398029937)
                    ·
                      refine ⟨2325449134159368298522453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3100598845545824398029937 2325449134159368298522453)
                      ·
                        rfl

theorem cell23_4528796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_4528796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528796 prefixEnd_4528796 := by exact prefixLift 4528796
  have htrace : WordTrace (prefixWord ++ tailWord_4528796) baseStart_4528796 baseEnd_4528796 := by
    simpa [prefixWord, tailWord_4528796, baseEnd_4528796] using wordTrace_append hprefix tailTrace_4528796
  have hstable : (prefixWord ++ tailWord_4528796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528796).length < 2 ^ (prefixWord ++ tailWord_4528796).sum := by decide
  have hdescent : baseEnd_4528796 < baseStart_4528796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528829 : List Nat := [1, 4, 1, 2, 1, 5, 2, 1, 2, 1, 3]
def baseStart_4528829 : Nat := 118140960795 + 4528829 * 2 ^ 59
def prefixEnd_4528829 : Nat := 4983230072969 + 3 ^ 40 * 4528829 * 2
def baseEnd_4528829 : Nat := 2325466079020966669409801

theorem tailTrace_4528829 : CollatzResearch.WordTrace tailWord_4528829 prefixEnd_4528829 2325466079020966669409801 := by
  unfold tailWord_4528829
  simp only [CollatzResearch.WordTrace]
  refine ⟨165179963709833470259821541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110119975806555646839881027 165179963709833470259821541)
  ·
    refine ⟨30971243195593775673716539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165179963709833470259821541 30971243195593775673716539)
    ·
      refine ⟨46456864793390663510574809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30971243195593775673716539 46456864793390663510574809)
      ·
        refine ⟨34842648595042997632931107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46456864793390663510574809 34842648595042997632931107)
        ·
          refine ⟨52263972892564496449396661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34842648595042997632931107 52263972892564496449396661)
          ·
            refine ⟨4899747458677921542130937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52263972892564496449396661 4899747458677921542130937)
            ·
              refine ⟨3674810594008441156598203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4899747458677921542130937 3674810594008441156598203)
              ·
                refine ⟨5512215891012661734897305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3674810594008441156598203 5512215891012661734897305)
                ·
                  refine ⟨4134161918259496301172979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5512215891012661734897305 4134161918259496301172979)
                  ·
                    refine ⟨6201242877389244451759469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4134161918259496301172979 6201242877389244451759469)
                    ·
                      refine ⟨2325466079020966669409801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6201242877389244451759469 2325466079020966669409801)
                      ·
                        rfl

theorem cell23_4528829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_4528829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528829 prefixEnd_4528829 := by exact prefixLift 4528829
  have htrace : WordTrace (prefixWord ++ tailWord_4528829) baseStart_4528829 baseEnd_4528829 := by
    simpa [prefixWord, tailWord_4528829, baseEnd_4528829] using wordTrace_append hprefix tailTrace_4528829
  have hstable : (prefixWord ++ tailWord_4528829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528829).length < 2 ^ (prefixWord ++ tailWord_4528829).sum := by decide
  have hdescent : baseEnd_4528829 < baseStart_4528829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528869 : List Nat := [1, 3, 1, 4, 1, 3, 2, 2, 2, 2, 2]
def baseStart_4528869 : Nat := 118140960795 + 4528869 * 2 ^ 59
def prefixEnd_4528869 : Nat := 4983230072969 + 3 ^ 40 * 4528869 * 2
def baseEnd_4528869 : Nat := 2325486618247146512909617

theorem tailTrace_4528869 : CollatzResearch.WordTrace tailWord_4528869 prefixEnd_4528869 2325486618247146512909617 := by
  unfold tailWord_4528869
  simp only [CollatzResearch.WordTrace]
  refine ⟨165181422629688557091277661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110120948419792371394185107 165181422629688557091277661)
  ·
    refine ⟨61943033486133208909229123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165181422629688557091277661 61943033486133208909229123)
    ·
      refine ⟨92914550229199813363843685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61943033486133208909229123 92914550229199813363843685)
      ·
        refine ⟨17421478167974965005720691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92914550229199813363843685 17421478167974965005720691)
        ·
          refine ⟨26132217251962447508581037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17421478167974965005720691 26132217251962447508581037)
          ·
            refine ⟨9799581469485917815717889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26132217251962447508581037 9799581469485917815717889)
            ·
              refine ⟨7349686102114438361788417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9799581469485917815717889 7349686102114438361788417)
              ·
                refine ⟨5512264576585828771341313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7349686102114438361788417 5512264576585828771341313)
                ·
                  refine ⟨4134198432439371578505985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5512264576585828771341313 4134198432439371578505985)
                  ·
                    refine ⟨3100648824329528683879489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4134198432439371578505985 3100648824329528683879489)
                    ·
                      refine ⟨2325486618247146512909617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3100648824329528683879489 2325486618247146512909617)
                      ·
                        rfl

theorem cell23_4528869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_4528869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528869 prefixEnd_4528869 := by exact prefixLift 4528869
  have htrace : WordTrace (prefixWord ++ tailWord_4528869) baseStart_4528869 baseEnd_4528869 := by
    simpa [prefixWord, tailWord_4528869, baseEnd_4528869] using wordTrace_append hprefix tailTrace_4528869
  have hstable : (prefixWord ++ tailWord_4528869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528869).length < 2 ^ (prefixWord ++ tailWord_4528869).sum := by decide
  have hdescent : baseEnd_4528869 < baseStart_4528869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4528969 : List Nat := [1, 2, 1, 1, 2, 7, 1, 3, 1, 4]
def baseStart_4528969 : Nat := 118140960795 + 4528969 * 2 ^ 59
def prefixEnd_4528969 : Nat := 4983230072969 + 3 ^ 40 * 4528969 * 2
def baseEnd_4528969 : Nat := 775179322104198707219719

theorem tailTrace_4528969 : CollatzResearch.WordTrace tailWord_4528969 prefixEnd_4528969 775179322104198707219719 := by
  unfold tailWord_4528969
  simp only [CollatzResearch.WordTrace]
  refine ⟨165185069929326274169917961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110123379952884182779945307 165185069929326274169917961)
  ·
    refine ⟨123888802446994705627438471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165185069929326274169917961 123888802446994705627438471)
    ·
      refine ⟨185833203670492058441157707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123888802446994705627438471 185833203670492058441157707)
      ·
        refine ⟨278749805505738087661736561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185833203670492058441157707 278749805505738087661736561)
        ·
          refine ⟨209062354129303565746302421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278749805505738087661736561 209062354129303565746302421)
          ·
            refine ⟨4899898924905552322178963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 209062354129303565746302421 4899898924905552322178963)
            ·
              refine ⟨7349848387358328483268445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4899898924905552322178963 7349848387358328483268445)
              ·
                refine ⟨2756193145259373181225667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7349848387358328483268445 2756193145259373181225667)
                ·
                  refine ⟨4134289717889059771838501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756193145259373181225667 4134289717889059771838501)
                  ·
                    refine ⟨775179322104198707219719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4134289717889059771838501 775179322104198707219719)
                    ·
                      rfl

theorem cell23_4528969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 1, 4].length) (baseStart_4528969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4528969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4528969 prefixEnd_4528969 := by exact prefixLift 4528969
  have htrace : WordTrace (prefixWord ++ tailWord_4528969) baseStart_4528969 baseEnd_4528969 := by
    simpa [prefixWord, tailWord_4528969, baseEnd_4528969] using wordTrace_append hprefix tailTrace_4528969
  have hstable : (prefixWord ++ tailWord_4528969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4528969).length < 2 ^ (prefixWord ++ tailWord_4528969).sum := by decide
  have hdescent : baseEnd_4528969 < baseStart_4528969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4528969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529015 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 2, 6, 2]
def baseStart_4529015 : Nat := 118140960795 + 4529015 * 2 ^ 59
def prefixEnd_4529015 : Nat := 4983230072969 + 3 ^ 40 * 4529015 * 2
def baseEnd_4529015 : Nat := 2325561586422702941683945

theorem tailTrace_4529015 : CollatzResearch.WordTrace tailWord_4529015 prefixEnd_4529015 2325561586422702941683945 := by
  unfold tailWord_4529015
  simp only [CollatzResearch.WordTrace]
  refine ⟨165186747687159624026092499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110124498458106416017394999 165186747687159624026092499)
  ·
    refine ⟨247780121530739436039138749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165186747687159624026092499 247780121530739436039138749)
    ·
      refine ⟨92917545574027288514677031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247780121530739436039138749 92917545574027288514677031)
      ·
        refine ⟨139376318361040932772015547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92917545574027288514677031 139376318361040932772015547)
        ·
          refine ⟨209064477541561399158023321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139376318361040932772015547 209064477541561399158023321)
          ·
            refine ⟨156798358156171049368517491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209064477541561399158023321 156798358156171049368517491)
            ·
              refine ⟨235197537234256574052776237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156798358156171049368517491 235197537234256574052776237)
              ·
                refine ⟨88199076462846215269791089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235197537234256574052776237 88199076462846215269791089)
                ·
                  refine ⟨66149307347134661452343317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88199076462846215269791089 66149307347134661452343317)
                  ·
                    refine ⟨3100748781896937255578593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66149307347134661452343317 3100748781896937255578593)
                    ·
                      refine ⟨2325561586422702941683945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3100748781896937255578593 2325561586422702941683945)
                      ·
                        rfl

theorem cell23_4529015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 6, 2].length) (baseStart_4529015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529015 prefixEnd_4529015 := by exact prefixLift 4529015
  have htrace : WordTrace (prefixWord ++ tailWord_4529015) baseStart_4529015 baseEnd_4529015 := by
    simpa [prefixWord, tailWord_4529015, baseEnd_4529015] using wordTrace_append hprefix tailTrace_4529015
  have hstable : (prefixWord ++ tailWord_4529015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529015).length < 2 ^ (prefixWord ++ tailWord_4529015).sum := by decide
  have hdescent : baseEnd_4529015 < baseStart_4529015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529035 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 5]
def baseStart_4529035 : Nat := 118140960795 + 4529035 * 2 ^ 59
def prefixEnd_4529035 : Nat := 4983230072969 + 3 ^ 40 * 4529035 * 2
def baseEnd_4529035 : Nat := 2325571856035792863433853

theorem tailTrace_4529035 : CollatzResearch.WordTrace tailWord_4529035 prefixEnd_4529035 2325571856035792863433853 := by
  unfold tailWord_4529035
  simp only [CollatzResearch.WordTrace]
  refine ⟨165187477147087167441820559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110124984764724778294547039 165187477147087167441820559)
  ·
    refine ⟨247781215720630751162730839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165187477147087167441820559 247781215720630751162730839)
    ·
      refine ⟨371671823580946126744096259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247781215720630751162730839 371671823580946126744096259)
      ·
        refine ⟨557507735371419190116144389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371671823580946126744096259 557507735371419190116144389)
        ·
          refine ⟨104532700382141098146777073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 557507735371419190116144389 104532700382141098146777073)
          ·
            refine ⟨78399525286605823610082805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104532700382141098146777073 78399525286605823610082805)
            ·
              refine ⟨7349955495619295963445263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78399525286605823610082805 7349955495619295963445263)
              ·
                refine ⟨11024933243428943945167895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7349955495619295963445263 11024933243428943945167895)
                ·
                  refine ⟨16537399865143415917751843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11024933243428943945167895 16537399865143415917751843)
                  ·
                    refine ⟨24806099797715123876627765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16537399865143415917751843 24806099797715123876627765)
                    ·
                      refine ⟨2325571856035792863433853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24806099797715123876627765 2325571856035792863433853)
                      ·
                        rfl

theorem cell23_4529035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 5].length) (baseStart_4529035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529035 prefixEnd_4529035 := by exact prefixLift 4529035
  have htrace : WordTrace (prefixWord ++ tailWord_4529035) baseStart_4529035 baseEnd_4529035 := by
    simpa [prefixWord, tailWord_4529035, baseEnd_4529035] using wordTrace_append hprefix tailTrace_4529035
  have hstable : (prefixWord ++ tailWord_4529035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529035).length < 2 ^ (prefixWord ++ tailWord_4529035).sum := by decide
  have hdescent : baseEnd_4529035 < baseStart_4529035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529038 : List Nat := [4, 1, 1, 17]
def baseStart_4529038 : Nat := 118140960795 + 4529038 * 2 ^ 59
def prefixEnd_4529038 : Nat := 4983230072969 + 3 ^ 40 * 4529038 * 2
def baseEnd_4529038 : Nat := 1063362321206107156697

theorem tailTrace_4529038 : CollatzResearch.WordTrace tailWord_4529038 prefixEnd_4529038 1063362321206107156697 := by
  unfold tailWord_4529038
  simp only [CollatzResearch.WordTrace]
  refine ⟨20648448320759537369272471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110125057710717532636119845 20648448320759537369272471)
  ·
    refine ⟨30972672481139306053908707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20648448320759537369272471 30972672481139306053908707)
    ·
      refine ⟨46459008721708959080863061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30972672481139306053908707 46459008721708959080863061)
      ·
        refine ⟨1063362321206107156697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 46459008721708959080863061 1063362321206107156697)
        ·
          rfl

theorem cell23_4529038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 17].length) (baseStart_4529038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529038 prefixEnd_4529038 := by exact prefixLift 4529038
  have htrace : WordTrace (prefixWord ++ tailWord_4529038) baseStart_4529038 baseEnd_4529038 := by
    simpa [prefixWord, tailWord_4529038, baseEnd_4529038] using wordTrace_append hprefix tailTrace_4529038
  have hstable : (prefixWord ++ tailWord_4529038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529038).length < 2 ^ (prefixWord ++ tailWord_4529038).sum := by decide
  have hdescent : baseEnd_4529038 < baseStart_4529038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529055 : List Nat := [1, 1, 2, 5, 2, 1, 3, 8]
def baseStart_4529055 : Nat := 118140960795 + 4529055 * 2 ^ 59
def prefixEnd_4529055 : Nat := 4983230072969 + 3 ^ 40 * 4529055 * 2
def baseEnd_4529055 : Nat := 86132671320328992043843

theorem tailTrace_4529055 : CollatzResearch.WordTrace tailWord_4529055 prefixEnd_4529055 86132671320328992043843 := by
  unfold tailWord_4529055
  simp only [CollatzResearch.WordTrace]
  refine ⟨165188206607014710857548619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110125471071343140571699079 165188206607014710857548619)
  ·
    refine ⟨247782309910522066286322929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165188206607014710857548619 247782309910522066286322929)
    ·
      refine ⟨185836732432891549714742197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247782309910522066286322929 185836732432891549714742197)
      ·
        refine ⟨17422193665583582785757081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 185836732432891549714742197 17422193665583582785757081)
        ·
          refine ⟨13066645249187687089317811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17422193665583582785757081 13066645249187687089317811)
          ·
            refine ⟨19599967873781530633976717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13066645249187687089317811 19599967873781530633976717)
            ·
              refine ⟨7349987952668073987741269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19599967873781530633976717 7349987952668073987741269)
              ·
                refine ⟨86132671320328992043843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7349987952668073987741269 86132671320328992043843)
                ·
                  rfl

theorem cell23_4529055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 8].length) (baseStart_4529055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529055 prefixEnd_4529055 := by exact prefixLift 4529055
  have htrace : WordTrace (prefixWord ++ tailWord_4529055) baseStart_4529055 baseEnd_4529055 := by
    simpa [prefixWord, tailWord_4529055, baseEnd_4529055] using wordTrace_append hprefix tailTrace_4529055
  have hstable : (prefixWord ++ tailWord_4529055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529055).length < 2 ^ (prefixWord ++ tailWord_4529055).sum := by decide
  have hdescent : baseEnd_4529055 < baseStart_4529055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529082 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3]
def baseStart_4529082 : Nat := 118140960795 + 4529082 * 2 ^ 59
def prefixEnd_4529082 : Nat := 4983230072969 + 3 ^ 40 * 4529082 * 2
def baseEnd_4529082 : Nat := 2325595989626554179546137

theorem tailTrace_4529082 : CollatzResearch.WordTrace tailWord_4529082 prefixEnd_4529082 2325595989626554179546137 := by
  unfold tailWord_4529082
  simp only [CollatzResearch.WordTrace]
  refine ⟨41297297844479223617195375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110126127585277929645854333 41297297844479223617195375)
  ·
    refine ⟨61945946766718835425793063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41297297844479223617195375 61945946766718835425793063)
    ·
      refine ⟨92918920150078253138689595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61945946766718835425793063 92918920150078253138689595)
      ·
        refine ⟨139378380225117379708034393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92918920150078253138689595 139378380225117379708034393)
        ·
          refine ⟨104533785168838034781025795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139378380225117379708034393 104533785168838034781025795)
          ·
            refine ⟨156800677753257052171538693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104533785168838034781025795 156800677753257052171538693)
            ·
              refine ⟨29400127078735697282163505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156800677753257052171538693 29400127078735697282163505)
              ·
                refine ⟨22050095309051772961622629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29400127078735697282163505 22050095309051772961622629)
                ·
                  refine ⟨4134392870447207430304243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22050095309051772961622629 4134392870447207430304243)
                  ·
                    refine ⟨6201589305670811145456365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4134392870447207430304243 6201589305670811145456365)
                    ·
                      refine ⟨2325595989626554179546137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6201589305670811145456365 2325595989626554179546137)
                      ·
                        rfl

theorem cell23_4529082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3].length) (baseStart_4529082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529082 prefixEnd_4529082 := by exact prefixLift 4529082
  have htrace : WordTrace (prefixWord ++ tailWord_4529082) baseStart_4529082 baseEnd_4529082 := by
    simpa [prefixWord, tailWord_4529082, baseEnd_4529082] using wordTrace_append hprefix tailTrace_4529082
  have hstable : (prefixWord ++ tailWord_4529082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529082).length < 2 ^ (prefixWord ++ tailWord_4529082).sum := by decide
  have hdescent : baseEnd_4529082 < baseStart_4529082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529099 : List Nat := [1, 1, 1, 1, 3, 5, 3, 2, 2, 1, 3]
def baseStart_4529099 : Nat := 118140960795 + 4529099 * 2 ^ 59
def prefixEnd_4529099 : Nat := 4983230072969 + 3 ^ 40 * 4529099 * 2
def baseEnd_4529099 : Nat := 2325604718797680613033559

theorem tailTrace_4529099 : CollatzResearch.WordTrace tailWord_4529099 prefixEnd_4529099 2325604718797680613033559 := by
  unfold tailWord_4529099
  simp only [CollatzResearch.WordTrace]
  refine ⟨165189811418855306372150351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110126540945903537581433567 165189811418855306372150351)
  ·
    refine ⟨247784717128282959558225527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165189811418855306372150351 247784717128282959558225527)
    ·
      refine ⟨371677075692424439337338291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247784717128282959558225527 371677075692424439337338291)
      ·
        refine ⟨557515613538636659006007437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371677075692424439337338291 557515613538636659006007437)
        ·
          refine ⟨209068355076988747127252789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 557515613538636659006007437 209068355076988747127252789)
          ·
            refine ⟨19600158288467695043179949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 209068355076988747127252789 19600158288467695043179949)
            ·
              refine ⟨7350059358175385641192481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19600158288467695043179949 7350059358175385641192481)
              ·
                refine ⟨5512544518631539230894361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7350059358175385641192481 5512544518631539230894361)
                ·
                  refine ⟨4134408388973654423170771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5512544518631539230894361 4134408388973654423170771)
                  ·
                    refine ⟨6201612583460481634756157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4134408388973654423170771 6201612583460481634756157)
                    ·
                      refine ⟨2325604718797680613033559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6201612583460481634756157 2325604718797680613033559)
                      ·
                        rfl

theorem cell23_4529099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 1, 3].length) (baseStart_4529099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529099 prefixEnd_4529099 := by exact prefixLift 4529099
  have htrace : WordTrace (prefixWord ++ tailWord_4529099) baseStart_4529099 baseEnd_4529099 := by
    simpa [prefixWord, tailWord_4529099, baseEnd_4529099] using wordTrace_append hprefix tailTrace_4529099
  have hstable : (prefixWord ++ tailWord_4529099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529099).length < 2 ^ (prefixWord ++ tailWord_4529099).sum := by decide
  have hdescent : baseEnd_4529099 < baseStart_4529099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529142 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_4529142 : Nat := 118140960795 + 4529142 * 2 ^ 59
def prefixEnd_4529142 : Nat := 4983230072969 + 3 ^ 40 * 4529142 * 2
def baseEnd_4529142 : Nat := 2325626798465823944795861

theorem tailTrace_4529142 : CollatzResearch.WordTrace tailWord_4529142 prefixEnd_4529142 2325626798465823944795861 := by
  unfold tailWord_4529142
  simp only [CollatzResearch.WordTrace]
  refine ⟨10324461234856220294747855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110127586505133016477310453 10324461234856220294747855)
  ·
    refine ⟨15486691852284330442121783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10324461234856220294747855 15486691852284330442121783)
    ·
      refine ⟨23230037778426495663182675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15486691852284330442121783 23230037778426495663182675)
      ·
        refine ⟨34845056667639743494774013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23230037778426495663182675 34845056667639743494774013)
        ·
          refine ⟨13066896250364903810540255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34845056667639743494774013 13066896250364903810540255)
          ·
            refine ⟨19600344375547355715810383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13066896250364903810540255 19600344375547355715810383)
            ·
              refine ⟨29400516563321033573715575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19600344375547355715810383 29400516563321033573715575)
              ·
                refine ⟨44100774844981550360573363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29400516563321033573715575 44100774844981550360573363)
                ·
                  refine ⟨66151162267472325540860045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44100774844981550360573363 66151162267472325540860045)
                  ·
                    refine ⟨24806685850302122077822517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66151162267472325540860045 24806685850302122077822517)
                    ·
                      refine ⟨2325626798465823944795861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24806685850302122077822517 2325626798465823944795861)
                      ·
                        rfl

theorem cell23_4529142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_4529142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529142 prefixEnd_4529142 := by exact prefixLift 4529142
  have htrace : WordTrace (prefixWord ++ tailWord_4529142) baseStart_4529142 baseEnd_4529142 := by
    simpa [prefixWord, tailWord_4529142, baseEnd_4529142] using wordTrace_append hprefix tailTrace_4529142
  have hstable : (prefixWord ++ tailWord_4529142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529142).length < 2 ^ (prefixWord ++ tailWord_4529142).sum := by decide
  have hdescent : baseEnd_4529142 < baseStart_4529142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529162 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 7]
def baseStart_4529162 : Nat := 118140960795 + 4529162 * 2 ^ 59
def prefixEnd_4529162 : Nat := 4983230072969 + 3 ^ 40 * 4529162 * 2
def baseEnd_4529162 : Nat := 258404118675434874060641

theorem tailTrace_4529162 : CollatzResearch.WordTrace tailWord_4529162 prefixEnd_4529162 258404118675434874060641 := by
  unfold tailWord_4529162
  simp only [CollatzResearch.WordTrace]
  refine ⟨41298027304406767032923435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110128072811751378754462493 41298027304406767032923435)
  ·
    refine ⟨61947040956610150549385153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41298027304406767032923435 61947040956610150549385153)
    ·
      refine ⟨46460280717457612912038865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61947040956610150549385153 46460280717457612912038865)
      ·
        refine ⟨34845210538093209684029149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46460280717457612912038865 34845210538093209684029149)
        ·
          refine ⟨13066953951784953631510931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34845210538093209684029149 13066953951784953631510931)
          ·
            refine ⟨19600430927677430447266397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13066953951784953631510931 19600430927677430447266397)
            ·
              refine ⟨7350161597879036417724899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19600430927677430447266397 7350161597879036417724899)
              ·
                refine ⟨11025242396818554626587349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7350161597879036417724899 11025242396818554626587349)
                ·
                  refine ⟨258404118675434874060641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11025242396818554626587349 258404118675434874060641)
                  ·
                    rfl

theorem cell23_4529162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 7].length) (baseStart_4529162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529162 prefixEnd_4529162 := by exact prefixLift 4529162
  have htrace : WordTrace (prefixWord ++ tailWord_4529162) baseStart_4529162 baseEnd_4529162 := by
    simpa [prefixWord, tailWord_4529162, baseEnd_4529162] using wordTrace_append hprefix tailTrace_4529162
  have hstable : (prefixWord ++ tailWord_4529162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529162).length < 2 ^ (prefixWord ++ tailWord_4529162).sum := by decide
  have hdescent : baseEnd_4529162 < baseStart_4529162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529173 : List Nat := [1, 3, 2, 1, 4, 1, 4, 1, 2, 2, 2]
def baseStart_4529173 : Nat := 118140960795 + 4529173 * 2 ^ 59
def prefixEnd_4529173 : Nat := 4983230072969 + 3 ^ 40 * 4529173 * 2
def baseEnd_4529173 : Nat := 2325642716366113323508219

theorem tailTrace_4529173 : CollatzResearch.WordTrace tailWord_4529173 prefixEnd_4529173 2325642716366113323508219 := by
  unfold tailWord_4529173
  simp only [CollatzResearch.WordTrace]
  refine ⟨165192510420587217010344173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110128340280391478006896115 165192510420587217010344173)
  ·
    refine ⟨61947191407720206378879065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165192510420587217010344173 61947191407720206378879065)
    ·
      refine ⟨46460393555790154784159299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61947191407720206378879065 46460393555790154784159299)
      ·
        refine ⟨69690590333685232176238949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46460393555790154784159299 69690590333685232176238949)
        ·
          refine ⟨13066985687565981033044803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69690590333685232176238949 13066985687565981033044803)
          ·
            refine ⟨19600478531348971549567205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13066985687565981033044803 19600478531348971549567205)
            ·
              refine ⟨3675089724627932165543851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19600478531348971549567205 3675089724627932165543851)
              ·
                refine ⟨5512634586941898248315777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3675089724627932165543851 5512634586941898248315777)
                ·
                  refine ⟨4134475940206423686236833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5512634586941898248315777 4134475940206423686236833)
                  ·
                    refine ⟨3100856955154817764677625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4134475940206423686236833 3100856955154817764677625)
                    ·
                      refine ⟨2325642716366113323508219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3100856955154817764677625 2325642716366113323508219)
                      ·
                        rfl

theorem cell23_4529173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_4529173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529173 prefixEnd_4529173 := by exact prefixLift 4529173
  have htrace : WordTrace (prefixWord ++ tailWord_4529173) baseStart_4529173 baseEnd_4529173 := by
    simpa [prefixWord, tailWord_4529173, baseEnd_4529173] using wordTrace_append hprefix tailTrace_4529173
  have hstable : (prefixWord ++ tailWord_4529173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529173).length < 2 ^ (prefixWord ++ tailWord_4529173).sum := by decide
  have hdescent : baseEnd_4529173 < baseStart_4529173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529215 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 5]
def baseStart_4529215 : Nat := 118140960795 + 4529215 * 2 ^ 59
def prefixEnd_4529215 : Nat := 4983230072969 + 3 ^ 40 * 4529215 * 2
def baseEnd_4529215 : Nat := 2325664282553602159183025

theorem tailTrace_4529215 : CollatzResearch.WordTrace tailWord_4529215 prefixEnd_4529215 2325664282553602159183025 := by
  unfold tailWord_4529215
  simp only [CollatzResearch.WordTrace]
  refine ⟨165194042286435058183373099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110129361524290038788915399 165194042286435058183373099)
  ·
    refine ⟨247791063429652587275059649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165194042286435058183373099 247791063429652587275059649)
    ·
      refine ⟨185843297572239440456294737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247791063429652587275059649 185843297572239440456294737)
      ·
        refine ⟨139382473179179580342221053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185843297572239440456294737 139382473179179580342221053)
        ·
          refine ⟨52268427442192342628332895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139382473179179580342221053 52268427442192342628332895)
          ·
            refine ⟨78402641163288513942499343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52268427442192342628332895 78402641163288513942499343)
            ·
              refine ⟨117603961744932770913749015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78402641163288513942499343 117603961744932770913749015)
              ·
                refine ⟨176405942617399156370623523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117603961744932770913749015 176405942617399156370623523)
                ·
                  refine ⟨264608913926098734555935285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176405942617399156370623523 264608913926098734555935285)
                  ·
                    refine ⟨24807085680571756364618933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 264608913926098734555935285 24807085680571756364618933)
                    ·
                      refine ⟨2325664282553602159183025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24807085680571756364618933 2325664282553602159183025)
                      ·
                        rfl

theorem cell23_4529215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_4529215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529215 prefixEnd_4529215 := by exact prefixLift 4529215
  have htrace : WordTrace (prefixWord ++ tailWord_4529215) baseStart_4529215 baseEnd_4529215 := by
    simpa [prefixWord, tailWord_4529215, baseEnd_4529215] using wordTrace_append hprefix tailTrace_4529215
  have hstable : (prefixWord ++ tailWord_4529215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529215).length < 2 ^ (prefixWord ++ tailWord_4529215).sum := by decide
  have hdescent : baseEnd_4529215 < baseStart_4529215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529225 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 4, 1, 6]
def baseStart_4529225 : Nat := 118140960795 + 4529225 * 2 ^ 59
def prefixEnd_4529225 : Nat := 4983230072969 + 3 ^ 40 * 4529225 * 2
def baseEnd_4529225 : Nat := 2325669417360147120057979

theorem tailTrace_4529225 : CollatzResearch.WordTrace tailWord_4529225 prefixEnd_4529225 2325669417360147120057979 := by
  unfold tailWord_4529225
  simp only [CollatzResearch.WordTrace]
  refine ⟨165194407016398829891237129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110129604677599219927491419 165194407016398829891237129)
  ·
    refine ⟨123895805262299122418427847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165194407016398829891237129 123895805262299122418427847)
    ·
      refine ⟨185843707893448683627641771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123895805262299122418427847 185843707893448683627641771)
      ·
        refine ⟨278765561840173025441462657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185843707893448683627641771 278765561840173025441462657)
        ·
          refine ⟨209074171380129769081096993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278765561840173025441462657 209074171380129769081096993)
          ·
            refine ⟨156805628535097326810822745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209074171380129769081096993 156805628535097326810822745)
            ·
              refine ⟨117604221401322995108117059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156805628535097326810822745 117604221401322995108117059)
              ·
                refine ⟨176406332101984492662175589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117604221401322995108117059 176406332101984492662175589)
                ·
                  refine ⟨33076187269122092374157923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 176406332101984492662175589 33076187269122092374157923)
                  ·
                    refine ⟨49614280903683138561236885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33076187269122092374157923 49614280903683138561236885)
                    ·
                      refine ⟨2325669417360147120057979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49614280903683138561236885 2325669417360147120057979)
                      ·
                        rfl

theorem cell23_4529225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_4529225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529225 prefixEnd_4529225 := by exact prefixLift 4529225
  have htrace : WordTrace (prefixWord ++ tailWord_4529225) baseStart_4529225 baseEnd_4529225 := by
    simpa [prefixWord, tailWord_4529225, baseEnd_4529225] using wordTrace_append hprefix tailTrace_4529225
  have hstable : (prefixWord ++ tailWord_4529225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529225).length < 2 ^ (prefixWord ++ tailWord_4529225).sum := by decide
  have hdescent : baseEnd_4529225 < baseStart_4529225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529232 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 3]
def baseStart_4529232 : Nat := 118140960795 + 4529232 * 2 ^ 59
def prefixEnd_4529232 : Nat := 4983230072969 + 3 ^ 40 * 4529232 * 2
def baseEnd_4529232 : Nat := 2325673011724728592670447

theorem tailTrace_4529232 : CollatzResearch.WordTrace tailWord_4529232 prefixEnd_4529232 2325673011724728592670447 := by
  unfold tailWord_4529232
  simp only [CollatzResearch.WordTrace]
  refine ⟨82597331163686735043370975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110129774884915646724494633 82597331163686735043370975)
  ·
    refine ⟨123895996745530102565056463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82597331163686735043370975 123895996745530102565056463)
    ·
      refine ⟨185843995118295153847584695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123895996745530102565056463 185843995118295153847584695)
      ·
        refine ⟨278765992677442730771377043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185843995118295153847584695 278765992677442730771377043)
        ·
          refine ⟨418148989016164096157065565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278765992677442730771377043 418148989016164096157065565)
          ·
            refine ⟨156805870881061536058899587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 418148989016164096157065565 156805870881061536058899587)
            ·
              refine ⟨235208806321592304088349381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156805870881061536058899587 235208806321592304088349381)
              ·
                refine ⟨44101651185298557016565509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 235208806321592304088349381 44101651185298557016565509)
                ·
                  refine ⟨8269059597243479440606033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44101651185298557016565509 8269059597243479440606033)
                  ·
                    refine ⟨6201794697932609580454525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8269059597243479440606033 6201794697932609580454525)
                    ·
                      refine ⟨2325673011724728592670447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6201794697932609580454525 2325673011724728592670447)
                      ·
                        rfl

theorem cell23_4529232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 3].length) (baseStart_4529232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529232 prefixEnd_4529232 := by exact prefixLift 4529232
  have htrace : WordTrace (prefixWord ++ tailWord_4529232) baseStart_4529232 baseEnd_4529232 := by
    simpa [prefixWord, tailWord_4529232, baseEnd_4529232] using wordTrace_append hprefix tailTrace_4529232
  have hstable : (prefixWord ++ tailWord_4529232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529232).length < 2 ^ (prefixWord ++ tailWord_4529232).sum := by decide
  have hdescent : baseEnd_4529232 < baseStart_4529232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529249 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 2, 2, 3]
def baseStart_4529249 : Nat := 118140960795 + 4529249 * 2 ^ 59
def prefixEnd_4529249 : Nat := 4983230072969 + 3 ^ 40 * 4529249 * 2
def baseEnd_4529249 : Nat := 2325681740895855026157869

theorem tailTrace_4529249 : CollatzResearch.WordTrace tailWord_4529249 prefixEnd_4529249 2325681740895855026157869 := by
  unfold tailWord_4529249
  simp only [CollatzResearch.WordTrace]
  refine ⟨165195282368311881990110801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110130188245541254660073867 165195282368311881990110801)
  ·
    refine ⟨123896461776233911492583101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165195282368311881990110801 123896461776233911492583101)
    ·
      refine ⟨46461173166087716809718663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123896461776233911492583101 46461173166087716809718663)
      ·
        refine ⟨69691759749131575214577995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46461173166087716809718663 69691759749131575214577995)
        ·
          refine ⟨104537639623697362821866993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69691759749131575214577995 104537639623697362821866993)
          ·
            refine ⟨78403229717773022116400245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104537639623697362821866993 78403229717773022116400245)
            ·
              refine ⟨7350302786041220823412523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78403229717773022116400245 7350302786041220823412523)
              ·
                refine ⟨11025454179061831235118785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7350302786041220823412523 11025454179061831235118785)
                ·
                  refine ⟨8269090634296373426339089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11025454179061831235118785 8269090634296373426339089)
                  ·
                    refine ⟨6201817975722280069754317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8269090634296373426339089 6201817975722280069754317)
                    ·
                      refine ⟨2325681740895855026157869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6201817975722280069754317 2325681740895855026157869)
                      ·
                        rfl

theorem cell23_4529249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_4529249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529249 prefixEnd_4529249 := by exact prefixLift 4529249
  have htrace : WordTrace (prefixWord ++ tailWord_4529249) baseStart_4529249 baseEnd_4529249 := by
    simpa [prefixWord, tailWord_4529249, baseEnd_4529249] using wordTrace_append hprefix tailTrace_4529249
  have hstable : (prefixWord ++ tailWord_4529249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529249).length < 2 ^ (prefixWord ++ tailWord_4529249).sum := by decide
  have hdescent : baseEnd_4529249 < baseStart_4529249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529289 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 1, 5, 2]
def baseStart_4529289 : Nat := 118140960795 + 4529289 * 2 ^ 59
def prefixEnd_4529289 : Nat := 4983230072969 + 3 ^ 40 * 4529289 * 2
def baseEnd_4529289 : Nat := 2325702280122034869657685

theorem tailTrace_4529289 : CollatzResearch.WordTrace tailWord_4529289 prefixEnd_4529289 2325702280122034869657685 := by
  unfold tailWord_4529289
  simp only [CollatzResearch.WordTrace]
  refine ⟨165196741288166968821566921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110131160858777979214377947 165196741288166968821566921)
  ·
    refine ⟨123897555966125226616175191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165196741288166968821566921 123897555966125226616175191)
    ·
      refine ⟨185846333949187839924262787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123897555966125226616175191 185846333949187839924262787)
      ·
        refine ⟨278769500923781759886394181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185846333949187839924262787 278769500923781759886394181)
        ·
          refine ⟨52269281423209079978698909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 278769500923781759886394181 52269281423209079978698909)
          ·
            refine ⟨19600980533703404992012091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52269281423209079978698909 19600980533703404992012091)
            ·
              refine ⟨29401470800555107488018137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19600980533703404992012091 29401470800555107488018137)
              ·
                refine ⟨22051103100416330616013603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29401470800555107488018137 22051103100416330616013603)
                ·
                  refine ⟨33076654650624495924020405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22051103100416330616013603 33076654650624495924020405)
                  ·
                    refine ⟨3100936373496046492876913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33076654650624495924020405 3100936373496046492876913)
                    ·
                      refine ⟨2325702280122034869657685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3100936373496046492876913 2325702280122034869657685)
                      ·
                        rfl

theorem cell23_4529289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 5, 2].length) (baseStart_4529289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529289 prefixEnd_4529289 := by exact prefixLift 4529289
  have htrace : WordTrace (prefixWord ++ tailWord_4529289) baseStart_4529289 baseEnd_4529289 := by
    simpa [prefixWord, tailWord_4529289, baseEnd_4529289] using wordTrace_append hprefix tailTrace_4529289
  have hstable : (prefixWord ++ tailWord_4529289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529289).length < 2 ^ (prefixWord ++ tailWord_4529289).sum := by decide
  have hdescent : baseEnd_4529289 < baseStart_4529289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529306 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2]
def baseStart_4529306 : Nat := 118140960795 + 4529306 * 2 ^ 59
def prefixEnd_4529306 : Nat := 4983230072969 + 3 ^ 40 * 4529306 * 2
def baseEnd_4529306 : Nat := 2325711009293161303145107

theorem tailTrace_4529306 : CollatzResearch.WordTrace tailWord_4529306 prefixEnd_4529306 2325711009293161303145107 := by
  unfold tailWord_4529306
  simp only [CollatzResearch.WordTrace]
  refine ⟨41299340332276345181233943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110131574219403587149957181 41299340332276345181233943)
  ·
    refine ⟨61949010498414517771850915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41299340332276345181233943 61949010498414517771850915)
    ·
      refine ⟨92923515747621776657776373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61949010498414517771850915 92923515747621776657776373)
      ·
        refine ⟨8711579601339541561666535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92923515747621776657776373 8711579601339541561666535)
        ·
          refine ⟨13067369402009312342499803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8711579601339541561666535 13067369402009312342499803)
          ·
            refine ⟨19601054103013968513749705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13067369402009312342499803 19601054103013968513749705)
            ·
              refine ⟨14700790577260476385312279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19601054103013968513749705 14700790577260476385312279)
              ·
                refine ⟨22051185865890714577968419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14700790577260476385312279 22051185865890714577968419)
                ·
                  refine ⟨33076778798836071866952629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22051185865890714577968419 33076778798836071866952629)
                  ·
                    refine ⟨3100948012390881737526809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33076778798836071866952629 3100948012390881737526809)
                    ·
                      refine ⟨2325711009293161303145107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3100948012390881737526809 2325711009293161303145107)
                      ·
                        rfl

theorem cell23_4529306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_4529306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529306 prefixEnd_4529306 := by exact prefixLift 4529306
  have htrace : WordTrace (prefixWord ++ tailWord_4529306) baseStart_4529306 baseEnd_4529306 := by
    simpa [prefixWord, tailWord_4529306, baseEnd_4529306] using wordTrace_append hprefix tailTrace_4529306
  have hstable : (prefixWord ++ tailWord_4529306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529306).length < 2 ^ (prefixWord ++ tailWord_4529306).sum := by decide
  have hdescent : baseEnd_4529306 < baseStart_4529306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529312 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 3, 6]
def baseStart_4529312 : Nat := 118140960795 + 4529312 * 2 ^ 59
def prefixEnd_4529312 : Nat := 4983230072969 + 3 ^ 40 * 4529312 * 2
def baseEnd_4529312 : Nat := 775238030059029426556693

theorem tailTrace_4529312 : CollatzResearch.WordTrace tailWord_4529312 prefixEnd_4529312 775238030059029426556693 := by
  unfold tailWord_4529312
  simp only [CollatzResearch.WordTrace]
  refine ⟨82598790083541821874827095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110131720111389095833102793 82598790083541821874827095)
  ·
    refine ⟨123898185125312732812240643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82598790083541821874827095 123898185125312732812240643)
    ·
      refine ⟨185847277687969099218360965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123898185125312732812240643 185847277687969099218360965)
      ·
        refine ⟨34846364566494206103442681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185847277687969099218360965 34846364566494206103442681)
        ·
          refine ⟨26134773424870654577582011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34846364566494206103442681 26134773424870654577582011)
          ·
            refine ⟨39202160137305981866373017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26134773424870654577582011 39202160137305981866373017)
            ·
              refine ⟨29401620102979486399779763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39202160137305981866373017 29401620102979486399779763)
              ·
                refine ⟨44102430154469229599669645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29401620102979486399779763 44102430154469229599669645)
                ·
                  refine ⟨16538411307925961099876117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44102430154469229599669645 16538411307925961099876117)
                  ·
                    refine ⟨775238030059029426556693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16538411307925961099876117 775238030059029426556693)
                    ·
                      rfl

theorem cell23_4529312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3, 6].length) (baseStart_4529312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529312 prefixEnd_4529312 := by exact prefixLift 4529312
  have htrace : WordTrace (prefixWord ++ tailWord_4529312) baseStart_4529312 baseEnd_4529312 := by
    simpa [prefixWord, tailWord_4529312, baseEnd_4529312] using wordTrace_append hprefix tailTrace_4529312
  have hstable : (prefixWord ++ tailWord_4529312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529312).length < 2 ^ (prefixWord ++ tailWord_4529312).sum := by decide
  have hdescent : baseEnd_4529312 < baseStart_4529312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529330 : List Nat := [3, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3]
def baseStart_4529330 : Nat := 118140960795 + 4529330 * 2 ^ 59
def prefixEnd_4529330 : Nat := 4983230072969 + 3 ^ 40 * 4529330 * 2
def baseEnd_4529330 : Nat := 2325723332828869209244997

theorem tailTrace_4529330 : CollatzResearch.WordTrace tailWord_4529330 prefixEnd_4529330 2325723332828869209244997 := by
  unfold tailWord_4529330
  simp only [CollatzResearch.WordTrace]
  refine ⟨41299559170254608205952361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110132157787345621882539629 41299559170254608205952361)
  ·
    refine ⟨30974669377690956154464271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41299559170254608205952361 30974669377690956154464271)
    ·
      refine ⟨46462004066536434231696407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30974669377690956154464271 46462004066536434231696407)
      ·
        refine ⟨69693006099804651347544611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46462004066536434231696407 69693006099804651347544611)
        ·
          refine ⟨104539509149706977021316917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69693006099804651347544611 104539509149706977021316917)
          ·
            refine ⟨9800578982785029095748461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104539509149706977021316917 9800578982785029095748461)
            ·
              refine ⟨3675217118544385910905673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9800578982785029095748461 3675217118544385910905673)
              ·
                refine ⟨2756412838908289433179255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3675217118544385910905673 2756412838908289433179255)
                ·
                  refine ⟨4134619258362434149768883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756412838908289433179255 4134619258362434149768883)
                  ·
                    refine ⟨6201928887543651224653325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4134619258362434149768883 6201928887543651224653325)
                    ·
                      refine ⟨2325723332828869209244997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6201928887543651224653325 2325723332828869209244997)
                      ·
                        rfl

theorem cell23_4529330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_4529330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529330 prefixEnd_4529330 := by exact prefixLift 4529330
  have htrace : WordTrace (prefixWord ++ tailWord_4529330) baseStart_4529330 baseEnd_4529330 := by
    simpa [prefixWord, tailWord_4529330, baseEnd_4529330] using wordTrace_append hprefix tailTrace_4529330
  have hstable : (prefixWord ++ tailWord_4529330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529330).length < 2 ^ (prefixWord ++ tailWord_4529330).sum := by decide
  have hdescent : baseEnd_4529330 < baseStart_4529330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529336 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 3, 2, 2]
def baseStart_4529336 : Nat := 118140960795 + 4529336 * 2 ^ 59
def prefixEnd_4529336 : Nat := 4983230072969 + 3 ^ 40 * 4529336 * 2
def baseEnd_4529336 : Nat := 2325726413712796185769969

theorem tailTrace_4529336 : CollatzResearch.WordTrace tailWord_4529336 prefixEnd_4529336 2325726413712796185769969 := by
  unfold tailWord_4529336
  simp only [CollatzResearch.WordTrace]
  refine ⟨82599227759498347924263931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110132303679331130565685241 82599227759498347924263931)
  ·
    refine ⟨123898841639247521886395897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82599227759498347924263931 123898841639247521886395897)
    ·
      refine ⟨92924131229435641414796923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123898841639247521886395897 92924131229435641414796923)
      ·
        refine ⟨139386196844153462122195385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92924131229435641414796923 139386196844153462122195385)
        ·
          refine ⟨104539647633115096591646539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139386196844153462122195385 104539647633115096591646539)
          ·
            refine ⟨156809471449672644887469809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104539647633115096591646539 156809471449672644887469809)
            ·
              refine ⟨117607103587254483665602357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156809471449672644887469809 117607103587254483665602357)
              ·
                refine ⟨11025665961305107843650221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117607103587254483665602357 11025665961305107843650221)
                ·
                  refine ⟨4134624735489415441368833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11025665961305107843650221 4134624735489415441368833)
                  ·
                    refine ⟨3100968551617061581026625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4134624735489415441368833 3100968551617061581026625)
                    ·
                      refine ⟨2325726413712796185769969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3100968551617061581026625 2325726413712796185769969)
                      ·
                        rfl

theorem cell23_4529336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 3, 2, 2].length) (baseStart_4529336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529336 prefixEnd_4529336 := by exact prefixLift 4529336
  have htrace : WordTrace (prefixWord ++ tailWord_4529336) baseStart_4529336 baseEnd_4529336 := by
    simpa [prefixWord, tailWord_4529336, baseEnd_4529336] using wordTrace_append hprefix tailTrace_4529336
  have hstable : (prefixWord ++ tailWord_4529336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529336).length < 2 ^ (prefixWord ++ tailWord_4529336).sum := by decide
  have hdescent : baseEnd_4529336 < baseStart_4529336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529350 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_4529350 : Nat := 118140960795 + 4529350 * 2 ^ 59
def prefixEnd_4529350 : Nat := 4983230072969 + 3 ^ 40 * 4529350 * 2
def baseEnd_4529350 : Nat := 775244534147319710331635

theorem tailTrace_4529350 : CollatzResearch.WordTrace tailWord_4529350 prefixEnd_4529350 775244534147319710331635 := by
  unfold tailWord_4529350
  simp only [CollatzResearch.WordTrace]
  refine ⟨5162467691904561757485547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 110132644093963984159691669 5162467691904561757485547)
  ·
    refine ⟨7743701537856842636228321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5162467691904561757485547 7743701537856842636228321)
    ·
      refine ⟨5807776153392631977171241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7743701537856842636228321 5807776153392631977171241)
      ·
        refine ⟨4355832115044473982878431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5807776153392631977171241 4355832115044473982878431)
        ·
          refine ⟨6533748172566710974317647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4355832115044473982878431 6533748172566710974317647)
          ·
            refine ⟨9800622258850066461476471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6533748172566710974317647 9800622258850066461476471)
            ·
              refine ⟨14700933388275099692214707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9800622258850066461476471 14700933388275099692214707)
              ·
                refine ⟨22051400082412649538322061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14700933388275099692214707 22051400082412649538322061)
                ·
                  refine ⟨8269275030904743576870773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22051400082412649538322061 8269275030904743576870773)
                  ·
                    refine ⟨775244534147319710331635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8269275030904743576870773 775244534147319710331635)
                    ·
                      rfl

theorem cell23_4529350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_4529350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529350 prefixEnd_4529350 := by exact prefixLift 4529350
  have htrace : WordTrace (prefixWord ++ tailWord_4529350) baseStart_4529350 baseEnd_4529350 := by
    simpa [prefixWord, tailWord_4529350, baseEnd_4529350] using wordTrace_append hprefix tailTrace_4529350
  have hstable : (prefixWord ++ tailWord_4529350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529350).length < 2 ^ (prefixWord ++ tailWord_4529350).sum := by decide
  have hdescent : baseEnd_4529350 < baseStart_4529350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529357 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_4529357 : Nat := 118140960795 + 4529357 * 2 ^ 59
def prefixEnd_4529357 : Nat := 4983230072969 + 3 ^ 40 * 4529357 * 2
def baseEnd_4529357 : Nat := 2325737196806540603607373

theorem tailTrace_4529357 : CollatzResearch.WordTrace tailWord_4529357 prefixEnd_4529357 2325737196806540603607373 := by
  unfold tailWord_4529357
  simp only [CollatzResearch.WordTrace]
  refine ⟨165199221451920616435042325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110132814301280410956694883 165199221451920616435042325)
  ·
    refine ⟨7743713505558778895392609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 165199221451920616435042325 7743713505558778895392609)
    ·
      refine ⟨5807785129169084171544457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7743713505558778895392609 5807785129169084171544457)
      ·
        refine ⟨4355838846876813128658343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5807785129169084171544457 4355838846876813128658343)
        ·
          refine ⟨6533758270315219692987515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4355838846876813128658343 6533758270315219692987515)
          ·
            refine ⟨9800637405472829539481273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6533758270315219692987515 9800637405472829539481273)
            ·
              refine ⟨7350478054104622154610955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9800637405472829539481273 7350478054104622154610955)
              ·
                refine ⟨11025717081156933231916433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7350478054104622154610955 11025717081156933231916433)
                ·
                  refine ⟨8269287810867699923937325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11025717081156933231916433 8269287810867699923937325)
                  ·
                    refine ⟨3100982929075387471476497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8269287810867699923937325 3100982929075387471476497)
                    ·
                      refine ⟨2325737196806540603607373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3100982929075387471476497 2325737196806540603607373)
                      ·
                        rfl

theorem cell23_4529357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_4529357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529357 prefixEnd_4529357 := by exact prefixLift 4529357
  have htrace : WordTrace (prefixWord ++ tailWord_4529357) baseStart_4529357 baseEnd_4529357 := by
    simpa [prefixWord, tailWord_4529357, baseEnd_4529357] using wordTrace_append hprefix tailTrace_4529357
  have hstable : (prefixWord ++ tailWord_4529357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529357).length < 2 ^ (prefixWord ++ tailWord_4529357).sum := by decide
  have hdescent : baseEnd_4529357 < baseStart_4529357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529373 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_4529373 : Nat := 118140960795 + 4529373 * 2 ^ 59
def prefixEnd_4529373 : Nat := 4983230072969 + 3 ^ 40 * 4529373 * 2
def baseEnd_4529373 : Nat := 2325745412497012541007299

theorem tailTrace_4529373 : CollatzResearch.WordTrace tailWord_4529373 prefixEnd_4529373 2325745412497012541007299 := by
  unfold tailWord_4529373
  simp only [CollatzResearch.WordTrace]
  refine ⟨165199805019862651167624773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110133203346575100778416515 165199805019862651167624773)
  ·
    refine ⟨30974963441224247093929645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165199805019862651167624773 30974963441224247093929645)
    ·
      refine ⟨11615611290459092660223617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30974963441224247093929645 11615611290459092660223617)
      ·
        refine ⟨8711708467844319495167713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11615611290459092660223617 8711708467844319495167713)
        ·
          refine ⟨6533781350883239621375785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8711708467844319495167713 6533781350883239621375785)
          ·
            refine ⟨4900336013162429716031839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6533781350883239621375785 4900336013162429716031839)
            ·
              refine ⟨7350504019743644574047759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4900336013162429716031839 7350504019743644574047759)
              ·
                refine ⟨11025756029615466861071639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7350504019743644574047759 11025756029615466861071639)
                ·
                  refine ⟨16538634044423200291607459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11025756029615466861071639 16538634044423200291607459)
                  ·
                    refine ⟨24807951066634800437411189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16538634044423200291607459 24807951066634800437411189)
                    ·
                      refine ⟨2325745412497012541007299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24807951066634800437411189 2325745412497012541007299)
                      ·
                        rfl

theorem cell23_4529373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_4529373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529373 prefixEnd_4529373 := by exact prefixLift 4529373
  have htrace : WordTrace (prefixWord ++ tailWord_4529373) baseStart_4529373 baseEnd_4529373 := by
    simpa [prefixWord, tailWord_4529373, baseEnd_4529373] using wordTrace_append hprefix tailTrace_4529373
  have hstable : (prefixWord ++ tailWord_4529373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529373).length < 2 ^ (prefixWord ++ tailWord_4529373).sum := by decide
  have hdescent : baseEnd_4529373 < baseStart_4529373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529387 : List Nat := [1, 1, 1, 1, 2, 8, 2, 2, 1, 2, 2]
def baseStart_4529387 : Nat := 118140960795 + 4529387 * 2 ^ 59
def prefixEnd_4529387 : Nat := 4983230072969 + 3 ^ 40 * 4529387 * 2
def baseEnd_4529387 : Nat := 2325752601226175486232235

theorem tailTrace_4529387 : CollatzResearch.WordTrace tailWord_4529387 prefixEnd_4529387 2325752601226175486232235 := by
  unfold tailWord_4529387
  simp only [CollatzResearch.WordTrace]
  refine ⟨165200315641811931558634415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110133543761207954372422943 165200315641811931558634415)
  ·
    refine ⟨247800473462717897337951623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165200315641811931558634415 247800473462717897337951623)
    ·
      refine ⟨371700710194076846006927435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247800473462717897337951623 371700710194076846006927435)
      ·
        refine ⟨557551065291115269010391153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371700710194076846006927435 557551065291115269010391153)
        ·
          refine ⟨418163298968336451757793365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557551065291115269010391153 418163298968336451757793365)
          ·
            refine ⟨4900351159785192794036641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 418163298968336451757793365 4900351159785192794036641)
            ·
              refine ⟨3675263369838894595527481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4900351159785192794036641 3675263369838894595527481)
              ·
                refine ⟨2756447527379170946645611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3675263369838894595527481 2756447527379170946645611)
                ·
                  refine ⟨4134671291068756419968417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756447527379170946645611 4134671291068756419968417)
                  ·
                    refine ⟨3101003468301567314976313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4134671291068756419968417 3101003468301567314976313)
                    ·
                      refine ⟨2325752601226175486232235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3101003468301567314976313 2325752601226175486232235)
                      ·
                        rfl

theorem cell23_4529387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 1, 2, 2].length) (baseStart_4529387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529387 prefixEnd_4529387 := by exact prefixLift 4529387
  have htrace : WordTrace (prefixWord ++ tailWord_4529387) baseStart_4529387 baseEnd_4529387 := by
    simpa [prefixWord, tailWord_4529387, baseEnd_4529387] using wordTrace_append hprefix tailTrace_4529387
  have hstable : (prefixWord ++ tailWord_4529387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529387).length < 2 ^ (prefixWord ++ tailWord_4529387).sum := by decide
  have hdescent : baseEnd_4529387 < baseStart_4529387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529389 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_4529389 : Nat := 118140960795 + 4529389 * 2 ^ 59
def prefixEnd_4529389 : Nat := 4983230072969 + 3 ^ 40 * 4529389 * 2
def baseEnd_4529389 : Nat := 775251209395828159469075

theorem tailTrace_4529389 : CollatzResearch.WordTrace tailWord_4529389 prefixEnd_4529389 775251209395828159469075 := by
  unfold tailWord_4529389
  simp only [CollatzResearch.WordTrace]
  refine ⟨165200388587804685900207221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110133592391869790600138147 165200388587804685900207221)
  ·
    refine ⟨15487536430106689303144427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165200388587804685900207221 15487536430106689303144427)
    ·
      refine ⟨23231304645160033954716641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15487536430106689303144427 23231304645160033954716641)
      ·
        refine ⟨17423478483870025466037481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23231304645160033954716641 17423478483870025466037481)
        ·
          refine ⟨13067608862902519099528111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17423478483870025466037481 13067608862902519099528111)
          ·
            refine ⟨19601413294353778649292167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13067608862902519099528111 19601413294353778649292167)
            ·
              refine ⟨29402119941530667973938251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19601413294353778649292167 29402119941530667973938251)
              ·
                refine ⟨44103179912296001960907377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29402119941530667973938251 44103179912296001960907377)
                ·
                  refine ⟨33077384934222001470680533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44103179912296001960907377 33077384934222001470680533)
                  ·
                    refine ⟨775251209395828159469075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33077384934222001470680533 775251209395828159469075)
                    ·
                      rfl

theorem cell23_4529389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_4529389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529389 prefixEnd_4529389 := by exact prefixLift 4529389
  have htrace : WordTrace (prefixWord ++ tailWord_4529389) baseStart_4529389 baseEnd_4529389 := by
    simpa [prefixWord, tailWord_4529389, baseEnd_4529389] using wordTrace_append hprefix tailTrace_4529389
  have hstable : (prefixWord ++ tailWord_4529389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529389).length < 2 ^ (prefixWord ++ tailWord_4529389).sum := by decide
  have hdescent : baseEnd_4529389 < baseStart_4529389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529443 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 4, 2, 2]
def baseStart_4529443 : Nat := 118140960795 + 4529443 * 2 ^ 59
def prefixEnd_4529443 : Nat := 4983230072969 + 3 ^ 40 * 4529443 * 2
def baseEnd_4529443 : Nat := 2325781356142827267131977

theorem tailTrace_4529443 : CollatzResearch.WordTrace tailWord_4529443 prefixEnd_4529443 2325781356142827267131977 := by
  unfold tailWord_4529443
  simp only [CollatzResearch.WordTrace]
  refine ⟨165202358129609053122672983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110134905419739368748448655 165202358129609053122672983)
  ·
    refine ⟨247803537194413579684009475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165202358129609053122672983 247803537194413579684009475)
    ·
      refine ⟨371705305791620369526014213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247803537194413579684009475 371705305791620369526014213)
      ·
        refine ⟨69694744835928819286127665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 371705305791620369526014213 69694744835928819286127665)
        ·
          refine ⟨52271058626946614464595749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69694744835928819286127665 52271058626946614464595749)
          ·
            refine ⟨9800823492552490212111703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52271058626946614464595749 9800823492552490212111703)
            ·
              refine ⟨14701235238828735318167555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9800823492552490212111703 14701235238828735318167555)
              ·
                refine ⟨22051852858243102977251333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14701235238828735318167555 22051852858243102977251333)
                ·
                  refine ⟨4134722410920581808234625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22051852858243102977251333 4134722410920581808234625)
                  ·
                    refine ⟨3101041808190436356175969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4134722410920581808234625 3101041808190436356175969)
                    ·
                      refine ⟨2325781356142827267131977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3101041808190436356175969 2325781356142827267131977)
                      ·
                        rfl

theorem cell23_4529443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_4529443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529443 prefixEnd_4529443 := by exact prefixLift 4529443
  have htrace : WordTrace (prefixWord ++ tailWord_4529443) baseStart_4529443 baseEnd_4529443 := by
    simpa [prefixWord, tailWord_4529443, baseEnd_4529443] using wordTrace_append hprefix tailTrace_4529443
  have hstable : (prefixWord ++ tailWord_4529443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529443).length < 2 ^ (prefixWord ++ tailWord_4529443).sum := by decide
  have hdescent : baseEnd_4529443 < baseStart_4529443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529479 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 1, 7]
def baseStart_4529479 : Nat := 118140960795 + 4529479 * 2 ^ 59
def prefixEnd_4529479 : Nat := 4983230072969 + 3 ^ 40 * 4529479 * 2
def baseEnd_4529479 : Nat := 775266613815463042093937

theorem tailTrace_4529479 : CollatzResearch.WordTrace tailWord_4529479 prefixEnd_4529479 775266613815463042093937 := by
  unfold tailWord_4529479
  simp only [CollatzResearch.WordTrace]
  refine ⟨165203671157478631270983491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110135780771652420847322327 165203671157478631270983491)
  ·
    refine ⟨247805506736217946906475237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165203671157478631270983491 247805506736217946906475237)
    ·
      refine ⟨46463532513040865044964107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 247805506736217946906475237 46463532513040865044964107)
      ·
        refine ⟨69695298769561297567446161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46463532513040865044964107 69695298769561297567446161)
        ·
          refine ⟨52271474077170973175584621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69695298769561297567446161 52271474077170973175584621)
          ·
            refine ⟨19601802778939114940844233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52271474077170973175584621 19601802778939114940844233)
            ·
              refine ⟨14701352084204336205633175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19601802778939114940844233 14701352084204336205633175)
              ·
                refine ⟨22052028126306504308449763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14701352084204336205633175 22052028126306504308449763)
                ·
                  refine ⟨33078042189459756462674645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22052028126306504308449763 33078042189459756462674645)
                  ·
                    refine ⟨775266613815463042093937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33078042189459756462674645 775266613815463042093937)
                    ·
                      rfl

theorem cell23_4529479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_4529479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529479 prefixEnd_4529479 := by exact prefixLift 4529479
  have htrace : WordTrace (prefixWord ++ tailWord_4529479) baseStart_4529479 baseEnd_4529479 := by
    simpa [prefixWord, tailWord_4529479, baseEnd_4529479] using wordTrace_append hprefix tailTrace_4529479
  have hstable : (prefixWord ++ tailWord_4529479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529479).length < 2 ^ (prefixWord ++ tailWord_4529479).sum := by decide
  have hdescent : baseEnd_4529479 < baseStart_4529479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529489 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 1, 2, 5]
def baseStart_4529489 : Nat := 118140960795 + 4529489 * 2 ^ 59
def prefixEnd_4529489 : Nat := 4983230072969 + 3 ^ 40 * 4529489 * 2
def baseEnd_4529489 : Nat := 2325804976252934087156765

theorem tailTrace_4529489 : CollatzResearch.WordTrace tailWord_4529489 prefixEnd_4529489 2325804976252934087156765 := by
  unfold tailWord_4529489
  simp only [CollatzResearch.WordTrace]
  refine ⟨165204035887442402978847521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110136023924961601985898347 165204035887442402978847521)
  ·
    refine ⟨123903026915581802234135641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165204035887442402978847521 123903026915581802234135641)
    ·
      refine ⟨92927270186686351675601731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123903026915581802234135641 92927270186686351675601731)
      ·
        refine ⟨139390905280029527513402597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92927270186686351675601731 139390905280029527513402597)
        ·
          refine ⟨26135794740005536408762987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139390905280029527513402597 26135794740005536408762987)
          ·
            refine ⟨39203692110008304613144481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26135794740005536408762987 39203692110008304613144481)
            ·
              refine ⟨29402769082506228459858361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39203692110008304613144481 29402769082506228459858361)
              ·
                refine ⟨22052076811879671344893771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29402769082506228459858361 22052076811879671344893771)
                ·
                  refine ⟨33078115217819507017340657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22052076811879671344893771 33078115217819507017340657)
                  ·
                    refine ⟨24808586413364630263005493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33078115217819507017340657 24808586413364630263005493)
                    ·
                      refine ⟨2325804976252934087156765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24808586413364630263005493 2325804976252934087156765)
                      ·
                        rfl

theorem cell23_4529489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_4529489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529489 prefixEnd_4529489 := by exact prefixLift 4529489
  have htrace : WordTrace (prefixWord ++ tailWord_4529489) baseStart_4529489 baseEnd_4529489 := by
    simpa [prefixWord, tailWord_4529489, baseEnd_4529489] using wordTrace_append hprefix tailTrace_4529489
  have hstable : (prefixWord ++ tailWord_4529489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529489).length < 2 ^ (prefixWord ++ tailWord_4529489).sum := by decide
  have hdescent : baseEnd_4529489 < baseStart_4529489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529506 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_4529506 : Nat := 118140960795 + 4529506 * 2 ^ 59
def prefixEnd_4529506 : Nat := 4983230072969 + 3 ^ 40 * 4529506 * 2
def baseEnd_4529506 : Nat := 2325813705424060520644187

theorem tailTrace_4529506 : CollatzResearch.WordTrace tailWord_4529506 prefixEnd_4529506 2325813705424060520644187 := by
  unfold tailWord_4529506
  simp only [CollatzResearch.WordTrace]
  refine ⟨41301163982095203720554093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110136437285587209921477581 41301163982095203720554093)
  ·
    refine ⟨15487936493285701395207785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41301163982095203720554093 15487936493285701395207785)
    ·
      refine ⟨11615952369964276046405839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15487936493285701395207785 11615952369964276046405839)
      ·
        refine ⟨17423928554946414069608759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11615952369964276046405839 17423928554946414069608759)
        ·
          refine ⟨26135892832419621104413139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17423928554946414069608759 26135892832419621104413139)
          ·
            refine ⟨39203839248629431656619709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26135892832419621104413139 39203839248629431656619709)
            ·
              refine ⟨14701439718236036871232391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39203839248629431656619709 14701439718236036871232391)
              ·
                refine ⟨22052159577354055306848587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14701439718236036871232391 22052159577354055306848587)
                ·
                  refine ⟨33078239366031082960272881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22052159577354055306848587 33078239366031082960272881)
                  ·
                    refine ⟨24808679524523312220204661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33078239366031082960272881 24808679524523312220204661)
                    ·
                      refine ⟨2325813705424060520644187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24808679524523312220204661 2325813705424060520644187)
                      ·
                        rfl

theorem cell23_4529506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_4529506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529506 prefixEnd_4529506 := by exact prefixLift 4529506
  have htrace : WordTrace (prefixWord ++ tailWord_4529506) baseStart_4529506 baseEnd_4529506 := by
    simpa [prefixWord, tailWord_4529506, baseEnd_4529506] using wordTrace_append hprefix tailTrace_4529506
  have hstable : (prefixWord ++ tailWord_4529506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529506).length < 2 ^ (prefixWord ++ tailWord_4529506).sum := by decide
  have hdescent : baseEnd_4529506 < baseStart_4529506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529529 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 2, 4, 4]
def baseStart_4529529 : Nat := 118140960795 + 4529529 * 2 ^ 59
def prefixEnd_4529529 : Nat := 4983230072969 + 3 ^ 40 * 4529529 * 2
def baseEnd_4529529 : Nat := 2325825515479113930656581

theorem tailTrace_4529529 : CollatzResearch.WordTrace tailWord_4529529 prefixEnd_4529529 2325825515479113930656581 := by
  unfold tailWord_4529529
  simp only [CollatzResearch.WordTrace]
  refine ⟨165205494807297489810303641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110136996538198326540202427 165205494807297489810303641)
  ·
    refine ⟨123904121105473117357727731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165205494807297489810303641 123904121105473117357727731)
    ·
      refine ⟨185856181658209676036591597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123904121105473117357727731 185856181658209676036591597)
      ·
        refine ⟨69696068121828628513721849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185856181658209676036591597 69696068121828628513721849)
        ·
          refine ⟨52272051091371471385291387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69696068121828628513721849 52272051091371471385291387)
          ·
            refine ⟨78408076637057207077937081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52272051091371471385291387 78408076637057207077937081)
            ·
              refine ⟨58806057477792905308452811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78408076637057207077937081 58806057477792905308452811)
              ·
                refine ⟨88209086216689357962679217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58806057477792905308452811 88209086216689357962679217)
                ·
                  refine ⟨66156814662517018472009413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88209086216689357962679217 66156814662517018472009413)
                  ·
                    refine ⟨12404402749221940963501765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66156814662517018472009413 12404402749221940963501765)
                    ·
                      refine ⟨2325825515479113930656581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12404402749221940963501765 2325825515479113930656581)
                      ·
                        rfl

theorem cell23_4529529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_4529529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529529 prefixEnd_4529529 := by exact prefixLift 4529529
  have htrace : WordTrace (prefixWord ++ tailWord_4529529) baseStart_4529529 baseEnd_4529529 := by
    simpa [prefixWord, tailWord_4529529, baseEnd_4529529] using wordTrace_append hprefix tailTrace_4529529
  have hstable : (prefixWord ++ tailWord_4529529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529529).length < 2 ^ (prefixWord ++ tailWord_4529529).sum := by decide
  have hdescent : baseEnd_4529529 < baseStart_4529529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529559 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 6]
def baseStart_4529559 : Nat := 118140960795 + 4529559 * 2 ^ 59
def prefixEnd_4529559 : Nat := 4983230072969 + 3 ^ 40 * 4529559 * 2
def baseEnd_4529559 : Nat := 2325840919898748813281443

theorem tailTrace_4529559 : CollatzResearch.WordTrace tailWord_4529559 prefixEnd_4529559 2325840919898748813281443 := by
  unfold tailWord_4529559
  simp only [CollatzResearch.WordTrace]
  refine ⟨165206588997188804933895731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110137725998125869955930487 165206588997188804933895731)
  ·
    refine ⟨247809883495783207400843597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165206588997188804933895731 247809883495783207400843597)
    ·
      refine ⟨92928706310918702775316349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247809883495783207400843597 92928706310918702775316349)
      ·
        refine ⟨34848264866594513540743631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92928706310918702775316349 34848264866594513540743631)
        ·
          refine ⟨52272397299891770311115447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34848264866594513540743631 52272397299891770311115447)
          ·
            refine ⟨78408595949837655466673171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52272397299891770311115447 78408595949837655466673171)
            ·
              refine ⟨117612893924756483200009757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78408595949837655466673171 117612893924756483200009757)
              ·
                refine ⟨44104835221783681200003659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117612893924756483200009757 44104835221783681200003659)
                ·
                  refine ⟨66157252832675521800005489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44104835221783681200003659 66157252832675521800005489)
                  ·
                    refine ⟨49617939624506641350004117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66157252832675521800005489 49617939624506641350004117)
                    ·
                      refine ⟨2325840919898748813281443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49617939624506641350004117 2325840919898748813281443)
                      ·
                        rfl

theorem cell23_4529559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_4529559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529559 prefixEnd_4529559 := by exact prefixLift 4529559
  have htrace : WordTrace (prefixWord ++ tailWord_4529559) baseStart_4529559 baseEnd_4529559 := by
    simpa [prefixWord, tailWord_4529559, baseEnd_4529559] using wordTrace_append hprefix tailTrace_4529559
  have hstable : (prefixWord ++ tailWord_4529559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529559).length < 2 ^ (prefixWord ++ tailWord_4529559).sum := by decide
  have hdescent : baseEnd_4529559 < baseStart_4529559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529600 : List Nat := [2, 1, 1, 2, 3, 1, 3, 5, 1, 1, 3]
def baseStart_4529600 : Nat := 118140960795 + 4529600 * 2 ^ 59
def prefixEnd_4529600 : Nat := 4983230072969 + 3 ^ 40 * 4529600 * 2
def baseEnd_4529600 : Nat := 2325861972605583152868755

theorem tailTrace_4529600 : CollatzResearch.WordTrace tailWord_4529600 prefixEnd_4529600 2325861972605583152868755 := by
  unfold tailWord_4529600
  simp only [CollatzResearch.WordTrace]
  refine ⟨82604042195020134468069127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110138722926693512624092169 82604042195020134468069127)
  ·
    refine ⟨123906063292530201702103691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82604042195020134468069127 123906063292530201702103691)
    ·
      refine ⟨185859094938795302553155537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123906063292530201702103691 185859094938795302553155537)
      ·
        refine ⟨139394321204096476914866653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185859094938795302553155537 139394321204096476914866653)
        ·
          refine ⟨52272870451536178843074995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139394321204096476914866653 52272870451536178843074995)
          ·
            refine ⟨78409305677304268264612493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52272870451536178843074995 78409305677304268264612493)
            ·
              refine ⟨29403489628989100599229685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78409305677304268264612493 29403489628989100599229685)
              ·
                refine ⟨2756577152717728181177783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29403489628989100599229685 2756577152717728181177783)
                ·
                  refine ⟨4134865729076592271766675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756577152717728181177783 4134865729076592271766675)
                  ·
                    refine ⟨6202298593614888407650013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4134865729076592271766675 6202298593614888407650013)
                    ·
                      refine ⟨2325861972605583152868755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6202298593614888407650013 2325861972605583152868755)
                      ·
                        rfl

theorem cell23_4529600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 1, 1, 3].length) (baseStart_4529600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529600 prefixEnd_4529600 := by exact prefixLift 4529600
  have htrace : WordTrace (prefixWord ++ tailWord_4529600) baseStart_4529600 baseEnd_4529600 := by
    simpa [prefixWord, tailWord_4529600, baseEnd_4529600] using wordTrace_append hprefix tailTrace_4529600
  have hstable : (prefixWord ++ tailWord_4529600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529600).length < 2 ^ (prefixWord ++ tailWord_4529600).sum := by decide
  have hdescent : baseEnd_4529600 < baseStart_4529600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529603 : List Nat := [1, 1, 1, 3, 1, 1, 8, 1, 1, 5]
def baseStart_4529603 : Nat := 118140960795 + 4529603 * 2 ^ 59
def prefixEnd_4529603 : Nat := 4983230072969 + 3 ^ 40 * 4529603 * 2
def baseEnd_4529603 : Nat := 775287837682515547043747

theorem tailTrace_4529603 : CollatzResearch.WordTrace tailWord_4529603 prefixEnd_4529603 775287837682515547043747 := by
  unfold tailWord_4529603
  simp only [CollatzResearch.WordTrace]
  refine ⟨165208193809029400448497463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110138795872686266965664975 165208193809029400448497463)
  ·
    refine ⟨247812290713544100672746195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165208193809029400448497463 247812290713544100672746195)
    ·
      refine ⟨371718436070316151009119293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247812290713544100672746195 371718436070316151009119293)
      ·
        refine ⟨139394413526368556628419735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 371718436070316151009119293 139394413526368556628419735)
        ·
          refine ⟨209091620289552834942629603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139394413526368556628419735 209091620289552834942629603)
          ·
            refine ⟨313637430434329252413944405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209091620289552834942629603 313637430434329252413944405)
            ·
              refine ⟨3675438637902295926725911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 313637430434329252413944405 3675438637902295926725911)
              ·
                refine ⟨5513157956853443890088867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3675438637902295926725911 5513157956853443890088867)
                ·
                  refine ⟨8269736935280165835133301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5513157956853443890088867 8269736935280165835133301)
                  ·
                    refine ⟨775287837682515547043747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8269736935280165835133301 775287837682515547043747)
                    ·
                      rfl

theorem cell23_4529603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 1, 5].length) (baseStart_4529603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529603 prefixEnd_4529603 := by exact prefixLift 4529603
  have htrace : WordTrace (prefixWord ++ tailWord_4529603) baseStart_4529603 baseEnd_4529603 := by
    simpa [prefixWord, tailWord_4529603, baseEnd_4529603] using wordTrace_append hprefix tailTrace_4529603
  have hstable : (prefixWord ++ tailWord_4529603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529603).length < 2 ^ (prefixWord ++ tailWord_4529603).sum := by decide
  have hdescent : baseEnd_4529603 < baseStart_4529603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529616 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 4, 4]
def baseStart_4529616 : Nat := 118140960795 + 4529616 * 2 ^ 59
def prefixEnd_4529616 : Nat := 4983230072969 + 3 ^ 40 * 4529616 * 2
def baseEnd_4529616 : Nat := 775290062765351696756227

theorem tailTrace_4529616 : CollatzResearch.WordTrace tailWord_4529616 prefixEnd_4529616 775290062765351696756227 := by
  unfold tailWord_4529616
  simp only [CollatzResearch.WordTrace]
  refine ⟨82604333978991151834360351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110139111971988202445813801 82604333978991151834360351)
  ·
    refine ⟨123906500968486727751540527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82604333978991151834360351 123906500968486727751540527)
    ·
      refine ⟨185859751452730091627310791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123906500968486727751540527 185859751452730091627310791)
      ·
        refine ⟨278789627179095137440966187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185859751452730091627310791 278789627179095137440966187)
        ·
          refine ⟨418184440768642706161449281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278789627179095137440966187 418184440768642706161449281)
          ·
            refine ⟨313638330576482029621086961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418184440768642706161449281 313638330576482029621086961)
            ·
              refine ⟨235228747932361522215815221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313638330576482029621086961 235228747932361522215815221)
              ·
                refine ⟨22052695118658892707732677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 235228747932361522215815221 22052695118658892707732677)
                ·
                  refine ⟨4134880334748542382699877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22052695118658892707732677 4134880334748542382699877)
                  ·
                    refine ⟨775290062765351696756227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4134880334748542382699877 775290062765351696756227)
                    ·
                      rfl

theorem cell23_4529616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 4, 4].length) (baseStart_4529616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529616 prefixEnd_4529616 := by exact prefixLift 4529616
  have htrace : WordTrace (prefixWord ++ tailWord_4529616) baseStart_4529616 baseEnd_4529616 := by
    simpa [prefixWord, tailWord_4529616, baseEnd_4529616] using wordTrace_append hprefix tailTrace_4529616
  have hstable : (prefixWord ++ tailWord_4529616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529616).length < 2 ^ (prefixWord ++ tailWord_4529616).sum := by decide
  have hdescent : baseEnd_4529616 < baseStart_4529616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529626 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5]
def baseStart_4529626 : Nat := 118140960795 + 4529626 * 2 ^ 59
def prefixEnd_4529626 : Nat := 4983230072969 + 3 ^ 40 * 4529626 * 2
def baseEnd_4529626 : Nat := 2325875323102600051143635

theorem tailTrace_4529626 : CollatzResearch.WordTrace tailWord_4529626 prefixEnd_4529626 2325875323102600051143635 := by
  unfold tailWord_4529626
  simp only [CollatzResearch.WordTrace]
  refine ⟨41302258171986518844146183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110139355125297383584389821 41302258171986518844146183)
  ·
    refine ⟨61953387257979778266219275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41302258171986518844146183 61953387257979778266219275)
    ·
      refine ⟨92930080886969667399328913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61953387257979778266219275 92930080886969667399328913)
      ·
        refine ⟨69697560665227250549496685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92930080886969667399328913 69697560665227250549496685)
        ·
          refine ⟨26136585249460218956061257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69697560665227250549496685 26136585249460218956061257)
          ·
            refine ⟨19602438937095164217045943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26136585249460218956061257 19602438937095164217045943)
            ·
              refine ⟨29403658405642746325568915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19602438937095164217045943 29403658405642746325568915)
              ·
                refine ⟨44105487608464119488353373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29403658405642746325568915 44105487608464119488353373)
                ·
                  refine ⟨16539557853174044808132515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44105487608464119488353373 16539557853174044808132515)
                  ·
                    refine ⟨24809336779761067212198773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16539557853174044808132515 24809336779761067212198773)
                    ·
                      refine ⟨2325875323102600051143635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24809336779761067212198773 2325875323102600051143635)
                      ·
                        rfl

theorem cell23_4529626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_4529626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529626 prefixEnd_4529626 := by exact prefixLift 4529626
  have htrace : WordTrace (prefixWord ++ tailWord_4529626) baseStart_4529626 baseEnd_4529626 := by
    simpa [prefixWord, tailWord_4529626, baseEnd_4529626] using wordTrace_append hprefix tailTrace_4529626
  have hstable : (prefixWord ++ tailWord_4529626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529626).length < 2 ^ (prefixWord ++ tailWord_4529626).sum := by decide
  have hdescent : baseEnd_4529626 < baseStart_4529626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529633 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 1, 6]
def baseStart_4529633 : Nat := 118140960795 + 4529633 * 2 ^ 59
def prefixEnd_4529633 : Nat := 4983230072969 + 3 ^ 40 * 4529633 * 2
def baseEnd_4529633 : Nat := 775292972489060507918701

theorem tailTrace_4529633 : CollatzResearch.WordTrace tailWord_4529633 prefixEnd_4529633 775292972489060507918701 := by
  unfold tailWord_4529633
  simp only [CollatzResearch.WordTrace]
  refine ⟨165209287998920715572089553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110139525332613810381393035 165209287998920715572089553)
  ·
    refine ⟨123906965999190536679067165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165209287998920715572089553 123906965999190536679067165)
    ·
      refine ⟨46465112249696451254650187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123906965999190536679067165 46465112249696451254650187)
      ·
        refine ⟨69697668374544676881975281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46465112249696451254650187 69697668374544676881975281)
        ·
          refine ⟨52273251280908507661481461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69697668374544676881975281 52273251280908507661481461)
          ·
            refine ⟨4900617307585172593263887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52273251280908507661481461 4900617307585172593263887)
            ·
              refine ⟨7350925961377758889895831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4900617307585172593263887 7350925961377758889895831)
              ·
                refine ⟨11026388942066638334843747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7350925961377758889895831 11026388942066638334843747)
                ·
                  refine ⟨16539583413099957502265621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11026388942066638334843747 16539583413099957502265621)
                  ·
                    refine ⟨775292972489060507918701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16539583413099957502265621 775292972489060507918701)
                    ·
                      rfl

theorem cell23_4529633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_4529633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529633 prefixEnd_4529633 := by exact prefixLift 4529633
  have htrace : WordTrace (prefixWord ++ tailWord_4529633) baseStart_4529633 baseEnd_4529633 := by
    simpa [prefixWord, tailWord_4529633, baseEnd_4529633] using wordTrace_append hprefix tailTrace_4529633
  have hstable : (prefixWord ++ tailWord_4529633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529633).length < 2 ^ (prefixWord ++ tailWord_4529633).sum := by decide
  have hdescent : baseEnd_4529633 < baseStart_4529633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529640 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 3, 2, 2]
def baseStart_4529640 : Nat := 118140960795 + 4529640 * 2 ^ 59
def prefixEnd_4529640 : Nat := 4983230072969 + 3 ^ 40 * 4529640 * 2
def baseEnd_4529640 : Nat := 2325882511831762996368571

theorem tailTrace_4529640 : CollatzResearch.WordTrace tailWord_4529640 prefixEnd_4529640 2325882511831762996368571 := by
  unfold tailWord_4529640
  simp only [CollatzResearch.WordTrace]
  refine ⟨82604771654947677883797187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110139695539930237178396249 82604771654947677883797187)
  ·
    refine ⟨123907157482421516825695781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82604771654947677883797187 123907157482421516825695781)
    ·
      refine ⟨23232592027954034404817959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123907157482421516825695781 23232592027954034404817959)
      ·
        refine ⟨34848888041931051607226939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23232592027954034404817959 34848888041931051607226939)
        ·
          refine ⟨52273332062896577410840409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34848888041931051607226939 52273332062896577410840409)
          ·
            refine ⟨39204999047172433058130307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52273332062896577410840409 39204999047172433058130307)
            ·
              refine ⟨58807498570758649587195461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39204999047172433058130307 58807498570758649587195461)
              ·
                refine ⟨11026405982017246797599149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58807498570758649587195461 11026405982017246797599149)
                ·
                  refine ⟨4134902243256467549099681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11026405982017246797599149 4134902243256467549099681)
                  ·
                    refine ⟨3101176682442350661824761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4134902243256467549099681 3101176682442350661824761)
                    ·
                      refine ⟨2325882511831762996368571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3101176682442350661824761 2325882511831762996368571)
                      ·
                        rfl

theorem cell23_4529640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_4529640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529640 prefixEnd_4529640 := by exact prefixLift 4529640
  have htrace : WordTrace (prefixWord ++ tailWord_4529640) baseStart_4529640 baseEnd_4529640 := by
    simpa [prefixWord, tailWord_4529640, baseEnd_4529640] using wordTrace_append hprefix tailTrace_4529640
  have hstable : (prefixWord ++ tailWord_4529640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529640).length < 2 ^ (prefixWord ++ tailWord_4529640).sum := by decide
  have hdescent : baseEnd_4529640 < baseStart_4529640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529646 : List Nat := [4, 1, 2, 1, 2, 1, 3, 9]
def baseStart_4529646 : Nat := 118140960795 + 4529646 * 2 ^ 59
def prefixEnd_4529646 : Nat := 4983230072969 + 3 ^ 40 * 4529646 * 2
def baseEnd_4529646 : Nat := 86143910841321850847909

theorem tailTrace_4529646 : CollatzResearch.WordTrace tailWord_4529646 prefixEnd_4529646 86143910841321850847909 := by
  unfold tailWord_4529646
  simp only [CollatzResearch.WordTrace]
  refine ⟨20651220268484202349039099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110139841431915745861541861 20651220268484202349039099)
  ·
    refine ⟨30976830402726303523558649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20651220268484202349039099 30976830402726303523558649)
    ·
      refine ⟨23232622802044727642668987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30976830402726303523558649 23232622802044727642668987)
      ·
        refine ⟨34848934203067091464003481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23232622802044727642668987 34848934203067091464003481)
        ·
          refine ⟨26136700652300318598002611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34848934203067091464003481 26136700652300318598002611)
          ·
            refine ⟨39205050978450477897003917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26136700652300318598002611 39205050978450477897003917)
            ·
              refine ⟨14701894116918929211376469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39205050978450477897003917 14701894116918929211376469)
              ·
                refine ⟨86143910841321850847909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14701894116918929211376469 86143910841321850847909)
                ·
                  rfl

theorem cell23_4529646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 9].length) (baseStart_4529646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529646 prefixEnd_4529646 := by exact prefixLift 4529646
  have htrace : WordTrace (prefixWord ++ tailWord_4529646) baseStart_4529646 baseEnd_4529646 := by
    simpa [prefixWord, tailWord_4529646, baseEnd_4529646] using wordTrace_append hprefix tailTrace_4529646
  have hstable : (prefixWord ++ tailWord_4529646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529646).length < 2 ^ (prefixWord ++ tailWord_4529646).sum := by decide
  have hdescent : baseEnd_4529646 < baseStart_4529646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529673 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 4, 1, 3]
def baseStart_4529673 : Nat := 118140960795 + 4529673 * 2 ^ 59
def prefixEnd_4529673 : Nat := 4983230072969 + 3 ^ 40 * 4529673 * 2
def baseEnd_4529673 : Nat := 2325899456693361367255919

theorem tailTrace_4529673 : CollatzResearch.WordTrace tailWord_4529673 prefixEnd_4529673 2325899456693361367255919 := by
  unfold tailWord_4529673
  simp only [CollatzResearch.WordTrace]
  refine ⟨165210746918775802403545673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110140497945850534935697115 165210746918775802403545673)
  ·
    refine ⟨123908060189081851802659255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165210746918775802403545673 123908060189081851802659255)
    ·
      refine ⟨185862090283622777703988883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123908060189081851802659255 185862090283622777703988883)
      ·
        refine ⟨278793135425434166555983325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185862090283622777703988883 278793135425434166555983325)
        ·
          refine ⟨104547425784537812458493747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 278793135425434166555983325 104547425784537812458493747)
          ·
            refine ⟨156821138676806718687740621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104547425784537812458493747 156821138676806718687740621)
            ·
              refine ⟨58807927003802519507902733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156821138676806718687740621 58807927003802519507902733)
              ·
                refine ⟨22052972626425944815463525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58807927003802519507902733 22052972626425944815463525)
                ·
                  refine ⟨4134932367454864652899411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22052972626425944815463525 4134932367454864652899411)
                  ·
                    refine ⟨6202398551182296979349117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4134932367454864652899411 6202398551182296979349117)
                    ·
                      refine ⟨2325899456693361367255919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6202398551182296979349117 2325899456693361367255919)
                      ·
                        rfl

theorem cell23_4529673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 1, 3].length) (baseStart_4529673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529673 prefixEnd_4529673 := by exact prefixLift 4529673
  have htrace : WordTrace (prefixWord ++ tailWord_4529673) baseStart_4529673 baseEnd_4529673 := by
    simpa [prefixWord, tailWord_4529673, baseEnd_4529673] using wordTrace_append hprefix tailTrace_4529673
  have hstable : (prefixWord ++ tailWord_4529673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529673).length < 2 ^ (prefixWord ++ tailWord_4529673).sum := by decide
  have hdescent : baseEnd_4529673 < baseStart_4529673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529770 : List Nat := [3, 1, 3, 2, 1, 2, 1, 5, 5]
def baseStart_4529770 : Nat := 118140960795 + 4529770 * 2 ^ 59
def prefixEnd_4529770 : Nat := 4983230072969 + 3 ^ 40 * 4529770 * 2
def baseEnd_4529770 : Nat := 258438807146316387526997

theorem tailTrace_4529770 : CollatzResearch.WordTrace tailWord_4529770 prefixEnd_4529770 258438807146316387526997 := by
  unfold tailWord_4529770
  simp only [CollatzResearch.WordTrace]
  refine ⟨41303571199856096992456691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110142856532949591979884509 41303571199856096992456691)
  ·
    refine ⟨61955356799784145488685037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41303571199856096992456691 61955356799784145488685037)
    ·
      refine ⟨23233258799919054558256889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61955356799784145488685037 23233258799919054558256889)
      ·
        refine ⟨17424944099939290918692667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23233258799919054558256889 17424944099939290918692667)
        ·
          refine ⟨26137416149908936378039001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17424944099939290918692667 26137416149908936378039001)
          ·
            refine ⟨19603062112431702283529251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26137416149908936378039001 19603062112431702283529251)
            ·
              refine ⟨29404593168647553425293877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19603062112431702283529251 29404593168647553425293877)
              ·
                refine ⟨2756680609560708133621301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29404593168647553425293877 2756680609560708133621301)
                ·
                  refine ⟨258438807146316387526997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2756680609560708133621301 258438807146316387526997)
                  ·
                    rfl

theorem cell23_4529770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 5].length) (baseStart_4529770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529770 prefixEnd_4529770 := by exact prefixLift 4529770
  have htrace : WordTrace (prefixWord ++ tailWord_4529770) baseStart_4529770 baseEnd_4529770 := by
    simpa [prefixWord, tailWord_4529770, baseEnd_4529770] using wordTrace_append hprefix tailTrace_4529770
  have hstable : (prefixWord ++ tailWord_4529770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529770).length < 2 ^ (prefixWord ++ tailWord_4529770).sum := by decide
  have hdescent : baseEnd_4529770 < baseStart_4529770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529781 : List Nat := [1, 3, 4, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_4529781 : Nat := 118140960795 + 4529781 * 2 ^ 59
def prefixEnd_4529781 : Nat := 4983230072969 + 3 ^ 40 * 4529781 * 2
def baseEnd_4529781 : Nat := 2325954912604046944705423

theorem tailTrace_4529781 : CollatzResearch.WordTrace tailWord_4529781 prefixEnd_4529781 2325954912604046944705423 := by
  unfold tailWord_4529781
  simp only [CollatzResearch.WordTrace]
  refine ⟨165214686002384536848477197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110143124001589691232318131 165214686002384536848477197)
  ·
    refine ⟨61955507250894201318178949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165214686002384536848477197 61955507250894201318178949)
    ·
      refine ⟨11616657609542662747158553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61955507250894201318178949 11616657609542662747158553)
      ·
        refine ⟨8712493207156997060368915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11616657609542662747158553 8712493207156997060368915)
        ·
          refine ⟨13068739810735495590553373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8712493207156997060368915 13068739810735495590553373)
          ·
            refine ⟨4900777429025810846457515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13068739810735495590553373 4900777429025810846457515)
            ·
              refine ⟨7351166143538716269686273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4900777429025810846457515 7351166143538716269686273)
              ·
                refine ⟨5513374607654037202264705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7351166143538716269686273 5513374607654037202264705)
                ·
                  refine ⟨4135030955740527901698529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5513374607654037202264705 4135030955740527901698529)
                  ·
                    refine ⟨3101273216805395926273897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4135030955740527901698529 3101273216805395926273897)
                    ·
                      refine ⟨2325954912604046944705423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3101273216805395926273897 2325954912604046944705423)
                      ·
                        rfl

theorem cell23_4529781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_4529781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529781 prefixEnd_4529781 := by exact prefixLift 4529781
  have htrace : WordTrace (prefixWord ++ tailWord_4529781) baseStart_4529781 baseEnd_4529781 := by
    simpa [prefixWord, tailWord_4529781, baseEnd_4529781] using wordTrace_append hprefix tailTrace_4529781
  have hstable : (prefixWord ++ tailWord_4529781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529781).length < 2 ^ (prefixWord ++ tailWord_4529781).sum := by decide
  have hdescent : baseEnd_4529781 < baseStart_4529781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529843 : List Nat := [1, 1, 1, 2, 3, 3, 2, 4, 6]
def baseStart_4529843 : Nat := 118140960795 + 4529843 * 2 ^ 59
def prefixEnd_4529843 : Nat := 4983230072969 + 3 ^ 40 * 4529843 * 2
def baseEnd_4529843 : Nat := 258442972044958411347793

theorem tailTrace_4529843 : CollatzResearch.WordTrace tailWord_4529843 prefixEnd_4529843 258442972044958411347793 := by
  unfold tailWord_4529843
  simp only [CollatzResearch.WordTrace]
  refine ⟨165216947328159921437234183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110144631552106614291489455 165216947328159921437234183)
  ·
    refine ⟨247825420992239882155851275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165216947328159921437234183 247825420992239882155851275)
    ·
      refine ⟨371738131488359823233776913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247825420992239882155851275 371738131488359823233776913)
      ·
        refine ⟨278803598616269867425332685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371738131488359823233776913 278803598616269867425332685)
        ·
          refine ⟨104551349481101200284499757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 278803598616269867425332685 104551349481101200284499757)
          ·
            refine ⟨39206756055412950106687409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104551349481101200284499757 39206756055412950106687409)
            ·
              refine ⟨29405067041559712580015557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39206756055412950106687409 29405067041559712580015557)
              ·
                refine ⟨5513450070292446108752917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29405067041559712580015557 5513450070292446108752917)
                ·
                  refine ⟨258442972044958411347793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5513450070292446108752917 258442972044958411347793)
                  ·
                    rfl

theorem cell23_4529843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 6].length) (baseStart_4529843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529843 prefixEnd_4529843 := by exact prefixLift 4529843
  have htrace : WordTrace (prefixWord ++ tailWord_4529843) baseStart_4529843 baseEnd_4529843 := by
    simpa [prefixWord, tailWord_4529843, baseEnd_4529843] using wordTrace_append hprefix tailTrace_4529843
  have hstable : (prefixWord ++ tailWord_4529843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529843).length < 2 ^ (prefixWord ++ tailWord_4529843).sum := by decide
  have hdescent : baseEnd_4529843 < baseStart_4529843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529847 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 3, 4]
def baseStart_4529847 : Nat := 118140960795 + 4529847 * 2 ^ 59
def prefixEnd_4529847 : Nat := 4983230072969 + 3 ^ 40 * 4529847 * 2
def baseEnd_4529847 : Nat := 775329600775747895493373

theorem tailTrace_4529847 : CollatzResearch.WordTrace tailWord_4529847 prefixEnd_4529847 775329600775747895493373 := by
  unfold tailWord_4529847
  simp only [CollatzResearch.WordTrace]
  refine ⟨165217093220145430120379795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110144728813430286746919863 165217093220145430120379795)
  ·
    refine ⟨247825639830218145180569693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165217093220145430120379795 247825639830218145180569693)
    ·
      refine ⟨92934614936331804442713635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247825639830218145180569693 92934614936331804442713635)
      ·
        refine ⟨139401922404497706664070453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92934614936331804442713635 139401922404497706664070453)
        ·
          refine ⟨13068930225421659999756605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139401922404497706664070453 13068930225421659999756605)
          ·
            refine ⟨4900848834533122499908727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13068930225421659999756605 4900848834533122499908727)
            ·
              refine ⟨7351273251799683749863091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4900848834533122499908727 7351273251799683749863091)
              ·
                refine ⟨11026909877699525624794637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7351273251799683749863091 11026909877699525624794637)
                ·
                  refine ⟨4135091204137322109297989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11026909877699525624794637 4135091204137322109297989)
                  ·
                    refine ⟨775329600775747895493373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4135091204137322109297989 775329600775747895493373)
                    ·
                      rfl

theorem cell23_4529847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_4529847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529847 prefixEnd_4529847 := by exact prefixLift 4529847
  have htrace : WordTrace (prefixWord ++ tailWord_4529847) baseStart_4529847 baseEnd_4529847 := by
    simpa [prefixWord, tailWord_4529847, baseEnd_4529847] using wordTrace_append hprefix tailTrace_4529847
  have hstable : (prefixWord ++ tailWord_4529847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529847).length < 2 ^ (prefixWord ++ tailWord_4529847).sum := by decide
  have hdescent : baseEnd_4529847 < baseStart_4529847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529860 : List Nat := [2, 3, 3, 1, 1, 1, 3, 3, 6]
def baseStart_4529860 : Nat := 118140960795 + 4529860 * 2 ^ 59
def prefixEnd_4529860 : Nat := 4983230072969 + 3 ^ 40 * 4529860 * 2
def baseEnd_4529860 : Nat := 258443941952861348401951

theorem tailTrace_4529860 : CollatzResearch.WordTrace tailWord_4529860 prefixEnd_4529860 258443941952861348401951 := by
  unfold tailWord_4529860
  simp only [CollatzResearch.WordTrace]
  refine ⟨82608783684549166670301517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110145044912732222227068689 82608783684549166670301517)
  ·
    refine ⟨30978293881705937501363069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82608783684549166670301517 30978293881705937501363069)
    ·
      refine ⟨11616860205639726563011151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30978293881705937501363069 11616860205639726563011151)
      ·
        refine ⟨17425290308459589844516727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11616860205639726563011151 17425290308459589844516727)
        ·
          refine ⟨26137935462689384766775091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17425290308459589844516727 26137935462689384766775091)
          ·
            refine ⟨39206903194034077150162637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26137935462689384766775091 39206903194034077150162637)
            ·
              refine ⟨14702588697762778931310989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39206903194034077150162637 14702588697762778931310989)
              ·
                refine ⟨5513470761661042099241621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14702588697762778931310989 5513470761661042099241621)
                ·
                  refine ⟨258443941952861348401951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5513470761661042099241621 258443941952861348401951)
                  ·
                    rfl

theorem cell23_4529860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_4529860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529860 prefixEnd_4529860 := by exact prefixLift 4529860
  have htrace : WordTrace (prefixWord ++ tailWord_4529860) baseStart_4529860 baseEnd_4529860 := by
    simpa [prefixWord, tailWord_4529860, baseEnd_4529860] using wordTrace_append hprefix tailTrace_4529860
  have hstable : (prefixWord ++ tailWord_4529860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529860).length < 2 ^ (prefixWord ++ tailWord_4529860).sum := by decide
  have hdescent : baseEnd_4529860 < baseStart_4529860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529903 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 3, 6]
def baseStart_4529903 : Nat := 118140960795 + 4529903 * 2 ^ 59
def prefixEnd_4529903 : Nat := 4983230072969 + 3 ^ 40 * 4529903 * 2
def baseEnd_4529903 : Nat := 775339185747965155793287

theorem tailTrace_4529903 : CollatzResearch.WordTrace tailWord_4529903 prefixEnd_4529903 775339185747965155793287 := by
  unfold tailWord_4529903
  simp only [CollatzResearch.WordTrace]
  refine ⟨165219135707942551684418363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110146090471961701122945575 165219135707942551684418363)
  ·
    refine ⟨247828703561913827526627545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165219135707942551684418363 247828703561913827526627545)
    ·
      refine ⟨185871527671435370644970659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247828703561913827526627545 185871527671435370644970659)
      ·
        refine ⟨278807291507153055967455989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185871527671435370644970659 278807291507153055967455989)
        ·
          refine ⟨26138183578795598996948999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 278807291507153055967455989 26138183578795598996948999)
          ·
            refine ⟨39207275368193398495423499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26138183578795598996948999 39207275368193398495423499)
            ·
              refine ⟨58810913052290097743135249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39207275368193398495423499 58810913052290097743135249)
              ·
                refine ⟨44108184789217573307351437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58810913052290097743135249 44108184789217573307351437)
                ·
                  refine ⟨16540569295956589990256789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44108184789217573307351437 16540569295956589990256789)
                  ·
                    refine ⟨775339185747965155793287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16540569295956589990256789 775339185747965155793287)
                    ·
                      rfl

theorem cell23_4529903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 6].length) (baseStart_4529903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529903 prefixEnd_4529903 := by exact prefixLift 4529903
  have htrace : WordTrace (prefixWord ++ tailWord_4529903) baseStart_4529903 baseEnd_4529903 := by
    simpa [prefixWord, tailWord_4529903, baseEnd_4529903] using wordTrace_append hprefix tailTrace_4529903
  have hstable : (prefixWord ++ tailWord_4529903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529903).length < 2 ^ (prefixWord ++ tailWord_4529903).sum := by decide
  have hdescent : baseEnd_4529903 < baseStart_4529903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529923 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 6]
def baseStart_4529923 : Nat := 118140960795 + 4529923 * 2 ^ 59
def prefixEnd_4529923 : Nat := 4983230072969 + 3 ^ 40 * 4529923 * 2
def baseEnd_4529923 : Nat := 2326027826856985389129769

theorem tailTrace_4529923 : CollatzResearch.WordTrace tailWord_4529923 prefixEnd_4529923 2326027826856985389129769 := by
  unfold tailWord_4529923
  simp only [CollatzResearch.WordTrace]
  refine ⟨165219865167870095100146423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110146576778580063400097615 165219865167870095100146423)
  ·
    refine ⟨247829797751805142650219635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165219865167870095100146423 247829797751805142650219635)
    ·
      refine ⟨371744696627707713975329453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247829797751805142650219635 371744696627707713975329453)
      ·
        refine ⟨139404261235390392740748545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 371744696627707713975329453 139404261235390392740748545)
        ·
          refine ⟨104553195926542794555561409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139404261235390392740748545 104553195926542794555561409)
          ·
            refine ⟨78414896944907095916671057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104553195926542794555561409 78414896944907095916671057)
            ·
              refine ⟨58811172708680321937503293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78414896944907095916671057 58811172708680321937503293)
              ·
                refine ⟨22054189765755120726563735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58811172708680321937503293 22054189765755120726563735)
                ·
                  refine ⟨33081284648632681089845603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22054189765755120726563735 33081284648632681089845603)
                  ·
                    refine ⟨49621926972949021634768405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33081284648632681089845603 49621926972949021634768405)
                    ·
                      refine ⟨2326027826856985389129769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49621926972949021634768405 2326027826856985389129769)
                      ·
                        rfl

theorem cell23_4529923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_4529923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529923 prefixEnd_4529923 := by exact prefixLift 4529923
  have htrace : WordTrace (prefixWord ++ tailWord_4529923) baseStart_4529923 baseEnd_4529923 := by
    simpa [prefixWord, tailWord_4529923, baseEnd_4529923] using wordTrace_append hprefix tailTrace_4529923
  have hstable : (prefixWord ++ tailWord_4529923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529923).length < 2 ^ (prefixWord ++ tailWord_4529923).sum := by decide
  have hdescent : baseEnd_4529923 < baseStart_4529923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529938 : List Nat := [3, 2, 4, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_4529938 : Nat := 118140960795 + 4529938 * 2 ^ 59
def prefixEnd_4529938 : Nat := 4983230072969 + 3 ^ 40 * 4529938 * 2
def baseEnd_4529938 : Nat := 2326035529066802830442201

theorem tailTrace_4529938 : CollatzResearch.WordTrace tailWord_4529938 prefixEnd_4529938 2326035529066802830442201 := by
  unfold tailWord_4529938
  simp only [CollatzResearch.WordTrace]
  refine ⟨41305103065703938165485617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110146941508543835107961645 41305103065703938165485617)
  ·
    refine ⟨30978827299277953624114213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41305103065703938165485617 30978827299277953624114213)
    ·
      refine ⟨5808530118614616304521415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30978827299277953624114213 5808530118614616304521415)
      ·
        refine ⟨8712795177921924456782123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5808530118614616304521415 8712795177921924456782123)
        ·
          refine ⟨13069192766882886685173185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8712795177921924456782123 13069192766882886685173185)
          ·
            refine ⟨9801894575162165013879889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13069192766882886685173185 9801894575162165013879889)
            ·
              refine ⟨7351420931371623760409917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9801894575162165013879889 7351420931371623760409917)
              ·
                refine ⟨2756782849264358910153719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7351420931371623760409917 2756782849264358910153719)
                ·
                  refine ⟨4135174273896538365230579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756782849264358910153719 4135174273896538365230579)
                  ·
                    refine ⟨6202761410844807547845869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4135174273896538365230579 6202761410844807547845869)
                    ·
                      refine ⟨2326035529066802830442201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6202761410844807547845869 2326035529066802830442201)
                      ·
                        rfl

theorem cell23_4529938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_4529938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529938 prefixEnd_4529938 := by exact prefixLift 4529938
  have htrace : WordTrace (prefixWord ++ tailWord_4529938) baseStart_4529938 baseEnd_4529938 := by
    simpa [prefixWord, tailWord_4529938, baseEnd_4529938] using wordTrace_append hprefix tailTrace_4529938
  have hstable : (prefixWord ++ tailWord_4529938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529938).length < 2 ^ (prefixWord ++ tailWord_4529938).sum := by decide
  have hdescent : baseEnd_4529938 < baseStart_4529938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4529974 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_4529974 : Nat := 118140960795 + 4529974 * 2 ^ 59
def prefixEnd_4529974 : Nat := 4983230072969 + 3 ^ 40 * 4529974 * 2
def baseEnd_4529974 : Nat := 2326054014370364689592035

theorem tailTrace_4529974 : CollatzResearch.WordTrace tailWord_4529974 prefixEnd_4529974 2326054014370364689592035 := by
  unfold tailWord_4529974
  simp only [CollatzResearch.WordTrace]
  refine ⟨10326357830667833175640811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110147816860456887206835317 10326357830667833175640811)
  ·
    refine ⟨15489536746001749763461217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10326357830667833175640811 15489536746001749763461217)
    ·
      refine ⟨11617152559501312322595913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15489536746001749763461217 11617152559501312322595913)
      ·
        refine ⟨8712864419625984241946935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11617152559501312322595913 8712864419625984241946935)
        ·
          refine ⟨13069296629438976362920403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8712864419625984241946935 13069296629438976362920403)
          ·
            refine ⟨19603944944158464544380605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13069296629438976362920403 19603944944158464544380605)
            ·
              refine ⟨7351479354059424204142727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19603944944158464544380605 7351479354059424204142727)
              ·
                refine ⟨11027219031089136306214091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7351479354059424204142727 11027219031089136306214091)
                ·
                  refine ⟨16540828546633704459321137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11027219031089136306214091 16540828546633704459321137)
                  ·
                    refine ⟨12405621409975278344490853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16540828546633704459321137 12405621409975278344490853)
                    ·
                      refine ⟨2326054014370364689592035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12405621409975278344490853 2326054014370364689592035)
                      ·
                        rfl

theorem cell23_4529974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_4529974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4529974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4529974 prefixEnd_4529974 := by exact prefixLift 4529974
  have htrace : WordTrace (prefixWord ++ tailWord_4529974) baseStart_4529974 baseEnd_4529974 := by
    simpa [prefixWord, tailWord_4529974, baseEnd_4529974] using wordTrace_append hprefix tailTrace_4529974
  have hstable : (prefixWord ++ tailWord_4529974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4529974).length < 2 ^ (prefixWord ++ tailWord_4529974).sum := by decide
  have hdescent : baseEnd_4529974 < baseStart_4529974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4529974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530057 : List Nat := [1, 2, 1, 1, 5, 1, 2, 5, 5]
def baseStart_4530057 : Nat := 118140960795 + 4530057 * 2 ^ 59
def prefixEnd_4530057 : Nat := 4983230072969 + 3 ^ 40 * 4530057 * 2
def baseEnd_4530057 : Nat := 258455181473854207206017

theorem tailTrace_4530057 : CollatzResearch.WordTrace tailWord_4530057 prefixEnd_4530057 258455181473854207206017 := by
  unfold tailWord_4530057
  simp only [CollatzResearch.WordTrace]
  refine ⟨165224752549384635985524425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110149835032923090657016283 165224752549384635985524425)
  ·
    refine ⟨123918564412038476989143319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165224752549384635985524425 123918564412038476989143319)
    ·
      refine ⟨185877846618057715483714979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123918564412038476989143319 185877846618057715483714979)
      ·
        refine ⟨278816769927086573225572469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185877846618057715483714979 278816769927086573225572469)
        ·
          refine ⟨26139072180664366239897419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 278816769927086573225572469 26139072180664366239897419)
          ·
            refine ⟨39208608270996549359846129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26139072180664366239897419 39208608270996549359846129)
            ·
              refine ⟨29406456203247412019884597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39208608270996549359846129 29406456203247412019884597)
              ·
                refine ⟨2756855269054444876864181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29406456203247412019884597 2756855269054444876864181)
                ·
                  refine ⟨258455181473854207206017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2756855269054444876864181 258455181473854207206017)
                  ·
                    rfl

theorem cell23_4530057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 5].length) (baseStart_4530057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530057 prefixEnd_4530057 := by exact prefixLift 4530057
  have htrace : WordTrace (prefixWord ++ tailWord_4530057) baseStart_4530057 baseEnd_4530057 := by
    simpa [prefixWord, tailWord_4530057, baseEnd_4530057] using wordTrace_append hprefix tailTrace_4530057
  have hstable : (prefixWord ++ tailWord_4530057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530057).length < 2 ^ (prefixWord ++ tailWord_4530057).sum := by decide
  have hdescent : baseEnd_4530057 < baseStart_4530057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530068 : List Nat := [2, 4, 2, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_4530068 : Nat := 118140960795 + 4530068 * 2 ^ 59
def prefixEnd_4530068 : Nat := 4983230072969 + 3 ^ 40 * 4530068 * 2
def baseEnd_4530068 : Nat := 2326102281551887321816603

theorem tailTrace_4530068 : CollatzResearch.WordTrace tailWord_4530068 prefixEnd_4530068 2326102281551887321816603 := by
  unfold tailWord_4530068
  simp only [CollatzResearch.WordTrace]
  refine ⟨82612576876172392432087429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110150102501563189909449905 82612576876172392432087429)
  ·
    refine ⟨15489858164282323581016393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82612576876172392432087429 15489858164282323581016393)
    ·
      refine ⟨11617393623211742685762295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15489858164282323581016393 11617393623211742685762295)
      ·
        refine ⟨17426090434817614028643443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11617393623211742685762295 17426090434817614028643443)
        ·
          refine ⟨26139135652226421042965165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17426090434817614028643443 26139135652226421042965165)
          ·
            refine ⟨9802175869584907891111937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26139135652226421042965165 9802175869584907891111937)
            ·
              refine ⟨7351631902188680918333953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9802175869584907891111937 7351631902188680918333953)
              ·
                refine ⟨5513723926641510688750465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7351631902188680918333953 5513723926641510688750465)
                ·
                  refine ⟨4135292944981133016562849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5513723926641510688750465 4135292944981133016562849)
                  ·
                    refine ⟨3101469708735849762422137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4135292944981133016562849 3101469708735849762422137)
                    ·
                      refine ⟨2326102281551887321816603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3101469708735849762422137 2326102281551887321816603)
                      ·
                        rfl

theorem cell23_4530068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_4530068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530068 prefixEnd_4530068 := by exact prefixLift 4530068
  have htrace : WordTrace (prefixWord ++ tailWord_4530068) baseStart_4530068 baseEnd_4530068 := by
    simpa [prefixWord, tailWord_4530068, baseEnd_4530068] using wordTrace_append hprefix tailTrace_4530068
  have hstable : (prefixWord ++ tailWord_4530068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530068).length < 2 ^ (prefixWord ++ tailWord_4530068).sum := by decide
  have hdescent : baseEnd_4530068 < baseStart_4530068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530074 : List Nat := [3, 1, 1, 4, 2, 2, 1, 4, 5]
def baseStart_4530074 : Nat := 118140960795 + 4530074 * 2 ^ 59
def prefixEnd_4530074 : Nat := 4983230072969 + 3 ^ 40 * 4530074 * 2
def baseEnd_4530074 : Nat := 258456151381757144260175

theorem tailTrace_4530074 : CollatzResearch.WordTrace tailWord_4530074 prefixEnd_4530074 258456151381757144260175 := by
  unfold tailWord_4530074
  simp only [CollatzResearch.WordTrace]
  refine ⟨41306343147580761972223319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110150248393548698592595517 41306343147580761972223319)
  ·
    refine ⟨61959514721371142958334979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41306343147580761972223319 61959514721371142958334979)
    ·
      refine ⟨92939272082056714437502469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61959514721371142958334979 92939272082056714437502469)
      ·
        refine ⟨17426113515385633957031713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92939272082056714437502469 17426113515385633957031713)
        ·
          refine ⟨13069585136539225467773785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17426113515385633957031713 13069585136539225467773785)
          ·
            refine ⟨9802188852404419100830339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13069585136539225467773785 9802188852404419100830339)
            ·
              refine ⟨14703283278606628651245509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9802188852404419100830339 14703283278606628651245509)
              ·
                refine ⟨2756865614738742872108533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14703283278606628651245509 2756865614738742872108533)
                ·
                  refine ⟨258456151381757144260175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2756865614738742872108533 258456151381757144260175)
                  ·
                    rfl

theorem cell23_4530074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 5].length) (baseStart_4530074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530074 prefixEnd_4530074 := by exact prefixLift 4530074
  have htrace : WordTrace (prefixWord ++ tailWord_4530074) baseStart_4530074 baseEnd_4530074 := by
    simpa [prefixWord, tailWord_4530074, baseEnd_4530074] using wordTrace_append hprefix tailTrace_4530074
  have hstable : (prefixWord ++ tailWord_4530074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530074).length < 2 ^ (prefixWord ++ tailWord_4530074).sum := by decide
  have hdescent : baseEnd_4530074 < baseStart_4530074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530107 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 4, 4, 2]
def baseStart_4530107 : Nat := 118140960795 + 4530107 * 2 ^ 59
def prefixEnd_4530107 : Nat := 4983230072969 + 3 ^ 40 * 4530107 * 2
def baseEnd_4530107 : Nat := 2326122307297412669228923

theorem tailTrace_4530107 : CollatzResearch.WordTrace tailWord_4530107 prefixEnd_4530107 2326122307297412669228923 := by
  unfold tailWord_4530107
  simp only [CollatzResearch.WordTrace]
  refine ⟨165226576199203494524844575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110151050799468996349896383 165226576199203494524844575)
  ·
    refine ⟨247839864298805241787266863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165226576199203494524844575 247839864298805241787266863)
    ·
      refine ⟨371759796448207862680900295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247839864298805241787266863 371759796448207862680900295)
      ·
        refine ⟨557639694672311794021350443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371759796448207862680900295 557639694672311794021350443)
        ·
          refine ⟨836459542008467691032025665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557639694672311794021350443 836459542008467691032025665)
          ·
            refine ⟨627344656506350768274019249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 836459542008467691032025665 627344656506350768274019249)
            ·
              refine ⟨470508492379763076205514437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627344656506350768274019249 470508492379763076205514437)
              ·
                refine ⟨88220342321205576788533957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 470508492379763076205514437 88220342321205576788533957)
                ·
                  refine ⟨16541314185226045647850117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88220342321205576788533957 16541314185226045647850117)
                  ·
                    refine ⟨3101496409729883558971897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16541314185226045647850117 3101496409729883558971897)
                    ·
                      refine ⟨2326122307297412669228923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3101496409729883558971897 2326122307297412669228923)
                      ·
                        rfl

theorem cell23_4530107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 4, 2].length) (baseStart_4530107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530107 prefixEnd_4530107 := by exact prefixLift 4530107
  have htrace : WordTrace (prefixWord ++ tailWord_4530107) baseStart_4530107 baseEnd_4530107 := by
    simpa [prefixWord, tailWord_4530107, baseEnd_4530107] using wordTrace_append hprefix tailTrace_4530107
  have hstable : (prefixWord ++ tailWord_4530107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530107).length < 2 ^ (prefixWord ++ tailWord_4530107).sum := by decide
  have hdescent : baseEnd_4530107 < baseStart_4530107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530124 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 2, 4, 2]
def baseStart_4530124 : Nat := 118140960795 + 4530124 * 2 ^ 59
def prefixEnd_4530124 : Nat := 4983230072969 + 3 ^ 40 * 4530124 * 2
def baseEnd_4530124 : Nat := 2326131036468539102716345

theorem tailTrace_4530124 : CollatzResearch.WordTrace tailWord_4530124 prefixEnd_4530124 2326131036468539102716345 := by
  unfold tailWord_4530124
  simp only [CollatzResearch.WordTrace]
  refine ⟨82613598120070953214106713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110151464160094604285475617 82613598120070953214106713)
  ·
    refine ⟨61960198590053214910580035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82613598120070953214106713 61960198590053214910580035)
    ·
      refine ⟨92940297885079822365870053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61960198590053214910580035 92940297885079822365870053)
      ·
        refine ⟨17426305853452466693600635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92940297885079822365870053 17426305853452466693600635)
        ·
          refine ⟨26139458780178700040400953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17426305853452466693600635 26139458780178700040400953)
          ·
            refine ⟨19604594085134025030300715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26139458780178700040400953 19604594085134025030300715)
            ·
              refine ⟨29406891127701037545451073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19604594085134025030300715 29406891127701037545451073)
              ·
                refine ⟨22055168345775778159088305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29406891127701037545451073 22055168345775778159088305)
                ·
                  refine ⟨16541376259331833619316229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22055168345775778159088305 16541376259331833619316229)
                  ·
                    refine ⟨3101508048624718803621793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16541376259331833619316229 3101508048624718803621793)
                    ·
                      refine ⟨2326131036468539102716345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3101508048624718803621793 2326131036468539102716345)
                      ·
                        rfl

theorem cell23_4530124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_4530124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530124 prefixEnd_4530124 := by exact prefixLift 4530124
  have htrace : WordTrace (prefixWord ++ tailWord_4530124) baseStart_4530124 baseEnd_4530124 := by
    simpa [prefixWord, tailWord_4530124, baseEnd_4530124] using wordTrace_append hprefix tailTrace_4530124
  have hstable : (prefixWord ++ tailWord_4530124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530124).length < 2 ^ (prefixWord ++ tailWord_4530124).sum := by decide
  have hdescent : baseEnd_4530124 < baseStart_4530124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530127 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 3]
def baseStart_4530127 : Nat := 118140960795 + 4530127 * 2 ^ 59
def prefixEnd_4530127 : Nat := 4983230072969 + 3 ^ 40 * 4530127 * 2
def baseEnd_4530127 : Nat := 2326132576910502590978831

theorem tailTrace_4530127 : CollatzResearch.WordTrace tailWord_4530127 prefixEnd_4530127 2326132576910502590978831 := by
  unfold tailWord_4530127
  simp only [CollatzResearch.WordTrace]
  refine ⟨165227305659131037940572635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110151537106087358627048423 165227305659131037940572635)
  ·
    refine ⟨247840958488696556910858953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165227305659131037940572635 247840958488696556910858953)
    ·
      refine ⟨185880718866522417683144215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247840958488696556910858953 185880718866522417683144215)
      ·
        refine ⟨278821078299783626524716323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185880718866522417683144215 278821078299783626524716323)
        ·
          refine ⟨418231617449675439787074485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278821078299783626524716323 418231617449675439787074485)
          ·
            refine ⟨39209214135907072480038233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 418231617449675439787074485 39209214135907072480038233)
            ·
              refine ⟨29406910601930304360028675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39209214135907072480038233 29406910601930304360028675)
              ·
                refine ⟨44110365902895456540043013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29406910601930304360028675 44110365902895456540043013)
                ·
                  refine ⟨8270693606792898101258065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44110365902895456540043013 8270693606792898101258065)
                  ·
                    refine ⟨6203020205094673575943549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8270693606792898101258065 6203020205094673575943549)
                    ·
                      refine ⟨2326132576910502590978831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6203020205094673575943549 2326132576910502590978831)
                      ·
                        rfl

theorem cell23_4530127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 3].length) (baseStart_4530127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530127 prefixEnd_4530127 := by exact prefixLift 4530127
  have htrace : WordTrace (prefixWord ++ tailWord_4530127) baseStart_4530127 baseEnd_4530127 := by
    simpa [prefixWord, tailWord_4530127, baseEnd_4530127] using wordTrace_append hprefix tailTrace_4530127
  have hstable : (prefixWord ++ tailWord_4530127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530127).length < 2 ^ (prefixWord ++ tailWord_4530127).sum := by decide
  have hdescent : baseEnd_4530127 < baseStart_4530127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530207 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 1, 6]
def baseStart_4530207 : Nat := 118140960795 + 4530207 * 2 ^ 59
def prefixEnd_4530207 : Nat := 4983230072969 + 3 ^ 40 * 4530207 * 2
def baseEnd_4530207 : Nat := 775391218454287425992821

theorem tailTrace_4530207 : CollatzResearch.WordTrace tailWord_4530207 prefixEnd_4530207 775391218454287425992821 := by
  unfold tailWord_4530207
  simp only [CollatzResearch.WordTrace]
  refine ⟨165230223498841211603484875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110153482332560807735656583 165230223498841211603484875)
  ·
    refine ⟨247845335248261817405227313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165230223498841211603484875 247845335248261817405227313)
    ·
      refine ⟨185884001436196363053920485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247845335248261817405227313 185884001436196363053920485)
      ·
        refine ⟨34853250269286818072610091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185884001436196363053920485 34853250269286818072610091)
        ·
          refine ⟨52279875403930227108915137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34853250269286818072610091 52279875403930227108915137)
          ·
            refine ⟨39209906552947670331686353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52279875403930227108915137 39209906552947670331686353)
            ·
              refine ⟨29407429914710752748764765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39209906552947670331686353 29407429914710752748764765)
              ·
                refine ⟨11027786218016532280786787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29407429914710752748764765 11027786218016532280786787)
                ·
                  refine ⟨16541679327024798421180181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11027786218016532280786787 16541679327024798421180181)
                  ·
                    refine ⟨775391218454287425992821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16541679327024798421180181 775391218454287425992821)
                    ·
                      rfl

theorem cell23_4530207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 6].length) (baseStart_4530207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530207 prefixEnd_4530207 := by exact prefixLift 4530207
  have htrace : WordTrace (prefixWord ++ tailWord_4530207) baseStart_4530207 baseEnd_4530207 := by
    simpa [prefixWord, tailWord_4530207, baseEnd_4530207] using wordTrace_append hprefix tailTrace_4530207
  have hstable : (prefixWord ++ tailWord_4530207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530207).length < 2 ^ (prefixWord ++ tailWord_4530207).sum := by decide
  have hdescent : baseEnd_4530207 < baseStart_4530207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530218 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_4530218 : Nat := 118140960795 + 4530218 * 2 ^ 59
def prefixEnd_4530218 : Nat := 4983230072969 + 3 ^ 40 * 4530218 * 2
def baseEnd_4530218 : Nat := 2326179303650061734940913

theorem tailTrace_4530218 : CollatzResearch.WordTrace tailWord_4530218 prefixEnd_4530218 2326179303650061734940913 := by
  unfold tailWord_4530218
  simp only [CollatzResearch.WordTrace]
  refine ⟨41307656175450340120533827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110153749801200906988090205 41307656175450340120533827)
  ·
    refine ⟨61961484263175510180800741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41307656175450340120533827 61961484263175510180800741)
    ·
      refine ⟨11617778299345408158900139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61961484263175510180800741 11617778299345408158900139)
      ·
        refine ⟨17426667449018112238350209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11617778299345408158900139 17426667449018112238350209)
        ·
          refine ⟨13070000586763584178762657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17426667449018112238350209 13070000586763584178762657)
          ·
            refine ⟨9802500440072688134071993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13070000586763584178762657 9802500440072688134071993)
            ·
              refine ⟨7351875330054516100553995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9802500440072688134071993 7351875330054516100553995)
              ·
                refine ⟨11027812995081774150830993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7351875330054516100553995 11027812995081774150830993)
                ·
                  refine ⟨8270859746311330613123245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11027812995081774150830993 8270859746311330613123245)
                  ·
                    refine ⟨3101572404866748979921217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8270859746311330613123245 3101572404866748979921217)
                    ·
                      refine ⟨2326179303650061734940913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3101572404866748979921217 2326179303650061734940913)
                      ·
                        rfl

theorem cell23_4530218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_4530218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530218 prefixEnd_4530218 := by exact prefixLift 4530218
  have htrace : WordTrace (prefixWord ++ tailWord_4530218) baseStart_4530218 baseEnd_4530218 := by
    simpa [prefixWord, tailWord_4530218, baseEnd_4530218] using wordTrace_append hprefix tailTrace_4530218
  have hstable : (prefixWord ++ tailWord_4530218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530218).length < 2 ^ (prefixWord ++ tailWord_4530218).sum := by decide
  have hdescent : baseEnd_4530218 < baseStart_4530218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530227 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 4]
def baseStart_4530227 : Nat := 118140960795 + 4530227 * 2 ^ 59
def prefixEnd_4530227 : Nat := 4983230072969 + 3 ^ 40 * 4530227 * 2
def baseEnd_4530227 : Nat := 2326183924975952199728371

theorem tailTrace_4530227 : CollatzResearch.WordTrace tailWord_4530227 prefixEnd_4530227 2326183924975952199728371 := by
  unfold tailWord_4530227
  simp only [CollatzResearch.WordTrace]
  refine ⟨165230952958768755019212935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110153968639179170012808623 165230952958768755019212935)
  ·
    refine ⟨247846429438153132528819403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165230952958768755019212935 247846429438153132528819403)
    ·
      refine ⟨371769644157229698793229105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247846429438153132528819403 371769644157229698793229105)
      ·
        refine ⟨278827233117922274094921829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371769644157229698793229105 278827233117922274094921829)
        ·
          refine ⟨52280106209610426392797843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 278827233117922274094921829 52280106209610426392797843)
          ·
            refine ⟨78420159314415639589196765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52280106209610426392797843 78420159314415639589196765)
            ·
              refine ⟨29407559742905864845948787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78420159314415639589196765 29407559742905864845948787)
              ·
                refine ⟨44111339614358797268923181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29407559742905864845948787 44111339614358797268923181)
                ·
                  refine ⟨16541752355384548975846193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44111339614358797268923181 16541752355384548975846193)
                  ·
                    refine ⟨12406314266538411731884645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16541752355384548975846193 12406314266538411731884645)
                    ·
                      refine ⟨2326183924975952199728371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12406314266538411731884645 2326183924975952199728371)
                      ·
                        rfl

theorem cell23_4530227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_4530227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530227 prefixEnd_4530227 := by exact prefixLift 4530227
  have htrace : WordTrace (prefixWord ++ tailWord_4530227) baseStart_4530227 baseEnd_4530227 := by
    simpa [prefixWord, tailWord_4530227, baseEnd_4530227] using wordTrace_append hprefix tailTrace_4530227
  have hstable : (prefixWord ++ tailWord_4530227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530227).length < 2 ^ (prefixWord ++ tailWord_4530227).sum := by decide
  have hdescent : baseEnd_4530227 < baseStart_4530227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530241 : List Nat := [1, 2, 5, 1, 2, 1, 1, 4, 2, 4]
def baseStart_4530241 : Nat := 118140960795 + 4530241 * 2 ^ 59
def prefixEnd_4530241 : Nat := 4983230072969 + 3 ^ 40 * 4530241 * 2
def baseEnd_4530241 : Nat := 775397037901705048317769

theorem tailTrace_4530241 : CollatzResearch.WordTrace tailWord_4530241 prefixEnd_4530241 775397037901705048317769 := by
  unfold tailWord_4530241
  simp only [CollatzResearch.WordTrace]
  refine ⟨165231463580718035410222577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110154309053812023606815051 165231463580718035410222577)
  ·
    refine ⟨123923597685538526557666933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165231463580718035410222577 123923597685538526557666933)
    ·
      refine ⟨11617837283019236864781275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123923597685538526557666933 11617837283019236864781275)
      ·
        refine ⟨17426755924528855297171913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11617837283019236864781275 17426755924528855297171913)
        ·
          refine ⟨13070066943396641472878935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17426755924528855297171913 13070066943396641472878935)
          ·
            refine ⟨19605100415094962209318403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13070066943396641472878935 19605100415094962209318403)
            ·
              refine ⟨29407650622642443313977605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19605100415094962209318403 29407650622642443313977605)
              ·
                refine ⟨5513934491745458121370801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29407650622642443313977605 5513934491745458121370801)
                ·
                  refine ⟨4135450868809093591028101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5513934491745458121370801 4135450868809093591028101)
                  ·
                    refine ⟨775397037901705048317769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4135450868809093591028101 775397037901705048317769)
                    ·
                      rfl

theorem cell23_4530241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_4530241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530241 prefixEnd_4530241 := by exact prefixLift 4530241
  have htrace : WordTrace (prefixWord ++ tailWord_4530241) baseStart_4530241 baseEnd_4530241 := by
    simpa [prefixWord, tailWord_4530241, baseEnd_4530241] using wordTrace_append hprefix tailTrace_4530241
  have hstable : (prefixWord ++ tailWord_4530241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530241).length < 2 ^ (prefixWord ++ tailWord_4530241).sum := by decide
  have hdescent : baseEnd_4530241 < baseStart_4530241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530254 : List Nat := [4, 1, 1, 1, 1, 6, 1, 8]
def baseStart_4530254 : Nat := 118140960795 + 4530254 * 2 ^ 59
def prefixEnd_4530254 : Nat := 4983230072969 + 3 ^ 40 * 4530254 * 2
def baseEnd_4530254 : Nat := 86155473664949022003361

theorem tailTrace_4530254 : CollatzResearch.WordTrace tailWord_4530254 prefixEnd_4530254 86155473664949022003361 := by
  unfold tailWord_4530254
  simp only [CollatzResearch.WordTrace]
  refine ⟨20653992216208867328805727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110154625153113959086963877 20653992216208867328805727)
  ·
    refine ⟨30980988324313300993208591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20653992216208867328805727 30980988324313300993208591)
    ·
      refine ⟨46471482486469951489812887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30980988324313300993208591 46471482486469951489812887)
      ·
        refine ⟨69707223729704927234719331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46471482486469951489812887 69707223729704927234719331)
        ·
          refine ⟨104560835594557390852078997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69707223729704927234719331 104560835594557390852078997)
          ·
            refine ⟨4901289168494877696191203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 104560835594557390852078997 4901289168494877696191203)
            ·
              refine ⟨7351933752742316544286805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4901289168494877696191203 7351933752742316544286805)
              ·
                refine ⟨86155473664949022003361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7351933752742316544286805 86155473664949022003361)
                ·
                  rfl

theorem cell23_4530254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 8].length) (baseStart_4530254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530254 prefixEnd_4530254 := by exact prefixLift 4530254
  have htrace : WordTrace (prefixWord ++ tailWord_4530254) baseStart_4530254 baseEnd_4530254 := by
    simpa [prefixWord, tailWord_4530254, baseEnd_4530254] using wordTrace_append hprefix tailTrace_4530254
  have hstable : (prefixWord ++ tailWord_4530254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530254).length < 2 ^ (prefixWord ++ tailWord_4530254).sum := by decide
  have hdescent : baseEnd_4530254 < baseStart_4530254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530264 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 1, 3, 3]
def baseStart_4530264 : Nat := 118140960795 + 4530264 * 2 ^ 59
def prefixEnd_4530264 : Nat := 4983230072969 + 3 ^ 40 * 4530264 * 2
def baseEnd_4530264 : Nat := 2326202923760168554965701

theorem tailTrace_4530264 : CollatzResearch.WordTrace tailWord_4530264 prefixEnd_4530264 2326202923760168554965701 := by
  unfold tailWord_4530264
  simp only [CollatzResearch.WordTrace]
  refine ⟨82616151229817355169154923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110154868306423140225539897 82616151229817355169154923)
  ·
    refine ⟨123924226844726032753732385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82616151229817355169154923 123924226844726032753732385)
    ·
      refine ⟨92943170133544524565299289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123924226844726032753732385 92943170133544524565299289)
      ·
        refine ⟨69707377600158393423974467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92943170133544524565299289 69707377600158393423974467)
        ·
          refine ⟨104561066400237590135961701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69707377600158393423974467 104561066400237590135961701)
          ·
            refine ⟨19605199950044548150492819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104561066400237590135961701 19605199950044548150492819)
            ·
              refine ⟨29407799925066822225739229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19605199950044548150492819 29407799925066822225739229)
              ·
                refine ⟨11027924971900058334652211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29407799925066822225739229 11027924971900058334652211)
                ·
                  refine ⟨16541887457850087501978317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11027924971900058334652211 16541887457850087501978317)
                  ·
                    refine ⟨6203207796693782813241869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16541887457850087501978317 6203207796693782813241869)
                    ·
                      refine ⟨2326202923760168554965701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6203207796693782813241869 2326202923760168554965701)
                      ·
                        rfl

theorem cell23_4530264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_4530264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530264 prefixEnd_4530264 := by exact prefixLift 4530264
  have htrace : WordTrace (prefixWord ++ tailWord_4530264) baseStart_4530264 baseEnd_4530264 := by
    simpa [prefixWord, tailWord_4530264, baseEnd_4530264] using wordTrace_append hprefix tailTrace_4530264
  have hstable : (prefixWord ++ tailWord_4530264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530264).length < 2 ^ (prefixWord ++ tailWord_4530264).sum := by decide
  have hdescent : baseEnd_4530264 < baseStart_4530264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530282 : List Nat := [3, 1, 3, 2, 3, 1, 2, 3, 1, 2, 2]
def baseStart_4530282 : Nat := 118140960795 + 4530282 * 2 ^ 59
def prefixEnd_4530282 : Nat := 4983230072969 + 3 ^ 40 * 4530282 * 2
def baseEnd_4530282 : Nat := 2326212166411949484540619

theorem tailTrace_4530282 : CollatzResearch.WordTrace tailWord_4530282 prefixEnd_4530282 2326212166411949484540619 := by
  unfold tailWord_4530282
  simp only [CollatzResearch.WordTrace]
  refine ⟨41308239743392374853116275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110155305982379666274976733 41308239743392374853116275)
  ·
    refine ⟨61962359615088562279674413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41308239743392374853116275 61962359615088562279674413)
    ·
      refine ⟨23235884855658210854877905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61962359615088562279674413 23235884855658210854877905)
      ·
        refine ⟨17426913641743658141158429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23235884855658210854877905 17426913641743658141158429)
        ·
          refine ⟨6535092615653871802934411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17426913641743658141158429 6535092615653871802934411)
          ·
            refine ⟨9802638923480807704401617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6535092615653871802934411 9802638923480807704401617)
            ·
              refine ⟨7351979192610605778301213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9802638923480807704401617 7351979192610605778301213)
              ·
                refine ⟨2756992197228977166862955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7351979192610605778301213 2756992197228977166862955)
                ·
                  refine ⟨4135488295843465750294433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756992197228977166862955 4135488295843465750294433)
                  ·
                    refine ⟨3101616221882599312720825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4135488295843465750294433 3101616221882599312720825)
                    ·
                      refine ⟨2326212166411949484540619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3101616221882599312720825 2326212166411949484540619)
                      ·
                        rfl

theorem cell23_4530282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_4530282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530282 prefixEnd_4530282 := by exact prefixLift 4530282
  have htrace : WordTrace (prefixWord ++ tailWord_4530282) baseStart_4530282 baseEnd_4530282 := by
    simpa [prefixWord, tailWord_4530282, baseEnd_4530282] using wordTrace_append hprefix tailTrace_4530282
  have hstable : (prefixWord ++ tailWord_4530282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530282).length < 2 ^ (prefixWord ++ tailWord_4530282).sum := by decide
  have hdescent : baseEnd_4530282 < baseStart_4530282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530314 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 2, 6]
def baseStart_4530314 : Nat := 118140960795 + 4530314 * 2 ^ 59
def prefixEnd_4530314 : Nat := 4983230072969 + 3 ^ 40 * 4530314 * 2
def baseEnd_4530314 : Nat := 775409532597631119780157

theorem tailTrace_4530314 : CollatzResearch.WordTrace tailWord_4530314 prefixEnd_4530314 775409532597631119780157 := by
  unfold tailWord_4530314
  simp only [CollatzResearch.WordTrace]
  refine ⟨41308531527363392219407499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110156084072969045918419997 41308531527363392219407499)
  ·
    refine ⟨61962797291045088329111249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41308531527363392219407499 61962797291045088329111249)
    ·
      refine ⟨46472097968283816246833437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61962797291045088329111249 46472097968283816246833437)
      ·
        refine ⟨17427036738106431092562539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46472097968283816246833437 17427036738106431092562539)
        ·
          refine ⟨26140555107159646638843809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17427036738106431092562539 26140555107159646638843809)
          ·
            refine ⟨19605416330369734979132857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26140555107159646638843809 19605416330369734979132857)
            ·
              refine ⟨14704062247777301234349643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19605416330369734979132857 14704062247777301234349643)
              ·
                refine ⟨22056093371665951851524465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14704062247777301234349643 22056093371665951851524465)
                ·
                  refine ⟨16542070028749463888643349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22056093371665951851524465 16542070028749463888643349)
                  ·
                    refine ⟨775409532597631119780157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16542070028749463888643349 775409532597631119780157)
                    ·
                      rfl

theorem cell23_4530314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_4530314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530314 prefixEnd_4530314 := by exact prefixLift 4530314
  have htrace : WordTrace (prefixWord ++ tailWord_4530314) baseStart_4530314 baseEnd_4530314 := by
    simpa [prefixWord, tailWord_4530314, baseEnd_4530314] using wordTrace_append hprefix tailTrace_4530314
  have hstable : (prefixWord ++ tailWord_4530314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530314).length < 2 ^ (prefixWord ++ tailWord_4530314).sum := by decide
  have hdescent : baseEnd_4530314 < baseStart_4530314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530372 : List Nat := [2, 3, 3, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_4530372 : Nat := 118140960795 + 4530372 * 2 ^ 59
def prefixEnd_4530372 : Nat := 4983230072969 + 3 ^ 40 * 4530372 * 2
def baseEnd_4530372 : Nat := 2326258379670854132415205

theorem tailTrace_4530372 : CollatzResearch.WordTrace tailWord_4530372 prefixEnd_4530372 2326258379670854132415205 := by
  unfold tailWord_4530372
  simp only [CollatzResearch.WordTrace]
  refine ⟨82618120771621722391620685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110157494362162296522160913 82618120771621722391620685)
  ·
    refine ⟨30981795289358145896857757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82618120771621722391620685 30981795289358145896857757)
    ·
      refine ⟨11618173233509304711321659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30981795289358145896857757 11618173233509304711321659)
      ·
        refine ⟨17427259850263957066982489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11618173233509304711321659 17427259850263957066982489)
        ·
          refine ⟨13070444887697967800236867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17427259850263957066982489 13070444887697967800236867)
          ·
            refine ⟨19605667331546951700355301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13070444887697967800236867 19605667331546951700355301)
            ·
              refine ⟨3676062624665053443816619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19605667331546951700355301 3676062624665053443816619)
              ·
                refine ⟨5514093936997580165724929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3676062624665053443816619 5514093936997580165724929)
                ·
                  refine ⟨4135570452748185124293697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5514093936997580165724929 4135570452748185124293697)
                  ·
                    refine ⟨3101677839561138843220273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4135570452748185124293697 3101677839561138843220273)
                    ·
                      refine ⟨2326258379670854132415205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3101677839561138843220273 2326258379670854132415205)
                      ·
                        rfl

theorem cell23_4530372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_4530372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530372 prefixEnd_4530372 := by exact prefixLift 4530372
  have htrace : WordTrace (prefixWord ++ tailWord_4530372) baseStart_4530372 baseEnd_4530372 := by
    simpa [prefixWord, tailWord_4530372, baseEnd_4530372] using wordTrace_append hprefix tailTrace_4530372
  have hstable : (prefixWord ++ tailWord_4530372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530372).length < 2 ^ (prefixWord ++ tailWord_4530372).sum := by decide
  have hdescent : baseEnd_4530372 < baseStart_4530372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530394 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4]
def baseStart_4530394 : Nat := 118140960795 + 4530394 * 2 ^ 59
def prefixEnd_4530394 : Nat := 4983230072969 + 3 ^ 40 * 4530394 * 2
def baseEnd_4530394 : Nat := 2326269676245253046340103

theorem tailTrace_4530394 : CollatzResearch.WordTrace tailWord_4530394 prefixEnd_4530394 2326269676245253046340103 := by
  unfold tailWord_4530394
  simp only [CollatzResearch.WordTrace]
  refine ⟨41309260987290935635135559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110158029299442495027028157 41309260987290935635135559)
  ·
    refine ⟨61963891480936403452703339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41309260987290935635135559 61963891480936403452703339)
    ·
      refine ⟨92945837221404605179055009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61963891480936403452703339 92945837221404605179055009)
      ·
        refine ⟨69709377916053453884291257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92945837221404605179055009 69709377916053453884291257)
        ·
          refine ⟨52282033437040090413218443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69709377916053453884291257 52282033437040090413218443)
          ·
            refine ⟨78423050155560135619827665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52282033437040090413218443 78423050155560135619827665)
            ·
              refine ⟨58817287616670101714870749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78423050155560135619827665 58817287616670101714870749)
              ·
                refine ⟨22056482856251288143076531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58817287616670101714870749 22056482856251288143076531)
                ·
                  refine ⟨33084724284376932214614797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22056482856251288143076531 33084724284376932214614797)
                  ·
                    refine ⟨12406771606641349580480549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33084724284376932214614797 12406771606641349580480549)
                    ·
                      refine ⟨2326269676245253046340103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12406771606641349580480549 2326269676245253046340103)
                      ·
                        rfl

theorem cell23_4530394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_4530394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530394 prefixEnd_4530394 := by exact prefixLift 4530394
  have htrace : WordTrace (prefixWord ++ tailWord_4530394) baseStart_4530394 baseEnd_4530394 := by
    simpa [prefixWord, tailWord_4530394, baseEnd_4530394] using wordTrace_append hprefix tailTrace_4530394
  have hstable : (prefixWord ++ tailWord_4530394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530394).length < 2 ^ (prefixWord ++ tailWord_4530394).sum := by decide
  have hdescent : baseEnd_4530394 < baseStart_4530394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530411 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 2, 4, 2]
def baseStart_4530411 : Nat := 118140960795 + 4530411 * 2 ^ 59
def prefixEnd_4530411 : Nat := 4983230072969 + 3 ^ 40 * 4530411 * 2
def baseEnd_4530411 : Nat := 2326278405416379479827525

theorem tailTrace_4530411 : CollatzResearch.WordTrace tailWord_4530411 prefixEnd_4530411 2326278405416379479827525 := by
  unfold tailWord_4530411
  simp only [CollatzResearch.WordTrace]
  refine ⟨165237663990102154443911087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110158442660068102962607391 165237663990102154443911087)
  ·
    refine ⟨247856495985153231665866631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165237663990102154443911087 247856495985153231665866631)
    ·
      refine ⟨371784743977729847498799947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247856495985153231665866631 371784743977729847498799947)
      ·
        refine ⟨557677115966594771248199921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371784743977729847498799947 557677115966594771248199921)
        ·
          refine ⟨418257836974946078436149941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557677115966594771248199921 418257836974946078436149941)
          ·
            refine ⟨39211672216401194853389057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 418257836974946078436149941 39211672216401194853389057)
            ·
              refine ⟨29408754162300896140041793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39211672216401194853389057 29408754162300896140041793)
              ·
                refine ⟨22056565621725672105031345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29408754162300896140041793 22056565621725672105031345)
                ·
                  refine ⟨16542424216294254078773509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22056565621725672105031345 16542424216294254078773509)
                  ·
                    refine ⟨3101704540555172639770033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16542424216294254078773509 3101704540555172639770033)
                    ·
                      refine ⟨2326278405416379479827525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3101704540555172639770033 2326278405416379479827525)
                      ·
                        rfl

theorem cell23_4530411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 4, 2].length) (baseStart_4530411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530411 prefixEnd_4530411 := by exact prefixLift 4530411
  have htrace : WordTrace (prefixWord ++ tailWord_4530411) baseStart_4530411 baseEnd_4530411 := by
    simpa [prefixWord, tailWord_4530411, baseEnd_4530411] using wordTrace_append hprefix tailTrace_4530411
  have hstable : (prefixWord ++ tailWord_4530411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530411).length < 2 ^ (prefixWord ++ tailWord_4530411).sum := by decide
  have hdescent : baseEnd_4530411 < baseStart_4530411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530414 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_4530414 : Nat := 118140960795 + 4530414 * 2 ^ 59
def prefixEnd_4530414 : Nat := 4983230072969 + 3 ^ 40 * 4530414 * 2
def baseEnd_4530414 : Nat := 2326279945858342968090011

theorem tailTrace_4530414 : CollatzResearch.WordTrace tailWord_4530414 prefixEnd_4530414 2326279945858342968090011 := by
  unfold tailWord_4530414
  simp only [CollatzResearch.WordTrace]
  refine ⟨20654721676136410744533787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110158515606060857304180197 20654721676136410744533787)
  ·
    refine ⟨30982082514204616116800681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20654721676136410744533787 30982082514204616116800681)
    ·
      refine ⟨23236561885653462087600511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30982082514204616116800681 23236561885653462087600511)
      ·
        refine ⟨34854842828480193131400767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23236561885653462087600511 34854842828480193131400767)
        ·
          refine ⟨52282264242720289697101151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34854842828480193131400767 52282264242720289697101151)
          ·
            refine ⟨78423396364080434545651727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52282264242720289697101151 78423396364080434545651727)
            ·
              refine ⟨117635094546120651818477591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78423396364080434545651727 117635094546120651818477591)
              ·
                refine ⟨176452641819180977727716387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117635094546120651818477591 176452641819180977727716387)
                ·
                  refine ⟨264678962728771466591574581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176452641819180977727716387 264678962728771466591574581)
                  ·
                    refine ⟨24813652755822324992960117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 264678962728771466591574581 24813652755822324992960117)
                    ·
                      refine ⟨2326279945858342968090011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24813652755822324992960117 2326279945858342968090011)
                      ·
                        rfl

theorem cell23_4530414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_4530414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530414 prefixEnd_4530414 := by exact prefixLift 4530414
  have htrace : WordTrace (prefixWord ++ tailWord_4530414) baseStart_4530414 baseEnd_4530414 := by
    simpa [prefixWord, tailWord_4530414, baseEnd_4530414] using wordTrace_append hprefix tailTrace_4530414
  have hstable : (prefixWord ++ tailWord_4530414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530414).length < 2 ^ (prefixWord ++ tailWord_4530414).sum := by decide
  have hdescent : baseEnd_4530414 < baseStart_4530414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530428 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 2, 4, 2]
def baseStart_4530428 : Nat := 118140960795 + 4530428 * 2 ^ 59
def prefixEnd_4530428 : Nat := 4983230072969 + 3 ^ 40 * 4530428 * 2
def baseEnd_4530428 : Nat := 2326287134587505913314947

theorem tailTrace_4530428 : CollatzResearch.WordTrace tailWord_4530428 prefixEnd_4530428 2326287134587505913314947 := by
  unfold tailWord_4530428
  simp only [CollatzResearch.WordTrace]
  refine ⟨82619142015520283173639969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110158856020693710898186625 82619142015520283173639969)
  ·
    refine ⟨61964356511640212380229977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82619142015520283173639969 61964356511640212380229977)
    ·
      refine ⟨46473267383730159285172483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61964356511640212380229977 46473267383730159285172483)
      ·
        refine ⟨69709901075595238927758725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46473267383730159285172483 69709901075595238927758725)
        ·
          refine ⟨13070606451674107298954761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69709901075595238927758725 13070606451674107298954761)
          ·
            refine ⟨9802954838755580474216071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13070606451674107298954761 9802954838755580474216071)
            ·
              refine ⟨14704432258133370711324107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9802954838755580474216071 14704432258133370711324107)
              ·
                refine ⟨22056648387200056066986161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14704432258133370711324107 22056648387200056066986161)
                ·
                  refine ⟨16542486290400042050239621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22056648387200056066986161 16542486290400042050239621)
                  ·
                    refine ⟨3101716179450007884419929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16542486290400042050239621 3101716179450007884419929)
                    ·
                      refine ⟨2326287134587505913314947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3101716179450007884419929 2326287134587505913314947)
                      ·
                        rfl

theorem cell23_4530428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_4530428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530428 prefixEnd_4530428 := by exact prefixLift 4530428
  have htrace : WordTrace (prefixWord ++ tailWord_4530428) baseStart_4530428 baseEnd_4530428 := by
    simpa [prefixWord, tailWord_4530428, baseEnd_4530428] using wordTrace_append hprefix tailTrace_4530428
  have hstable : (prefixWord ++ tailWord_4530428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530428).length < 2 ^ (prefixWord ++ tailWord_4530428).sum := by decide
  have hdescent : baseEnd_4530428 < baseStart_4530428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530455 : List Nat := [1, 1, 3, 4, 1, 3, 2, 3, 1, 4]
def baseStart_4530455 : Nat := 118140960795 + 4530455 * 2 ^ 59
def prefixEnd_4530455 : Nat := 4983230072969 + 3 ^ 40 * 4530455 * 2
def baseEnd_4530455 : Nat := 775433666188392435892441

theorem tailTrace_4530455 : CollatzResearch.WordTrace tailWord_4530455 prefixEnd_4530455 775433666188392435892441 := by
  unfold tailWord_4530455
  simp only [CollatzResearch.WordTrace]
  refine ⟨165239268801942749958512819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110159512534628499972341879 165239268801942749958512819)
  ·
    refine ⟨247858903202914124937769229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165239268801942749958512819 247858903202914124937769229)
    ·
      refine ⟨92947088701092796851663461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247858903202914124937769229 92947088701092796851663461)
      ·
        refine ⟨17427579131454899409686899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92947088701092796851663461 17427579131454899409686899)
        ·
          refine ⟨26141368697182349114530349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17427579131454899409686899 26141368697182349114530349)
          ·
            refine ⟨9803013261443380917948881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26141368697182349114530349 9803013261443380917948881)
            ·
              refine ⟨7352259946082535688461661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9803013261443380917948881 7352259946082535688461661)
              ·
                refine ⟨2757097479780950883173123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7352259946082535688461661 2757097479780950883173123)
                ·
                  refine ⟨4135646219671426324759685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2757097479780950883173123 4135646219671426324759685)
                  ·
                    refine ⟨775433666188392435892441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4135646219671426324759685 775433666188392435892441)
                    ·
                      rfl

theorem cell23_4530455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 1, 4].length) (baseStart_4530455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530455 prefixEnd_4530455 := by exact prefixLift 4530455
  have htrace : WordTrace (prefixWord ++ tailWord_4530455) baseStart_4530455 baseEnd_4530455 := by
    simpa [prefixWord, tailWord_4530455, baseEnd_4530455] using wordTrace_append hprefix tailTrace_4530455
  have hstable : (prefixWord ++ tailWord_4530455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530455).length < 2 ^ (prefixWord ++ tailWord_4530455).sum := by decide
  have hdescent : baseEnd_4530455 < baseStart_4530455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530468 : List Nat := [2, 3, 1, 3, 1, 4, 1, 2, 6]
def baseStart_4530468 : Nat := 118140960795 + 4530468 * 2 ^ 59
def prefixEnd_4530468 : Nat := 4983230072969 + 3 ^ 40 * 4530468 * 2
def baseEnd_4530468 : Nat := 258478630423742861868307

theorem tailTrace_4530468 : CollatzResearch.WordTrace tailWord_4530468 prefixEnd_4530468 258478630423742861868307 := by
  unfold tailWord_4530468
  simp only [CollatzResearch.WordTrace]
  refine ⟨82619871475447826589368029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110159828633930435452490705 82619871475447826589368029)
  ·
    refine ⟨30982451803292934971013011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82619871475447826589368029 30982451803292934971013011)
    ·
      refine ⟨46473677704939402456519517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30982451803292934971013011 46473677704939402456519517)
      ·
        refine ⟨17427629139352275921194819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46473677704939402456519517 17427629139352275921194819)
        ·
          refine ⟨26141443709028413881792229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17427629139352275921194819 26141443709028413881792229)
          ·
            refine ⟨4901520695442827602836043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26141443709028413881792229 4901520695442827602836043)
            ·
              refine ⟨7352281043164241404254065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4901520695442827602836043 7352281043164241404254065)
              ·
                refine ⟨5514210782373181053190549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7352281043164241404254065 5514210782373181053190549)
                ·
                  refine ⟨258478630423742861868307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5514210782373181053190549 258478630423742861868307)
                  ·
                    rfl

theorem cell23_4530468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_4530468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530468 prefixEnd_4530468 := by exact prefixLift 4530468
  have htrace : WordTrace (prefixWord ++ tailWord_4530468) baseStart_4530468 baseEnd_4530468 := by
    simpa [prefixWord, tailWord_4530468, baseEnd_4530468] using wordTrace_append hprefix tailTrace_4530468
  have hstable : (prefixWord ++ tailWord_4530468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530468).length < 2 ^ (prefixWord ++ tailWord_4530468).sum := by decide
  have hdescent : baseEnd_4530468 < baseStart_4530468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530512 : List Nat := [2, 1, 1, 1, 1, 8, 1, 3, 1, 1, 3]
def baseStart_4530512 : Nat := 118140960795 + 4530512 * 2 ^ 59
def prefixEnd_4530512 : Nat := 4983230072969 + 3 ^ 40 * 4530512 * 2
def baseEnd_4530512 : Nat := 2326330266962483584664561

theorem tailTrace_4530512 : CollatzResearch.WordTrace tailWord_4530512 prefixEnd_4530512 2326330266962483584664561 := by
  unfold tailWord_4530512
  simp only [CollatzResearch.WordTrace]
  refine ⟨82620673881368124346668895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110160898508490832462225193 82620673881368124346668895)
  ·
    refine ⟨123931010822052186520003343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82620673881368124346668895 123931010822052186520003343)
    ·
      refine ⟨185896516233078279780005015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123931010822052186520003343 185896516233078279780005015)
      ·
        refine ⟨278844774349617419670007523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185896516233078279780005015 278844774349617419670007523)
        ·
          refine ⟨418267161524426129505011285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278844774349617419670007523 418267161524426129505011285)
          ·
            refine ⟨4901568299114368705136851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 418267161524426129505011285 4901568299114368705136851)
            ·
              refine ⟨7352352448671553057705277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4901568299114368705136851 7352352448671553057705277)
              ·
                refine ⟨2757132168251832396639479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7352352448671553057705277 2757132168251832396639479)
                ·
                  refine ⟨4135698252377748594959219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2757132168251832396639479 4135698252377748594959219)
                  ·
                    refine ⟨6203547378566622892438829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4135698252377748594959219 6203547378566622892438829)
                    ·
                      refine ⟨2326330266962483584664561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6203547378566622892438829 2326330266962483584664561)
                      ·
                        rfl

theorem cell23_4530512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 1, 1, 3].length) (baseStart_4530512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530512 prefixEnd_4530512 := by exact prefixLift 4530512
  have htrace : WordTrace (prefixWord ++ tailWord_4530512) baseStart_4530512 baseEnd_4530512 := by
    simpa [prefixWord, tailWord_4530512, baseEnd_4530512] using wordTrace_append hprefix tailTrace_4530512
  have hstable : (prefixWord ++ tailWord_4530512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530512).length < 2 ^ (prefixWord ++ tailWord_4530512).sum := by decide
  have hdescent : baseEnd_4530512 < baseStart_4530512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530521 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 5, 2, 3]
def baseStart_4530521 : Nat := 118140960795 + 4530521 * 2 ^ 59
def prefixEnd_4530521 : Nat := 4983230072969 + 3 ^ 40 * 4530521 * 2
def baseEnd_4530521 : Nat := 2326334888288374049452019

theorem tailTrace_4530521 : CollatzResearch.WordTrace tailWord_4530521 prefixEnd_4530521 2326334888288374049452019 := by
  unfold tailWord_4530521
  simp only [CollatzResearch.WordTrace]
  refine ⟨165241676019703643230415417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110161117346469095486943611 165241676019703643230415417)
  ·
    refine ⟨123931257014777732422811563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165241676019703643230415417 123931257014777732422811563)
    ·
      refine ⟨185896885522166598634217345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123931257014777732422811563 185896885522166598634217345)
      ·
        refine ⟨139422664141624948975663009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185896885522166598634217345 139422664141624948975663009)
        ·
          refine ⟨104566998106218711731747257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139422664141624948975663009 104566998106218711731747257)
          ·
            refine ⟨78425248579664033798810443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104566998106218711731747257 78425248579664033798810443)
            ·
              refine ⟨117637872869496050698215665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78425248579664033798810443 117637872869496050698215665)
              ·
                refine ⟨88228404652122038023661749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117637872869496050698215665 88228404652122038023661749)
                ·
                  refine ⟨8271412936136441064718289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88228404652122038023661749 8271412936136441064718289)
                  ·
                    refine ⟨6203559702102330798538717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8271412936136441064718289 6203559702102330798538717)
                    ·
                      refine ⟨2326334888288374049452019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6203559702102330798538717 2326334888288374049452019)
                      ·
                        rfl

theorem cell23_4530521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_4530521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530521 prefixEnd_4530521 := by exact prefixLift 4530521
  have htrace : WordTrace (prefixWord ++ tailWord_4530521) baseStart_4530521 baseEnd_4530521 := by
    simpa [prefixWord, tailWord_4530521, baseEnd_4530521] using wordTrace_append hprefix tailTrace_4530521
  have hstable : (prefixWord ++ tailWord_4530521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530521).length < 2 ^ (prefixWord ++ tailWord_4530521).sum := by decide
  have hdescent : baseEnd_4530521 < baseStart_4530521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530538 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_4530538 : Nat := 118140960795 + 4530538 * 2 ^ 59
def prefixEnd_4530538 : Nat := 4983230072969 + 3 ^ 40 * 4530538 * 2
def baseEnd_4530538 : Nat := 2326343617459500482939441

theorem tailTrace_4530538 : CollatzResearch.WordTrace tailWord_4530538 prefixEnd_4530538 2326343617459500482939441 := by
  unfold tailWord_4530538
  simp only [CollatzResearch.WordTrace]
  refine ⟨41310574015160513783446067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110161530707094703422522845 41310574015160513783446067)
  ·
    refine ⟨61965861022740770675169101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41310574015160513783446067 61965861022740770675169101)
    ·
      refine ⟨23237197883527789003188413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61965861022740770675169101 23237197883527789003188413)
      ·
        refine ⟨8713949206322920876195655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23237197883527789003188413 8713949206322920876195655)
        ·
          refine ⟨13070923809484381314293483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8713949206322920876195655 13070923809484381314293483)
          ·
            refine ⟨19606385714226571971440225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13070923809484381314293483 19606385714226571971440225)
            ·
              refine ⟨14704789285669928978580169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19606385714226571971440225 14704789285669928978580169)
              ·
                refine ⟨11028591964252446733935127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14704789285669928978580169 11028591964252446733935127)
                ·
                  refine ⟨16542887946378670100902691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11028591964252446733935127 16542887946378670100902691)
                  ·
                    refine ⟨24814331919568005151354037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16542887946378670100902691 24814331919568005151354037)
                    ·
                      refine ⟨2326343617459500482939441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24814331919568005151354037 2326343617459500482939441)
                      ·
                        rfl

theorem cell23_4530538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_4530538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530538 prefixEnd_4530538 := by exact prefixLift 4530538
  have htrace : WordTrace (prefixWord ++ tailWord_4530538) baseStart_4530538 baseEnd_4530538 := by
    simpa [prefixWord, tailWord_4530538, baseEnd_4530538] using wordTrace_append hprefix tailTrace_4530538
  have hstable : (prefixWord ++ tailWord_4530538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530538).length < 2 ^ (prefixWord ++ tailWord_4530538).sum := by decide
  have hdescent : baseEnd_4530538 < baseStart_4530538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530541 : List Nat := [1, 5, 1, 1, 1, 2, 4, 8]
def baseStart_4530541 : Nat := 118140960795 + 4530541 * 2 ^ 59
def prefixEnd_4530541 : Nat := 4983230072969 + 3 ^ 40 * 4530541 * 2
def baseEnd_4530541 : Nat := 86160931774128295229701

theorem tailTrace_4530541 : CollatzResearch.WordTrace tailWord_4530541 prefixEnd_4530541 86160931774128295229701 := by
  unfold tailWord_4530541
  simp only [CollatzResearch.WordTrace]
  refine ⟨165242405479631186646143477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110161603653087457764095651 165242405479631186646143477)
  ·
    refine ⟨15491475513715423748075951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165242405479631186646143477 15491475513715423748075951)
    ·
      refine ⟨23237213270573135622113927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15491475513715423748075951 23237213270573135622113927)
      ·
        refine ⟨34855819905859703433170891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23237213270573135622113927 34855819905859703433170891)
        ·
          refine ⟨52283729858789555149756337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34855819905859703433170891 52283729858789555149756337)
          ·
            refine ⟨39212797394092166362317253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52283729858789555149756337 39212797394092166362317253)
            ·
              refine ⟨7352399511392281192934485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39212797394092166362317253 7352399511392281192934485)
              ·
                refine ⟨86160931774128295229701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7352399511392281192934485 86160931774128295229701)
                ·
                  rfl

theorem cell23_4530541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 8].length) (baseStart_4530541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530541 prefixEnd_4530541 := by exact prefixLift 4530541
  have htrace : WordTrace (prefixWord ++ tailWord_4530541) baseStart_4530541 baseEnd_4530541 := by
    simpa [prefixWord, tailWord_4530541, baseEnd_4530541] using wordTrace_append hprefix tailTrace_4530541
  have hstable : (prefixWord ++ tailWord_4530541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530541).length < 2 ^ (prefixWord ++ tailWord_4530541).sum := by decide
  have hdescent : baseEnd_4530541 < baseStart_4530541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530555 : List Nat := [1, 1, 1, 1, 1, 9, 1, 2, 1, 2, 3]
def baseStart_4530555 : Nat := 118140960795 + 4530555 * 2 ^ 59
def prefixEnd_4530555 : Nat := 4983230072969 + 3 ^ 40 * 4530555 * 2
def baseEnd_4530555 : Nat := 2326352346630626916426863

theorem tailTrace_4530555 : CollatzResearch.WordTrace tailWord_4530555 prefixEnd_4530555 2326352346630626916426863 := by
  unfold tailWord_4530555
  simp only [CollatzResearch.WordTrace]
  refine ⟨165242916101580467037153119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110161944067720311358102079 165242916101580467037153119)
  ·
    refine ⟨247864374152370700555729679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165242916101580467037153119 247864374152370700555729679)
    ·
      refine ⟨371796561228556050833594519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247864374152370700555729679 371796561228556050833594519)
      ·
        refine ⟨557694841842834076250391779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371796561228556050833594519 557694841842834076250391779)
        ·
          refine ⟨836542262764251114375587669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557694841842834076250391779 836542262764251114375587669)
          ·
            refine ⟨4901614820884283873294459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 836542262764251114375587669 4901614820884283873294459)
            ·
              refine ⟨7352422231326425809941689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4901614820884283873294459 7352422231326425809941689)
              ·
                refine ⟨5514316673494819357456267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7352422231326425809941689 5514316673494819357456267)
                ·
                  refine ⟨8271475010242229036184401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5514316673494819357456267 8271475010242229036184401)
                  ·
                    refine ⟨6203606257681671777138301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8271475010242229036184401 6203606257681671777138301)
                    ·
                      refine ⟨2326352346630626916426863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6203606257681671777138301 2326352346630626916426863)
                      ·
                        rfl

theorem cell23_4530555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 2, 3].length) (baseStart_4530555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530555 prefixEnd_4530555 := by exact prefixLift 4530555
  have htrace : WordTrace (prefixWord ++ tailWord_4530555) baseStart_4530555 baseEnd_4530555 := by
    simpa [prefixWord, tailWord_4530555, baseEnd_4530555] using wordTrace_append hprefix tailTrace_4530555
  have hstable : (prefixWord ++ tailWord_4530555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530555).length < 2 ^ (prefixWord ++ tailWord_4530555).sum := by decide
  have hdescent : baseEnd_4530555 < baseStart_4530555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530568 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 1, 3, 3]
def baseStart_4530568 : Nat := 118140960795 + 4530568 * 2 ^ 59
def prefixEnd_4530568 : Nat := 4983230072969 + 3 ^ 40 * 4530568 * 2
def baseEnd_4530568 : Nat := 2326359021879135365564303

theorem tailTrace_4530568 : CollatzResearch.WordTrace tailWord_4530568 prefixEnd_4530568 2326359021879135365564303 := by
  unfold tailWord_4530568
  simp only [CollatzResearch.WordTrace]
  refine ⟨82621695125266685128688179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110162260167022246838250905 82621695125266685128688179)
  ·
    refine ⟨123932542687900027693032269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82621695125266685128688179 123932542687900027693032269)
    ·
      refine ⟨46474703507962510384887101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123932542687900027693032269 46474703507962510384887101)
      ·
        refine ⟨17428013815485941394332663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46474703507962510384887101 17428013815485941394332663)
        ·
          refine ⟨26142020723228912091498995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17428013815485941394332663 26142020723228912091498995)
          ·
            refine ⟨39213031084843368137248493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26142020723228912091498995 39213031084843368137248493)
            ·
              refine ⟨14704886656816263051468185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39213031084843368137248493 14704886656816263051468185)
              ·
                refine ⟨11028664992612197288601139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14704886656816263051468185 11028664992612197288601139)
                ·
                  refine ⟨16542997488918295932901709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11028664992612197288601139 16542997488918295932901709)
                  ·
                    refine ⟨6203624058344360974838141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16542997488918295932901709 6203624058344360974838141)
                    ·
                      refine ⟨2326359021879135365564303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6203624058344360974838141 2326359021879135365564303)
                      ·
                        rfl

theorem cell23_4530568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_4530568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530568 prefixEnd_4530568 := by exact prefixLift 4530568
  have htrace : WordTrace (prefixWord ++ tailWord_4530568) baseStart_4530568 baseEnd_4530568 := by
    simpa [prefixWord, tailWord_4530568, baseEnd_4530568] using wordTrace_append hprefix tailTrace_4530568
  have hstable : (prefixWord ++ tailWord_4530568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530568).length < 2 ^ (prefixWord ++ tailWord_4530568).sum := by decide
  have hdescent : baseEnd_4530568 < baseStart_4530568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530585 : List Nat := [1, 2, 1, 2, 1, 4, 4, 2, 2, 1, 3]
def baseStart_4530585 : Nat := 118140960795 + 4530585 * 2 ^ 59
def prefixEnd_4530585 : Nat := 4983230072969 + 3 ^ 40 * 4530585 * 2
def baseEnd_4530585 : Nat := 2326367751050261799051725

theorem tailTrace_4530585 : CollatzResearch.WordTrace tailWord_4530585 prefixEnd_4530585 2326367751050261799051725 := by
  unfold tailWord_4530585
  simp only [CollatzResearch.WordTrace]
  refine ⟨165244010291471782160745209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110162673527647854773830139 165244010291471782160745209)
  ·
    refine ⟨123933007718603836620558907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165244010291471782160745209 123933007718603836620558907)
    ·
      refine ⟨185899511577905754930838361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123933007718603836620558907 185899511577905754930838361)
      ·
        refine ⟨139424633683429316198128771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185899511577905754930838361 139424633683429316198128771)
        ·
          refine ⟨209136950525143974297193157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139424633683429316198128771 209136950525143974297193157)
          ·
            refine ⟨39213178223464495180723717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 209136950525143974297193157 39213178223464495180723717)
            ·
              refine ⟨7352470916899592846385697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39213178223464495180723717 7352470916899592846385697)
              ·
                refine ⟨5514353187674694634789273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7352470916899592846385697 5514353187674694634789273)
                ·
                  refine ⟨4135764890756020976091955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5514353187674694634789273 4135764890756020976091955)
                  ·
                    refine ⟨6203647336134031464137933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4135764890756020976091955 6203647336134031464137933)
                    ·
                      refine ⟨2326367751050261799051725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6203647336134031464137933 2326367751050261799051725)
                      ·
                        rfl

theorem cell23_4530585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 1, 3].length) (baseStart_4530585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530585 prefixEnd_4530585 := by exact prefixLift 4530585
  have htrace : WordTrace (prefixWord ++ tailWord_4530585) baseStart_4530585 baseEnd_4530585 := by
    simpa [prefixWord, tailWord_4530585, baseEnd_4530585] using wordTrace_append hprefix tailTrace_4530585
  have hstable : (prefixWord ++ tailWord_4530585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530585).length < 2 ^ (prefixWord ++ tailWord_4530585).sum := by decide
  have hdescent : baseEnd_4530585 < baseStart_4530585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530586 : List Nat := [3, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2]
def baseStart_4530586 : Nat := 118140960795 + 4530586 * 2 ^ 59
def prefixEnd_4530586 : Nat := 4983230072969 + 3 ^ 40 * 4530586 * 2
def baseEnd_4530586 : Nat := 2326368264530916295139221

theorem tailTrace_4530586 : CollatzResearch.WordTrace tailWord_4530586 prefixEnd_4530586 2326368264530916295139221 := by
  unfold tailWord_4530586
  simp only [CollatzResearch.WordTrace]
  refine ⟨41311011691117039832882903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110162697842978772887687741 41311011691117039832882903)
  ·
    refine ⟨61966517536675559749324355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41311011691117039832882903 61966517536675559749324355)
    ·
      refine ⟨92949776305013339623986533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61966517536675559749324355 92949776305013339623986533)
      ·
        refine ⟨17428083057190001179497475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92949776305013339623986533 17428083057190001179497475)
        ·
          refine ⟨26142124585785001769246213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17428083057190001179497475 26142124585785001769246213)
          ·
            refine ⟨4901648359834687831733665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26142124585785001769246213 4901648359834687831733665)
            ·
              refine ⟨3676236269876015873800249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4901648359834687831733665 3676236269876015873800249)
              ·
                refine ⟨2757177202407011905350187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3676236269876015873800249 2757177202407011905350187)
                ·
                  refine ⟨4135765803610517858025281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2757177202407011905350187 4135765803610517858025281)
                  ·
                    refine ⟨3101824352707888393518961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4135765803610517858025281 3101824352707888393518961)
                    ·
                      refine ⟨2326368264530916295139221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3101824352707888393518961 2326368264530916295139221)
                      ·
                        rfl

theorem cell23_4530586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_4530586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530586 prefixEnd_4530586 := by exact prefixLift 4530586
  have htrace : WordTrace (prefixWord ++ tailWord_4530586) baseStart_4530586 baseEnd_4530586 := by
    simpa [prefixWord, tailWord_4530586, baseEnd_4530586] using wordTrace_append hprefix tailTrace_4530586
  have hstable : (prefixWord ++ tailWord_4530586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530586).length < 2 ^ (prefixWord ++ tailWord_4530586).sum := by decide
  have hdescent : baseEnd_4530586 < baseStart_4530586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530591 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 4]
def baseStart_4530591 : Nat := 118140960795 + 4530591 * 2 ^ 59
def prefixEnd_4530591 : Nat := 4983230072969 + 3 ^ 40 * 4530591 * 2
def baseEnd_4530591 : Nat := 2326370831934188775576697

theorem tailTrace_4530591 : CollatzResearch.WordTrace tailWord_4530591 prefixEnd_4530591 2326370831934188775576697 := by
  unfold tailWord_4530591
  simp only [CollatzResearch.WordTrace]
  refine ⟨165244229129450045185463627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110162819419633363456975751 165244229129450045185463627)
  ·
    refine ⟨247866343694175067778195441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165244229129450045185463627 247866343694175067778195441)
    ·
      refine ⟨185899757770631300833646581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247866343694175067778195441 185899757770631300833646581)
      ·
        refine ⟨17428102290996684453154367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 185899757770631300833646581 17428102290996684453154367)
        ·
          refine ⟨26142153436495026679731551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17428102290996684453154367 26142153436495026679731551)
          ·
            refine ⟨39213230154742540019597327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26142153436495026679731551 39213230154742540019597327)
            ·
              refine ⟨58819845232113810029395991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39213230154742540019597327 58819845232113810029395991)
              ·
                refine ⟨88229767848170715044093987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58819845232113810029395991 88229767848170715044093987)
                ·
                  refine ⟨132344651772256072566140981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88229767848170715044093987 132344651772256072566140981)
                  ·
                    refine ⟨12407311103649006803075717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 132344651772256072566140981 12407311103649006803075717)
                    ·
                      refine ⟨2326370831934188775576697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12407311103649006803075717 2326370831934188775576697)
                      ·
                        rfl

theorem cell23_4530591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_4530591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530591 prefixEnd_4530591 := by exact prefixLift 4530591
  have htrace : WordTrace (prefixWord ++ tailWord_4530591) baseStart_4530591 baseEnd_4530591 := by
    simpa [prefixWord, tailWord_4530591, baseEnd_4530591] using wordTrace_append hprefix tailTrace_4530591
  have hstable : (prefixWord ++ tailWord_4530591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530591).length < 2 ^ (prefixWord ++ tailWord_4530591).sum := by decide
  have hdescent : baseEnd_4530591 < baseStart_4530591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530659 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 1, 4, 2]
def baseStart_4530659 : Nat := 118140960795 + 4530659 * 2 ^ 59
def prefixEnd_4530659 : Nat := 4983230072969 + 3 ^ 40 * 4530659 * 2
def baseEnd_4530659 : Nat := 2326405748618694509526385

theorem tailTrace_4530659 : CollatzResearch.WordTrace tailWord_4530659 prefixEnd_4530659 2326405748618694509526385 := by
  unfold tailWord_4530659
  simp only [CollatzResearch.WordTrace]
  refine ⟨165246709293203692798939031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110164472862135795199292687 165246709293203692798939031)
  ·
    refine ⟨247870063939805539198408547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165246709293203692798939031 247870063939805539198408547)
    ·
      refine ⟨371805095909708308797612821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247870063939805539198408547 371805095909708308797612821)
      ·
        refine ⟨17428363870767576974888101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 371805095909708308797612821 17428363870767576974888101)
        ·
          refine ⟨3267818225768920682791519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17428363870767576974888101 3267818225768920682791519)
          ·
            refine ⟨4901727338653381024187279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3267818225768920682791519 4901727338653381024187279)
            ·
              refine ⟨7352591007980071536280919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4901727338653381024187279 7352591007980071536280919)
              ·
                refine ⟨11028886511970107304421379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7352591007980071536280919 11028886511970107304421379)
                ·
                  refine ⟨16543329767955160956632069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11028886511970107304421379 16543329767955160956632069)
                  ·
                    refine ⟨3101874331491592679368513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16543329767955160956632069 3101874331491592679368513)
                    ·
                      refine ⟨2326405748618694509526385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3101874331491592679368513 2326405748618694509526385)
                      ·
                        rfl

theorem cell23_4530659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_4530659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530659 prefixEnd_4530659 := by exact prefixLift 4530659
  have htrace : WordTrace (prefixWord ++ tailWord_4530659) baseStart_4530659 baseEnd_4530659 := by
    simpa [prefixWord, tailWord_4530659, baseEnd_4530659] using wordTrace_append hprefix tailTrace_4530659
  have hstable : (prefixWord ++ tailWord_4530659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530659).length < 2 ^ (prefixWord ++ tailWord_4530659).sum := by decide
  have hdescent : baseEnd_4530659 < baseStart_4530659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530671 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 5]
def baseStart_4530671 : Nat := 118140960795 + 4530671 * 2 ^ 59
def prefixEnd_4530671 : Nat := 4983230072969 + 3 ^ 40 * 4530671 * 2
def baseEnd_4530671 : Nat := 2326411910386548462576329

theorem tailTrace_4530671 : CollatzResearch.WordTrace tailWord_4530671 prefixEnd_4530671 2326411910386548462576329 := by
  unfold tailWord_4530671
  simp only [CollatzResearch.WordTrace]
  refine ⟨165247146969160218848375867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110164764646106812565583911 165247146969160218848375867)
  ·
    refine ⟨247870720453740328272563801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165247146969160218848375867 247870720453740328272563801)
    ·
      refine ⟨185903040340305246204422851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247870720453740328272563801 185903040340305246204422851)
      ·
        refine ⟨278854560510457869306634277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185903040340305246204422851 278854560510457869306634277)
        ·
          refine ⟨52285230095710850494993927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 278854560510457869306634277 52285230095710850494993927)
          ·
            refine ⟨78427845143566275742490891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52285230095710850494993927 78427845143566275742490891)
            ·
              refine ⟨117641767715349413613736337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78427845143566275742490891 117641767715349413613736337)
              ·
                refine ⟨88231325786512060210302253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117641767715349413613736337 88231325786512060210302253)
                ·
                  refine ⟨33086747169942022578863345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88231325786512060210302253 33086747169942022578863345)
                  ·
                    refine ⟨24815060377456516934147509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33086747169942022578863345 24815060377456516934147509)
                    ·
                      refine ⟨2326411910386548462576329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24815060377456516934147509 2326411910386548462576329)
                      ·
                        rfl

theorem cell23_4530671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_4530671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530671 prefixEnd_4530671 := by exact prefixLift 4530671
  have htrace : WordTrace (prefixWord ++ tailWord_4530671) baseStart_4530671 baseEnd_4530671 := by
    simpa [prefixWord, tailWord_4530671, baseEnd_4530671] using wordTrace_append hprefix tailTrace_4530671
  have hstable : (prefixWord ++ tailWord_4530671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530671).length < 2 ^ (prefixWord ++ tailWord_4530671).sum := by decide
  have hdescent : baseEnd_4530671 < baseStart_4530671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530678 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_4530678 : Nat := 118140960795 + 4530678 * 2 ^ 59
def prefixEnd_4530678 : Nat := 4983230072969 + 3 ^ 40 * 4530678 * 2
def baseEnd_4530678 : Nat := 775471834917043311729599

theorem tailTrace_4530678 : CollatzResearch.WordTrace tailWord_4530678 prefixEnd_4530678 775471834917043311729599 := by
  unfold tailWord_4530678
  simp only [CollatzResearch.WordTrace]
  refine ⟨10327962642508428690242543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110164934853423239362587125 10327962642508428690242543)
  ·
    refine ⟨15491943963762643035363815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10327962642508428690242543 15491943963762643035363815)
    ·
      refine ⟨23237915945643964553045723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15491943963762643035363815 23237915945643964553045723)
      ·
        refine ⟨34856873918465946829568585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23237915945643964553045723 34856873918465946829568585)
        ·
          refine ⟨26142655438849460122176439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34856873918465946829568585 26142655438849460122176439)
          ·
            refine ⟨39213983158274190183264659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26142655438849460122176439 39213983158274190183264659)
            ·
              refine ⟨58820974737411285274896989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39213983158274190183264659 58820974737411285274896989)
              ·
                refine ⟨22057865526529231978086371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58820974737411285274896989 22057865526529231978086371)
                ·
                  refine ⟨33086798289793847967129557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22057865526529231978086371 33086798289793847967129557)
                  ·
                    refine ⟨775471834917043311729599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33086798289793847967129557 775471834917043311729599)
                    ·
                      rfl

theorem cell23_4530678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_4530678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530678 prefixEnd_4530678 := by exact prefixLift 4530678
  have htrace : WordTrace (prefixWord ++ tailWord_4530678) baseStart_4530678 baseEnd_4530678 := by
    simpa [prefixWord, tailWord_4530678, baseEnd_4530678] using wordTrace_append hprefix tailTrace_4530678
  have hstable : (prefixWord ++ tailWord_4530678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530678).length < 2 ^ (prefixWord ++ tailWord_4530678).sum := by decide
  have hdescent : baseEnd_4530678 < baseStart_4530678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530695 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 2, 5]
def baseStart_4530695 : Nat := 118140960795 + 4530695 * 2 ^ 59
def prefixEnd_4530695 : Nat := 4983230072969 + 3 ^ 40 * 4530695 * 2
def baseEnd_4530695 : Nat := 775474744640752122892073

theorem tailTrace_4530695 : CollatzResearch.WordTrace tailWord_4530695 prefixEnd_4530695 775474744640752122892073 := by
  unfold tailWord_4530695
  simp only [CollatzResearch.WordTrace]
  refine ⟨165248022321073270947249539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110165348214048847298166359 165248022321073270947249539)
  ·
    refine ⟨247872033481609906420874309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165248022321073270947249539 247872033481609906420874309)
    ·
      refine ⟨46476006277801857453913933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 247872033481609906420874309 46476006277801857453913933)
      ·
        refine ⟨17428502354175696545217725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46476006277801857453913933 17428502354175696545217725)
        ·
          refine ⟨6535688382815886204456647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17428502354175696545217725 6535688382815886204456647)
          ·
            refine ⟨9803532574223829306684971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6535688382815886204456647 9803532574223829306684971)
            ·
              refine ⟨14705298861335743960027457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9803532574223829306684971 14705298861335743960027457)
              ·
                refine ⟨11028974146001807970020593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14705298861335743960027457 11028974146001807970020593)
                ·
                  refine ⟨8271730609501355977515445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11028974146001807970020593 8271730609501355977515445)
                  ·
                    refine ⟨775474744640752122892073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8271730609501355977515445 775474744640752122892073)
                    ·
                      rfl

theorem cell23_4530695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_4530695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530695 prefixEnd_4530695 := by exact prefixLift 4530695
  have htrace : WordTrace (prefixWord ++ tailWord_4530695) baseStart_4530695 baseEnd_4530695 := by
    simpa [prefixWord, tailWord_4530695, baseEnd_4530695] using wordTrace_append hprefix tailTrace_4530695
  have hstable : (prefixWord ++ tailWord_4530695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530695).length < 2 ^ (prefixWord ++ tailWord_4530695).sum := by decide
  have hdescent : baseEnd_4530695 < baseStart_4530695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530759 : List Nat := [1, 1, 4, 1, 4, 1, 4, 2, 1, 4]
def baseStart_4530759 : Nat := 118140960795 + 4530759 * 2 ^ 59
def prefixEnd_4530759 : Nat := 4983230072969 + 3 ^ 40 * 4530759 * 2
def baseEnd_4530759 : Nat := 775485698894714706091975

theorem tailTrace_4530759 : CollatzResearch.WordTrace tailWord_4530759 prefixEnd_4530759 775485698894714706091975 := by
  unfold tailWord_4530759
  simp only [CollatzResearch.WordTrace]
  refine ⟨165250356592841409877579331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110166904395227606585052887 165250356592841409877579331)
  ·
    refine ⟨247875534889262114816368997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165250356592841409877579331 247875534889262114816368997)
    ·
      refine ⟨46476662791736646528069187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 247875534889262114816368997 46476662791736646528069187)
      ·
        refine ⟨69714994187604969792103781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46476662791736646528069187 69714994187604969792103781)
        ·
          refine ⟨13071561410175931836019459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69714994187604969792103781 13071561410175931836019459)
          ·
            refine ⟨19607342115263897754029189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13071561410175931836019459 19607342115263897754029189)
            ·
              refine ⟨3676376646611980828880473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19607342115263897754029189 3676376646611980828880473)
              ·
                refine ⟨2757282484958985621660355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3676376646611980828880473 2757282484958985621660355)
                ·
                  refine ⟨4135923727438478432490533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2757282484958985621660355 4135923727438478432490533)
                  ·
                    refine ⟨775485698894714706091975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4135923727438478432490533 775485698894714706091975)
                    ·
                      rfl

theorem cell23_4530759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_4530759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530759 prefixEnd_4530759 := by exact prefixLift 4530759
  have htrace : WordTrace (prefixWord ++ tailWord_4530759) baseStart_4530759 baseEnd_4530759 := by
    simpa [prefixWord, tailWord_4530759, baseEnd_4530759] using wordTrace_append hprefix tailTrace_4530759
  have hstable : (prefixWord ++ tailWord_4530759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530759).length < 2 ^ (prefixWord ++ tailWord_4530759).sum := by decide
  have hdescent : baseEnd_4530759 < baseStart_4530759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530775 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 1, 5, 2]
def baseStart_4530775 : Nat := 118140960795 + 4530775 * 2 ^ 59
def prefixEnd_4530775 : Nat := 4983230072969 + 3 ^ 40 * 4530775 * 2
def baseEnd_4530775 : Nat := 2326465312374616055675851

theorem tailTrace_4530775 : CollatzResearch.WordTrace tailWord_4530775 prefixEnd_4530775 2326465312374616055675851 := by
  unfold tailWord_4530775
  simp only [CollatzResearch.WordTrace]
  refine ⟨165250940160783444610161779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110167293440522296406774519 165250940160783444610161779)
  ·
    refine ⟨247876410241175166915242669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165250940160783444610161779 247876410241175166915242669)
    ·
      refine ⟨92953653840440687593216001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247876410241175166915242669 92953653840440687593216001)
      ·
        refine ⟨69715240380330515694912001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92953653840440687593216001 69715240380330515694912001)
        ·
          refine ⟨52286430285247886771184001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69715240380330515694912001 52286430285247886771184001)
          ·
            refine ⟨39214822713935915078388001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52286430285247886771184001 39214822713935915078388001)
            ·
              refine ⟨29411117035451936308791001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39214822713935915078388001 29411117035451936308791001)
              ·
                refine ⟨22058337776588952231593251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29411117035451936308791001 22058337776588952231593251)
                ·
                  refine ⟨33087506664883428347389877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22058337776588952231593251 33087506664883428347389877)
                  ·
                    refine ⟨3101953749832821407567801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33087506664883428347389877 3101953749832821407567801)
                    ·
                      refine ⟨2326465312374616055675851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3101953749832821407567801 2326465312374616055675851)
                      ·
                        rfl

theorem cell23_4530775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_4530775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530775 prefixEnd_4530775 := by exact prefixLift 4530775
  have htrace : WordTrace (prefixWord ++ tailWord_4530775) baseStart_4530775 baseEnd_4530775 := by
    simpa [prefixWord, tailWord_4530775, baseEnd_4530775] using wordTrace_append hprefix tailTrace_4530775
  have hstable : (prefixWord ++ tailWord_4530775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530775).length < 2 ^ (prefixWord ++ tailWord_4530775).sum := by decide
  have hdescent : baseEnd_4530775 < baseStart_4530775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530786 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_4530786 : Nat := 118140960795 + 4530786 * 2 ^ 59
def prefixEnd_4530786 : Nat := 4983230072969 + 3 ^ 40 * 4530786 * 2
def baseEnd_4530786 : Nat := 2326470960661815512638301

theorem tailTrace_4530786 : CollatzResearch.WordTrace tailWord_4530786 prefixEnd_4530786 2326470960661815512638301 := by
  unfold tailWord_4530786
  simp only [CollatzResearch.WordTrace]
  refine ⟨41312835340935898372203053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110167560909162395659208141 41312835340935898372203053)
  ·
    refine ⟨15492313252850961889576145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41312835340935898372203053 15492313252850961889576145)
    ·
      refine ⟨11619234939638221417182109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15492313252850961889576145 11619234939638221417182109)
      ·
        refine ⟨4357213102364333031443291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11619234939638221417182109 4357213102364333031443291)
        ·
          refine ⟨6535819653546499547164937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4357213102364333031443291 6535819653546499547164937)
          ·
            refine ⟨4901864740159874660373703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6535819653546499547164937 4901864740159874660373703)
            ·
              refine ⟨7352797110239811990560555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4901864740159874660373703 7352797110239811990560555)
              ·
                refine ⟨11029195665359717985840833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7352797110239811990560555 11029195665359717985840833)
                ·
                  refine ⟨8271896749019788489380625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11029195665359717985840833 8271896749019788489380625)
                  ·
                    refine ⟨6203922561764841367035469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8271896749019788489380625 6203922561764841367035469)
                    ·
                      refine ⟨2326470960661815512638301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6203922561764841367035469 2326470960661815512638301)
                      ·
                        rfl

theorem cell23_4530786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_4530786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530786 prefixEnd_4530786 := by exact prefixLift 4530786
  have htrace : WordTrace (prefixWord ++ tailWord_4530786) baseStart_4530786 baseEnd_4530786 := by
    simpa [prefixWord, tailWord_4530786, baseEnd_4530786] using wordTrace_append hprefix tailTrace_4530786
  have hstable : (prefixWord ++ tailWord_4530786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530786).length < 2 ^ (prefixWord ++ tailWord_4530786).sum := by decide
  have hdescent : baseEnd_4530786 < baseStart_4530786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530802 : List Nat := [3, 2, 1, 2, 4, 1, 1, 3, 1, 5]
def baseStart_4530802 : Nat := 118140960795 + 4530802 * 2 ^ 59
def prefixEnd_4530802 : Nat := 4983230072969 + 3 ^ 40 * 4530802 * 2
def baseEnd_4530802 : Nat := 775493058784095816679409

theorem tailTrace_4530802 : CollatzResearch.WordTrace tailWord_4530802 prefixEnd_4530802 775493058784095816679409 := by
  unfold tailWord_4530802
  simp only [CollatzResearch.WordTrace]
  refine ⟨41312981232921407055348665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110167949954457085480929773 41312981232921407055348665)
  ·
    refine ⟨30984735924691055291511499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41312981232921407055348665 30984735924691055291511499)
    ·
      refine ⟨46477103887036582937267249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30984735924691055291511499 46477103887036582937267249)
      ·
        refine ⟨34857827915277437202950437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46477103887036582937267249 34857827915277437202950437)
        ·
          refine ⟨6535842734114519475553207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34857827915277437202950437 6535842734114519475553207)
          ·
            refine ⟨9803764101171779213329811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6535842734114519475553207 9803764101171779213329811)
            ·
              refine ⟨14705646151757668819994717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9803764101171779213329811 14705646151757668819994717)
              ·
                refine ⟨5514617306909125807498019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14705646151757668819994717 5514617306909125807498019)
                ·
                  refine ⟨8271925960363688711247029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5514617306909125807498019 8271925960363688711247029)
                  ·
                    refine ⟨775493058784095816679409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8271925960363688711247029 775493058784095816679409)
                    ·
                      rfl

theorem cell23_4530802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_4530802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530802 prefixEnd_4530802 := by exact prefixLift 4530802
  have htrace : WordTrace (prefixWord ++ tailWord_4530802) baseStart_4530802 baseEnd_4530802 := by
    simpa [prefixWord, tailWord_4530802, baseEnd_4530802] using wordTrace_append hprefix tailTrace_4530802
  have hstable : (prefixWord ++ tailWord_4530802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530802).length < 2 ^ (prefixWord ++ tailWord_4530802).sum := by decide
  have hdescent : baseEnd_4530802 < baseStart_4530802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530815 : List Nat := [1, 1, 2, 2, 1, 1, 1, 8, 2, 4]
def baseStart_4530815 : Nat := 118140960795 + 4530815 * 2 ^ 59
def prefixEnd_4530815 : Nat := 4983230072969 + 3 ^ 40 * 4530815 * 2
def baseEnd_4530815 : Nat := 775495283866931966391889

theorem tailTrace_4530815 : CollatzResearch.WordTrace tailWord_4530815 prefixEnd_4530815 775495283866931966391889 := by
  unfold tailWord_4530815
  simp only [CollatzResearch.WordTrace]
  refine ⟨165252399080638531441617899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110168266053759020961078599 165252399080638531441617899)
  ·
    refine ⟨247878598620957797162426849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165252399080638531441617899 247878598620957797162426849)
    ·
      refine ⟨185908948965718347871820137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247878598620957797162426849 185908948965718347871820137)
      ·
        refine ⟨139431711724288760903865103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185908948965718347871820137 139431711724288760903865103)
        ·
          refine ⟨209147567586433141355797655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139431711724288760903865103 209147567586433141355797655)
          ·
            refine ⟨313721351379649712033696483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209147567586433141355797655 313721351379649712033696483)
            ·
              refine ⟨470582027069474568050544725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313721351379649712033696483 470582027069474568050544725)
              ·
                refine ⟨5514633129720405094342321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 470582027069474568050544725 5514633129720405094342321)
                ·
                  refine ⟨4135974847290303820756741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5514633129720405094342321 4135974847290303820756741)
                  ·
                    refine ⟨775495283866931966391889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4135974847290303820756741 775495283866931966391889)
                    ·
                      rfl

theorem cell23_4530815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 4].length) (baseStart_4530815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530815 prefixEnd_4530815 := by exact prefixLift 4530815
  have htrace : WordTrace (prefixWord ++ tailWord_4530815) baseStart_4530815 baseEnd_4530815 := by
    simpa [prefixWord, tailWord_4530815, baseEnd_4530815] using wordTrace_append hprefix tailTrace_4530815
  have hstable : (prefixWord ++ tailWord_4530815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530815).length < 2 ^ (prefixWord ++ tailWord_4530815).sum := by decide
  have hdescent : baseEnd_4530815 < baseStart_4530815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530845 : List Nat := [1, 4, 2, 1, 1, 1, 6, 7]
def baseStart_4530845 : Nat := 118140960795 + 4530845 * 2 ^ 59
def prefixEnd_4530845 : Nat := 4983230072969 + 3 ^ 40 * 4530845 * 2
def baseEnd_4530845 : Nat := 86166713185941880807427

theorem tailTrace_4530845 : CollatzResearch.WordTrace tailWord_4530845 prefixEnd_4530845 86166713185941880807427 := by
  unfold tailWord_4530845
  simp only [CollatzResearch.WordTrace]
  refine ⟨165253493270529846565209989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110168995513686564376806659 165253493270529846565209989)
  ·
    refine ⟨30985029988224346230976873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165253493270529846565209989 30985029988224346230976873)
    ·
      refine ⟨23238772491168259673232655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30985029988224346230976873 23238772491168259673232655)
      ·
        refine ⟨34858158736752389509848983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23238772491168259673232655 34858158736752389509848983)
        ·
          refine ⟨52287238105128584264773475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34858158736752389509848983 52287238105128584264773475)
          ·
            refine ⟨78430857157692876397160213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52287238105128584264773475 78430857157692876397160213)
            ·
              refine ⟨3676446429266853581116885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78430857157692876397160213 3676446429266853581116885)
              ·
                refine ⟨86166713185941880807427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3676446429266853581116885 86166713185941880807427)
                ·
                  rfl

theorem cell23_4530845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 7].length) (baseStart_4530845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530845 prefixEnd_4530845 := by exact prefixLift 4530845
  have htrace : WordTrace (prefixWord ++ tailWord_4530845) baseStart_4530845 baseEnd_4530845 := by
    simpa [prefixWord, tailWord_4530845, baseEnd_4530845] using wordTrace_append hprefix tailTrace_4530845
  have hstable : (prefixWord ++ tailWord_4530845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530845).length < 2 ^ (prefixWord ++ tailWord_4530845).sum := by decide
  have hdescent : baseEnd_4530845 < baseStart_4530845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
