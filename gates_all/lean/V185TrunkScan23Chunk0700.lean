import V185TrunkScan23Chunk0699

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4138787 : List Nat := [1, 1, 1, 4, 2, 1, 6, 1, 6]
def baseStart_4138787 : Nat := 118140960795 + 4138787 * 2 ^ 59
def prefixEnd_4138787 : Nat := 4983230072969 + 3 ^ 40 * 4138787 * 2
def baseEnd_4138787 : Nat := 236131895286667078947619

theorem tailTrace_4138787 : CollatzResearch.WordTrace tailWord_4138787 prefixEnd_4138787 236131895286667078947619 := by
  unfold tailWord_4138787
  simp only [CollatzResearch.WordTrace]
  refine ⟨150953963256889022389622615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100635975504592681593081743 150953963256889022389622615)
  ·
    refine ⟨226430944885333533584433923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150953963256889022389622615 226430944885333533584433923)
    ·
      refine ⟨339646417328000300376650885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226430944885333533584433923 339646417328000300376650885)
      ·
        refine ⟨63683703249000056320622041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339646417328000300376650885 63683703249000056320622041)
        ·
          refine ⟨47762777436750042240466531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63683703249000056320622041 47762777436750042240466531)
          ·
            refine ⟨71644166155125063360699797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47762777436750042240466531 71644166155125063360699797)
            ·
              refine ⟨3358320288521487345032803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71644166155125063360699797 3358320288521487345032803)
              ·
                refine ⟨5037480432782231017549205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3358320288521487345032803 5037480432782231017549205)
                ·
                  refine ⟨236131895286667078947619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5037480432782231017549205 236131895286667078947619)
                  ·
                    rfl

theorem cell23_4138787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 6].length) (baseStart_4138787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138787 prefixEnd_4138787 := by exact prefixLift 4138787
  have htrace : WordTrace (prefixWord ++ tailWord_4138787) baseStart_4138787 baseEnd_4138787 := by
    simpa [prefixWord, tailWord_4138787, baseEnd_4138787] using wordTrace_append hprefix tailTrace_4138787
  have hstable : (prefixWord ++ tailWord_4138787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138787).length < 2 ^ (prefixWord ++ tailWord_4138787).sum := by decide
  have hdescent : baseEnd_4138787 < baseStart_4138787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138824 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 2, 3, 2]
def baseStart_4138824 : Nat := 118140960795 + 4138824 * 2 ^ 59
def prefixEnd_4138824 : Nat := 4983230072969 + 3 ^ 40 * 4138824 * 2
def baseEnd_4138824 : Nat := 2125206056364220065765901

theorem tailTrace_4138824 : CollatzResearch.WordTrace tailWord_4138824 prefixEnd_4138824 2125206056364220065765901 := by
  unfold tailWord_4138824
  simp only [CollatzResearch.WordTrace]
  refine ⟨75477656378877488854359763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100636875171836651805813017 75477656378877488854359763)
  ·
    refine ⟨113216484568316233281539645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75477656378877488854359763 113216484568316233281539645)
    ·
      refine ⟨42456181713118587480577367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113216484568316233281539645 42456181713118587480577367)
      ·
        refine ⟨63684272569677881220866051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42456181713118587480577367 63684272569677881220866051)
        ·
          refine ⟨95526408854516821831299077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63684272569677881220866051 95526408854516821831299077)
          ·
            refine ⟨17911201660221904093368577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95526408854516821831299077 17911201660221904093368577)
            ·
              refine ⟨13433401245166428070026433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17911201660221904093368577 13433401245166428070026433)
              ·
                refine ⟨10075050933874821052519825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13433401245166428070026433 10075050933874821052519825)
                ·
                  refine ⟨7556288200406115789389869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10075050933874821052519825 7556288200406115789389869)
                  ·
                    refine ⟨2833608075152293421021201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7556288200406115789389869 2833608075152293421021201)
                    ·
                      refine ⟨2125206056364220065765901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2833608075152293421021201 2125206056364220065765901)
                      ·
                        rfl

theorem cell23_4138824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_4138824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138824 prefixEnd_4138824 := by exact prefixLift 4138824
  have htrace : WordTrace (prefixWord ++ tailWord_4138824) baseStart_4138824 baseEnd_4138824 := by
    simpa [prefixWord, tailWord_4138824, baseEnd_4138824] using wordTrace_append hprefix tailTrace_4138824
  have hstable : (prefixWord ++ tailWord_4138824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138824).length < 2 ^ (prefixWord ++ tailWord_4138824).sum := by decide
  have hdescent : baseEnd_4138824 < baseStart_4138824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138837 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_4138837 : Nat := 118140960795 + 4138837 * 2 ^ 59
def prefixEnd_4138837 : Nat := 4983230072969 + 3 ^ 40 * 4138837 * 2
def baseEnd_4138837 : Nat := 2125212731612728514903341

theorem tailTrace_4138837 : CollatzResearch.WordTrace tailWord_4138837 prefixEnd_4138837 2125212731612728514903341 := by
  unfold tailWord_4138837
  simp only [CollatzResearch.WordTrace]
  refine ⟨150955786906707880928942765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100637191271138587285961843 150955786906707880928942765)
  ·
    refine ⟨56608420090015455348353537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150955786906707880928942765 56608420090015455348353537)
    ·
      refine ⟨42456315067511591511265153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56608420090015455348353537 42456315067511591511265153)
      ·
        refine ⟨31842236300633693633448865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42456315067511591511265153 31842236300633693633448865)
        ·
          refine ⟨23881677225475270225086649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31842236300633693633448865 23881677225475270225086649)
          ·
            refine ⟨17911257919106452668814987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23881677225475270225086649 17911257919106452668814987)
            ·
              refine ⟨26866886878659679003222481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17911257919106452668814987 26866886878659679003222481)
              ·
                refine ⟨20150165158994759252416861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26866886878659679003222481 20150165158994759252416861)
                ·
                  refine ⟨7556311934623034719656323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20150165158994759252416861 7556311934623034719656323)
                  ·
                    refine ⟨11334467901934552079484485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7556311934623034719656323 11334467901934552079484485)
                    ·
                      refine ⟨2125212731612728514903341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11334467901934552079484485 2125212731612728514903341)
                      ·
                        rfl

theorem cell23_4138837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_4138837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138837 prefixEnd_4138837 := by exact prefixLift 4138837
  have htrace : WordTrace (prefixWord ++ tailWord_4138837) baseStart_4138837 baseEnd_4138837 := by
    simpa [prefixWord, tailWord_4138837, baseEnd_4138837] using wordTrace_append hprefix tailTrace_4138837
  have hstable : (prefixWord ++ tailWord_4138837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138837).length < 2 ^ (prefixWord ++ tailWord_4138837).sum := by decide
  have hdescent : baseEnd_4138837 < baseStart_4138837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138847 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 1, 6]
def baseStart_4138847 : Nat := 118140960795 + 4138847 * 2 ^ 59
def prefixEnd_4138847 : Nat := 4983230072969 + 3 ^ 40 * 4138847 * 2
def baseEnd_4138847 : Nat := 708405955473091158592765

theorem tailTrace_4138847 : CollatzResearch.WordTrace tailWord_4138847 prefixEnd_4138847 708405955473091158592765 := by
  unfold tailWord_4138847
  simp only [CollatzResearch.WordTrace]
  refine ⟨150956151636671652636806795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100637434424447768424537863 150956151636671652636806795)
  ·
    refine ⟨226434227455007478955210193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150956151636671652636806795 226434227455007478955210193)
    ·
      refine ⟨169825670591255609216407645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226434227455007478955210193 169825670591255609216407645)
      ·
        refine ⟨63684626471720853456152867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169825670591255609216407645 63684626471720853456152867)
        ·
          refine ⟨95526939707581280184229301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63684626471720853456152867 95526939707581280184229301)
          ·
            refine ⟨8955650597585745017271497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95526939707581280184229301 8955650597585745017271497)
            ·
              refine ⟨6716737948189308762953623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8955650597585745017271497 6716737948189308762953623)
              ·
                refine ⟨10075106922283963144430435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6716737948189308762953623 10075106922283963144430435)
                ·
                  refine ⟨15112660383425944716645653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10075106922283963144430435 15112660383425944716645653)
                  ·
                    refine ⟨708405955473091158592765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15112660383425944716645653 708405955473091158592765)
                    ·
                      rfl

theorem cell23_4138847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 6].length) (baseStart_4138847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138847 prefixEnd_4138847 := by exact prefixLift 4138847
  have htrace : WordTrace (prefixWord ++ tailWord_4138847) baseStart_4138847 baseEnd_4138847 := by
    simpa [prefixWord, tailWord_4138847, baseEnd_4138847] using wordTrace_append hprefix tailTrace_4138847
  have hstable : (prefixWord ++ tailWord_4138847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138847).length < 2 ^ (prefixWord ++ tailWord_4138847).sum := by decide
  have hdescent : baseEnd_4138847 < baseStart_4138847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138881 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 4, 4]
def baseStart_4138881 : Nat := 118140960795 + 4138881 * 2 ^ 59
def prefixEnd_4138881 : Nat := 4983230072969 + 3 ^ 40 * 4138881 * 2
def baseEnd_4138881 : Nat := 708411774920508780917713

theorem tailTrace_4138881 : CollatzResearch.WordTrace tailWord_4138881 prefixEnd_4138881 708411774920508780917713 := by
  unfold tailWord_4138881
  simp only [CollatzResearch.WordTrace]
  refine ⟨150957391718548476443544497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100638261145698984295696331 150957391718548476443544497)
  ·
    refine ⟨113218043788911357332658373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150957391718548476443544497 113218043788911357332658373)
    ·
      refine ⟨21228383210420879499873445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113218043788911357332658373 21228383210420879499873445)
      ·
        refine ⟨3980321851953914906226271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21228383210420879499873445 3980321851953914906226271)
        ·
          refine ⟨5970482777930872359339407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3980321851953914906226271 5970482777930872359339407)
          ·
            refine ⟨8955724166896308539009111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5970482777930872359339407 8955724166896308539009111)
            ·
              refine ⟨13433586250344462808513667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8955724166896308539009111 13433586250344462808513667)
              ·
                refine ⟨20150379375516694212770501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13433586250344462808513667 20150379375516694212770501)
                ·
                  refine ⟨3778196132909380164894469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20150379375516694212770501 3778196132909380164894469)
                  ·
                    refine ⟨708411774920508780917713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3778196132909380164894469 708411774920508780917713)
                    ·
                      rfl

theorem cell23_4138881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_4138881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138881 prefixEnd_4138881 := by exact prefixLift 4138881
  have htrace : WordTrace (prefixWord ++ tailWord_4138881) baseStart_4138881 baseEnd_4138881 := by
    simpa [prefixWord, tailWord_4138881, baseEnd_4138881] using wordTrace_append hprefix tailTrace_4138881
  have hstable : (prefixWord ++ tailWord_4138881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138881).length < 2 ^ (prefixWord ++ tailWord_4138881).sum := by decide
  have hdescent : baseEnd_4138881 < baseStart_4138881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138888 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 3, 2, 2]
def baseStart_4138888 : Nat := 118140960795 + 4138888 * 2 ^ 59
def prefixEnd_4138888 : Nat := 4983230072969 + 3 ^ 40 * 4138888 * 2
def baseEnd_4138888 : Nat := 2125238919126107815365607

theorem tailTrace_4138888 : CollatzResearch.WordTrace tailWord_4138888 prefixEnd_4138888 2125238919126107815365607 := by
  unfold tailWord_4138888
  simp only [CollatzResearch.WordTrace]
  refine ⟨75478823514761558319524659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100638431353015411092699545 75478823514761558319524659)
  ·
    refine ⟨113218235272142337479286989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75478823514761558319524659 113218235272142337479286989)
    ·
      refine ⟨42456838227053376554732621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113218235272142337479286989 42456838227053376554732621)
      ·
        refine ⟨15921314335145016208024733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42456838227053376554732621 15921314335145016208024733)
        ·
          refine ⟨5970492875679381078009275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15921314335145016208024733 5970492875679381078009275)
          ·
            refine ⟨8955739313519071617013913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5970492875679381078009275 8955739313519071617013913)
            ·
              refine ⟨6716804485139303712760435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8955739313519071617013913 6716804485139303712760435)
              ·
                refine ⟨10075206727708955569140653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6716804485139303712760435 10075206727708955569140653)
                ·
                  refine ⟨3778202522890858338427745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10075206727708955569140653 3778202522890858338427745)
                  ·
                    refine ⟨2833651892168143753820809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3778202522890858338427745 2833651892168143753820809)
                    ·
                      refine ⟨2125238919126107815365607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2833651892168143753820809 2125238919126107815365607)
                      ·
                        rfl

theorem cell23_4138888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_4138888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138888 prefixEnd_4138888 := by exact prefixLift 4138888
  have htrace : WordTrace (prefixWord ++ tailWord_4138888) baseStart_4138888 baseEnd_4138888 := by
    simpa [prefixWord, tailWord_4138888, baseEnd_4138888] using wordTrace_append hprefix tailTrace_4138888
  have hstable : (prefixWord ++ tailWord_4138888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138888).length < 2 ^ (prefixWord ++ tailWord_4138888).sum := by decide
  have hdescent : baseEnd_4138888 < baseStart_4138888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138898 : List Nat := [3, 2, 3, 2, 1, 2, 3, 1, 2, 4]
def baseStart_4138898 : Nat := 118140960795 + 4138898 * 2 ^ 59
def prefixEnd_4138898 : Nat := 4983230072969 + 3 ^ 40 * 4138898 * 2
def baseEnd_4138898 : Nat := 708414684644217592080187

theorem tailTrace_4138898 : CollatzResearch.WordTrace tailWord_4138898 prefixEnd_4138898 708414684644217592080187 := by
  unfold tailWord_4138898
  simp only [CollatzResearch.WordTrace]
  refine ⟨37739502939871722086728337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100638674506324592231275565 37739502939871722086728337)
  ·
    refine ⟨28304627204903791565046253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37739502939871722086728337 28304627204903791565046253)
    ·
      refine ⟨10614235201838921836892345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28304627204903791565046253 10614235201838921836892345)
      ·
        refine ⟨7960676401379191377669259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10614235201838921836892345 7960676401379191377669259)
        ·
          refine ⟨11941014602068787066503889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7960676401379191377669259 11941014602068787066503889)
          ·
            refine ⟨8955760951551590299877917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11941014602068787066503889 8955760951551590299877917)
            ·
              refine ⟨3358410356831846362454219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8955760951551590299877917 3358410356831846362454219)
              ·
                refine ⟨5037615535247769543681329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3358410356831846362454219 5037615535247769543681329)
                ·
                  refine ⟨3778211651435827157760997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5037615535247769543681329 3778211651435827157760997)
                  ·
                    refine ⟨708414684644217592080187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3778211651435827157760997 708414684644217592080187)
                    ·
                      rfl

theorem cell23_4138898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_4138898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138898 prefixEnd_4138898 := by exact prefixLift 4138898
  have htrace : WordTrace (prefixWord ++ tailWord_4138898) baseStart_4138898 baseEnd_4138898 := by
    simpa [prefixWord, tailWord_4138898, baseEnd_4138898] using wordTrace_append hprefix tailTrace_4138898
  have hstable : (prefixWord ++ tailWord_4138898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138898).length < 2 ^ (prefixWord ++ tailWord_4138898).sum := by decide
  have hdescent : baseEnd_4138898 < baseStart_4138898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138911 : List Nat := [1, 1, 2, 5, 4, 1, 2, 7]
def baseStart_4138911 : Nat := 118140960795 + 4138911 * 2 ^ 59
def prefixEnd_4138911 : Nat := 4983230072969 + 3 ^ 40 * 4138911 * 2
def baseEnd_4138911 : Nat := 78712989969672637976963

theorem tailTrace_4138911 : CollatzResearch.WordTrace tailWord_4138911 prefixEnd_4138911 78712989969672637976963 := by
  unfold tailWord_4138911
  simp only [CollatzResearch.WordTrace]
  refine ⟨150958485908439791567136587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100638990605626527711424391 150958485908439791567136587)
  ·
    refine ⟨226437728862659687350704881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150958485908439791567136587 226437728862659687350704881)
    ·
      refine ⟨169828296646994765513028661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226437728862659687350704881 169828296646994765513028661)
      ·
        refine ⟨15921402810655759266846437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169828296646994765513028661 15921402810655759266846437)
        ·
          refine ⟨2985263026997954862533707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15921402810655759266846437 2985263026997954862533707)
          ·
            refine ⟨4477894540496932293800561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2985263026997954862533707 4477894540496932293800561)
            ·
              refine ⟨3358420905372699220350421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4477894540496932293800561 3358420905372699220350421)
              ·
                refine ⟨78712989969672637976963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3358420905372699220350421 78712989969672637976963)
                ·
                  rfl

theorem cell23_4138911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 7].length) (baseStart_4138911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138911 prefixEnd_4138911 := by exact prefixLift 4138911
  have htrace : WordTrace (prefixWord ++ tailWord_4138911) baseStart_4138911 baseEnd_4138911 := by
    simpa [prefixWord, tailWord_4138911, baseEnd_4138911] using wordTrace_append hprefix tailTrace_4138911
  have hstable : (prefixWord ++ tailWord_4138911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138911).length < 2 ^ (prefixWord ++ tailWord_4138911).sum := by decide
  have hdescent : baseEnd_4138911 < baseStart_4138911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138984 : List Nat := [2, 1, 4, 1, 1, 1, 1, 7, 5]
def baseStart_4138984 : Nat := 118140960795 + 4138984 * 2 ^ 59
def prefixEnd_4138984 : Nat := 4983230072969 + 3 ^ 40 * 4138984 * 2
def baseEnd_4138984 : Nat := 236143134807659937751685

theorem tailTrace_4138984 : CollatzResearch.WordTrace tailWord_4138984 prefixEnd_4138984 236143134807659937751685 := by
  unfold tailWord_4138984
  simp only [CollatzResearch.WordTrace]
  refine ⟨75480574218587662517272003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100640765624783550023029337 75480574218587662517272003)
  ·
    refine ⟨113220861327881493775908005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75480574218587662517272003 113220861327881493775908005)
    ·
      refine ⟨21228911498977780082982751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113220861327881493775908005 21228911498977780082982751)
      ·
        refine ⟨31843367248466670124474127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21228911498977780082982751 31843367248466670124474127)
        ·
          refine ⟨47765050872700005186711191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31843367248466670124474127 47765050872700005186711191)
          ·
            refine ⟨71647576309050007780066787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47765050872700005186711191 71647576309050007780066787)
            ·
              refine ⟨107471364463575011670100181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71647576309050007780066787 107471364463575011670100181)
              ·
                refine ⟨2518860104615039336017973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 107471364463575011670100181 2518860104615039336017973)
                ·
                  refine ⟨236143134807659937751685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2518860104615039336017973 236143134807659937751685)
                  ·
                    rfl

theorem cell23_4138984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 5].length) (baseStart_4138984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4138984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4138984 prefixEnd_4138984 := by exact prefixLift 4138984
  have htrace : WordTrace (prefixWord ++ tailWord_4138984) baseStart_4138984 baseEnd_4138984 := by
    simpa [prefixWord, tailWord_4138984, baseEnd_4138984] using wordTrace_append hprefix tailTrace_4138984
  have hstable : (prefixWord ++ tailWord_4138984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138984).length < 2 ^ (prefixWord ++ tailWord_4138984).sum := by decide
  have hdescent : baseEnd_4138984 < baseStart_4138984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139001 : List Nat := [1, 2, 1, 3, 1, 4, 4, 2, 5]
def baseStart_4139001 : Nat := 118140960795 + 4139001 * 2 ^ 59
def prefixEnd_4139001 : Nat := 4983230072969 + 3 ^ 40 * 4139001 * 2
def baseEnd_4139001 : Nat := 236144104715562874805843

theorem tailTrace_4139001 : CollatzResearch.WordTrace tailWord_4139001 prefixEnd_4139001 236144104715562874805843 := by
  unfold tailWord_4139001
  simp only [CollatzResearch.WordTrace]
  refine ⟨150961768478113736937912857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100641178985409157958608571 150961768478113736937912857)
  ·
    refine ⟨113221326358585302703434643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150961768478113736937912857 113221326358585302703434643)
    ·
      refine ⟨169831989537877954055151965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113221326358585302703434643 169831989537877954055151965)
      ·
        refine ⟨63686996076704232770681987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169831989537877954055151965 63686996076704232770681987)
        ·
          refine ⟨95530494115056349156022981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63686996076704232770681987 95530494115056349156022981)
          ·
            refine ⟨17911967646573065466754309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95530494115056349156022981 17911967646573065466754309)
            ·
              refine ⟨3358493933732449775016433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17911967646573065466754309 3358493933732449775016433)
              ·
                refine ⟨2518870450299337331262325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3358493933732449775016433 2518870450299337331262325)
                ·
                  refine ⟨236144104715562874805843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2518870450299337331262325 236144104715562874805843)
                  ·
                    rfl

theorem cell23_4139001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 5].length) (baseStart_4139001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139001 prefixEnd_4139001 := by exact prefixLift 4139001
  have htrace : WordTrace (prefixWord ++ tailWord_4139001) baseStart_4139001 baseEnd_4139001 := by
    simpa [prefixWord, tailWord_4139001, baseEnd_4139001] using wordTrace_append hprefix tailTrace_4139001
  have hstable : (prefixWord ++ tailWord_4139001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139001).length < 2 ^ (prefixWord ++ tailWord_4139001).sum := by decide
  have hdescent : baseEnd_4139001 < baseStart_4139001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139004 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 1, 7, 2]
def baseStart_4139004 : Nat := 118140960795 + 4139004 * 2 ^ 59
def prefixEnd_4139004 : Nat := 4983230072969 + 3 ^ 40 * 4139004 * 2
def baseEnd_4139004 : Nat := 2125298482882029361515073

theorem tailTrace_4139004 : CollatzResearch.WordTrace tailWord_4139004 prefixEnd_4139004 2125298482882029361515073 := by
  unfold tailWord_4139004
  simp only [CollatzResearch.WordTrace]
  refine ⟨75480938948551434225136033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100641251931401912300181377 75480938948551434225136033)
  ·
    refine ⟨56610704211413575668852025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75480938948551434225136033 56610704211413575668852025)
    ·
      refine ⟨42458028158560181751639019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56610704211413575668852025 42458028158560181751639019)
      ·
        refine ⟨63687042237840272627458529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42458028158560181751639019 63687042237840272627458529)
        ·
          refine ⟨47765281678380204470593897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63687042237840272627458529 47765281678380204470593897)
          ·
            refine ⟨35823961258785153352945423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47765281678380204470593897 35823961258785153352945423)
            ·
              refine ⟨53735941888177730029418135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35823961258785153352945423 53735941888177730029418135)
              ·
                refine ⟨80603912832266595044127203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53735941888177730029418135 80603912832266595044127203)
                ·
                  refine ⟨120905869248399892566190805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80603912832266595044127203 120905869248399892566190805)
                  ·
                    refine ⟨2833731310509372482020097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 120905869248399892566190805 2833731310509372482020097)
                    ·
                      refine ⟨2125298482882029361515073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2833731310509372482020097 2125298482882029361515073)
                      ·
                        rfl

theorem cell23_4139004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_4139004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139004 prefixEnd_4139004 := by exact prefixLift 4139004
  have htrace : WordTrace (prefixWord ++ tailWord_4139004) baseStart_4139004 baseEnd_4139004 := by
    simpa [prefixWord, tailWord_4139004, baseEnd_4139004] using wordTrace_append hprefix tailTrace_4139004
  have hstable : (prefixWord ++ tailWord_4139004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139004).length < 2 ^ (prefixWord ++ tailWord_4139004).sum := by decide
  have hdescent : baseEnd_4139004 < baseStart_4139004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139034 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4]
def baseStart_4139034 : Nat := 118140960795 + 4139034 * 2 ^ 59
def prefixEnd_4139034 : Nat := 4983230072969 + 3 ^ 40 * 4139034 * 2
def baseEnd_4139034 : Nat := 2125313887301664244139935

theorem tailTrace_4139034 : CollatzResearch.WordTrace tailWord_4139034 prefixEnd_4139034 2125313887301664244139935 := by
  unfold tailWord_4139034
  simp only [CollatzResearch.WordTrace]
  refine ⟨37740743021748545893466039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100641981391329455715909437 37740743021748545893466039)
  ·
    refine ⟨56611114532622818840199059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37740743021748545893466039 56611114532622818840199059)
    ·
      refine ⟨84916671798934228260298589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56611114532622818840199059 84916671798934228260298589)
      ·
        refine ⟨31843751924600335597611971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84916671798934228260298589 31843751924600335597611971)
        ·
          refine ⟨47765627886900503396417957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31843751924600335597611971 47765627886900503396417957)
          ·
            refine ⟨8956055228793844386828367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47765627886900503396417957 8956055228793844386828367)
            ·
              refine ⟨13434082843190766580242551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8956055228793844386828367 13434082843190766580242551)
              ·
                refine ⟨20151124264786149870363827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13434082843190766580242551 20151124264786149870363827)
                ·
                  refine ⟨30226686397179224805545741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20151124264786149870363827 30226686397179224805545741)
                  ·
                    refine ⟨11335007398942209302079653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30226686397179224805545741 11335007398942209302079653)
                    ·
                      refine ⟨2125313887301664244139935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11335007398942209302079653 2125313887301664244139935)
                      ·
                        rfl

theorem cell23_4139034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_4139034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139034 prefixEnd_4139034 := by exact prefixLift 4139034
  have htrace : WordTrace (prefixWord ++ tailWord_4139034) baseStart_4139034 baseEnd_4139034 := by
    simpa [prefixWord, tailWord_4139034, baseEnd_4139034] using wordTrace_append hprefix tailTrace_4139034
  have hstable : (prefixWord ++ tailWord_4139034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139034).length < 2 ^ (prefixWord ++ tailWord_4139034).sum := by decide
  have hdescent : baseEnd_4139034 < baseStart_4139034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139077 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 3, 2, 6]
def baseStart_4139077 : Nat := 118140960795 + 4139077 * 2 ^ 59
def prefixEnd_4139077 : Nat := 4983230072969 + 3 ^ 40 * 4139077 * 2
def baseEnd_4139077 : Nat := 2125335966969807575902237

theorem tailTrace_4139077 : CollatzResearch.WordTrace tailWord_4139077 prefixEnd_4139077 2125335966969807575902237 := by
  unfold tailWord_4139077
  simp only [CollatzResearch.WordTrace]
  refine ⟨150964540425838401917679485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100643026950558934611786323 150964540425838401917679485)
  ·
    refine ⟨56611702659689400719129807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150964540425838401917679485 56611702659689400719129807)
    ·
      refine ⟨84917553989534101078694711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56611702659689400719129807 84917553989534101078694711)
      ·
        refine ⟨127376330984301151618042067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84917553989534101078694711 127376330984301151618042067)
        ·
          refine ⟨191064496476451727427063101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127376330984301151618042067 191064496476451727427063101)
          ·
            refine ⟨71649186178669397785148663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191064496476451727427063101 71649186178669397785148663)
            ·
              refine ⟨107473779268004096677722995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71649186178669397785148663 107473779268004096677722995)
              ·
                refine ⟨161210668902006145016584493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107473779268004096677722995 161210668902006145016584493)
                ·
                  refine ⟨60454000838252304381219185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161210668902006145016584493 60454000838252304381219185)
                  ·
                    refine ⟨45340500628689228285914389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60454000838252304381219185 45340500628689228285914389)
                    ·
                      refine ⟨2125335966969807575902237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45340500628689228285914389 2125335966969807575902237)
                      ·
                        rfl

theorem cell23_4139077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_4139077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139077 prefixEnd_4139077 := by exact prefixLift 4139077
  have htrace : WordTrace (prefixWord ++ tailWord_4139077) baseStart_4139077 baseEnd_4139077 := by
    simpa [prefixWord, tailWord_4139077, baseEnd_4139077] using wordTrace_append hprefix tailTrace_4139077
  have hstable : (prefixWord ++ tailWord_4139077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139077).length < 2 ^ (prefixWord ++ tailWord_4139077).sum := by decide
  have hdescent : baseEnd_4139077 < baseStart_4139077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139078 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_4139078 : Nat := 118140960795 + 4139078 * 2 ^ 59
def prefixEnd_4139078 : Nat := 4983230072969 + 3 ^ 40 * 4139078 * 2
def baseEnd_4139078 : Nat := 708445493483487357329911

theorem tailTrace_4139078 : CollatzResearch.WordTrace tailWord_4139078 prefixEnd_4139078 708445493483487357329911 := by
  unfold tailWord_4139078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4717643028088586846514559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100643051265889852725643925 4717643028088586846514559)
  ·
    refine ⟨7076464542132880269771839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4717643028088586846514559 7076464542132880269771839)
    ·
      refine ⟨10614696813199320404657759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7076464542132880269771839 10614696813199320404657759)
      ·
        refine ⟨15922045219798980606986639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10614696813199320404657759 15922045219798980606986639)
        ·
          refine ⟨23883067829698470910479959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15922045219798980606986639 23883067829698470910479959)
          ·
            refine ⟨35824601744547706365719939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23883067829698470910479959 35824601744547706365719939)
            ·
              refine ⟨53736902616821559548579909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35824601744547706365719939 53736902616821559548579909)
              ·
                refine ⟨10075669240654042415358733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53736902616821559548579909 10075669240654042415358733)
                ·
                  refine ⟨3778375965245265905759525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10075669240654042415358733 3778375965245265905759525)
                  ·
                    refine ⟨708445493483487357329911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3778375965245265905759525 708445493483487357329911)
                    ·
                      rfl

theorem cell23_4139078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_4139078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139078 prefixEnd_4139078 := by exact prefixLift 4139078
  have htrace : WordTrace (prefixWord ++ tailWord_4139078) baseStart_4139078 baseEnd_4139078 := by
    simpa [prefixWord, tailWord_4139078, baseEnd_4139078] using wordTrace_append hprefix tailTrace_4139078
  have hstable : (prefixWord ++ tailWord_4139078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139078).length < 2 ^ (prefixWord ++ tailWord_4139078).sum := by decide
  have hdescent : baseEnd_4139078 < baseStart_4139078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139141 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 3, 1, 4]
def baseStart_4139141 : Nat := 118140960795 + 4139141 * 2 ^ 59
def prefixEnd_4139141 : Nat := 4983230072969 + 3 ^ 40 * 4139141 * 2
def baseEnd_4139141 : Nat := 2125368829731695325501943

theorem tailTrace_4139141 : CollatzResearch.WordTrace tailWord_4139141 prefixEnd_4139141 2125368829731695325501943 := by
  unfold tailWord_4139141
  simp only [CollatzResearch.WordTrace]
  refine ⟨150966874697606540848009277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100644583131737693898672851 150966874697606540848009277)
  ·
    refine ⟨56612578011602452818003479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150966874697606540848009277 56612578011602452818003479)
    ·
      refine ⟨84918867017403679227005219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56612578011602452818003479 84918867017403679227005219)
      ·
        refine ⟨127378300526105518840507829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84918867017403679227005219 127378300526105518840507829)
        ·
          refine ⟨11941715674322392391297609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127378300526105518840507829 11941715674322392391297609)
          ·
            refine ⟨8956286755741794293473207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11941715674322392391297609 8956286755741794293473207)
            ·
              refine ⟨13434430133612691440209811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8956286755741794293473207 13434430133612691440209811)
              ·
                refine ⟨20151645200419037160314717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13434430133612691440209811 20151645200419037160314717)
                ·
                  refine ⟨7556866950157138935118019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20151645200419037160314717 7556866950157138935118019)
                  ·
                    refine ⟨11335300425235708402677029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7556866950157138935118019 11335300425235708402677029)
                    ·
                      refine ⟨2125368829731695325501943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11335300425235708402677029 2125368829731695325501943)
                      ·
                        rfl

theorem cell23_4139141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_4139141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139141 prefixEnd_4139141 := by exact prefixLift 4139141
  have htrace : WordTrace (prefixWord ++ tailWord_4139141) baseStart_4139141 baseEnd_4139141 := by
    simpa [prefixWord, tailWord_4139141, baseEnd_4139141] using wordTrace_append hprefix tailTrace_4139141
  have hstable : (prefixWord ++ tailWord_4139141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139141).length < 2 ^ (prefixWord ++ tailWord_4139141).sum := by decide
  have hdescent : baseEnd_4139141 < baseStart_4139141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139161 : List Nat := [1, 2, 1, 2, 1, 2, 1, 7, 1, 2, 3]
def baseStart_4139161 : Nat := 118140960795 + 4139161 * 2 ^ 59
def prefixEnd_4139161 : Nat := 4983230072969 + 3 ^ 40 * 4139161 * 2
def baseEnd_4139161 : Nat := 2125379099344785247251851

theorem tailTrace_4139161 : CollatzResearch.WordTrace tailWord_4139161 prefixEnd_4139161 2125379099344785247251851 := by
  unfold tailWord_4139161
  simp only [CollatzResearch.WordTrace]
  refine ⟨150967604157534084263737337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100645069438356056175824891 150967604157534084263737337)
  ·
    refine ⟨113225703118150563197803003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150967604157534084263737337 113225703118150563197803003)
    ·
      refine ⟨169838554677225844796704505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113225703118150563197803003 169838554677225844796704505)
      ·
        refine ⟨127378916007919383597528379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169838554677225844796704505 127378916007919383597528379)
        ·
          refine ⟨191068374011879075396292569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127378916007919383597528379 191068374011879075396292569)
          ·
            refine ⟨143301280508909306547219427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191068374011879075396292569 143301280508909306547219427)
            ·
              refine ⟨214951920763363959820829141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143301280508909306547219427 214951920763363959820829141)
              ·
                refine ⟨5037935642891342808300683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 214951920763363959820829141 5037935642891342808300683)
                ·
                  refine ⟨7556903464337014212451025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5037935642891342808300683 7556903464337014212451025)
                  ·
                    refine ⟨5667677598252760659338269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7556903464337014212451025 5667677598252760659338269)
                    ·
                      refine ⟨2125379099344785247251851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5667677598252760659338269 2125379099344785247251851)
                      ·
                        rfl

theorem cell23_4139161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_4139161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139161 prefixEnd_4139161 := by exact prefixLift 4139161
  have htrace : WordTrace (prefixWord ++ tailWord_4139161) baseStart_4139161 baseEnd_4139161 := by
    simpa [prefixWord, tailWord_4139161, baseEnd_4139161] using wordTrace_append hprefix tailTrace_4139161
  have hstable : (prefixWord ++ tailWord_4139161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139161).length < 2 ^ (prefixWord ++ tailWord_4139161).sum := by decide
  have hdescent : baseEnd_4139161 < baseStart_4139161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139168 : List Nat := [2, 1, 1, 4, 2, 3, 2, 2, 2, 4]
def baseStart_4139168 : Nat := 118140960795 + 4139168 * 2 ^ 59
def prefixEnd_4139168 : Nat := 4983230072969 + 3 ^ 40 * 4139168 * 2
def baseEnd_4139168 : Nat := 708460897903122239954773

theorem tailTrace_4139168 : CollatzResearch.WordTrace tailWord_4139168 prefixEnd_4139168 708460897903122239954773 := by
  unfold tailWord_4139168
  simp only [CollatzResearch.WordTrace]
  refine ⟨75483929734254362229621079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100645239645672482972828105 75483929734254362229621079)
  ·
    refine ⟨113225894601381543344431619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75483929734254362229621079 113225894601381543344431619)
    ·
      refine ⟨169838841902072315016647429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113225894601381543344431619 169838841902072315016647429)
      ·
        refine ⟨31844782856638559065621393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169838841902072315016647429 31844782856638559065621393)
        ·
          refine ⟨23883587142478919299216045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31844782856638559065621393 23883587142478919299216045)
          ·
            refine ⟨8956345178429594737206017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23883587142478919299216045 8956345178429594737206017)
            ·
              refine ⟨6717258883822196052904513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8956345178429594737206017 6717258883822196052904513)
              ·
                refine ⟨5037944162866647039678385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6717258883822196052904513 5037944162866647039678385)
                ·
                  refine ⟨3778458122149985279758789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5037944162866647039678385 3778458122149985279758789)
                  ·
                    refine ⟨708460897903122239954773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3778458122149985279758789 708460897903122239954773)
                    ·
                      rfl

theorem cell23_4139168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 2, 4].length) (baseStart_4139168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139168 prefixEnd_4139168 := by exact prefixLift 4139168
  have htrace : WordTrace (prefixWord ++ tailWord_4139168) baseStart_4139168 baseEnd_4139168 := by
    simpa [prefixWord, tailWord_4139168, baseEnd_4139168] using wordTrace_append hprefix tailTrace_4139168
  have hstable : (prefixWord ++ tailWord_4139168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139168).length < 2 ^ (prefixWord ++ tailWord_4139168).sum := by decide
  have hdescent : baseEnd_4139168 < baseStart_4139168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139181 : List Nat := [1, 5, 2, 1, 2, 1, 3, 8]
def baseStart_4139181 : Nat := 118140960795 + 4139181 * 2 ^ 59
def prefixEnd_4139181 : Nat := 4983230072969 + 3 ^ 40 * 4139181 * 2
def baseEnd_4139181 : Nat := 78718124776217598851917

theorem tailTrace_4139181 : CollatzResearch.WordTrace tailWord_4139181 prefixEnd_4139181 78718124776217598851917 := by
  unfold tailWord_4139181
  simp only [CollatzResearch.WordTrace]
  refine ⟨150968333617461627679465397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100645555744974418452976931 150968333617461627679465397)
  ·
    refine ⟨14153281276637027594949881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150968333617461627679465397 14153281276637027594949881)
    ·
      refine ⟨10614960957477770696212411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14153281276637027594949881 10614960957477770696212411)
      ·
        refine ⟨15922441436216656044318617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10614960957477770696212411 15922441436216656044318617)
        ·
          refine ⟨11941831077162492033238963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15922441436216656044318617 11941831077162492033238963)
          ·
            refine ⟨17912746615743738049858445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11941831077162492033238963 17912746615743738049858445)
            ·
              refine ⟨6717279980903901768696917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17912746615743738049858445 6717279980903901768696917)
              ·
                refine ⟨78718124776217598851917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6717279980903901768696917 78718124776217598851917)
                ·
                  rfl

theorem cell23_4139181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 8].length) (baseStart_4139181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139181 prefixEnd_4139181 := by exact prefixLift 4139181
  have htrace : WordTrace (prefixWord ++ tailWord_4139181) baseStart_4139181 baseEnd_4139181 := by
    simpa [prefixWord, tailWord_4139181, baseEnd_4139181] using wordTrace_append hprefix tailTrace_4139181
  have hstable : (prefixWord ++ tailWord_4139181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139181).length < 2 ^ (prefixWord ++ tailWord_4139181).sum := by decide
  have hdescent : baseEnd_4139181 < baseStart_4139181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139191 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 3]
def baseStart_4139191 : Nat := 118140960795 + 4139191 * 2 ^ 59
def prefixEnd_4139191 : Nat := 4983230072969 + 3 ^ 40 * 4139191 * 2
def baseEnd_4139191 : Nat := 2125394503764420129876713

theorem tailTrace_4139191 : CollatzResearch.WordTrace tailWord_4139191 prefixEnd_4139191 2125394503764420129876713 := by
  unfold tailWord_4139191
  simp only [CollatzResearch.WordTrace]
  refine ⟨150968698347425399387329427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100645798898283599591552951 150968698347425399387329427)
  ·
    refine ⟨226453047521138099080994141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150968698347425399387329427 226453047521138099080994141)
    ·
      refine ⟨84919892820426787155372803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226453047521138099080994141 84919892820426787155372803)
      ·
        refine ⟨127379839230640180733059205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84919892820426787155372803 127379839230640180733059205)
        ·
          refine ⟨23883719855745033887448601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127379839230640180733059205 23883719855745033887448601)
          ·
            refine ⟨17912789891808775415586451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23883719855745033887448601 17912789891808775415586451)
            ·
              refine ⟨26869184837713163123379677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17912789891808775415586451 26869184837713163123379677)
              ·
                refine ⟨10075944314142436171267379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26869184837713163123379677 10075944314142436171267379)
                ·
                  refine ⟨15113916471213654256901069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10075944314142436171267379 15113916471213654256901069)
                  ·
                    refine ⟨5667718676705120346337901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15113916471213654256901069 5667718676705120346337901)
                    ·
                      refine ⟨2125394503764420129876713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5667718676705120346337901 2125394503764420129876713)
                      ·
                        rfl

theorem cell23_4139191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_4139191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139191 prefixEnd_4139191 := by exact prefixLift 4139191
  have htrace : WordTrace (prefixWord ++ tailWord_4139191) baseStart_4139191 baseEnd_4139191 := by
    simpa [prefixWord, tailWord_4139191, baseEnd_4139191] using wordTrace_append hprefix tailTrace_4139191
  have hstable : (prefixWord ++ tailWord_4139191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139191).length < 2 ^ (prefixWord ++ tailWord_4139191).sum := by decide
  have hdescent : baseEnd_4139191 < baseStart_4139191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139198 : List Nat := [4, 2, 1, 1, 4, 1, 3, 7]
def baseStart_4139198 : Nat := 118140960795 + 4139198 * 2 ^ 59
def prefixEnd_4139198 : Nat := 4983230072969 + 3 ^ 40 * 4139198 * 2
def baseEnd_4139198 : Nat := 78718448078851911203303

theorem tailTrace_4139198 : CollatzResearch.WordTrace tailWord_4139198 prefixEnd_4139198 78718448078851911203303 := by
  unfold tailWord_4139198
  simp only [CollatzResearch.WordTrace]
  refine ⟨18871119207300004947854281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100645969105600026388556165 18871119207300004947854281)
  ·
    refine ⟨14153339405475003710890711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18871119207300004947854281 14153339405475003710890711)
    ·
      refine ⟨21230009108212505566336067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14153339405475003710890711 21230009108212505566336067)
      ·
        refine ⟨31845013662318758349504101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21230009108212505566336067 31845013662318758349504101)
        ·
          refine ⟨5970940061684767190532019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31845013662318758349504101 5970940061684767190532019)
          ·
            refine ⟨8956410092527150785798029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5970940061684767190532019 8956410092527150785798029)
            ·
              refine ⟨3358653784697681544674261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8956410092527150785798029 3358653784697681544674261)
              ·
                refine ⟨78718448078851911203303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3358653784697681544674261 78718448078851911203303)
                ·
                  rfl

theorem cell23_4139198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 7].length) (baseStart_4139198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139198 prefixEnd_4139198 := by exact prefixLift 4139198
  have htrace : WordTrace (prefixWord ++ tailWord_4139198) baseStart_4139198 baseEnd_4139198 := by
    simpa [prefixWord, tailWord_4139198, baseEnd_4139198] using wordTrace_append hprefix tailTrace_4139198
  have hstable : (prefixWord ++ tailWord_4139198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139198).length < 2 ^ (prefixWord ++ tailWord_4139198).sum := by decide
  have hdescent : baseEnd_4139198 < baseStart_4139198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139268 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_4139268 : Nat := 118140960795 + 4139268 * 2 ^ 59
def prefixEnd_4139268 : Nat := 4983230072969 + 3 ^ 40 * 4139268 * 2
def baseEnd_4139268 : Nat := 2125434041774816328613859

theorem tailTrace_4139268 : CollatzResearch.WordTrace tailWord_4139268 prefixEnd_4139268 2125434041774816328613859 := by
  unfold tailWord_4139268
  simp only [CollatzResearch.WordTrace]
  refine ⟨75485753384073220768941229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100647671178764294358588305 75485753384073220768941229)
  ·
    refine ⟨28307157519027457788352961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75485753384073220768941229 28307157519027457788352961)
    ·
      refine ⟨21230368139270593341264721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28307157519027457788352961 21230368139270593341264721)
      ·
        refine ⟨15922776104452945005948541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21230368139270593341264721 15922776104452945005948541)
        ·
          refine ⟨5971041039169854377230703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15922776104452945005948541 5971041039169854377230703)
          ·
            refine ⟨8956561558754781565846055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5971041039169854377230703 8956561558754781565846055)
            ·
              refine ⟨13434842338132172348769083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8956561558754781565846055 13434842338132172348769083)
              ·
                refine ⟨20152263507198258523153625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13434842338132172348769083 20152263507198258523153625)
                ·
                  refine ⟨15114197630398693892365219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20152263507198258523153625 15114197630398693892365219)
                  ·
                    refine ⟨22671296445598040838547829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15114197630398693892365219 22671296445598040838547829)
                    ·
                      refine ⟨2125434041774816328613859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22671296445598040838547829 2125434041774816328613859)
                      ·
                        rfl

theorem cell23_4139268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_4139268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139268 prefixEnd_4139268 := by exact prefixLift 4139268
  have htrace : WordTrace (prefixWord ++ tailWord_4139268) baseStart_4139268 baseEnd_4139268 := by
    simpa [prefixWord, tailWord_4139268, baseEnd_4139268] using wordTrace_append hprefix tailTrace_4139268
  have hstable : (prefixWord ++ tailWord_4139268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139268).length < 2 ^ (prefixWord ++ tailWord_4139268).sum := by decide
  have hdescent : baseEnd_4139268 < baseStart_4139268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139303 : List Nat := [1, 1, 8, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_4139303 : Nat := 118140960795 + 4139303 * 2 ^ 59
def prefixEnd_4139303 : Nat := 4983230072969 + 3 ^ 40 * 4139303 * 2
def baseEnd_4139303 : Nat := 2125452013597723691676199

theorem tailTrace_4139303 : CollatzResearch.WordTrace tailWord_4139303 prefixEnd_4139303 2125452013597723691676199 := by
  unfold tailWord_4139303
  simp only [CollatzResearch.WordTrace]
  refine ⟨150972783323019642515406563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100648522215346428343604375 150972783323019642515406563)
  ·
    refine ⟨226459174984529463773109845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150972783323019642515406563 226459174984529463773109845)
    ·
      refine ⟨2653818456849954653591131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 226459174984529463773109845 2653818456849954653591131)
      ·
        refine ⟨3980727685274931980386697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2653818456849954653591131 3980727685274931980386697)
        ·
          refine ⟨2985545763956198985290023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3980727685274931980386697 2985545763956198985290023)
          ·
            refine ⟨4478318645934298477935035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2985545763956198985290023 4478318645934298477935035)
            ·
              refine ⟨6717477968901447716902553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4478318645934298477935035 6717477968901447716902553)
              ·
                refine ⟨5038108476676085787676915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6717477968901447716902553 5038108476676085787676915)
                ·
                  refine ⟨7557162715014128681515373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5038108476676085787676915 7557162715014128681515373)
                  ·
                    refine ⟨2833936018130298255568265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7557162715014128681515373 2833936018130298255568265)
                    ·
                      refine ⟨2125452013597723691676199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2833936018130298255568265 2125452013597723691676199)
                      ·
                        rfl

theorem cell23_4139303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_4139303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139303 prefixEnd_4139303 := by exact prefixLift 4139303
  have htrace : WordTrace (prefixWord ++ tailWord_4139303) baseStart_4139303 baseEnd_4139303 := by
    simpa [prefixWord, tailWord_4139303, baseEnd_4139303] using wordTrace_append hprefix tailTrace_4139303
  have hstable : (prefixWord ++ tailWord_4139303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139303).length < 2 ^ (prefixWord ++ tailWord_4139303).sum := by decide
  have hdescent : baseEnd_4139303 < baseStart_4139303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139371 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 3]
def baseStart_4139371 : Nat := 118140960795 + 4139371 * 2 ^ 59
def prefixEnd_4139371 : Nat := 4983230072969 + 3 ^ 40 * 4139371 * 2
def baseEnd_4139371 : Nat := 2125486930282229425625885

theorem tailTrace_4139371 : CollatzResearch.WordTrace tailWord_4139371 prefixEnd_4139371 2125486930282229425625885 := by
  unfold tailWord_4139371
  simp only [CollatzResearch.WordTrace]
  refine ⟨150975263486773290128881967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100650175657848860085921311 150975263486773290128881967)
  ·
    refine ⟨226462895230159935193322951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150975263486773290128881967 226462895230159935193322951)
    ·
      refine ⟨339694342845239902789984427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226462895230159935193322951 339694342845239902789984427)
      ·
        refine ⟨509541514267859854184976641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339694342845239902789984427 509541514267859854184976641)
        ·
          refine ⟨382156135700894890638732481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509541514267859854184976641 382156135700894890638732481)
          ·
            refine ⟨286617101775671167979049361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382156135700894890638732481 286617101775671167979049361)
            ·
              refine ⟨214962826331753375984287021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286617101775671167979049361 214962826331753375984287021)
              ·
                refine ⟨80611059874407515994107633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214962826331753375984287021 80611059874407515994107633)
                ·
                  refine ⟨60458294905805636995580725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80611059874407515994107633 60458294905805636995580725)
                  ·
                    refine ⟨5667965147419278468335693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60458294905805636995580725 5667965147419278468335693)
                    ·
                      refine ⟨2125486930282229425625885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5667965147419278468335693 2125486930282229425625885)
                      ·
                        rfl

theorem cell23_4139371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 3].length) (baseStart_4139371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139371 prefixEnd_4139371 := by exact prefixLift 4139371
  have htrace : WordTrace (prefixWord ++ tailWord_4139371) baseStart_4139371 baseEnd_4139371 := by
    simpa [prefixWord, tailWord_4139371, baseEnd_4139371] using wordTrace_append hprefix tailTrace_4139371
  have hstable : (prefixWord ++ tailWord_4139371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139371).length < 2 ^ (prefixWord ++ tailWord_4139371).sum := by decide
  have hdescent : baseEnd_4139371 < baseStart_4139371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139372 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 2, 1, 4]
def baseStart_4139372 : Nat := 118140960795 + 4139372 * 2 ^ 59
def prefixEnd_4139372 : Nat := 4983230072969 + 3 ^ 40 * 4139372 * 2
def baseEnd_4139372 : Nat := 2125487443762883921713381

theorem tailTrace_4139372 : CollatzResearch.WordTrace tailWord_4139372 prefixEnd_4139372 2125487443762883921713381 := by
  unfold tailWord_4139372
  simp only [CollatzResearch.WordTrace]
  refine ⟨75487649979884833649834185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100650199973179778199778913 75487649979884833649834185)
  ·
    refine ⟨56615737484913625237375639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75487649979884833649834185 56615737484913625237375639)
    ·
      refine ⟨84923606227370437856063459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56615737484913625237375639 84923606227370437856063459)
      ·
        refine ⟨127385409341055656784095189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84923606227370437856063459 127385409341055656784095189)
        ·
          refine ⟨2985595531430991955877231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 127385409341055656784095189 2985595531430991955877231)
          ·
            refine ⟨4478393297146487933815847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2985595531430991955877231 4478393297146487933815847)
            ·
              refine ⟨6717589945719731900723771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4478393297146487933815847 6717589945719731900723771)
              ·
                refine ⟨10076384918579597851085657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6717589945719731900723771 10076384918579597851085657)
                ·
                  refine ⟨7557288688934698388314243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10076384918579597851085657 7557288688934698388314243)
                  ·
                    refine ⟨11335933033402047582471365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7557288688934698388314243 11335933033402047582471365)
                    ·
                      refine ⟨2125487443762883921713381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11335933033402047582471365 2125487443762883921713381)
                      ·
                        rfl

theorem cell23_4139372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 2, 1, 4].length) (baseStart_4139372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139372 prefixEnd_4139372 := by exact prefixLift 4139372
  have htrace : WordTrace (prefixWord ++ tailWord_4139372) baseStart_4139372 baseEnd_4139372 := by
    simpa [prefixWord, tailWord_4139372, baseEnd_4139372] using wordTrace_append hprefix tailTrace_4139372
  have hstable : (prefixWord ++ tailWord_4139372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139372).length < 2 ^ (prefixWord ++ tailWord_4139372).sum := by decide
  have hdescent : baseEnd_4139372 < baseStart_4139372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139395 : List Nat := [1, 1, 1, 3, 6, 2, 1, 2, 6]
def baseStart_4139395 : Nat := 118140960795 + 4139395 * 2 ^ 59
def prefixEnd_4139395 : Nat := 4983230072969 + 3 ^ 40 * 4139395 * 2
def baseEnd_4139395 : Nat := 236166583757548592413975

theorem tailTrace_4139395 : CollatzResearch.WordTrace tailWord_4139395 prefixEnd_4139395 236166583757548592413975 := by
  unfold tailWord_4139395
  simp only [CollatzResearch.WordTrace]
  refine ⟨150976138838686342227755639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100650759225790894818503759 150976138838686342227755639)
  ·
    refine ⟨226464208258029513341633459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150976138838686342227755639 226464208258029513341633459)
    ·
      refine ⟨339696312387044270012450189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226464208258029513341633459 339696312387044270012450189)
      ·
        refine ⟨127386117145141601254668821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339696312387044270012450189 127386117145141601254668821)
        ·
          refine ⟨5971224241178512558812601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 127386117145141601254668821 5971224241178512558812601)
          ·
            refine ⟨4478418180883884419109451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5971224241178512558812601 4478418180883884419109451)
            ·
              refine ⟨6717627271325826628664177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4478418180883884419109451 6717627271325826628664177)
              ·
                refine ⟨5038220453494369971498133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6717627271325826628664177 5038220453494369971498133)
                ·
                  refine ⟨236166583757548592413975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5038220453494369971498133 236166583757548592413975)
                  ·
                    rfl

theorem cell23_4139395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 6].length) (baseStart_4139395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139395 prefixEnd_4139395 := by exact prefixLift 4139395
  have htrace : WordTrace (prefixWord ++ tailWord_4139395) baseStart_4139395 baseEnd_4139395 := by
    simpa [prefixWord, tailWord_4139395, baseEnd_4139395] using wordTrace_append hprefix tailTrace_4139395
  have hstable : (prefixWord ++ tailWord_4139395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139395).length < 2 ^ (prefixWord ++ tailWord_4139395).sum := by decide
  have hdescent : baseEnd_4139395 < baseStart_4139395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139412 : List Nat := [2, 4, 2, 1, 3, 1, 3, 1, 6]
def baseStart_4139412 : Nat := 118140960795 + 4139412 * 2 ^ 59
def prefixEnd_4139412 : Nat := 4983230072969 + 3 ^ 40 * 4139412 * 2
def baseEnd_4139412 : Nat := 236167553665451529468133

theorem tailTrace_4139412 : CollatzResearch.WordTrace tailWord_4139412 prefixEnd_4139412 236167553665451529468133 := by
  unfold tailWord_4139412
  simp only [CollatzResearch.WordTrace]
  refine ⟨75488379439812377065562245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100651172586416502754082993 75488379439812377065562245)
  ·
    refine ⟨14154071144964820699792921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75488379439812377065562245 14154071144964820699792921)
    ·
      refine ⟨10615553358723615524844691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14154071144964820699792921 10615553358723615524844691)
      ·
        refine ⟨15923330038085423287267037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10615553358723615524844691 15923330038085423287267037)
        ·
          refine ⟨5971248764282033732725139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15923330038085423287267037 5971248764282033732725139)
          ·
            refine ⟨8956873146423050599087709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5971248764282033732725139 8956873146423050599087709)
            ·
              refine ⟨3358827429908643974657891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8956873146423050599087709 3358827429908643974657891)
              ·
                refine ⟨5038241144862965961986837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3358827429908643974657891 5038241144862965961986837)
                ·
                  refine ⟨236167553665451529468133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5038241144862965961986837 236167553665451529468133)
                  ·
                    rfl

theorem cell23_4139412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_4139412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139412 prefixEnd_4139412 := by exact prefixLift 4139412
  have htrace : WordTrace (prefixWord ++ tailWord_4139412) baseStart_4139412 baseEnd_4139412 := by
    simpa [prefixWord, tailWord_4139412, baseEnd_4139412] using wordTrace_append hprefix tailTrace_4139412
  have hstable : (prefixWord ++ tailWord_4139412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139412).length < 2 ^ (prefixWord ++ tailWord_4139412).sum := by decide
  have hdescent : baseEnd_4139412 < baseStart_4139412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139428 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_4139428 : Nat := 118140960795 + 4139428 * 2 ^ 59
def prefixEnd_4139428 : Nat := 4983230072969 + 3 ^ 40 * 4139428 * 2
def baseEnd_4139428 : Nat := 2125516198679535702613123

theorem tailTrace_4139428 : CollatzResearch.WordTrace tailWord_4139428 prefixEnd_4139428 2125516198679535702613123 := by
  unfold tailWord_4139428
  simp only [CollatzResearch.WordTrace]
  refine ⟨75488671223783394431853469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100651561631711192575804625 75488671223783394431853469)
  ·
    refine ⟨28308251708918772911945051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75488671223783394431853469 28308251708918772911945051)
    ·
      refine ⟨42462377563378159367917577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28308251708918772911945051 42462377563378159367917577)
      ·
        refine ⟨31846783172533619525938183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42462377563378159367917577 31846783172533619525938183)
        ·
          refine ⟨47770174758800429288907275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31846783172533619525938183 47770174758800429288907275)
          ·
            refine ⟨71655262138200643933360913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47770174758800429288907275 71655262138200643933360913)
            ·
              refine ⟨53741446603650482950020685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71655262138200643933360913 53741446603650482950020685)
              ·
                refine ⟨20153042476368931106257757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53741446603650482950020685 20153042476368931106257757)
                ·
                  refine ⟨7557390928638349164846659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20153042476368931106257757 7557390928638349164846659)
                  ·
                    refine ⟨11336086392957523747269989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7557390928638349164846659 11336086392957523747269989)
                    ·
                      refine ⟨2125516198679535702613123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11336086392957523747269989 2125516198679535702613123)
                      ·
                        rfl

theorem cell23_4139428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_4139428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139428 prefixEnd_4139428 := by exact prefixLift 4139428
  have htrace : WordTrace (prefixWord ++ tailWord_4139428) baseStart_4139428 baseEnd_4139428 := by
    simpa [prefixWord, tailWord_4139428, baseEnd_4139428] using wordTrace_append hprefix tailTrace_4139428
  have hstable : (prefixWord ++ tailWord_4139428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139428).length < 2 ^ (prefixWord ++ tailWord_4139428).sum := by decide
  have hdescent : baseEnd_4139428 < baseStart_4139428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139432 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_4139432 : Nat := 118140960795 + 4139432 * 2 ^ 59
def prefixEnd_4139432 : Nat := 4983230072969 + 3 ^ 40 * 4139432 * 2
def baseEnd_4139432 : Nat := 2125518252602153686963105

theorem tailTrace_4139432 : CollatzResearch.WordTrace tailWord_4139432 prefixEnd_4139432 2125518252602153686963105 := by
  unfold tailWord_4139432
  simp only [CollatzResearch.WordTrace]
  refine ⟨75488744169776148773426275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100651658893034865031235033 75488744169776148773426275)
  ·
    refine ⟨113233116254664223160139413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75488744169776148773426275 113233116254664223160139413)
    ·
      refine ⟨5307802324437385460631535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113233116254664223160139413 5307802324437385460631535)
      ·
        refine ⟨7961703486656078190947303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5307802324437385460631535 7961703486656078190947303)
        ·
          refine ⟨11942555229984117286420955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7961703486656078190947303 11942555229984117286420955)
          ·
            refine ⟨17913832844976175929631433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11942555229984117286420955 17913832844976175929631433)
            ·
              refine ⟨13435374633732131947223575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17913832844976175929631433 13435374633732131947223575)
              ·
                refine ⟨20153061950598197920835363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13435374633732131947223575 20153061950598197920835363)
                ·
                  refine ⟨30229592925897296881253045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20153061950598197920835363 30229592925897296881253045)
                  ·
                    refine ⟨2834024336802871582617473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30229592925897296881253045 2834024336802871582617473)
                    ·
                      refine ⟨2125518252602153686963105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2834024336802871582617473 2125518252602153686963105)
                      ·
                        rfl

theorem cell23_4139432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_4139432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139432 prefixEnd_4139432 := by exact prefixLift 4139432
  have htrace : WordTrace (prefixWord ++ tailWord_4139432) baseStart_4139432 baseEnd_4139432 := by
    simpa [prefixWord, tailWord_4139432, baseEnd_4139432] using wordTrace_append hprefix tailTrace_4139432
  have hstable : (prefixWord ++ tailWord_4139432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139432).length < 2 ^ (prefixWord ++ tailWord_4139432).sum := by decide
  have hdescent : baseEnd_4139432 < baseStart_4139432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139448 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 5, 2, 3]
def baseStart_4139448 : Nat := 118140960795 + 4139448 * 2 ^ 59
def prefixEnd_4139448 : Nat := 4983230072969 + 3 ^ 40 * 4139448 * 2
def baseEnd_4139448 : Nat := 2125526468292625624363031

theorem tailTrace_4139448 : CollatzResearch.WordTrace tailWord_4139448 prefixEnd_4139448 2125526468292625624363031 := by
  unfold tailWord_4139448
  simp only [CollatzResearch.WordTrace]
  refine ⟨75489035953747166139717499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100652047938329554852956665 75489035953747166139717499)
  ·
    refine ⟨113233553930620749209576249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75489035953747166139717499 113233553930620749209576249)
    ·
      refine ⟨84925165447965561907182187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113233553930620749209576249 84925165447965561907182187)
      ·
        refine ⟨127387748171948342860773281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84925165447965561907182187 127387748171948342860773281)
        ·
          refine ⟨95540811128961257145579961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127387748171948342860773281 95540811128961257145579961)
          ·
            refine ⟨71655608346720942859184971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95540811128961257145579961 71655608346720942859184971)
            ·
              refine ⟨107483412520081414288777457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71655608346720942859184971 107483412520081414288777457)
              ·
                refine ⟨80612559390061060716583093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107483412520081414288777457 80612559390061060716583093)
                ·
                  refine ⟨7557427442818224442179665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80612559390061060716583093 7557427442818224442179665)
                  ·
                    refine ⟨5668070582113668331634749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7557427442818224442179665 5668070582113668331634749)
                    ·
                      refine ⟨2125526468292625624363031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5668070582113668331634749 2125526468292625624363031)
                      ·
                        rfl

theorem cell23_4139448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_4139448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139448 prefixEnd_4139448 := by exact prefixLift 4139448
  have htrace : WordTrace (prefixWord ++ tailWord_4139448) baseStart_4139448 baseEnd_4139448 := by
    simpa [prefixWord, tailWord_4139448, baseEnd_4139448] using wordTrace_append hprefix tailTrace_4139448
  have hstable : (prefixWord ++ tailWord_4139448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139448).length < 2 ^ (prefixWord ++ tailWord_4139448).sum := by decide
  have hdescent : baseEnd_4139448 < baseStart_4139448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139471 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 6]
def baseStart_4139471 : Nat := 118140960795 + 4139471 * 2 ^ 59
def prefixEnd_4139471 : Nat := 4983230072969 + 3 ^ 40 * 4139471 * 2
def baseEnd_4139471 : Nat := 2125538278347679034375425

theorem tailTrace_4139471 : CollatzResearch.WordTrace tailWord_4139471 prefixEnd_4139471 2125538278347679034375425 := by
  unfold tailWord_4139471
  simp only [CollatzResearch.WordTrace]
  refine ⟨150978910786411007207522267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100652607190940671471681511 150978910786411007207522267)
  ·
    refine ⟨226468366179616510811283401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150978910786411007207522267 226468366179616510811283401)
    ·
      refine ⟨169851274634712383108462551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226468366179616510811283401 169851274634712383108462551)
      ·
        refine ⟨254776911952068574662693827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169851274634712383108462551 254776911952068574662693827)
        ·
          refine ⟨382165367928102861994040741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254776911952068574662693827 382165367928102861994040741)
          ·
            refine ⟨71656006486519286623882639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 382165367928102861994040741 71656006486519286623882639)
            ·
              refine ⟨107484009729778929935823959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71656006486519286623882639 107484009729778929935823959)
              ·
                refine ⟨161226014594668394903735939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107484009729778929935823959 161226014594668394903735939)
                ·
                  refine ⟨241839021892002592355603909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161226014594668394903735939 241839021892002592355603909)
                  ·
                    refine ⟨45344816604750486066675733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 241839021892002592355603909 45344816604750486066675733)
                    ·
                      refine ⟨2125538278347679034375425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45344816604750486066675733 2125538278347679034375425)
                      ·
                        rfl

theorem cell23_4139471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_4139471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139471 prefixEnd_4139471 := by exact prefixLift 4139471
  have htrace : WordTrace (prefixWord ++ tailWord_4139471) baseStart_4139471 baseEnd_4139471 := by
    simpa [prefixWord, tailWord_4139471, baseEnd_4139471] using wordTrace_append hprefix tailTrace_4139471
  have hstable : (prefixWord ++ tailWord_4139471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139471).length < 2 ^ (prefixWord ++ tailWord_4139471).sum := by decide
  have hdescent : baseEnd_4139471 < baseStart_4139471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139495 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_4139495 : Nat := 118140960795 + 4139495 * 2 ^ 59
def prefixEnd_4139495 : Nat := 4983230072969 + 3 ^ 40 * 4139495 * 2
def baseEnd_4139495 : Nat := 2125550601883386940475315

theorem tailTrace_4139495 : CollatzResearch.WordTrace tailWord_4139495 prefixEnd_4139495 2125550601883386940475315 := by
  unfold tailWord_4139495
  simp only [CollatzResearch.WordTrace]
  refine ⟨150979786138324059306395939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100653190758882706204263959 150979786138324059306395939)
  ·
    refine ⟨226469679207486088959593909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150979786138324059306395939 226469679207486088959593909)
    ·
      refine ⟨21231532425701820839961929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226469679207486088959593909 21231532425701820839961929)
      ·
        refine ⟨15923649319276365629971447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21231532425701820839961929 15923649319276365629971447)
        ·
          refine ⟨23885473978914548444957171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15923649319276365629971447 23885473978914548444957171)
          ·
            refine ⟨35828210968371822667435757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23885473978914548444957171 35828210968371822667435757)
            ·
              refine ⟨13435579113139433500288409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35828210968371822667435757 13435579113139433500288409)
              ·
                refine ⟨10076684334854575125216307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13435579113139433500288409 10076684334854575125216307)
                ·
                  refine ⟨15115026502281862687824461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10076684334854575125216307 15115026502281862687824461)
                  ·
                    refine ⟨5668134938355698507934173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15115026502281862687824461 5668134938355698507934173)
                    ·
                      refine ⟨2125550601883386940475315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5668134938355698507934173 2125550601883386940475315)
                      ·
                        rfl

theorem cell23_4139495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_4139495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139495 prefixEnd_4139495 := by exact prefixLift 4139495
  have htrace : WordTrace (prefixWord ++ tailWord_4139495) baseStart_4139495 baseEnd_4139495 := by
    simpa [prefixWord, tailWord_4139495, baseEnd_4139495] using wordTrace_append hprefix tailTrace_4139495
  have hstable : (prefixWord ++ tailWord_4139495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139495).length < 2 ^ (prefixWord ++ tailWord_4139495).sum := by decide
  have hdescent : baseEnd_4139495 < baseStart_4139495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139512 : List Nat := [2, 1, 2, 1, 1, 4, 4, 2, 2, 1, 3]
def baseStart_4139512 : Nat := 118140960795 + 4139512 * 2 ^ 59
def prefixEnd_4139512 : Nat := 4983230072969 + 3 ^ 40 * 4139512 * 2
def baseEnd_4139512 : Nat := 2125559331054513373962737

theorem tailTrace_4139512 : CollatzResearch.WordTrace tailWord_4139512 prefixEnd_4139512 2125559331054513373962737 := by
  unfold tailWord_4139512
  simp only [CollatzResearch.WordTrace]
  refine ⟨75490203089631235604882395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100653604119508314139843193 75490203089631235604882395)
  ·
    refine ⟨113235304634446853407323593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75490203089631235604882395 113235304634446853407323593)
    ·
      refine ⟨84926478475835140055492695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113235304634446853407323593 84926478475835140055492695)
      ·
        refine ⟨127389717713752710083239043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84926478475835140055492695 127389717713752710083239043)
        ·
          refine ⟨191084576570629065124858565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127389717713752710083239043 191084576570629065124858565)
          ·
            refine ⟨35828358106992949710910981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191084576570629065124858565 35828358106992949710910981)
            ·
              refine ⟨6717817145061178070795809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35828358106992949710910981 6717817145061178070795809)
              ·
                refine ⟨5038362858795883553096857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6717817145061178070795809 5038362858795883553096857)
                ·
                  refine ⟨3778772144096912664822643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5038362858795883553096857 3778772144096912664822643)
                  ·
                    refine ⟨5668158216145368997233965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3778772144096912664822643 5668158216145368997233965)
                    ·
                      refine ⟨2125559331054513373962737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5668158216145368997233965 2125559331054513373962737)
                      ·
                        rfl

theorem cell23_4139512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 2, 1, 3].length) (baseStart_4139512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139512 prefixEnd_4139512 := by exact prefixLift 4139512
  have htrace : WordTrace (prefixWord ++ tailWord_4139512) baseStart_4139512 baseEnd_4139512 := by
    simpa [prefixWord, tailWord_4139512, baseEnd_4139512] using wordTrace_append hprefix tailTrace_4139512
  have hstable : (prefixWord ++ tailWord_4139512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139512).length < 2 ^ (prefixWord ++ tailWord_4139512).sum := by decide
  have hdescent : baseEnd_4139512 < baseStart_4139512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139526 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_4139526 : Nat := 118140960795 + 4139526 * 2 ^ 59
def prefixEnd_4139526 : Nat := 4983230072969 + 3 ^ 40 * 4139526 * 2
def baseEnd_4139526 : Nat := 2125566519783676319187673

theorem tailTrace_4139526 : CollatzResearch.WordTrace tailWord_4139526 prefixEnd_4139526 2125566519783676319187673 := by
  unfold tailWord_4139526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4718153650037867237524201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100653944534141167733849621 4718153650037867237524201)
  ·
    refine ⟨3538615237528400428143151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4718153650037867237524201 3538615237528400428143151)
    ·
      refine ⟨5307922856292600642214727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3538615237528400428143151 5307922856292600642214727)
      ·
        refine ⟨7961884284438900963322091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5307922856292600642214727 7961884284438900963322091)
        ·
          refine ⟨11942826426658351444983137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7961884284438900963322091 11942826426658351444983137)
          ·
            refine ⟨8957119819993763583737353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11942826426658351444983137 8957119819993763583737353)
            ·
              refine ⟨6717839864995322687803015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8957119819993763583737353 6717839864995322687803015)
              ·
                refine ⟨10076759797492984031704523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6717839864995322687803015 10076759797492984031704523)
                ·
                  refine ⟨15115139696239476047556785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10076759797492984031704523 15115139696239476047556785)
                  ·
                    refine ⟨11336354772179607035667589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15115139696239476047556785 11336354772179607035667589)
                    ·
                      refine ⟨2125566519783676319187673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11336354772179607035667589 2125566519783676319187673)
                      ·
                        rfl

theorem cell23_4139526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_4139526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139526 prefixEnd_4139526 := by exact prefixLift 4139526
  have htrace : WordTrace (prefixWord ++ tailWord_4139526) baseStart_4139526 baseEnd_4139526 := by
    simpa [prefixWord, tailWord_4139526, baseEnd_4139526] using wordTrace_append hprefix tailTrace_4139526
  have hstable : (prefixWord ++ tailWord_4139526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139526).length < 2 ^ (prefixWord ++ tailWord_4139526).sum := by decide
  have hdescent : baseEnd_4139526 < baseStart_4139526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139535 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 1, 4, 2]
def baseStart_4139535 : Nat := 118140960795 + 4139535 * 2 ^ 59
def prefixEnd_4139535 : Nat := 4983230072969 + 3 ^ 40 * 4139535 * 2
def baseEnd_4139535 : Nat := 2125571141109566783975131

theorem tailTrace_4139535 : CollatzResearch.WordTrace tailWord_4139535 prefixEnd_4139535 2125571141109566783975131 := by
  unfold tailWord_4139535
  simp only [CollatzResearch.WordTrace]
  refine ⟨150981245058179146137852059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100654163372119430758568039 150981245058179146137852059)
  ·
    refine ⟨226471867587268719206778089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150981245058179146137852059 226471867587268719206778089)
    ·
      refine ⟨169853900690451539405083567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226471867587268719206778089 169853900690451539405083567)
      ·
        refine ⟨254780851035677309107625351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169853900690451539405083567 254780851035677309107625351)
        ·
          refine ⟨382171276553515963661438027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254780851035677309107625351 382171276553515963661438027)
          ·
            refine ⟨573256914830273945492157041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382171276553515963661438027 573256914830273945492157041)
            ·
              refine ⟨429942686122705459119117781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573256914830273945492157041 429942686122705459119117781)
              ·
                refine ⟨10076781706000909198104323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 429942686122705459119117781 10076781706000909198104323)
                ·
                  refine ⟨15115172559001363797156485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10076781706000909198104323 15115172559001363797156485)
                  ·
                    refine ⟨2834094854812755711966841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15115172559001363797156485 2834094854812755711966841)
                    ·
                      refine ⟨2125571141109566783975131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2834094854812755711966841 2125571141109566783975131)
                      ·
                        rfl

theorem cell23_4139535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 4, 2].length) (baseStart_4139535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139535 prefixEnd_4139535 := by exact prefixLift 4139535
  have htrace : WordTrace (prefixWord ++ tailWord_4139535) baseStart_4139535 baseEnd_4139535 := by
    simpa [prefixWord, tailWord_4139535, baseEnd_4139535] using wordTrace_append hprefix tailTrace_4139535
  have hstable : (prefixWord ++ tailWord_4139535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139535).length < 2 ^ (prefixWord ++ tailWord_4139535).sum := by decide
  have hdescent : baseEnd_4139535 < baseStart_4139535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139556 : List Nat := [2, 3, 1, 5, 1, 1, 1, 3, 1, 3, 2]
def baseStart_4139556 : Nat := 118140960795 + 4139556 * 2 ^ 59
def prefixEnd_4139556 : Nat := 4983230072969 + 3 ^ 40 * 4139556 * 2
def baseEnd_4139556 : Nat := 2125581924203311201812535

theorem tailTrace_4139556 : CollatzResearch.WordTrace tailWord_4139556 prefixEnd_4139556 2125581924203311201812535 := by
  unfold tailWord_4139556
  simp only [CollatzResearch.WordTrace]
  refine ⟨75491005495551533362183261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100654673994068711149577681 75491005495551533362183261)
  ·
    refine ⟨28309127060831825010818723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75491005495551533362183261 28309127060831825010818723)
    ·
      refine ⟨42463690591247737516228085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28309127060831825010818723 42463690591247737516228085)
      ·
        refine ⟨3980970992929475392146383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42463690591247737516228085 3980970992929475392146383)
        ·
          refine ⟨5971456489394213088219575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3980970992929475392146383 5971456489394213088219575)
          ·
            refine ⟨8957184734091319632329363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5971456489394213088219575 8957184734091319632329363)
            ·
              refine ⟨13435777101136979448494045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8957184734091319632329363 13435777101136979448494045)
              ·
                refine ⟨5038416412926367293185267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13435777101136979448494045 5038416412926367293185267)
                ·
                  refine ⟨7557624619389550939777901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5038416412926367293185267 7557624619389550939777901)
                  ·
                    refine ⟨2834109232271081602416713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7557624619389550939777901 2834109232271081602416713)
                    ·
                      refine ⟨2125581924203311201812535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2834109232271081602416713 2125581924203311201812535)
                      ·
                        rfl

theorem cell23_4139556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_4139556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139556 prefixEnd_4139556 := by exact prefixLift 4139556
  have htrace : WordTrace (prefixWord ++ tailWord_4139556) baseStart_4139556 baseEnd_4139556 := by
    simpa [prefixWord, tailWord_4139556, baseEnd_4139556] using wordTrace_append hprefix tailTrace_4139556
  have hstable : (prefixWord ++ tailWord_4139556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139556).length < 2 ^ (prefixWord ++ tailWord_4139556).sum := by decide
  have hdescent : baseEnd_4139556 < baseStart_4139556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139569 : List Nat := [1, 2, 2, 3, 1, 1, 5, 2, 2, 2, 2]
def baseStart_4139569 : Nat := 118140960795 + 4139569 * 2 ^ 59
def prefixEnd_4139569 : Nat := 4983230072969 + 3 ^ 40 * 4139569 * 2
def baseEnd_4139569 : Nat := 2125588599451819650949975

theorem tailTrace_4139569 : CollatzResearch.WordTrace tailWord_4139569 prefixEnd_4139569 2125588599451819650949975 := by
  unfold tailWord_4139569
  simp only [CollatzResearch.WordTrace]
  refine ⟨150982485140055969944589761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100654990093370646629726507 150982485140055969944589761)
  ·
    refine ⟨113236863855041977458442321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150982485140055969944589761 113236863855041977458442321)
    ·
      refine ⟨84927647891281483093831741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113236863855041977458442321 84927647891281483093831741)
      ·
        refine ⟨31847867959230556160186903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84927647891281483093831741 31847867959230556160186903)
        ·
          refine ⟨47771801938845834240280355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31847867959230556160186903 47771801938845834240280355)
          ·
            refine ⟨71657702908268751360420533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47771801938845834240280355 71657702908268751360420533)
            ·
              refine ⟨6717909647650195440039425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71657702908268751360420533 6717909647650195440039425)
              ·
                refine ⟨5038432235737646580029569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6717909647650195440039425 5038432235737646580029569)
                ·
                  refine ⟨3778824176803234935022177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5038432235737646580029569 3778824176803234935022177)
                  ·
                    refine ⟨2834118132602426201266633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3778824176803234935022177 2834118132602426201266633)
                    ·
                      refine ⟨2125588599451819650949975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2834118132602426201266633 2125588599451819650949975)
                      ·
                        rfl

theorem cell23_4139569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_4139569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139569 prefixEnd_4139569 := by exact prefixLift 4139569
  have htrace : WordTrace (prefixWord ++ tailWord_4139569) baseStart_4139569 baseEnd_4139569 := by
    simpa [prefixWord, tailWord_4139569, baseEnd_4139569] using wordTrace_append hprefix tailTrace_4139569
  have hstable : (prefixWord ++ tailWord_4139569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139569).length < 2 ^ (prefixWord ++ tailWord_4139569).sum := by decide
  have hdescent : baseEnd_4139569 < baseStart_4139569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139575 : List Nat := [1, 1, 3, 1, 2, 3, 1, 6, 5]
def baseStart_4139575 : Nat := 118140960795 + 4139575 * 2 ^ 59
def prefixEnd_4139575 : Nat := 4983230072969 + 3 ^ 40 * 4139575 * 2
def baseEnd_4139575 : Nat := 236176853370638514163883

theorem tailTrace_4139575 : CollatzResearch.WordTrace tailWord_4139575 prefixEnd_4139575 236176853370638514163883 := by
  unfold tailWord_4139575
  simp only [CollatzResearch.WordTrace]
  refine ⟨150982703978034232969308179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100655135985356155312872119 150982703978034232969308179)
  ·
    refine ⟨226474055967051349453962269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150982703978034232969308179 226474055967051349453962269)
    ·
      refine ⟨84927770987644256045235851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226474055967051349453962269 84927770987644256045235851)
      ·
        refine ⟨127391656481466384067853777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84927770987644256045235851 127391656481466384067853777)
        ·
          refine ⟨95543742361099788050890333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127391656481466384067853777 95543742361099788050890333)
          ·
            refine ⟨35828903385412420519083875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95543742361099788050890333 35828903385412420519083875)
            ·
              refine ⟨53743355078118630778625813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35828903385412420519083875 53743355078118630778625813)
              ·
                refine ⟨2519219769286810817748085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53743355078118630778625813 2519219769286810817748085)
                ·
                  refine ⟨236176853370638514163883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2519219769286810817748085 236176853370638514163883)
                  ·
                    rfl

theorem cell23_4139575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 5].length) (baseStart_4139575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139575 prefixEnd_4139575 := by exact prefixLift 4139575
  have htrace : WordTrace (prefixWord ++ tailWord_4139575) baseStart_4139575 baseEnd_4139575 := by
    simpa [prefixWord, tailWord_4139575, baseEnd_4139575] using wordTrace_append hprefix tailTrace_4139575
  have hstable : (prefixWord ++ tailWord_4139575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139575).length < 2 ^ (prefixWord ++ tailWord_4139575).sum := by decide
  have hdescent : baseEnd_4139575 < baseStart_4139575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139595 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 2, 5, 2]
def baseStart_4139595 : Nat := 118140960795 + 4139595 * 2 ^ 59
def prefixEnd_4139595 : Nat := 4983230072969 + 3 ^ 40 * 4139595 * 2
def baseEnd_4139595 : Nat := 2125601949948836549224855

theorem tailTrace_4139595 : CollatzResearch.WordTrace tailWord_4139595 prefixEnd_4139595 2125601949948836549224855 := by
  unfold tailWord_4139595
  simp only [CollatzResearch.WordTrace]
  refine ⟨150983433437961776385036239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100655622291974517590024159 150983433437961776385036239)
  ·
    refine ⟨226475150156942664577554359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150983433437961776385036239 226475150156942664577554359)
    ·
      refine ⟨339712725235413996866331539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226475150156942664577554359 339712725235413996866331539)
      ·
        refine ⟨509569087853120995299497309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339712725235413996866331539 509569087853120995299497309)
        ·
          refine ⟨191088407944920373237311491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 509569087853120995299497309 191088407944920373237311491)
          ·
            refine ⟨286632611917380559855967237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191088407944920373237311491 286632611917380559855967237)
            ·
              refine ⟨53743614734508854972993857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286632611917380559855967237 53743614734508854972993857)
              ·
                refine ⟨40307711050881641229745393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53743614734508854972993857 40307711050881641229745393)
                ·
                  refine ⟨30230783288161230922309045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40307711050881641229745393 30230783288161230922309045)
                  ·
                    refine ⟨2834135933265115398966473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30230783288161230922309045 2834135933265115398966473)
                    ·
                      refine ⟨2125601949948836549224855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2834135933265115398966473 2125601949948836549224855)
                      ·
                        rfl

theorem cell23_4139595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 5, 2].length) (baseStart_4139595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139595 prefixEnd_4139595 := by exact prefixLift 4139595
  have htrace : WordTrace (prefixWord ++ tailWord_4139595) baseStart_4139595 baseEnd_4139595 := by
    simpa [prefixWord, tailWord_4139595, baseEnd_4139595] using wordTrace_append hprefix tailTrace_4139595
  have hstable : (prefixWord ++ tailWord_4139595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139595).length < 2 ^ (prefixWord ++ tailWord_4139595).sum := by decide
  have hdescent : baseEnd_4139595 < baseStart_4139595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139635 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 3, 4]
def baseStart_4139635 : Nat := 118140960795 + 4139635 * 2 ^ 59
def prefixEnd_4139635 : Nat := 4983230072969 + 3 ^ 40 * 4139635 * 2
def baseEnd_4139635 : Nat := 708540829725005464241557

theorem tailTrace_4139635 : CollatzResearch.WordTrace tailWord_4139635 prefixEnd_4139635 708540829725005464241557 := by
  unfold tailWord_4139635
  simp only [CollatzResearch.WordTrace]
  refine ⟨150984892357816863216492359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100656594905211242144328239 150984892357816863216492359)
  ·
    refine ⟨226477338536725294824738539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150984892357816863216492359 226477338536725294824738539)
    ·
      refine ⟨339716007805087942237107809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226477338536725294824738539 339716007805087942237107809)
      ·
        refine ⟨254787005853815956677830857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339716007805087942237107809 254787005853815956677830857)
        ·
          refine ⟨191090254390361967508373143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254787005853815956677830857 191090254390361967508373143)
          ·
            refine ⟨286635381585542951262559715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191090254390361967508373143 286635381585542951262559715)
            ·
              refine ⟨429953072378314426893839573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286635381585542951262559715 429953072378314426893839573)
              ·
                refine ⟨10077025133866744380324365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 429953072378314426893839573 10077025133866744380324365)
                ·
                  refine ⟨3778884425200029142621637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10077025133866744380324365 3778884425200029142621637)
                  ·
                    refine ⟨708540829725005464241557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3778884425200029142621637 708540829725005464241557)
                    ·
                      rfl

theorem cell23_4139635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 4].length) (baseStart_4139635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139635 prefixEnd_4139635 := by exact prefixLift 4139635
  have htrace : WordTrace (prefixWord ++ tailWord_4139635) baseStart_4139635 baseEnd_4139635 := by
    simpa [prefixWord, tailWord_4139635, baseEnd_4139635] using wordTrace_append hprefix tailTrace_4139635
  have hstable : (prefixWord ++ tailWord_4139635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139635).length < 2 ^ (prefixWord ++ tailWord_4139635).sum := by decide
  have hdescent : baseEnd_4139635 < baseStart_4139635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139695 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 3, 5]
def baseStart_4139695 : Nat := 118140960795 + 4139695 * 2 ^ 59
def prefixEnd_4139695 : Nat := 4983230072969 + 3 ^ 40 * 4139695 * 2
def baseEnd_4139695 : Nat := 708551099338095385991465

theorem tailTrace_4139695 : CollatzResearch.WordTrace tailWord_4139695 prefixEnd_4139695 708551099338095385991465 := by
  unfold tailWord_4139695
  simp only [CollatzResearch.WordTrace]
  refine ⟨150987080737599493463676539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100658053825066328975784359 150987080737599493463676539)
  ·
    refine ⟨226480621106399240195514809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150987080737599493463676539 226480621106399240195514809)
    ·
      refine ⟨169860465829799430146636107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226480621106399240195514809 169860465829799430146636107)
      ·
        refine ⟨254790698744699145219954161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169860465829799430146636107 254790698744699145219954161)
        ·
          refine ⟨191093024058524358914965621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254790698744699145219954161 191093024058524358914965621)
          ·
            refine ⟨17914971005486658648278027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191093024058524358914965621 17914971005486658648278027)
            ·
              refine ⟨26872456508229987972417041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17914971005486658648278027 26872456508229987972417041)
              ·
                refine ⟨20154342381172490979312781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26872456508229987972417041 20154342381172490979312781)
                ·
                  refine ⟨7557878392939684117242293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20154342381172490979312781 7557878392939684117242293)
                  ·
                    refine ⟨708551099338095385991465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7557878392939684117242293 708551099338095385991465)
                    ·
                      rfl

theorem cell23_4139695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 5].length) (baseStart_4139695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139695 prefixEnd_4139695 := by exact prefixLift 4139695
  have htrace : WordTrace (prefixWord ++ tailWord_4139695) baseStart_4139695 baseEnd_4139695 := by
    simpa [prefixWord, tailWord_4139695, baseEnd_4139695] using wordTrace_append hprefix tailTrace_4139695
  have hstable : (prefixWord ++ tailWord_4139695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139695).length < 2 ^ (prefixWord ++ tailWord_4139695).sum := by decide
  have hdescent : baseEnd_4139695 < baseStart_4139695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139709 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 3, 1, 3]
def baseStart_4139709 : Nat := 118140960795 + 4139709 * 2 ^ 59
def prefixEnd_4139709 : Nat := 4983230072969 + 3 ^ 40 * 4139709 * 2
def baseEnd_4139709 : Nat := 2125660486743449103199331

theorem tailTrace_4139709 : CollatzResearch.WordTrace tailWord_4139709 prefixEnd_4139709 2125660486743449103199331 := by
  unfold tailWord_4139709
  simp only [CollatzResearch.WordTrace]
  refine ⟨150987591359548773854686181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100658394239699182569790787 150987591359548773854686181)
  ·
    refine ⟨28310173379915395097753659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150987591359548773854686181 28310173379915395097753659)
    ·
      refine ⟨42465260069873092646630489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28310173379915395097753659 42465260069873092646630489)
      ·
        refine ⟨31848945052404819484972867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42465260069873092646630489 31848945052404819484972867)
        ·
          refine ⟨47773417578607229227459301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31848945052404819484972867 47773417578607229227459301)
          ·
            refine ⟨8957515795988855480148619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47773417578607229227459301 8957515795988855480148619)
            ·
              refine ⟨13436273693983283220222929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8957515795988855480148619 13436273693983283220222929)
              ·
                refine ⟨10077205270487462415167197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13436273693983283220222929 10077205270487462415167197)
                ·
                  refine ⟨3778951976432798405687699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10077205270487462415167197 3778951976432798405687699)
                  ·
                    refine ⟨5668427964649197608531549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3778951976432798405687699 5668427964649197608531549)
                    ·
                      refine ⟨2125660486743449103199331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5668427964649197608531549 2125660486743449103199331)
                      ·
                        rfl

theorem cell23_4139709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_4139709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139709 prefixEnd_4139709 := by exact prefixLift 4139709
  have htrace : WordTrace (prefixWord ++ tailWord_4139709) baseStart_4139709 baseEnd_4139709 := by
    simpa [prefixWord, tailWord_4139709, baseEnd_4139709] using wordTrace_append hprefix tailTrace_4139709
  have hstable : (prefixWord ++ tailWord_4139709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139709).length < 2 ^ (prefixWord ++ tailWord_4139709).sum := by decide
  have hdescent : baseEnd_4139709 < baseStart_4139709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139713 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_4139713 : Nat := 118140960795 + 4139713 * 2 ^ 59
def prefixEnd_4139713 : Nat := 4983230072969 + 3 ^ 40 * 4139713 * 2
def baseEnd_4139713 : Nat := 2125662540666067087549313

theorem tailTrace_4139713 : CollatzResearch.WordTrace tailWord_4139713 prefixEnd_4139713 2125662540666067087549313 := by
  unfold tailWord_4139713
  simp only [CollatzResearch.WordTrace]
  refine ⟨150987737251534282537831793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100658491501022855025221195 150987737251534282537831793)
  ·
    refine ⟨113240802938650711903373845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150987737251534282537831793 113240802938650711903373845)
    ·
      refine ⟨5308162637749252120470649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113240802938650711903373845 5308162637749252120470649)
      ·
        refine ⟨3981121978311939090352987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5308162637749252120470649 3981121978311939090352987)
        ·
          refine ⟨5971682967467908635529481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3981121978311939090352987 5971682967467908635529481)
          ·
            refine ⟨4478762225600931476647111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5971682967467908635529481 4478762225600931476647111)
            ·
              refine ⟨6718143338401397214970667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4478762225600931476647111 6718143338401397214970667)
              ·
                refine ⟨10077215007602095822456001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6718143338401397214970667 10077215007602095822456001)
                ·
                  refine ⟨7557911255701571866842001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10077215007602095822456001 7557911255701571866842001)
                  ·
                    refine ⟨5668433441776178900131501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7557911255701571866842001 5668433441776178900131501)
                    ·
                      refine ⟨2125662540666067087549313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5668433441776178900131501 2125662540666067087549313)
                      ·
                        rfl

theorem cell23_4139713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_4139713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139713 prefixEnd_4139713 := by exact prefixLift 4139713
  have htrace : WordTrace (prefixWord ++ tailWord_4139713) baseStart_4139713 baseEnd_4139713 := by
    simpa [prefixWord, tailWord_4139713, baseEnd_4139713] using wordTrace_append hprefix tailTrace_4139713
  have hstable : (prefixWord ++ tailWord_4139713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139713).length < 2 ^ (prefixWord ++ tailWord_4139713).sum := by decide
  have hdescent : baseEnd_4139713 < baseStart_4139713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139726 : List Nat := [4, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3]
def baseStart_4139726 : Nat := 118140960795 + 4139726 * 2 ^ 59
def prefixEnd_4139726 : Nat := 4983230072969 + 3 ^ 40 * 4139726 * 2
def baseEnd_4139726 : Nat := 2125669215914575536686753

theorem tailTrace_4139726 : CollatzResearch.WordTrace tailWord_4139726 prefixEnd_4139726 2125669215914575536686753 := by
  unfold tailWord_4139726
  simp only [CollatzResearch.WordTrace]
  refine ⟨18873526425060898219756879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100658807600324790505370021 18873526425060898219756879)
  ·
    refine ⟨28310289637591347329635319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18873526425060898219756879 28310289637591347329635319)
    ·
      refine ⟨42465434456387020994452979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28310289637591347329635319 42465434456387020994452979)
      ·
        refine ⟨63698151684580531491679469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42465434456387020994452979 63698151684580531491679469)
        ·
          refine ⟨23886806881717699309379801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63698151684580531491679469 23886806881717699309379801)
          ·
            refine ⟨17915105161288274482034851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23886806881717699309379801 17915105161288274482034851)
            ·
              refine ⟨26872657741932411723052277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17915105161288274482034851 26872657741932411723052277)
              ·
                refine ⟨2519311663306163599036151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26872657741932411723052277 2519311663306163599036151)
                ·
                  refine ⟨3778967494959245398554227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2519311663306163599036151 3778967494959245398554227)
                  ·
                    refine ⟨5668451242438868097831341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3778967494959245398554227 5668451242438868097831341)
                    ·
                      refine ⟨2125669215914575536686753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5668451242438868097831341 2125669215914575536686753)
                      ·
                        rfl

theorem cell23_4139726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_4139726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139726 prefixEnd_4139726 := by exact prefixLift 4139726
  have htrace : WordTrace (prefixWord ++ tailWord_4139726) baseStart_4139726 baseEnd_4139726 := by
    simpa [prefixWord, tailWord_4139726, baseEnd_4139726] using wordTrace_append hprefix tailTrace_4139726
  have hstable : (prefixWord ++ tailWord_4139726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139726).length < 2 ^ (prefixWord ++ tailWord_4139726).sum := by decide
  have hdescent : baseEnd_4139726 < baseStart_4139726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139762 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_4139762 : Nat := 118140960795 + 4139762 * 2 ^ 59
def prefixEnd_4139762 : Nat := 4983230072969 + 3 ^ 40 * 4139762 * 2
def baseEnd_4139762 : Nat := 2125687701218137395836587

theorem tailTrace_4139762 : CollatzResearch.WordTrace tailWord_4139762 prefixEnd_4139762 2125687701218137395836587 := by
  unfold tailWord_4139762
  simp only [CollatzResearch.WordTrace]
  refine ⟨37747381107089190976591385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100659682952237842604243693 37747381107089190976591385)
  ·
    refine ⟨28310535830316893232443539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37747381107089190976591385 28310535830316893232443539)
    ·
      refine ⟨42465803745475339848665309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28310535830316893232443539 42465803745475339848665309)
      ·
        refine ⟨15924676404553252443249491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42465803745475339848665309 15924676404553252443249491)
        ·
          refine ⟨23887014606829878664874237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15924676404553252443249491 23887014606829878664874237)
          ·
            refine ⟨8957630477561204499327839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23887014606829878664874237 8957630477561204499327839)
            ·
              refine ⟨13436445716341806748991759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8957630477561204499327839 13436445716341806748991759)
              ·
                refine ⟨20154668574512710123487639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13436445716341806748991759 20154668574512710123487639)
                ·
                  refine ⟨30232002861769065185231459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20154668574512710123487639 30232002861769065185231459)
                  ·
                    refine ⟨45348004292653597777847189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30232002861769065185231459 45348004292653597777847189)
                    ·
                      refine ⟨2125687701218137395836587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45348004292653597777847189 2125687701218137395836587)
                      ·
                        rfl

theorem cell23_4139762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_4139762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139762 prefixEnd_4139762 := by exact prefixLift 4139762
  have htrace : WordTrace (prefixWord ++ tailWord_4139762) baseStart_4139762 baseEnd_4139762 := by
    simpa [prefixWord, tailWord_4139762, baseEnd_4139762] using wordTrace_append hprefix tailTrace_4139762
  have hstable : (prefixWord ++ tailWord_4139762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139762).length < 2 ^ (prefixWord ++ tailWord_4139762).sum := by decide
  have hdescent : baseEnd_4139762 < baseStart_4139762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139766 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2]
def baseStart_4139766 : Nat := 118140960795 + 4139766 * 2 ^ 59
def prefixEnd_4139766 : Nat := 4983230072969 + 3 ^ 40 * 4139766 * 2
def baseEnd_4139766 : Nat := 2125689755140755380186569

theorem tailTrace_4139766 : CollatzResearch.WordTrace tailWord_4139766 prefixEnd_4139766 2125689755140755380186569 := by
  unfold tailWord_4139766
  simp only [CollatzResearch.WordTrace]
  refine ⟨9436854395021392036844447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100659780213561515059674101 9436854395021392036844447)
  ·
    refine ⟨14155281592532088055266671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9436854395021392036844447 14155281592532088055266671)
    ·
      refine ⟨21232922388798132082900007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14155281592532088055266671 21232922388798132082900007)
      ·
        refine ⟨31849383583197198124350011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21232922388798132082900007 31849383583197198124350011)
        ·
          refine ⟨47774075374795797186525017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31849383583197198124350011 47774075374795797186525017)
          ·
            refine ⟨35830556531096847889893763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47774075374795797186525017 35830556531096847889893763)
            ·
              refine ⟨53745834796645271834840645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35830556531096847889893763 53745834796645271834840645)
              ·
                refine ⟨10077344024370988469032621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53745834796645271834840645 10077344024370988469032621)
                ·
                  refine ⟨3779004009139120675887233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10077344024370988469032621 3779004009139120675887233)
                  ·
                    refine ⟨2834253006854340506915425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3779004009139120675887233 2834253006854340506915425)
                    ·
                      refine ⟨2125689755140755380186569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2834253006854340506915425 2125689755140755380186569)
                      ·
                        rfl

theorem cell23_4139766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_4139766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139766 prefixEnd_4139766 := by exact prefixLift 4139766
  have htrace : WordTrace (prefixWord ++ tailWord_4139766) baseStart_4139766 baseEnd_4139766 := by
    simpa [prefixWord, tailWord_4139766, baseEnd_4139766] using wordTrace_append hprefix tailTrace_4139766
  have hstable : (prefixWord ++ tailWord_4139766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139766).length < 2 ^ (prefixWord ++ tailWord_4139766).sum := by decide
  have hdescent : baseEnd_4139766 < baseStart_4139766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139772 : List Nat := [2, 2, 2, 1, 3, 2, 4, 7]
def baseStart_4139772 : Nat := 118140960795 + 4139772 * 2 ^ 59
def prefixEnd_4139772 : Nat := 4983230072969 + 3 ^ 40 * 4139772 * 2
def baseEnd_4139772 : Nat := 78729364297210457655983

theorem tailTrace_4139772 : CollatzResearch.WordTrace tailWord_4139772 prefixEnd_4139772 78729364297210457655983 := by
  unfold tailWord_4139772
  simp only [CollatzResearch.WordTrace]
  refine ⟨75494944579160267807114785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100659926105547023742819713 75494944579160267807114785)
  ·
    refine ⟨56621208434370200855336089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75494944579160267807114785 56621208434370200855336089)
    ·
      refine ⟨42465906325777650641502067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56621208434370200855336089 42465906325777650641502067)
      ·
        refine ⟨63698859488666475962253101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42465906325777650641502067 63698859488666475962253101)
        ·
          refine ⟨23887072308249928485844913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63698859488666475962253101 23887072308249928485844913)
          ·
            refine ⟨17915304231187446364383685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23887072308249928485844913 17915304231187446364383685)
            ·
              refine ⟨3359119543347646193321941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17915304231187446364383685 3359119543347646193321941)
              ·
                refine ⟨78729364297210457655983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3359119543347646193321941 78729364297210457655983)
                ·
                  rfl

theorem cell23_4139772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 7].length) (baseStart_4139772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139772 prefixEnd_4139772 := by exact prefixLift 4139772
  have htrace : WordTrace (prefixWord ++ tailWord_4139772) baseStart_4139772 baseEnd_4139772 := by
    simpa [prefixWord, tailWord_4139772, baseEnd_4139772] using wordTrace_append hprefix tailTrace_4139772
  have hstable : (prefixWord ++ tailWord_4139772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139772).length < 2 ^ (prefixWord ++ tailWord_4139772).sum := by decide
  have hdescent : baseEnd_4139772 < baseStart_4139772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139795 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 5]
def baseStart_4139795 : Nat := 118140960795 + 4139795 * 2 ^ 59
def prefixEnd_4139795 : Nat := 4983230072969 + 3 ^ 40 * 4139795 * 2
def baseEnd_4139795 : Nat := 2125704646079735766723935

theorem tailTrace_4139795 : CollatzResearch.WordTrace tailWord_4139795 prefixEnd_4139795 2125704646079735766723935 := by
  unfold tailWord_4139795
  simp only [CollatzResearch.WordTrace]
  refine ⟨150990728037237210542316839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100660485358158140361544559 150990728037237210542316839)
  ·
    refine ⟨226486092055855815813475259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150990728037237210542316839 226486092055855815813475259)
    ·
      refine ⟨339729138083783723720212889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226486092055855815813475259 339729138083783723720212889)
      ·
        refine ⟨254796853562837792790159667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339729138083783723720212889 254796853562837792790159667)
        ·
          refine ⟨382195280344256689185239501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254796853562837792790159667 382195280344256689185239501)
          ·
            refine ⟨143323230129096258444464813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382195280344256689185239501 143323230129096258444464813)
            ·
              refine ⟨53746211298411096916674305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143323230129096258444464813 53746211298411096916674305)
              ·
                refine ⟨40309658473808322687505729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53746211298411096916674305 40309658473808322687505729)
                ·
                  refine ⟨30232243855356242015629297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40309658473808322687505729 30232243855356242015629297)
                  ·
                    refine ⟨22674182891517181511721973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30232243855356242015629297 22674182891517181511721973)
                    ·
                      refine ⟨2125704646079735766723935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22674182891517181511721973 2125704646079735766723935)
                      ·
                        rfl

theorem cell23_4139795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_4139795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139795 prefixEnd_4139795 := by exact prefixLift 4139795
  have htrace : WordTrace (prefixWord ++ tailWord_4139795) baseStart_4139795 baseEnd_4139795 := by
    simpa [prefixWord, tailWord_4139795, baseEnd_4139795] using wordTrace_append hprefix tailTrace_4139795
  have hstable : (prefixWord ++ tailWord_4139795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139795).length < 2 ^ (prefixWord ++ tailWord_4139795).sum := by decide
  have hdescent : baseEnd_4139795 < baseStart_4139795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139809 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 3, 3, 2]
def baseStart_4139809 : Nat := 118140960795 + 4139809 * 2 ^ 59
def prefixEnd_4139809 : Nat := 4983230072969 + 3 ^ 40 * 4139809 * 2
def baseEnd_4139809 : Nat := 2125711834808898711948871

theorem tailTrace_4139809 : CollatzResearch.WordTrace tailWord_4139809 prefixEnd_4139809 2125711834808898711948871 := by
  unfold tailWord_4139809
  simp only [CollatzResearch.WordTrace]
  refine ⟨150991238659186490933326481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100660825772790993955550987 150991238659186490933326481)
  ·
    refine ⟨113243428994389868199994861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150991238659186490933326481 113243428994389868199994861)
    ·
      refine ⟨42466285872896200574998073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113243428994389868199994861 42466285872896200574998073)
      ·
        refine ⟨31849714404672150431248555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42466285872896200574998073 31849714404672150431248555)
        ·
          refine ⟨47774571607008225646872833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31849714404672150431248555 47774571607008225646872833)
          ·
            refine ⟨35830928705256169235154625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47774571607008225646872833 35830928705256169235154625)
            ·
              refine ⟨26873196528942126926365969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35830928705256169235154625 26873196528942126926365969)
              ·
                refine ⟨20154897396706595194774477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26873196528942126926365969 20154897396706595194774477)
                ·
                  refine ⟨7558086523764973198040429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20154897396706595194774477 7558086523764973198040429)
                  ·
                    refine ⟨2834282446411864949265161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7558086523764973198040429 2834282446411864949265161)
                    ·
                      refine ⟨2125711834808898711948871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2834282446411864949265161 2125711834808898711948871)
                      ·
                        rfl

theorem cell23_4139809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_4139809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139809 prefixEnd_4139809 := by exact prefixLift 4139809
  have htrace : WordTrace (prefixWord ++ tailWord_4139809) baseStart_4139809 baseEnd_4139809 := by
    simpa [prefixWord, tailWord_4139809, baseEnd_4139809] using wordTrace_append hprefix tailTrace_4139809
  have hstable : (prefixWord ++ tailWord_4139809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139809).length < 2 ^ (prefixWord ++ tailWord_4139809).sum := by decide
  have hdescent : baseEnd_4139809 < baseStart_4139809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139816 : List Nat := [2, 1, 5, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_4139816 : Nat := 118140960795 + 4139816 * 2 ^ 59
def prefixEnd_4139816 : Nat := 4983230072969 + 3 ^ 40 * 4139816 * 2
def baseEnd_4139816 : Nat := 2125715429173480184561339

theorem tailTrace_4139816 : CollatzResearch.WordTrace tailWord_4139816 prefixEnd_4139816 2125715429173480184561339 := by
  unfold tailWord_4139816
  simp only [CollatzResearch.WordTrace]
  refine ⟨75495746985080565564415651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100660995980107420752554201 75495746985080565564415651)
  ·
    refine ⟨113243620477620848346623477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75495746985080565564415651 113243620477620848346623477)
    ·
      refine ⟨10616589419776954532495951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113243620477620848346623477 10616589419776954532495951)
      ·
        refine ⟨15924884129665431798743927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10616589419776954532495951 15924884129665431798743927)
        ·
          refine ⟨23887326194498147698115891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15924884129665431798743927 23887326194498147698115891)
          ·
            refine ⟨35830989291747221547173837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23887326194498147698115891 35830989291747221547173837)
            ·
              refine ⟨13436620984405208080190189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35830989291747221547173837 13436620984405208080190189)
              ·
                refine ⟨5038732869151953030071321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13436620984405208080190189 5038732869151953030071321)
                ·
                  refine ⟨3779049651863964772553491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5038732869151953030071321 3779049651863964772553491)
                  ·
                    refine ⟨5668574477795947158830237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3779049651863964772553491 5668574477795947158830237)
                    ·
                      refine ⟨2125715429173480184561339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5668574477795947158830237 2125715429173480184561339)
                      ·
                        rfl

theorem cell23_4139816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_4139816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139816 prefixEnd_4139816 := by exact prefixLift 4139816
  have htrace : WordTrace (prefixWord ++ tailWord_4139816) baseStart_4139816 baseEnd_4139816 := by
    simpa [prefixWord, tailWord_4139816, baseEnd_4139816] using wordTrace_append hprefix tailTrace_4139816
  have hstable : (prefixWord ++ tailWord_4139816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139816).length < 2 ^ (prefixWord ++ tailWord_4139816).sum := by decide
  have hdescent : baseEnd_4139816 < baseStart_4139816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139839 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 3, 4, 2]
def baseStart_4139839 : Nat := 118140960795 + 4139839 * 2 ^ 59
def prefixEnd_4139839 : Nat := 4983230072969 + 3 ^ 40 * 4139839 * 2
def baseEnd_4139839 : Nat := 2125727239228533594573733

theorem tailTrace_4139839 : CollatzResearch.WordTrace tailWord_4139839 prefixEnd_4139839 2125727239228533594573733 := by
  unfold tailWord_4139839
  simp only [CollatzResearch.WordTrace]
  refine ⟨150992332849077806056918571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100661555232718537371279047 150992332849077806056918571)
  ·
    refine ⟨226488499273616709085377857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150992332849077806056918571 226488499273616709085377857)
    ·
      refine ⟨169866374455212531814033393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226488499273616709085377857 169866374455212531814033393)
      ·
        refine ⟨127399780841409398860525045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169866374455212531814033393 127399780841409398860525045)
        ·
          refine ⟨11943729453882131143174223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127399780841409398860525045 11943729453882131143174223)
          ·
            refine ⟨17915594180823196714761335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11943729453882131143174223 17915594180823196714761335)
            ·
              refine ⟨26873391271234795072142003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17915594180823196714761335 26873391271234795072142003)
              ·
                refine ⟨40310086906852192608213005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26873391271234795072142003 40310086906852192608213005)
                ·
                  refine ⟨15116282590069572228079877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40310086906852192608213005 15116282590069572228079877)
                  ·
                    refine ⟨2834302985638044792764977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15116282590069572228079877 2834302985638044792764977)
                    ·
                      refine ⟨2125727239228533594573733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2834302985638044792764977 2125727239228533594573733)
                      ·
                        rfl

theorem cell23_4139839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 4, 2].length) (baseStart_4139839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139839 prefixEnd_4139839 := by exact prefixLift 4139839
  have htrace : WordTrace (prefixWord ++ tailWord_4139839) baseStart_4139839 baseEnd_4139839 := by
    simpa [prefixWord, tailWord_4139839, baseEnd_4139839] using wordTrace_append hprefix tailTrace_4139839
  have hstable : (prefixWord ++ tailWord_4139839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139839).length < 2 ^ (prefixWord ++ tailWord_4139839).sum := by decide
  have hdescent : baseEnd_4139839 < baseStart_4139839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139845 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 11]
def baseStart_4139845 : Nat := 118140960795 + 4139845 * 2 ^ 59
def prefixEnd_4139845 : Nat := 4983230072969 + 3 ^ 40 * 4139845 * 2
def baseEnd_4139845 : Nat := 236192257790273396788745

theorem tailTrace_4139845 : CollatzResearch.WordTrace tailWord_4139845 prefixEnd_4139845 236192257790273396788745 := by
  unfold tailWord_4139845
  simp only [CollatzResearch.WordTrace]
  refine ⟨150992551687056069081636989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100661701124704046054424659 150992551687056069081636989)
  ·
    refine ⟨56622206882646025905613871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150992551687056069081636989 56622206882646025905613871)
    ·
      refine ⟨84933310323969038858420807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56622206882646025905613871 84933310323969038858420807)
      ·
        refine ⟨127399965485953558287631211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84933310323969038858420807 127399965485953558287631211)
        ·
          refine ⟨191099948228930337431446817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127399965485953558287631211 191099948228930337431446817)
          ·
            refine ⟨143324961171697753073585113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191099948228930337431446817 143324961171697753073585113)
            ·
              refine ⟨107493720878773314805188835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143324961171697753073585113 107493720878773314805188835)
              ·
                refine ⟨161240581318159972207783253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107493720878773314805188835 161240581318159972207783253)
                ·
                  refine ⟨236192257790273396788745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 161240581318159972207783253 236192257790273396788745)
                  ·
                    rfl

theorem cell23_4139845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 11].length) (baseStart_4139845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139845 prefixEnd_4139845 := by exact prefixLift 4139845
  have htrace : WordTrace (prefixWord ++ tailWord_4139845) baseStart_4139845 baseEnd_4139845 := by
    simpa [prefixWord, tailWord_4139845, baseEnd_4139845] using wordTrace_append hprefix tailTrace_4139845
  have hstable : (prefixWord ++ tailWord_4139845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139845).length < 2 ^ (prefixWord ++ tailWord_4139845).sum := by decide
  have hdescent : baseEnd_4139845 < baseStart_4139845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139856 : List Nat := [2, 1, 1, 1, 1, 4, 3, 4, 2, 2, 2]
def baseStart_4139856 : Nat := 118140960795 + 4139856 * 2 ^ 59
def prefixEnd_4139856 : Nat := 4983230072969 + 3 ^ 40 * 4139856 * 2
def baseEnd_4139856 : Nat := 2125735968399660028061155

theorem tailTrace_4139856 : CollatzResearch.WordTrace tailWord_4139856 prefixEnd_4139856 2125735968399660028061155 := by
  unfold tailWord_4139856
  simp only [CollatzResearch.WordTrace]
  refine ⟨75496476445008108980143711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100661968593344145306858281 75496476445008108980143711)
  ·
    refine ⟨113244714667512163470215567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75496476445008108980143711 113244714667512163470215567)
    ·
      refine ⟨169867072001268245205323351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113244714667512163470215567 169867072001268245205323351)
      ·
        refine ⟨254800608001902367807985027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169867072001268245205323351 254800608001902367807985027)
        ·
          refine ⟨382200912002853551711977541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254800608001902367807985027 382200912002853551711977541)
          ·
            refine ⟨71662671000535040945995789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 382200912002853551711977541 71662671000535040945995789)
            ·
              refine ⟨26873501625200640354748421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71662671000535040945995789 26873501625200640354748421)
              ·
                refine ⟨5038781554725120066515329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26873501625200640354748421 5038781554725120066515329)
                ·
                  refine ⟨3779086166043840049886497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5038781554725120066515329 3779086166043840049886497)
                  ·
                    refine ⟨2834314624532880037414873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3779086166043840049886497 2834314624532880037414873)
                    ·
                      refine ⟨2125735968399660028061155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2834314624532880037414873 2125735968399660028061155)
                      ·
                        rfl

theorem cell23_4139856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 2, 2, 2].length) (baseStart_4139856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139856 prefixEnd_4139856 := by exact prefixLift 4139856
  have htrace : WordTrace (prefixWord ++ tailWord_4139856) baseStart_4139856 baseEnd_4139856 := by
    simpa [prefixWord, tailWord_4139856, baseEnd_4139856] using wordTrace_append hprefix tailTrace_4139856
  have hstable : (prefixWord ++ tailWord_4139856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139856).length < 2 ^ (prefixWord ++ tailWord_4139856).sum := by decide
  have hdescent : baseEnd_4139856 < baseStart_4139856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139939 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 3, 4]
def baseStart_4139939 : Nat := 118140960795 + 4139939 * 2 ^ 59
def prefixEnd_4139939 : Nat := 4983230072969 + 3 ^ 40 * 4139939 * 2
def baseEnd_4139939 : Nat := 708592862431327734441091

theorem tailTrace_4139939 : CollatzResearch.WordTrace tailWord_4139939 prefixEnd_4139939 708592862431327734441091 := by
  unfold tailWord_4139939
  simp only [CollatzResearch.WordTrace]
  refine ⟨150995980148715523135558871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100663986765810348757039247 150995980148715523135558871)
  ·
    refine ⟨226493970223073284703338307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150995980148715523135558871 226493970223073284703338307)
    ·
      refine ⟨339740955334609927055007461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226493970223073284703338307 339740955334609927055007461)
      ·
        refine ⟨63701429125239361322813899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339740955334609927055007461 63701429125239361322813899)
        ·
          refine ⟨95552143687859041984220849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63701429125239361322813899 95552143687859041984220849)
          ·
            refine ⟨71664107765894281488165637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95552143687859041984220849 71664107765894281488165637)
            ·
              refine ⟨13437020206105177779031057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71664107765894281488165637 13437020206105177779031057)
              ·
                refine ⟨10077765154578883334273293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13437020206105177779031057 10077765154578883334273293)
                ·
                  refine ⟨3779161932967081250352485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10077765154578883334273293 3779161932967081250352485)
                  ·
                    refine ⟨708592862431327734441091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3779161932967081250352485 708592862431327734441091)
                    ·
                      rfl

theorem cell23_4139939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 4].length) (baseStart_4139939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139939 prefixEnd_4139939 := by exact prefixLift 4139939
  have htrace : WordTrace (prefixWord ++ tailWord_4139939) baseStart_4139939 baseEnd_4139939 := by
    simpa [prefixWord, tailWord_4139939, baseEnd_4139939] using wordTrace_append hprefix tailTrace_4139939
  have hstable : (prefixWord ++ tailWord_4139939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139939).length < 2 ^ (prefixWord ++ tailWord_4139939).sum := by decide
  have hdescent : baseEnd_4139939 < baseStart_4139939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139966 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_4139966 : Nat := 118140960795 + 4139966 * 2 ^ 59
def prefixEnd_4139966 : Nat := 4983230072969 + 3 ^ 40 * 4139966 * 2
def baseEnd_4139966 : Nat := 2125792451271654597685649

theorem tailTrace_4139966 : CollatzResearch.WordTrace tailWord_4139966 prefixEnd_4139966 2125792451271654597685649 := by
  unfold tailWord_4139966
  simp only [CollatzResearch.WordTrace]
  refine ⟨18874620614952213343348969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100664643279745137831194501 18874620614952213343348969)
  ·
    refine ⟨14155965461214160007511727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18874620614952213343348969 14155965461214160007511727)
    ·
      refine ⟨21233948191821240011267591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14155965461214160007511727 21233948191821240011267591)
      ·
        refine ⟨31850922287731860016901387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21233948191821240011267591 31850922287731860016901387)
        ·
          refine ⟨47776383431597790025352081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31850922287731860016901387 47776383431597790025352081)
          ·
            refine ⟨35832287573698342519014061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47776383431597790025352081 35832287573698342519014061)
            ·
              refine ⟨13437107840136878444630273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35832287573698342519014061 13437107840136878444630273)
              ·
                refine ⟨10077830880102658833472705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13437107840136878444630273 10077830880102658833472705)
                ·
                  refine ⟨7558373160076994125104529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10077830880102658833472705 7558373160076994125104529)
                  ·
                    refine ⟨5668779870057745593828397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7558373160076994125104529 5668779870057745593828397)
                    ·
                      refine ⟨2125792451271654597685649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5668779870057745593828397 2125792451271654597685649)
                      ·
                        rfl

theorem cell23_4139966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_4139966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139966 prefixEnd_4139966 := by exact prefixLift 4139966
  have htrace : WordTrace (prefixWord ++ tailWord_4139966) baseStart_4139966 baseEnd_4139966 := by
    simpa [prefixWord, tailWord_4139966, baseEnd_4139966] using wordTrace_append hprefix tailTrace_4139966
  have hstable : (prefixWord ++ tailWord_4139966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139966).length < 2 ^ (prefixWord ++ tailWord_4139966).sum := by decide
  have hdescent : baseEnd_4139966 < baseStart_4139966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139986 : List Nat := [3, 2, 2, 3, 1, 2, 1, 3, 6]
def baseStart_4139986 : Nat := 118140960795 + 4139986 * 2 ^ 59
def prefixEnd_4139986 : Nat := 4983230072969 + 3 ^ 40 * 4139986 * 2
def baseEnd_4139986 : Nat := 236200302320527168826173

theorem tailTrace_4139986 : CollatzResearch.WordTrace tailWord_4139986 prefixEnd_4139986 236200302320527168826173 := by
  unfold tailWord_4139986
  simp only [CollatzResearch.WordTrace]
  refine ⟨37749423594886312540629953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100665129586363500108346541 37749423594886312540629953)
  ·
    refine ⟨28312067696164734405472465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37749423594886312540629953 28312067696164734405472465)
    ·
      refine ⟨21234050772123550804104349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28312067696164734405472465 21234050772123550804104349)
      ·
        refine ⟨7962769039546331551539131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21234050772123550804104349 7962769039546331551539131)
        ·
          refine ⟨11944153559319497327308697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7962769039546331551539131 11944153559319497327308697)
          ·
            refine ⟨8958115169489622995481523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11944153559319497327308697 8958115169489622995481523)
            ·
              refine ⟨13437172754234434493222285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8958115169489622995481523 13437172754234434493222285)
              ·
                refine ⟨5038939782837912934958357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13437172754234434493222285 5038939782837912934958357)
                ·
                  refine ⟨236200302320527168826173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5038939782837912934958357 236200302320527168826173)
                  ·
                    rfl

theorem cell23_4139986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_4139986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4139986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4139986 prefixEnd_4139986 := by exact prefixLift 4139986
  have htrace : WordTrace (prefixWord ++ tailWord_4139986) baseStart_4139986 baseEnd_4139986 := by
    simpa [prefixWord, tailWord_4139986, baseEnd_4139986] using wordTrace_append hprefix tailTrace_4139986
  have hstable : (prefixWord ++ tailWord_4139986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139986).length < 2 ^ (prefixWord ++ tailWord_4139986).sum := by decide
  have hdescent : baseEnd_4139986 < baseStart_4139986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140039 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_4140039 : Nat := 118140960795 + 4140039 * 2 ^ 59
def prefixEnd_4140039 : Nat := 4983230072969 + 3 ^ 40 * 4140039 * 2
def baseEnd_4140039 : Nat := 2125829935359432812072813

theorem tailTrace_4140039 : CollatzResearch.WordTrace tailWord_4140039 prefixEnd_4140039 2125829935359432812072813 := by
  unfold tailWord_4140039
  simp only [CollatzResearch.WordTrace]
  refine ⟨150999627448353240214199171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100666418298902160142799447 150999627448353240214199171)
  ·
    refine ⟨226499441172529860321298757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150999627448353240214199171 226499441172529860321298757)
    ·
      refine ⟨42468645219849348810243517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226499441172529860321298757 42468645219849348810243517)
      ·
        refine ⟨15925741957443505803841319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42468645219849348810243517 15925741957443505803841319)
        ·
          refine ⟨23888612936165258705761979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15925741957443505803841319 23888612936165258705761979)
          ·
            refine ⟨35832919404247888058642969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23888612936165258705761979 35832919404247888058642969)
            ·
              refine ⟨26874689553185916043982227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35832919404247888058642969 26874689553185916043982227)
              ·
                refine ⟨40312034329778874065973341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26874689553185916043982227 40312034329778874065973341)
                ·
                  refine ⟨15117012873667077774740003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40312034329778874065973341 15117012873667077774740003)
                  ·
                    refine ⟨22675519310500616662110005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15117012873667077774740003 22675519310500616662110005)
                    ·
                      refine ⟨2125829935359432812072813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22675519310500616662110005 2125829935359432812072813)
                      ·
                        rfl

theorem cell23_4140039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_4140039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140039 prefixEnd_4140039 := by exact prefixLift 4140039
  have htrace : WordTrace (prefixWord ++ tailWord_4140039) baseStart_4140039 baseEnd_4140039 := by
    simpa [prefixWord, tailWord_4140039, baseEnd_4140039] using wordTrace_append hprefix tailTrace_4140039
  have hstable : (prefixWord ++ tailWord_4140039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140039).length < 2 ^ (prefixWord ++ tailWord_4140039).sum := by decide
  have hdescent : baseEnd_4140039 < baseStart_4140039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140046 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 1, 6]
def baseStart_4140046 : Nat := 118140960795 + 4140046 * 2 ^ 59
def prefixEnd_4140046 : Nat := 4983230072969 + 3 ^ 40 * 4140046 * 2
def baseEnd_4140046 : Nat := 708611176574671428228427

theorem tailTrace_4140046 : CollatzResearch.WordTrace tailWord_4140046 prefixEnd_4140046 708611176574671428228427 := by
  unfold tailWord_4140046
  simp only [CollatzResearch.WordTrace]
  refine ⟨18874985344915985051212999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100666588506218586939802661 18874985344915985051212999)
  ·
    refine ⟨28312478017373977576819499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18874985344915985051212999 28312478017373977576819499)
    ·
      refine ⟨42468717026060966365229249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28312478017373977576819499 42468717026060966365229249)
      ·
        refine ⟨31851537769545724773921937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42468717026060966365229249 31851537769545724773921937)
        ·
          refine ⟨23888653327159293580441453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31851537769545724773921937 23888653327159293580441453)
          ·
            refine ⟨8958244997684735092665545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23888653327159293580441453 8958244997684735092665545)
            ·
              refine ⟨6718683748263551319499159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8958244997684735092665545 6718683748263551319499159)
              ·
                refine ⟨10078025622395326979248739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6718683748263551319499159 10078025622395326979248739)
                ·
                  refine ⟨15117038433592990468873109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10078025622395326979248739 15117038433592990468873109)
                  ·
                    refine ⟨708611176574671428228427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15117038433592990468873109 708611176574671428228427)
                    ·
                      rfl

theorem cell23_4140046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_4140046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140046 prefixEnd_4140046 := by exact prefixLift 4140046
  have htrace : WordTrace (prefixWord ++ tailWord_4140046) baseStart_4140046 baseEnd_4140046 := by
    simpa [prefixWord, tailWord_4140046, baseEnd_4140046] using wordTrace_append hprefix tailTrace_4140046
  have hstable : (prefixWord ++ tailWord_4140046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140046).length < 2 ^ (prefixWord ++ tailWord_4140046).sum := by decide
  have hdescent : baseEnd_4140046 < baseStart_4140046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140053 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 5, 2, 2]
def baseStart_4140053 : Nat := 118140960795 + 4140053 * 2 ^ 59
def prefixEnd_4140053 : Nat := 4983230072969 + 3 ^ 40 * 4140053 * 2
def baseEnd_4140053 : Nat := 2125837124088595757297749

theorem tailTrace_4140053 : CollatzResearch.WordTrace tailWord_4140053 prefixEnd_4140053 2125837124088595757297749 := by
  unfold tailWord_4140053
  simp only [CollatzResearch.WordTrace]
  refine ⟨151000138070302520605208813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100666758713535013736805875 151000138070302520605208813)
  ·
    refine ⟨56625051776363445226953305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151000138070302520605208813 56625051776363445226953305)
    ·
      refine ⟨42468788832272583920214979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56625051776363445226953305 42468788832272583920214979)
      ·
        refine ⟨63703183248408875880322469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42468788832272583920214979 63703183248408875880322469)
        ·
          refine ⟨11944346859076664227560463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63703183248408875880322469 11944346859076664227560463)
          ·
            refine ⟨17916520288614996341340695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11944346859076664227560463 17916520288614996341340695)
            ·
              refine ⟨26874780432922494512011043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17916520288614996341340695 26874780432922494512011043)
              ·
                refine ⟨40312170649383741768016565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26874780432922494512011043 40312170649383741768016565)
                ·
                  refine ⟨3779265998379725790751553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40312170649383741768016565 3779265998379725790751553)
                  ·
                    refine ⟨2834449498784794343063665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3779265998379725790751553 2834449498784794343063665)
                    ·
                      refine ⟨2125837124088595757297749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2834449498784794343063665 2125837124088595757297749)
                      ·
                        rfl

theorem cell23_4140053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_4140053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140053 prefixEnd_4140053 := by exact prefixLift 4140053
  have htrace : WordTrace (prefixWord ++ tailWord_4140053) baseStart_4140053 baseEnd_4140053 := by
    simpa [prefixWord, tailWord_4140053, baseEnd_4140053] using wordTrace_append hprefix tailTrace_4140053
  have hstable : (prefixWord ++ tailWord_4140053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140053).length < 2 ^ (prefixWord ++ tailWord_4140053).sum := by decide
  have hdescent : baseEnd_4140053 < baseStart_4140053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140056 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 3, 2, 3]
def baseStart_4140056 : Nat := 118140960795 + 4140056 * 2 ^ 59
def prefixEnd_4140056 : Nat := 4983230072969 + 3 ^ 40 * 4140056 * 2
def baseEnd_4140056 : Nat := 2125838664530559245560235

theorem tailTrace_4140056 : CollatzResearch.WordTrace tailWord_4140056 prefixEnd_4140056 2125838664530559245560235 := by
  unfold tailWord_4140056
  simp only [CollatzResearch.WordTrace]
  refine ⟨75500123744645826058784011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100666831659527768078378681 75500123744645826058784011)
  ·
    refine ⟨113250185616968739088176017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75500123744645826058784011 113250185616968739088176017)
    ·
      refine ⟨84937639212726554316132013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113250185616968739088176017 84937639212726554316132013)
      ·
        refine ⟨31851614704772457868549505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84937639212726554316132013 31851614704772457868549505)
        ·
          refine ⟨23888711028579343401412129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31851614704772457868549505 23888711028579343401412129)
          ·
            refine ⟨17916533271434507551059097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23888711028579343401412129 17916533271434507551059097)
            ·
              refine ⟨13437399953575880663294323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17916533271434507551059097 13437399953575880663294323)
              ·
                refine ⟨20156099930363820994941485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13437399953575880663294323 20156099930363820994941485)
                ·
                  refine ⟨7558537473886432873103057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20156099930363820994941485 7558537473886432873103057)
                  ·
                    refine ⟨5668903105414824654827293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7558537473886432873103057 5668903105414824654827293)
                    ·
                      refine ⟨2125838664530559245560235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5668903105414824654827293 2125838664530559245560235)
                      ·
                        rfl

theorem cell23_4140056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_4140056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140056 prefixEnd_4140056 := by exact prefixLift 4140056
  have htrace : WordTrace (prefixWord ++ tailWord_4140056) baseStart_4140056 baseEnd_4140056 := by
    simpa [prefixWord, tailWord_4140056, baseEnd_4140056] using wordTrace_append hprefix tailTrace_4140056
  have hstable : (prefixWord ++ tailWord_4140056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140056).length < 2 ^ (prefixWord ++ tailWord_4140056).sum := by decide
  have hdescent : baseEnd_4140056 < baseStart_4140056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140066 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_4140066 : Nat := 118140960795 + 4140066 * 2 ^ 59
def prefixEnd_4140066 : Nat := 4983230072969 + 3 ^ 40 * 4140066 * 2
def baseEnd_4140066 : Nat := 2125843799337104206435189

theorem tailTrace_4140066 : CollatzResearch.WordTrace tailWord_4140066 prefixEnd_4140066 2125843799337104206435189 := by
  unfold tailWord_4140066
  simp only [CollatzResearch.WordTrace]
  refine ⟨37750153054813855956358013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100667074812836949216954701 37750153054813855956358013)
  ·
    refine ⟨14156307395555195983634255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37750153054813855956358013 14156307395555195983634255)
    ·
      refine ⟨21234461093332793975451383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14156307395555195983634255 21234461093332793975451383)
      ·
        refine ⟨31851691639999190963177075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21234461093332793975451383 31851691639999190963177075)
        ·
          refine ⟨47777537459998786444765613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31851691639999190963177075 47777537459998786444765613)
          ·
            refine ⟨17916576547499544916787105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47777537459998786444765613 17916576547499544916787105)
            ·
              refine ⟨13437432410624658687590329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17916576547499544916787105 13437432410624658687590329)
              ·
                refine ⟨10078074307968494015692747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13437432410624658687590329 10078074307968494015692747)
                ·
                  refine ⟨15117111461952741023539121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10078074307968494015692747 15117111461952741023539121)
                  ·
                    refine ⟨11337833596464555767654341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15117111461952741023539121 11337833596464555767654341)
                    ·
                      refine ⟨2125843799337104206435189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11337833596464555767654341 2125843799337104206435189)
                      ·
                        rfl

theorem cell23_4140066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_4140066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140066 prefixEnd_4140066 := by exact prefixLift 4140066
  have htrace : WordTrace (prefixWord ++ tailWord_4140066) baseStart_4140066 baseEnd_4140066 := by
    simpa [prefixWord, tailWord_4140066, baseEnd_4140066] using wordTrace_append hprefix tailTrace_4140066
  have hstable : (prefixWord ++ tailWord_4140066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140066).length < 2 ^ (prefixWord ++ tailWord_4140066).sum := by decide
  have hdescent : baseEnd_4140066 < baseStart_4140066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140103 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 1, 3, 3]
def baseStart_4140103 : Nat := 118140960795 + 4140103 * 2 ^ 59
def prefixEnd_4140103 : Nat := 4983230072969 + 3 ^ 40 * 4140103 * 2
def baseEnd_4140103 : Nat := 2125862798121320561672519

theorem tailTrace_4140103 : CollatzResearch.WordTrace tailWord_4140103 prefixEnd_4140103 2125862798121320561672519 := by
  unfold tailWord_4140103
  simp only [CollatzResearch.WordTrace]
  refine ⟨151001961720121379144528963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100667974480080919429685975 151001961720121379144528963)
  ·
    refine ⟨226502942580182068716793445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151001961720121379144528963 226502942580182068716793445)
    ·
      refine ⟨42469301733784137884398771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226502942580182068716793445 42469301733784137884398771)
      ·
        refine ⟨63703952600676206826598157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42469301733784137884398771 63703952600676206826598157)
        ·
          refine ⟨23888982225253577559974309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63703952600676206826598157 23888982225253577559974309)
          ·
            refine ⟨4479184167235045792495183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23888982225253577559974309 4479184167235045792495183)
            ·
              refine ⟨6718776250852568688742775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4479184167235045792495183 6718776250852568688742775)
              ·
                refine ⟨10078164376278853033114163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6718776250852568688742775 10078164376278853033114163)
                ·
                  refine ⟨15117246564418279549671245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10078164376278853033114163 15117246564418279549671245)
                  ·
                    refine ⟨5668967461656854831126717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15117246564418279549671245 5668967461656854831126717)
                    ·
                      refine ⟨2125862798121320561672519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5668967461656854831126717 2125862798121320561672519)
                      ·
                        rfl

theorem cell23_4140103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_4140103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140103 prefixEnd_4140103 := by exact prefixLift 4140103
  have htrace : WordTrace (prefixWord ++ tailWord_4140103) baseStart_4140103 baseEnd_4140103 := by
    simpa [prefixWord, tailWord_4140103, baseEnd_4140103] using wordTrace_append hprefix tailTrace_4140103
  have hstable : (prefixWord ++ tailWord_4140103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140103).length < 2 ^ (prefixWord ++ tailWord_4140103).sum := by decide
  have hdescent : baseEnd_4140103 < baseStart_4140103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140113 : List Nat := [1, 2, 2, 1, 3, 1, 3, 4, 1, 3, 2]
def baseStart_4140113 : Nat := 118140960795 + 4140113 * 2 ^ 59
def prefixEnd_4140113 : Nat := 4983230072969 + 3 ^ 40 * 4140113 * 2
def baseEnd_4140113 : Nat := 2125867932927865522547473

theorem tailTrace_4140113 : CollatzResearch.WordTrace tailWord_4140113 prefixEnd_4140113 2125867932927865522547473 := by
  unfold tailWord_4140113
  simp only [CollatzResearch.WordTrace]
  refine ⟨151002326450085150852392993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100668217633390100568261995 151002326450085150852392993)
  ·
    refine ⟨113251744837563863139294745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151002326450085150852392993 113251744837563863139294745)
    ·
      refine ⟨84938808628172897354471059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113251744837563863139294745 84938808628172897354471059)
      ·
        refine ⟨127408212942259346031706589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84938808628172897354471059 127408212942259346031706589)
        ·
          refine ⟨47778079853347254761889971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127408212942259346031706589 47778079853347254761889971)
          ·
            refine ⟨71667119780020882142834957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47778079853347254761889971 71667119780020882142834957)
            ·
              refine ⟨26875169917507830803563109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71667119780020882142834957 26875169917507830803563109)
              ·
                refine ⟨5039094359532718275668083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26875169917507830803563109 5039094359532718275668083)
                ·
                  refine ⟨7558641539299077413502125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5039094359532718275668083 7558641539299077413502125)
                  ·
                    refine ⟨2834490577237154030063297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7558641539299077413502125 2834490577237154030063297)
                    ·
                      refine ⟨2125867932927865522547473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2834490577237154030063297 2125867932927865522547473)
                      ·
                        rfl

theorem cell23_4140113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 3, 2].length) (baseStart_4140113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140113 prefixEnd_4140113 := by exact prefixLift 4140113
  have htrace : WordTrace (prefixWord ++ tailWord_4140113) baseStart_4140113 baseEnd_4140113 := by
    simpa [prefixWord, tailWord_4140113, baseEnd_4140113] using wordTrace_append hprefix tailTrace_4140113
  have hstable : (prefixWord ++ tailWord_4140113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140113).length < 2 ^ (prefixWord ++ tailWord_4140113).sum := by decide
  have hdescent : baseEnd_4140113 < baseStart_4140113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140129 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_4140129 : Nat := 118140960795 + 4140129 * 2 ^ 59
def prefixEnd_4140129 : Nat := 4983230072969 + 3 ^ 40 * 4140129 * 2
def baseEnd_4140129 : Nat := 2125876148618337459947399

theorem tailTrace_4140129 : CollatzResearch.WordTrace tailWord_4140129 prefixEnd_4140129 2125876148618337459947399 := by
  unfold tailWord_4140129
  simp only [CollatzResearch.WordTrace]
  refine ⟨151002910018027185584975441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100668606678684790389983627 151002910018027185584975441)
  ·
    refine ⟨113252182513520389188731581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151002910018027185584975441 113252182513520389188731581)
    ·
      refine ⟨42469568442570145945774343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113252182513520389188731581 42469568442570145945774343)
      ·
        refine ⟨63704352663855218918661515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42469568442570145945774343 63704352663855218918661515)
        ·
          refine ⟨95556528995782828377992273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63704352663855218918661515 95556528995782828377992273)
          ·
            refine ⟨71667396746837121283494205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95556528995782828377992273 71667396746837121283494205)
            ·
              refine ⟨26875273780063920481310327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71667396746837121283494205 26875273780063920481310327)
              ·
                refine ⟨40312910670095880721965491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26875273780063920481310327 40312910670095880721965491)
                ·
                  refine ⟨60469366005143821082948237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40312910670095880721965491 60469366005143821082948237)
                  ·
                    refine ⟨22676012251928932906105589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60469366005143821082948237 22676012251928932906105589)
                    ·
                      refine ⟨2125876148618337459947399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22676012251928932906105589 2125876148618337459947399)
                      ·
                        rfl

theorem cell23_4140129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_4140129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140129 prefixEnd_4140129 := by exact prefixLift 4140129
  have htrace : WordTrace (prefixWord ++ tailWord_4140129) baseStart_4140129 baseEnd_4140129 := by
    simpa [prefixWord, tailWord_4140129, baseEnd_4140129] using wordTrace_append hprefix tailTrace_4140129
  have hstable : (prefixWord ++ tailWord_4140129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140129).length < 2 ^ (prefixWord ++ tailWord_4140129).sum := by decide
  have hdescent : baseEnd_4140129 < baseStart_4140129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140143 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 4, 2, 2]
def baseStart_4140143 : Nat := 118140960795 + 4140143 * 2 ^ 59
def prefixEnd_4140143 : Nat := 4983230072969 + 3 ^ 40 * 4140143 * 2
def baseEnd_4140143 : Nat := 2125883337347500405172335

theorem tailTrace_4140143 : CollatzResearch.WordTrace tailWord_4140143 prefixEnd_4140143 2125883337347500405172335 := by
  unfold tailWord_4140143
  simp only [CollatzResearch.WordTrace]
  refine ⟨151003420639976465975985083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100668947093317643983990055 151003420639976465975985083)
  ·
    refine ⟨226505130959964698963977625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151003420639976465975985083 226505130959964698963977625)
    ·
      refine ⟨169878848219973524222983219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226505130959964698963977625 169878848219973524222983219)
      ·
        refine ⟨254818272329960286334474829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169878848219973524222983219 254818272329960286334474829)
        ·
          refine ⟨95556852123735107375428061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254818272329960286334474829 95556852123735107375428061)
          ·
            refine ⟨35833819546400665265785523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95556852123735107375428061 35833819546400665265785523)
            ·
              refine ⟨53750729319600997898678285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35833819546400665265785523 53750729319600997898678285)
              ·
                refine ⟨20156523494850374212004357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53750729319600997898678285 20156523494850374212004357)
                ·
                  refine ⟨3779348155284445164750817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20156523494850374212004357 3779348155284445164750817)
                  ·
                    refine ⟨2834511116463333873563113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3779348155284445164750817 2834511116463333873563113)
                    ·
                      refine ⟨2125883337347500405172335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2834511116463333873563113 2125883337347500405172335)
                      ·
                        rfl

theorem cell23_4140143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 2, 2].length) (baseStart_4140143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140143 prefixEnd_4140143 := by exact prefixLift 4140143
  have htrace : WordTrace (prefixWord ++ tailWord_4140143) baseStart_4140143 baseEnd_4140143 := by
    simpa [prefixWord, tailWord_4140143, baseEnd_4140143] using wordTrace_append hprefix tailTrace_4140143
  have hstable : (prefixWord ++ tailWord_4140143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140143).length < 2 ^ (prefixWord ++ tailWord_4140143).sum := by decide
  have hdescent : baseEnd_4140143 < baseStart_4140143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140146 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 2, 4, 3]
def baseStart_4140146 : Nat := 118140960795 + 4140146 * 2 ^ 59
def prefixEnd_4140146 : Nat := 4983230072969 + 3 ^ 40 * 4140146 * 2
def baseEnd_4140146 : Nat := 2125884877789463893434821

theorem tailTrace_4140146 : CollatzResearch.WordTrace tailWord_4140146 prefixEnd_4140146 2125884877789463893434821 := by
  unfold tailWord_4140146
  simp only [CollatzResearch.WordTrace]
  refine ⟨37750882514741399372086073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100669020039310398325562861 37750882514741399372086073)
  ·
    refine ⟨28313161886056049529064555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37750882514741399372086073 28313161886056049529064555)
    ·
      refine ⟨42469742829084074293596833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28313161886056049529064555 42469742829084074293596833)
      ·
        refine ⟨31852307121813055720197625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42469742829084074293596833 31852307121813055720197625)
        ·
          refine ⟨23889230341359791790148219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31852307121813055720197625 23889230341359791790148219)
          ·
            refine ⟨35833845512039687685222329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23889230341359791790148219 35833845512039687685222329)
            ·
              refine ⟨26875384134029765763916747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35833845512039687685222329 26875384134029765763916747)
              ·
                refine ⟨40313076201044648645875121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26875384134029765763916747 40313076201044648645875121)
                ·
                  refine ⟨30234807150783486484406341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40313076201044648645875121 30234807150783486484406341)
                  ·
                    refine ⟨5669026340771903715826189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30234807150783486484406341 5669026340771903715826189)
                    ·
                      refine ⟨2125884877789463893434821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5669026340771903715826189 2125884877789463893434821)
                      ·
                        rfl

theorem cell23_4140146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_4140146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140146 prefixEnd_4140146 := by exact prefixLift 4140146
  have htrace : WordTrace (prefixWord ++ tailWord_4140146) baseStart_4140146 baseEnd_4140146 := by
    simpa [prefixWord, tailWord_4140146, baseEnd_4140146] using wordTrace_append hprefix tailTrace_4140146
  have hstable : (prefixWord ++ tailWord_4140146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140146).length < 2 ^ (prefixWord ++ tailWord_4140146).sum := by decide
  have hdescent : baseEnd_4140146 < baseStart_4140146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140179 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 1, 7]
def baseStart_4140179 : Nat := 118140960795 + 4140179 * 2 ^ 59
def prefixEnd_4140179 : Nat := 4983230072969 + 3 ^ 40 * 4140179 * 2
def baseEnd_4140179 : Nat := 708633940883687421440723

theorem tailTrace_4140179 : CollatzResearch.WordTrace tailWord_4140179 prefixEnd_4140179 708633940883687421440723 := by
  unfold tailWord_4140179
  simp only [CollatzResearch.WordTrace]
  refine ⟨151004733667846044124295591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100669822445230696082863727 151004733667846044124295591)
  ·
    refine ⟨226507100501769066186443387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151004733667846044124295591 226507100501769066186443387)
    ·
      refine ⟨339760650752653599279665081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226507100501769066186443387 339760650752653599279665081)
      ·
        refine ⟨254820488064490199459748811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339760650752653599279665081 254820488064490199459748811)
        ·
          refine ⟨382230732096735299189623217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254820488064490199459748811 382230732096735299189623217)
          ·
            refine ⟨286673049072551474392217413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382230732096735299189623217 286673049072551474392217413)
            ·
              refine ⟨53751196701103401448540765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286673049072551474392217413 53751196701103401448540765)
              ·
                refine ⟨20156698762913775543202787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53751196701103401448540765 20156698762913775543202787)
                ·
                  refine ⟨30235048144370663314804181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20156698762913775543202787 30235048144370663314804181)
                  ·
                    refine ⟨708633940883687421440723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30235048144370663314804181 708633940883687421440723)
                    ·
                      rfl

theorem cell23_4140179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 7].length) (baseStart_4140179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140179 prefixEnd_4140179 := by exact prefixLift 4140179
  have htrace : WordTrace (prefixWord ++ tailWord_4140179) baseStart_4140179 baseEnd_4140179 := by
    simpa [prefixWord, tailWord_4140179, baseEnd_4140179] using wordTrace_append hprefix tailTrace_4140179
  have hstable : (prefixWord ++ tailWord_4140179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140179).length < 2 ^ (prefixWord ++ tailWord_4140179).sum := by decide
  have hdescent : baseEnd_4140179 < baseStart_4140179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140194 : List Nat := [3, 3, 1, 3, 2, 1, 2, 2, 2, 2, 2]
def baseStart_4140194 : Nat := 118140960795 + 4140194 * 2 ^ 59
def prefixEnd_4140194 : Nat := 4983230072969 + 3 ^ 40 * 4140194 * 2
def baseEnd_4140194 : Nat := 2125909524860879705634601

theorem tailTrace_4140194 : CollatzResearch.WordTrace tailWord_4140194 prefixEnd_4140194 2125909524860879705634601 := by
  unfold tailWord_4140194
  simp only [CollatzResearch.WordTrace]
  refine ⟨37751320190697925421522909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100670187175194467790727757 37751320190697925421522909)
  ·
    refine ⟨14156745071511722033071091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37751320190697925421522909 14156745071511722033071091)
    ·
      refine ⟨21235117607267583049606637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14156745071511722033071091 21235117607267583049606637)
      ·
        refine ⟨7963169102725343643602489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21235117607267583049606637 7963169102725343643602489)
        ·
          refine ⟨5972376827044007732701867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7963169102725343643602489 5972376827044007732701867)
          ·
            refine ⟨8958565240566011599052801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5972376827044007732701867 8958565240566011599052801)
            ·
              refine ⟨6718923930424508699289601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8958565240566011599052801 6718923930424508699289601)
              ·
                refine ⟨5039192947818381524467201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6718923930424508699289601 5039192947818381524467201)
                ·
                  refine ⟨3779394710863786143350401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5039192947818381524467201 3779394710863786143350401)
                  ·
                    refine ⟨2834546033147839607512801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3779394710863786143350401 2834546033147839607512801)
                    ·
                      refine ⟨2125909524860879705634601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2834546033147839607512801 2125909524860879705634601)
                      ·
                        rfl

theorem cell23_4140194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_4140194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140194 prefixEnd_4140194 := by exact prefixLift 4140194
  have htrace : WordTrace (prefixWord ++ tailWord_4140194) baseStart_4140194 baseEnd_4140194 := by
    simpa [prefixWord, tailWord_4140194, baseEnd_4140194] using wordTrace_append hprefix tailTrace_4140194
  have hstable : (prefixWord ++ tailWord_4140194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140194).length < 2 ^ (prefixWord ++ tailWord_4140194).sum := by decide
  have hdescent : baseEnd_4140194 < baseStart_4140194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140256 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 8]
def baseStart_4140256 : Nat := 118140960795 + 4140256 * 2 ^ 59
def prefixEnd_4140256 : Nat := 4983230072969 + 3 ^ 40 * 4140256 * 2
def baseEnd_4140256 : Nat := 236215706740162051451035

theorem tailTrace_4140256 : CollatzResearch.WordTrace tailWord_4140256 prefixEnd_4140256 236215706740162051451035 := by
  unfold tailWord_4140256
  simp only [CollatzResearch.WordTrace]
  refine ⟨75503771044283543137424311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100671694725711390849899081 75503771044283543137424311)
  ·
    refine ⟨113255656566425314706136467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75503771044283543137424311 113255656566425314706136467)
    ·
      refine ⟨169883484849637972059204701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113255656566425314706136467 169883484849637972059204701)
      ·
        refine ⟨63706306818614239522201763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169883484849637972059204701 63706306818614239522201763)
        ·
          refine ⟨95559460227921359283302645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63706306818614239522201763 95559460227921359283302645)
          ·
            refine ⟨8958699396367627432809623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95559460227921359283302645 8958699396367627432809623)
            ·
              refine ⟨13438049094551441149214435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8958699396367627432809623 13438049094551441149214435)
              ·
                refine ⟨20157073641827161723821653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13438049094551441149214435 20157073641827161723821653)
                ·
                  refine ⟨236215706740162051451035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20157073641827161723821653 236215706740162051451035)
                  ·
                    rfl

theorem cell23_4140256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 8].length) (baseStart_4140256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140256 prefixEnd_4140256 := by exact prefixLift 4140256
  have htrace : WordTrace (prefixWord ++ tailWord_4140256) baseStart_4140256 baseEnd_4140256 := by
    simpa [prefixWord, tailWord_4140256, baseEnd_4140256] using wordTrace_append hprefix tailTrace_4140256
  have hstable : (prefixWord ++ tailWord_4140256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140256).length < 2 ^ (prefixWord ++ tailWord_4140256).sum := by decide
  have hdescent : baseEnd_4140256 < baseStart_4140256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140260 : List Nat := [2, 3, 1, 1, 1, 2, 4, 4, 1, 4]
def baseStart_4140260 : Nat := 118140960795 + 4140260 * 2 ^ 59
def prefixEnd_4140260 : Nat := 4983230072969 + 3 ^ 40 * 4140260 * 2
def baseEnd_4140260 : Nat := 708647804861358815803099

theorem tailTrace_4140260 : CollatzResearch.WordTrace tailWord_4140260 prefixEnd_4140260 708647804861358815803099 := by
  unfold tailWord_4140260
  simp only [CollatzResearch.WordTrace]
  refine ⟨75503843990276297478997117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100671791987035063305329489 75503843990276297478997117)
  ·
    refine ⟨28313941496353611554623919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75503843990276297478997117 28313941496353611554623919)
    ·
      refine ⟨42470912244530417331935879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28313941496353611554623919 42470912244530417331935879)
      ·
        refine ⟨63706368366795625997903819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42470912244530417331935879 63706368366795625997903819)
        ·
          refine ⟨95559552550193438996855729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63706368366795625997903819 95559552550193438996855729)
          ·
            refine ⟨71669664412645079247641797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95559552550193438996855729 71669664412645079247641797)
            ·
              refine ⟨13438062077370952358932837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71669664412645079247641797 13438062077370952358932837)
              ·
                refine ⟨2519636639507053567299907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13438062077370952358932837 2519636639507053567299907)
                ·
                  refine ⟨3779454959260580350949861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2519636639507053567299907 3779454959260580350949861)
                  ·
                    refine ⟨708647804861358815803099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3779454959260580350949861 708647804861358815803099)
                    ·
                      rfl

theorem cell23_4140260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_4140260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140260 prefixEnd_4140260 := by exact prefixLift 4140260
  have htrace : WordTrace (prefixWord ++ tailWord_4140260) baseStart_4140260 baseEnd_4140260 := by
    simpa [prefixWord, tailWord_4140260, baseEnd_4140260] using wordTrace_append hprefix tailTrace_4140260
  have hstable : (prefixWord ++ tailWord_4140260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140260).length < 2 ^ (prefixWord ++ tailWord_4140260).sum := by decide
  have hdescent : baseEnd_4140260 < baseStart_4140260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140293 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 1, 5, 2]
def baseStart_4140293 : Nat := 118140960795 + 4140293 * 2 ^ 59
def prefixEnd_4140293 : Nat := 4983230072969 + 3 ^ 40 * 4140293 * 2
def baseEnd_4140293 : Nat := 2125960359445674818296645

theorem tailTrace_4140293 : CollatzResearch.WordTrace tailWord_4140293 prefixEnd_4140293 2125960359445674818296645 := by
  unfold tailWord_4140293
  simp only [CollatzResearch.WordTrace]
  refine ⟨151008891589433041593945533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100672594392955361062630355 151008891589433041593945533)
  ·
    refine ⟨56628334346037390597729575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151008891589433041593945533 56628334346037390597729575)
    ·
      refine ⟨84942501519056085896594363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56628334346037390597729575 84942501519056085896594363)
      ·
        refine ⟨127413752278584128844891545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84942501519056085896594363 127413752278584128844891545)
        ·
          refine ⟨95560314208938096633668659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127413752278584128844891545 95560314208938096633668659)
          ·
            refine ⟨143340471313407144950502989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95560314208938096633668659 143340471313407144950502989)
            ·
              refine ⟨53752676742527679356438621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143340471313407144950502989 53752676742527679356438621)
              ·
                refine ⟨20157253778447879758664483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53752676742527679356438621 20157253778447879758664483)
                ·
                  refine ⟨30235880667671819637996725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20157253778447879758664483 30235880667671819637996725)
                  ·
                    refine ⟨2834613812594233091062193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30235880667671819637996725 2834613812594233091062193)
                    ·
                      refine ⟨2125960359445674818296645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2834613812594233091062193 2125960359445674818296645)
                      ·
                        rfl

theorem cell23_4140293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 5, 2].length) (baseStart_4140293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140293 prefixEnd_4140293 := by exact prefixLift 4140293
  have htrace : WordTrace (prefixWord ++ tailWord_4140293) baseStart_4140293 baseEnd_4140293 := by
    simpa [prefixWord, tailWord_4140293, baseEnd_4140293] using wordTrace_append hprefix tailTrace_4140293
  have hstable : (prefixWord ++ tailWord_4140293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140293).length < 2 ^ (prefixWord ++ tailWord_4140293).sum := by decide
  have hdescent : baseEnd_4140293 < baseStart_4140293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140317 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_4140317 : Nat := 118140960795 + 4140317 * 2 ^ 59
def prefixEnd_4140317 : Nat := 4983230072969 + 3 ^ 40 * 4140317 * 2
def baseEnd_4140317 : Nat := 2125972682981382724396535

theorem tailTrace_4140317 : CollatzResearch.WordTrace tailWord_4140317 prefixEnd_4140317 2125972682981382724396535 := by
  unfold tailWord_4140317
  simp only [CollatzResearch.WordTrace]
  refine ⟨151009766941346093692819205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100673177960897395795212803 151009766941346093692819205)
  ·
    refine ⟨28314331301502392567403601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151009766941346093692819205 28314331301502392567403601)
    ·
      refine ⟨21235748476126794425552701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28314331301502392567403601 21235748476126794425552701)
      ·
        refine ⟨7963405678547547909582263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21235748476126794425552701 7963405678547547909582263)
        ·
          refine ⟨11945108517821321864373395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7963405678547547909582263 11945108517821321864373395)
          ·
            refine ⟨17917662776731982796560093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11945108517821321864373395 17917662776731982796560093)
            ·
              refine ⟨6719123541274493548710035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17917662776731982796560093 6719123541274493548710035)
              ·
                refine ⟨10078685311911740323065053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6719123541274493548710035 10078685311911740323065053)
                ·
                  refine ⟨3779506991966902621149395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10078685311911740323065053 3779506991966902621149395)
                  ·
                    refine ⟨5669260487950353931724093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3779506991966902621149395 5669260487950353931724093)
                    ·
                      refine ⟨2125972682981382724396535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5669260487950353931724093 2125972682981382724396535)
                      ·
                        rfl

theorem cell23_4140317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_4140317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140317 prefixEnd_4140317 := by exact prefixLift 4140317
  have htrace : WordTrace (prefixWord ++ tailWord_4140317) baseStart_4140317 baseEnd_4140317 := by
    simpa [prefixWord, tailWord_4140317, baseEnd_4140317] using wordTrace_append hprefix tailTrace_4140317
  have hstable : (prefixWord ++ tailWord_4140317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140317).length < 2 ^ (prefixWord ++ tailWord_4140317).sum := by decide
  have hdescent : baseEnd_4140317 < baseStart_4140317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140336 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 6]
def baseStart_4140336 : Nat := 118140960795 + 4140336 * 2 ^ 59
def prefixEnd_4140336 : Nat := 4983230072969 + 3 ^ 40 * 4140336 * 2
def baseEnd_4140336 : Nat := 2125982439113818150058947

theorem tailTrace_4140336 : CollatzResearch.WordTrace tailWord_4140336 prefixEnd_4140336 2125982439113818150058947 := by
  unfold tailWord_4140336
  simp only [CollatzResearch.WordTrace]
  refine ⟨75505229964138629968880431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100673639952184839958507241 75505229964138629968880431)
  ·
    refine ⟨113257844946207944953320647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75505229964138629968880431 113257844946207944953320647)
    ·
      refine ⟨169886767419311917429980971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113257844946207944953320647 169886767419311917429980971)
      ·
        refine ⟨254830151128967876144971457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169886767419311917429980971 254830151128967876144971457)
        ·
          refine ⟨191122613346725907108728593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254830151128967876144971457 191122613346725907108728593)
          ·
            refine ⟨143341960010044430331546445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191122613346725907108728593 143341960010044430331546445)
            ·
              refine ⟨53753235003766661374329917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143341960010044430331546445 53753235003766661374329917)
              ·
                refine ⟨20157463126412498015373719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53753235003766661374329917 20157463126412498015373719)
                ·
                  refine ⟨30236194689618747023060579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20157463126412498015373719 30236194689618747023060579)
                  ·
                    refine ⟨45354292034428120534590869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30236194689618747023060579 45354292034428120534590869)
                    ·
                      refine ⟨2125982439113818150058947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45354292034428120534590869 2125982439113818150058947)
                      ·
                        rfl

theorem cell23_4140336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_4140336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140336 prefixEnd_4140336 := by exact prefixLift 4140336
  have htrace : WordTrace (prefixWord ++ tailWord_4140336) baseStart_4140336 baseEnd_4140336 := by
    simpa [prefixWord, tailWord_4140336, baseEnd_4140336] using wordTrace_append hprefix tailTrace_4140336
  have hstable : (prefixWord ++ tailWord_4140336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140336).length < 2 ^ (prefixWord ++ tailWord_4140336).sum := by decide
  have hdescent : baseEnd_4140336 < baseStart_4140336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140340 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_4140340 : Nat := 118140960795 + 4140340 * 2 ^ 59
def prefixEnd_4140340 : Nat := 4983230072969 + 3 ^ 40 * 4140340 * 2
def baseEnd_4140340 : Nat := 2125984493036436134408929

theorem tailTrace_4140340 : CollatzResearch.WordTrace tailWord_4140340 prefixEnd_4140340 2125984493036436134408929 := by
  unfold tailWord_4140340
  simp only [CollatzResearch.WordTrace]
  refine ⟨75505302910131384310453237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100673737213508512413937649 75505302910131384310453237)
  ·
    refine ⟨7078622147824817279104991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75505302910131384310453237 7078622147824817279104991)
    ·
      refine ⟨10617933221737225918657487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7078622147824817279104991 10617933221737225918657487)
      ·
        refine ⟨15926899832605838877986231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10617933221737225918657487 15926899832605838877986231)
        ·
          refine ⟨23890349748908758316979347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15926899832605838877986231 23890349748908758316979347)
          ·
            refine ⟨35835524623363137475469021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23890349748908758316979347 35835524623363137475469021)
            ·
              refine ⟨13438321733761176553300883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35835524623363137475469021 13438321733761176553300883)
              ·
                refine ⟨20157482600641764829951325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13438321733761176553300883 20157482600641764829951325)
                ·
                  refine ⟨7559055975240661811231747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20157482600641764829951325 7559055975240661811231747)
                  ·
                    refine ⟨11338583962860992716847621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7559055975240661811231747 11338583962860992716847621)
                    ·
                      refine ⟨2125984493036436134408929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11338583962860992716847621 2125984493036436134408929)
                      ·
                        rfl

theorem cell23_4140340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_4140340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140340 prefixEnd_4140340 := by exact prefixLift 4140340
  have htrace : WordTrace (prefixWord ++ tailWord_4140340) baseStart_4140340 baseEnd_4140340 := by
    simpa [prefixWord, tailWord_4140340, baseEnd_4140340] using wordTrace_append hprefix tailTrace_4140340
  have hstable : (prefixWord ++ tailWord_4140340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140340).length < 2 ^ (prefixWord ++ tailWord_4140340).sum := by decide
  have hdescent : baseEnd_4140340 < baseStart_4140340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140346 : List Nat := [3, 1, 1, 1, 4, 1, 1, 11]
def baseStart_4140346 : Nat := 118140960795 + 4140346 * 2 ^ 59
def prefixEnd_4140346 : Nat := 4983230072969 + 3 ^ 40 * 4140346 * 2
def baseEnd_4140346 : Nat := 78740280515569004108663

theorem tailTrace_4140346 : CollatzResearch.WordTrace tailWord_4140346 prefixEnd_4140346 78740280515569004108663 := by
  unfold tailWord_4140346
  simp only [CollatzResearch.WordTrace]
  refine ⟨37752706164560257911406223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100673883105494021097083261 37752706164560257911406223)
  ·
    refine ⟨56629059246840386867109335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37752706164560257911406223 56629059246840386867109335)
    ·
      refine ⟨84943588870260580300664003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56629059246840386867109335 84943588870260580300664003)
      ·
        refine ⟨127415383305390870450996005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84943588870260580300664003 127415383305390870450996005)
        ·
          refine ⟨23890384369760788209561751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127415383305390870450996005 23890384369760788209561751)
          ·
            refine ⟨35835576554641182314342627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23890384369760788209561751 35835576554641182314342627)
            ·
              refine ⟨53753364831961773471513941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35835576554641182314342627 53753364831961773471513941)
              ·
                refine ⟨78740280515569004108663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 53753364831961773471513941 78740280515569004108663)
                ·
                  rfl

theorem cell23_4140346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 11].length) (baseStart_4140346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140346 prefixEnd_4140346 := by exact prefixLift 4140346
  have htrace : WordTrace (prefixWord ++ tailWord_4140346) baseStart_4140346 baseEnd_4140346 := by
    simpa [prefixWord, tailWord_4140346, baseEnd_4140346] using wordTrace_append hprefix tailTrace_4140346
  have hstable : (prefixWord ++ tailWord_4140346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140346).length < 2 ^ (prefixWord ++ tailWord_4140346).sum := by decide
  have hdescent : baseEnd_4140346 < baseStart_4140346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140376 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 1, 9]
def baseStart_4140376 : Nat := 118140960795 + 4140376 * 2 ^ 59
def prefixEnd_4140376 : Nat := 4983230072969 + 3 ^ 40 * 4140376 * 2
def baseEnd_4140376 : Nat := 708667659446665997852921

theorem tailTrace_4140376 : CollatzResearch.WordTrace tailWord_4140376 prefixEnd_4140376 708667659446665997852921 := by
  unfold tailWord_4140376
  simp only [CollatzResearch.WordTrace]
  refine ⟨75505959424066173384608491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100674612565421564512811321 75505959424066173384608491)
  ·
    refine ⟨113258939136099260076912737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75505959424066173384608491 113258939136099260076912737)
    ·
      refine ⟨84944204352074445057684553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113258939136099260076912737 84944204352074445057684553)
      ·
        refine ⟨63708153264055833793263415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84944204352074445057684553 63708153264055833793263415)
        ·
          refine ⟨95562229896083750689895123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63708153264055833793263415 95562229896083750689895123)
          ·
            refine ⟨143343344844125626034842685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95562229896083750689895123 143343344844125626034842685)
            ·
              refine ⟨53753754316547109763066007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143343344844125626034842685 53753754316547109763066007)
              ·
                refine ⟨80630631474820664644599011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53753754316547109763066007 80630631474820664644599011)
                ·
                  refine ⟨120945947212230996966898517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80630631474820664644599011 120945947212230996966898517)
                  ·
                    refine ⟨708667659446665997852921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 120945947212230996966898517 708667659446665997852921)
                    ·
                      rfl

theorem cell23_4140376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_4140376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140376 prefixEnd_4140376 := by exact prefixLift 4140376
  have htrace : WordTrace (prefixWord ++ tailWord_4140376) baseStart_4140376 baseEnd_4140376 := by
    simpa [prefixWord, tailWord_4140376, baseEnd_4140376] using wordTrace_append hprefix tailTrace_4140376
  have hstable : (prefixWord ++ tailWord_4140376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140376).length < 2 ^ (prefixWord ++ tailWord_4140376).sum := by decide
  have hdescent : baseEnd_4140376 < baseStart_4140376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140400 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 3, 3, 2]
def baseStart_4140400 : Nat := 118140960795 + 4140400 * 2 ^ 59
def prefixEnd_4140400 : Nat := 4983230072969 + 3 ^ 40 * 4140400 * 2
def baseEnd_4140400 : Nat := 2126015301875705899658653

theorem tailTrace_4140400 : CollatzResearch.WordTrace tailWord_4140400 prefixEnd_4140400 2126015301875705899658653 := by
  unfold tailWord_4140400
  simp only [CollatzResearch.WordTrace]
  refine ⟨75506397100022699434045327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100675196133363599245393769 75506397100022699434045327)
  ·
    refine ⟨113259595650034049151067991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75506397100022699434045327 113259595650034049151067991)
    ·
      refine ⟨169889393475051073726601987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113259595650034049151067991 169889393475051073726601987)
      ·
        refine ⟨254834090212576610589902981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169889393475051073726601987 254834090212576610589902981)
        ·
          refine ⟨47781391914858114485606809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254834090212576610589902981 47781391914858114485606809)
          ·
            refine ⟨35836043936143585864205107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47781391914858114485606809 35836043936143585864205107)
            ·
              refine ⟨53754065904215378796307661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35836043936143585864205107 53754065904215378796307661)
              ·
                refine ⟨20157774714080767048615373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53754065904215378796307661 20157774714080767048615373)
                ·
                  refine ⟨7559165517780287643230765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20157774714080767048615373 7559165517780287643230765)
                  ·
                    refine ⟨2834687069167607866211537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7559165517780287643230765 2834687069167607866211537)
                    ·
                      refine ⟨2126015301875705899658653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2834687069167607866211537 2126015301875705899658653)
                      ·
                        rfl

theorem cell23_4140400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 3, 3, 2].length) (baseStart_4140400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140400 prefixEnd_4140400 := by exact prefixLift 4140400
  have htrace : WordTrace (prefixWord ++ tailWord_4140400) baseStart_4140400 baseEnd_4140400 := by
    simpa [prefixWord, tailWord_4140400, baseEnd_4140400] using wordTrace_append hprefix tailTrace_4140400
  have hstable : (prefixWord ++ tailWord_4140400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140400).length < 2 ^ (prefixWord ++ tailWord_4140400).sum := by decide
  have hdescent : baseEnd_4140400 < baseStart_4140400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140423 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 2, 6]
def baseStart_4140423 : Nat := 118140960795 + 4140423 * 2 ^ 59
def prefixEnd_4140423 : Nat := 4983230072969 + 3 ^ 40 * 4140423 * 2
def baseEnd_4140423 : Nat := 708675703976919769890349

theorem tailTrace_4140423 : CollatzResearch.WordTrace tailWord_4140423 prefixEnd_4140423 708675703976919769890349 := by
  unfold tailWord_4140423
  simp only [CollatzResearch.WordTrace]
  refine ⟨151013633078962073796177923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100675755385974715864118615 151013633078962073796177923)
  ·
    refine ⟨226520449618443110694266885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151013633078962073796177923 226520449618443110694266885)
    ·
      refine ⟨42472584303458083255175041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226520449618443110694266885 42472584303458083255175041)
      ·
        refine ⟨31854438227593562441381281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42472584303458083255175041 31854438227593562441381281)
        ·
          refine ⟨23890828670695171831035961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31854438227593562441381281 23890828670695171831035961)
          ·
            refine ⟨17918121503021378873276971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23890828670695171831035961 17918121503021378873276971)
            ·
              refine ⟨26877182254532068309915457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17918121503021378873276971 26877182254532068309915457)
              ·
                refine ⟨20157886690899051232436593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26877182254532068309915457 20157886690899051232436593)
                ·
                  refine ⟨15118415018174288424327445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20157886690899051232436593 15118415018174288424327445)
                  ·
                    refine ⟨708675703976919769890349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15118415018174288424327445 708675703976919769890349)
                    ·
                      rfl

theorem cell23_4140423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_4140423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140423 prefixEnd_4140423 := by exact prefixLift 4140423
  have htrace : WordTrace (prefixWord ++ tailWord_4140423) baseStart_4140423 baseEnd_4140423 := by
    simpa [prefixWord, tailWord_4140423, baseEnd_4140423] using wordTrace_append hprefix tailTrace_4140423
  have hstable : (prefixWord ++ tailWord_4140423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140423).length < 2 ^ (prefixWord ++ tailWord_4140423).sum := by decide
  have hdescent : baseEnd_4140423 < baseStart_4140423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140424 : List Nat := [2, 1, 3, 3, 1, 4, 1, 2, 2, 1, 3]
def baseStart_4140424 : Nat := 118140960795 + 4140424 * 2 ^ 59
def prefixEnd_4140424 : Nat := 4983230072969 + 3 ^ 40 * 4140424 * 2
def baseEnd_4140424 : Nat := 2126027625411413805758543

theorem tailTrace_4140424 : CollatzResearch.WordTrace tailWord_4140424 prefixEnd_4140424 2126027625411413805758543 := by
  unfold tailWord_4140424
  simp only [CollatzResearch.WordTrace]
  refine ⟨75506834775979225483482163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100675779701305633977976217 75506834775979225483482163)
  ·
    refine ⟨113260252163968838225223245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75506834775979225483482163 113260252163968838225223245)
    ·
      refine ⟨42472594561488314334458717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113260252163968838225223245 42472594561488314334458717)
      ·
        refine ⟨15927222960558117875422019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42472594561488314334458717 15927222960558117875422019)
        ·
          refine ⟨23890834440837176813133029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15927222960558117875422019 23890834440837176813133029)
          ·
            refine ⟨4479531457656970652462443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23890834440837176813133029 4479531457656970652462443)
            ·
              refine ⟨6719297186485455978693665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4479531457656970652462443 6719297186485455978693665)
              ·
                refine ⟨5039472889864091984020249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6719297186485455978693665 5039472889864091984020249)
                ·
                  refine ⟨3779604667398068988015187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5039472889864091984020249 3779604667398068988015187)
                  ·
                    refine ⟨5669407001097103482022781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3779604667398068988015187 5669407001097103482022781)
                    ·
                      refine ⟨2126027625411413805758543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5669407001097103482022781 2126027625411413805758543)
                      ·
                        rfl

theorem cell23_4140424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_4140424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140424 prefixEnd_4140424 := by exact prefixLift 4140424
  have htrace : WordTrace (prefixWord ++ tailWord_4140424) baseStart_4140424 baseEnd_4140424 := by
    simpa [prefixWord, tailWord_4140424, baseEnd_4140424] using wordTrace_append hprefix tailTrace_4140424
  have hstable : (prefixWord ++ tailWord_4140424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140424).length < 2 ^ (prefixWord ++ tailWord_4140424).sum := by decide
  have hdescent : baseEnd_4140424 < baseStart_4140424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140447 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 1, 4, 2]
def baseStart_4140447 : Nat := 118140960795 + 4140447 * 2 ^ 59
def prefixEnd_4140447 : Nat := 4983230072969 + 3 ^ 40 * 4140447 * 2
def baseEnd_4140447 : Nat := 2126039435466467215770937

theorem tailTrace_4140447 : CollatzResearch.WordTrace tailWord_4140447 prefixEnd_4140447 2126039435466467215770937 := by
  unfold tailWord_4140447
  simp only [CollatzResearch.WordTrace]
  refine ⟨151014508430875125895051595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100676338953916750596701063 151014508430875125895051595)
  ·
    refine ⟨226521762646312688842577393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151014508430875125895051595 226521762646312688842577393)
    ·
      refine ⟨169891321984734516631933045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226521762646312688842577393 169891321984734516631933045)
      ·
        refine ⟨15927311436068860934243723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169891321984734516631933045 15927311436068860934243723)
        ·
          refine ⟨23890967154103291401365585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15927311436068860934243723 23890967154103291401365585)
          ·
            refine ⟨17918225365577468551024189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23890967154103291401365585 17918225365577468551024189)
            ·
              refine ⟨6719334512091550706634071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17918225365577468551024189 6719334512091550706634071)
              ·
                refine ⟨10079001768137326059951107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6719334512091550706634071 10079001768137326059951107)
                ·
                  refine ⟨15118502652205989089926661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10079001768137326059951107 15118502652205989089926661)
                  ·
                    refine ⟨2834719247288622954361249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15118502652205989089926661 2834719247288622954361249)
                    ·
                      refine ⟨2126039435466467215770937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2834719247288622954361249 2126039435466467215770937)
                      ·
                        rfl

theorem cell23_4140447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_4140447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140447 prefixEnd_4140447 := by exact prefixLift 4140447
  have htrace : WordTrace (prefixWord ++ tailWord_4140447) baseStart_4140447 baseEnd_4140447 := by
    simpa [prefixWord, tailWord_4140447, baseEnd_4140447] using wordTrace_append hprefix tailTrace_4140447
  have hstable : (prefixWord ++ tailWord_4140447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140447).length < 2 ^ (prefixWord ++ tailWord_4140447).sum := by decide
  have hdescent : baseEnd_4140447 < baseStart_4140447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140463 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 3]
def baseStart_4140463 : Nat := 118140960795 + 4140463 * 2 ^ 59
def prefixEnd_4140463 : Nat := 4983230072969 + 3 ^ 40 * 4140463 * 2
def baseEnd_4140463 : Nat := 2126047651156939153170863

theorem tailTrace_4140463 : CollatzResearch.WordTrace tailWord_4140463 prefixEnd_4140463 2126047651156939153170863 := by
  unfold tailWord_4140463
  simp only [CollatzResearch.WordTrace]
  refine ⟨151015091998817160627634043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100676727999211440418422695 151015091998817160627634043)
  ·
    refine ⟨226522637998225740941451065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151015091998817160627634043 226522637998225740941451065)
    ·
      refine ⟨169891978498669305706088299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226522637998225740941451065 169891978498669305706088299)
      ·
        refine ⟨254837967748003958559132449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169891978498669305706088299 254837967748003958559132449)
        ·
          refine ⟨191128475811002968919349337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254837967748003958559132449 191128475811002968919349337)
          ·
            refine ⟨143346356858252226689512003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191128475811002968919349337 143346356858252226689512003)
            ·
              refine ⟨215019535287378340034268005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143346356858252226689512003 215019535287378340034268005)
              ·
                refine ⟨40316162866383438756425251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215019535287378340034268005 40316162866383438756425251)
                ·
                  refine ⟨60474244299575158134637877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40316162866383438756425251 60474244299575158134637877)
                  ·
                    refine ⟨5669460403085171075122301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60474244299575158134637877 5669460403085171075122301)
                    ·
                      refine ⟨2126047651156939153170863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5669460403085171075122301 2126047651156939153170863)
                      ·
                        rfl

theorem cell23_4140463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 3].length) (baseStart_4140463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140463 prefixEnd_4140463 := by exact prefixLift 4140463
  have htrace : WordTrace (prefixWord ++ tailWord_4140463) baseStart_4140463 baseEnd_4140463 := by
    simpa [prefixWord, tailWord_4140463, baseEnd_4140463] using wordTrace_append hprefix tailTrace_4140463
  have hstable : (prefixWord ++ tailWord_4140463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140463).length < 2 ^ (prefixWord ++ tailWord_4140463).sum := by decide
  have hdescent : baseEnd_4140463 < baseStart_4140463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140483 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 4, 5]
def baseStart_4140483 : Nat := 118140960795 + 4140483 * 2 ^ 59
def prefixEnd_4140483 : Nat := 4983230072969 + 3 ^ 40 * 4140483 * 2
def baseEnd_4140483 : Nat := 708685973590009691640257

theorem tailTrace_4140483 : CollatzResearch.WordTrace tailWord_4140483 prefixEnd_4140483 708685973590009691640257 := by
  unfold tailWord_4140483
  simp only [CollatzResearch.WordTrace]
  refine ⟨151015821458744704043362103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100677214305829802695574735 151015821458744704043362103)
  ·
    refine ⟨226523732188117056065043155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151015821458744704043362103 226523732188117056065043155)
    ·
      refine ⟨339785598282175584097564733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226523732188117056065043155 339785598282175584097564733)
      ·
        refine ⟨127419599355815844036586775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339785598282175584097564733 127419599355815844036586775)
        ·
          refine ⟨191129399033723766054880163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127419599355815844036586775 191129399033723766054880163)
          ·
            refine ⟨286694098550585649082320245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191129399033723766054880163 286694098550585649082320245)
            ·
              refine ⟨26877571739117404601467523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 286694098550585649082320245 26877571739117404601467523)
              ·
                refine ⟨40316357608676106902201285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26877571739117404601467523 40316357608676106902201285)
                ·
                  refine ⟨7559317051626770044162741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40316357608676106902201285 7559317051626770044162741)
                  ·
                    refine ⟨708685973590009691640257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7559317051626770044162741 708685973590009691640257)
                    ·
                      rfl

theorem cell23_4140483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 5].length) (baseStart_4140483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140483 prefixEnd_4140483 := by exact prefixLift 4140483
  have htrace : WordTrace (prefixWord ++ tailWord_4140483) baseStart_4140483 baseEnd_4140483 := by
    simpa [prefixWord, tailWord_4140483, baseEnd_4140483] using wordTrace_append hprefix tailTrace_4140483
  have hstable : (prefixWord ++ tailWord_4140483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140483).length < 2 ^ (prefixWord ++ tailWord_4140483).sum := by decide
  have hdescent : baseEnd_4140483 < baseStart_4140483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140487 : List Nat := [1, 1, 4, 1, 1, 3, 5, 2, 5]
def baseStart_4140487 : Nat := 118140960795 + 4140487 * 2 ^ 59
def prefixEnd_4140487 : Nat := 4983230072969 + 3 ^ 40 * 4140487 * 2
def baseEnd_4140487 : Nat := 236228886076960784363417

theorem tailTrace_4140487 : CollatzResearch.WordTrace tailWord_4140487 prefixEnd_4140487 236228886076960784363417 := by
  unfold tailWord_4140487
  simp only [CollatzResearch.WordTrace]
  refine ⟨151015967350730212726507715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100677311567153475151005143 151015967350730212726507715)
  ·
    refine ⟨226523951026095319089761573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151015967350730212726507715 226523951026095319089761573)
    ·
      refine ⟨42473240817392872329330295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226523951026095319089761573 42473240817392872329330295)
      ·
        refine ⟨63709861226089308493995443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42473240817392872329330295 63709861226089308493995443)
        ·
          refine ⟨95564791839133962740993165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63709861226089308493995443 95564791839133962740993165)
          ·
            refine ⟨35836796939675236027872437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95564791839133962740993165 35836796939675236027872437)
            ·
              refine ⟨3359699713094553377613041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35836796939675236027872437 3359699713094553377613041)
              ·
                refine ⟨2519774784820915033209781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3359699713094553377613041 2519774784820915033209781)
                ·
                  refine ⟨236228886076960784363417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2519774784820915033209781 236228886076960784363417)
                  ·
                    rfl

theorem cell23_4140487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 5].length) (baseStart_4140487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140487 prefixEnd_4140487 := by exact prefixLift 4140487
  have htrace : WordTrace (prefixWord ++ tailWord_4140487) baseStart_4140487 baseEnd_4140487 := by
    simpa [prefixWord, tailWord_4140487, baseEnd_4140487] using wordTrace_append hprefix tailTrace_4140487
  have hstable : (prefixWord ++ tailWord_4140487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140487).length < 2 ^ (prefixWord ++ tailWord_4140487).sum := by decide
  have hdescent : baseEnd_4140487 < baseStart_4140487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140503 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 4]
def baseStart_4140503 : Nat := 118140960795 + 4140503 * 2 ^ 59
def prefixEnd_4140503 : Nat := 4983230072969 + 3 ^ 40 * 4140503 * 2
def baseEnd_4140503 : Nat := 2126068190383118996670679

theorem tailTrace_4140503 : CollatzResearch.WordTrace tailWord_4140503 prefixEnd_4140503 2126068190383118996670679 := by
  unfold tailWord_4140503
  simp only [CollatzResearch.WordTrace]
  refine ⟨151016550918672247459090163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100677700612448164972726775 151016550918672247459090163)
  ·
    refine ⟨226524826378008371188635245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151016550918672247459090163 226524826378008371188635245)
    ·
      refine ⟨84946809891753139195738217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226524826378008371188635245 84946809891753139195738217)
      ·
        refine ⟨63710107418814854396803663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84946809891753139195738217 63710107418814854396803663)
        ·
          refine ⟨95565161128222281595205495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63710107418814854396803663 95565161128222281595205495)
          ·
            refine ⟨143347741692333422392808243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95565161128222281595205495 143347741692333422392808243)
            ·
              refine ⟨215021612538500133589212365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143347741692333422392808243 215021612538500133589212365)
              ·
                refine ⟨80633104701937550095954637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215021612538500133589212365 80633104701937550095954637)
                ·
                  refine ⟨30237414263226581285982989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80633104701937550095954637 30237414263226581285982989)
                  ·
                    refine ⟨11339030348709967982243621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30237414263226581285982989 11339030348709967982243621)
                    ·
                      refine ⟨2126068190383118996670679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11339030348709967982243621 2126068190383118996670679)
                      ·
                        rfl

theorem cell23_4140503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_4140503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140503 prefixEnd_4140503 := by exact prefixLift 4140503
  have htrace : WordTrace (prefixWord ++ tailWord_4140503) baseStart_4140503 baseEnd_4140503 := by
    simpa [prefixWord, tailWord_4140503, baseEnd_4140503] using wordTrace_append hprefix tailTrace_4140503
  have hstable : (prefixWord ++ tailWord_4140503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140503).length < 2 ^ (prefixWord ++ tailWord_4140503).sum := by decide
  have hdescent : baseEnd_4140503 < baseStart_4140503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140517 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 2, 5]
def baseStart_4140517 : Nat := 118140960795 + 4140517 * 2 ^ 59
def prefixEnd_4140517 : Nat := 4983230072969 + 3 ^ 40 * 4140517 * 2
def baseEnd_4140517 : Nat := 708691793037427313965205

theorem tailTrace_4140517 : CollatzResearch.WordTrace tailWord_4140517 prefixEnd_4140517 708691793037427313965205 := by
  unfold tailWord_4140517
  simp only [CollatzResearch.WordTrace]
  refine ⟨151017061540621527850099805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100678041027081018566733203 151017061540621527850099805)
  ·
    refine ⟨56631398077733072943787427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151017061540621527850099805 56631398077733072943787427)
    ·
      refine ⟨84947097116599609415681141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56631398077733072943787427 84947097116599609415681141)
      ·
        refine ⟨7963790354681213382720107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84947097116599609415681141 7963790354681213382720107)
        ·
          refine ⟨11945685532021820074080161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7963790354681213382720107 11945685532021820074080161)
          ·
            refine ⟨8959264149016365055560121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11945685532021820074080161 8959264149016365055560121)
            ·
              refine ⟨6719448111762273791670091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8959264149016365055560121 6719448111762273791670091)
              ·
                refine ⟨10079172167643410687505137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6719448111762273791670091 10079172167643410687505137)
                ·
                  refine ⟨7559379125732558015628853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10079172167643410687505137 7559379125732558015628853)
                  ·
                    refine ⟨708691793037427313965205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7559379125732558015628853 708691793037427313965205)
                    ·
                      rfl

theorem cell23_4140517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_4140517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140517 prefixEnd_4140517 := by exact prefixLift 4140517
  have htrace : WordTrace (prefixWord ++ tailWord_4140517) baseStart_4140517 baseEnd_4140517 := by
    simpa [prefixWord, tailWord_4140517, baseEnd_4140517] using wordTrace_append hprefix tailTrace_4140517
  have hstable : (prefixWord ++ tailWord_4140517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140517).length < 2 ^ (prefixWord ++ tailWord_4140517).sum := by decide
  have hdescent : baseEnd_4140517 < baseStart_4140517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140640 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 4]
def baseStart_4140640 : Nat := 118140960795 + 4140640 * 2 ^ 59
def prefixEnd_4140640 : Nat := 4983230072969 + 3 ^ 40 * 4140640 * 2
def baseEnd_4140640 : Nat := 2126138537232784960657549

theorem tailTrace_4140640 : CollatzResearch.WordTrace tailWord_4140640 prefixEnd_4140640 2126138537232784960657549 := by
  unfold tailWord_4140640
  simp only [CollatzResearch.WordTrace]
  refine ⟨75510773859587959928413687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100681031812783946571218249 75510773859587959928413687)
  ·
    refine ⟨113266160789381939892620531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75510773859587959928413687 113266160789381939892620531)
    ·
      refine ⟨169899241184072909838930797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113266160789381939892620531 169899241184072909838930797)
      ·
        refine ⟨63712215444027341189599049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169899241184072909838930797 63712215444027341189599049)
        ·
          refine ⟨47784161583020505892199287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63712215444027341189599049 47784161583020505892199287)
          ·
            refine ⟨71676242374530758838298931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47784161583020505892199287 71676242374530758838298931)
            ·
              refine ⟨107514363561796138257448397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71676242374530758838298931 107514363561796138257448397)
              ·
                refine ⟨40317886335673551846543149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107514363561796138257448397 40317886335673551846543149)
                ·
                  refine ⟨15119207375877581942453681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40317886335673551846543149 15119207375877581942453681)
                  ·
                    refine ⟨11339405531908186456840261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15119207375877581942453681 11339405531908186456840261)
                    ·
                      refine ⟨2126138537232784960657549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11339405531908186456840261 2126138537232784960657549)
                      ·
                        rfl

theorem cell23_4140640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_4140640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140640 prefixEnd_4140640 := by exact prefixLift 4140640
  have htrace : WordTrace (prefixWord ++ tailWord_4140640) baseStart_4140640 baseEnd_4140640 := by
    simpa [prefixWord, tailWord_4140640, baseEnd_4140640] using wordTrace_append hprefix tailTrace_4140640
  have hstable : (prefixWord ++ tailWord_4140640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140640).length < 2 ^ (prefixWord ++ tailWord_4140640).sum := by decide
  have hdescent : baseEnd_4140640 < baseStart_4140640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140650 : List Nat := [3, 1, 3, 2, 1, 2, 11]
def baseStart_4140650 : Nat := 118140960795 + 4140650 * 2 ^ 59
def prefixEnd_4140650 : Nat := 4983230072969 + 3 ^ 40 * 4140650 * 2
def baseEnd_4140650 : Nat := 26248687309127529895463

theorem tailTrace_4140650 : CollatzResearch.WordTrace tailWord_4140650 prefixEnd_4140650 26248687309127529895463 := by
  unfold tailWord_4140650
  simp only [CollatzResearch.WordTrace]
  refine ⟨37755478112284922891172851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100681274966093127709794269 37755478112284922891172851)
  ·
    refine ⟨56633217168427384336759277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37755478112284922891172851 56633217168427384336759277)
    ·
      refine ⟨21237456438160269126284729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56633217168427384336759277 21237456438160269126284729)
      ·
        refine ⟨15928092328620201844713547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21237456438160269126284729 15928092328620201844713547)
        ·
          refine ⟨23892138492930302767070321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15928092328620201844713547 23892138492930302767070321)
          ·
            refine ⟨17919103869697727075302741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23892138492930302767070321 17919103869697727075302741)
            ·
              refine ⟨26248687309127529895463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17919103869697727075302741 26248687309127529895463)
              ·
                rfl

theorem cell23_4140650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 11].length) (baseStart_4140650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140650 prefixEnd_4140650 := by exact prefixLift 4140650
  have htrace : WordTrace (prefixWord ++ tailWord_4140650) baseStart_4140650 baseEnd_4140650 := by
    simpa [prefixWord, tailWord_4140650, baseEnd_4140650] using wordTrace_append hprefix tailTrace_4140650
  have hstable : (prefixWord ++ tailWord_4140650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140650).length < 2 ^ (prefixWord ++ tailWord_4140650).sum := by decide
  have hdescent : baseEnd_4140650 < baseStart_4140650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140677 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 1, 3, 3]
def baseStart_4140677 : Nat := 118140960795 + 4140677 * 2 ^ 59
def prefixEnd_4140677 : Nat := 4983230072969 + 3 ^ 40 * 4140677 * 2
def baseEnd_4140677 : Nat := 2126157536017001315894879

theorem tailTrace_4140677 : CollatzResearch.WordTrace tailWord_4140677 prefixEnd_4140677 2126157536017001315894879 := by
  unfold tailWord_4140677
  simp only [CollatzResearch.WordTrace]
  refine ⟨151022897220041875175924285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100681931480027916783949523 151022897220041875175924285)
  ·
    refine ⟨56633586457515703190971607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151022897220041875175924285 56633586457515703190971607)
    ·
      refine ⟨84950379686273554786457411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56633586457515703190971607 84950379686273554786457411)
      ·
        refine ⟨127425569529410332179686117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84950379686273554786457411 127425569529410332179686117)
        ·
          refine ⟨23892294286764437283691147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127425569529410332179686117 23892294286764437283691147)
          ·
            refine ⟨35838441430146655925536721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23892294286764437283691147 35838441430146655925536721)
            ·
              refine ⟨26878831072609991944152541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35838441430146655925536721 26878831072609991944152541)
              ·
                refine ⟨10079561652228746979057203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26878831072609991944152541 10079561652228746979057203)
                ·
                  refine ⟨15119342478343120468585805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10079561652228746979057203 15119342478343120468585805)
                  ·
                    refine ⟨5669753429378670175719677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15119342478343120468585805 5669753429378670175719677)
                    ·
                      refine ⟨2126157536017001315894879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5669753429378670175719677 2126157536017001315894879)
                      ·
                        rfl

theorem cell23_4140677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_4140677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140677 prefixEnd_4140677 := by exact prefixLift 4140677
  have htrace : WordTrace (prefixWord ++ tailWord_4140677) baseStart_4140677 baseEnd_4140677 := by
    simpa [prefixWord, tailWord_4140677, baseEnd_4140677] using wordTrace_append hprefix tailTrace_4140677
  have hstable : (prefixWord ++ tailWord_4140677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140677).length < 2 ^ (prefixWord ++ tailWord_4140677).sum := by decide
  have hdescent : baseEnd_4140677 < baseStart_4140677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140717 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_4140717 : Nat := 118140960795 + 4140717 * 2 ^ 59
def prefixEnd_4140717 : Nat := 4983230072969 + 3 ^ 40 * 4140717 * 2
def baseEnd_4140717 : Nat := 2126178075243181159394695

theorem tailTrace_4140717 : CollatzResearch.WordTrace tailWord_4140717 prefixEnd_4140717 2126178075243181159394695 := by
  unfold tailWord_4140717
  simp only [CollatzResearch.WordTrace]
  refine ⟨151024356139896962007380405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100682904093264641338253603 151024356139896962007380405)
  ·
    refine ⟨14158533388115340188191913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151024356139896962007380405 14158533388115340188191913)
    ·
      refine ⟨10618900041086505141143935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14158533388115340188191913 10618900041086505141143935)
      ·
        refine ⟨15928350061629757711715903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10618900041086505141143935 15928350061629757711715903)
        ·
          refine ⟨23892525092444636567573855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15928350061629757711715903 23892525092444636567573855)
          ·
            refine ⟨35838787638666954851360783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23892525092444636567573855 35838787638666954851360783)
            ·
              refine ⟨53758181458000432277041175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35838787638666954851360783 53758181458000432277041175)
              ·
                refine ⟨80637272187000648415561763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53758181458000432277041175 80637272187000648415561763)
                ·
                  refine ⟨120955908280500972623342645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80637272187000648415561763 120955908280500972623342645)
                  ·
                    refine ⟨11339616401296966183438373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120955908280500972623342645 11339616401296966183438373)
                    ·
                      refine ⟨2126178075243181159394695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11339616401296966183438373 2126178075243181159394695)
                      ·
                        rfl

theorem cell23_4140717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_4140717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140717 prefixEnd_4140717 := by exact prefixLift 4140717
  have htrace : WordTrace (prefixWord ++ tailWord_4140717) baseStart_4140717 baseEnd_4140717 := by
    simpa [prefixWord, tailWord_4140717, baseEnd_4140717] using wordTrace_append hprefix tailTrace_4140717
  have hstable : (prefixWord ++ tailWord_4140717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140717).length < 2 ^ (prefixWord ++ tailWord_4140717).sum := by decide
  have hdescent : baseEnd_4140717 < baseStart_4140717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140720 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 5]
def baseStart_4140720 : Nat := 118140960795 + 4140720 * 2 ^ 59
def prefixEnd_4140720 : Nat := 4983230072969 + 3 ^ 40 * 4140720 * 2
def baseEnd_4140720 : Nat := 2126179615685144647657181

theorem tailTrace_4140720 : CollatzResearch.WordTrace tailWord_4140720 prefixEnd_4140720 2126179615685144647657181 := by
  unfold tailWord_4140720
  simp only [CollatzResearch.WordTrace]
  refine ⟨75512232779443046759869807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100682977039257395679826409 75512232779443046759869807)
  ·
    refine ⟨113268349169164570139804711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75512232779443046759869807 113268349169164570139804711)
    ·
      refine ⟨169902523753746855209707067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113268349169164570139804711 169902523753746855209707067)
      ·
        refine ⟨254853785630620282814560601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169902523753746855209707067 254853785630620282814560601)
        ·
          refine ⟨191140339222965212110920451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254853785630620282814560601 191140339222965212110920451)
          ·
            refine ⟨286710508834447818166380677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191140339222965212110920451 286710508834447818166380677)
            ·
              refine ⟨53758220406458965906196377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286710508834447818166380677 53758220406458965906196377)
              ·
                refine ⟨40318665304844224429647283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53758220406458965906196377 40318665304844224429647283)
                ·
                  refine ⟨60477997957266336644470925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40318665304844224429647283 60477997957266336644470925)
                  ·
                    refine ⟨22679249233974876241676597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60477997957266336644470925 22679249233974876241676597)
                    ·
                      refine ⟨2126179615685144647657181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22679249233974876241676597 2126179615685144647657181)
                      ·
                        rfl

theorem cell23_4140720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_4140720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140720 prefixEnd_4140720 := by exact prefixLift 4140720
  have htrace : WordTrace (prefixWord ++ tailWord_4140720) baseStart_4140720 baseEnd_4140720 := by
    simpa [prefixWord, tailWord_4140720, baseEnd_4140720] using wordTrace_append hprefix tailTrace_4140720
  have hstable : (prefixWord ++ tailWord_4140720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140720).length < 2 ^ (prefixWord ++ tailWord_4140720).sum := by decide
  have hdescent : baseEnd_4140720 < baseStart_4140720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140727 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 2, 6]
def baseStart_4140727 : Nat := 118140960795 + 4140727 * 2 ^ 59
def prefixEnd_4140727 : Nat := 4983230072969 + 3 ^ 40 * 4140727 * 2
def baseEnd_4140727 : Nat := 708727736683242040089883

theorem tailTrace_4140727 : CollatzResearch.WordTrace tailWord_4140727 prefixEnd_4140727 708727736683242040089883 := by
  unfold tailWord_4140727
  simp only [CollatzResearch.WordTrace]
  refine ⟨151024720869860733715244435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100683147246573822476829623 151024720869860733715244435)
  ·
    refine ⟨226537081304791100572866653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151024720869860733715244435 226537081304791100572866653)
    ·
      refine ⟨84951405489296662714824995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226537081304791100572866653 84951405489296662714824995)
      ·
        refine ⟨127427108233944994072237493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84951405489296662714824995 127427108233944994072237493)
        ·
          refine ⟨11946291396932343194272265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127427108233944994072237493 11946291396932343194272265)
          ·
            refine ⟨8959718547699257395704199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11946291396932343194272265 8959718547699257395704199)
            ·
              refine ⟨13439577821548886093556299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8959718547699257395704199 13439577821548886093556299)
              ·
                refine ⟨20159366732323329140334449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13439577821548886093556299 20159366732323329140334449)
                ·
                  refine ⟨15119525049242496855250837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20159366732323329140334449 15119525049242496855250837)
                  ·
                    refine ⟨708727736683242040089883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15119525049242496855250837 708727736683242040089883)
                    ·
                      rfl

theorem cell23_4140727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_4140727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140727 prefixEnd_4140727 := by exact prefixLift 4140727
  have htrace : WordTrace (prefixWord ++ tailWord_4140727) baseStart_4140727 baseEnd_4140727 := by
    simpa [prefixWord, tailWord_4140727, baseEnd_4140727] using wordTrace_append hprefix tailTrace_4140727
  have hstable : (prefixWord ++ tailWord_4140727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140727).length < 2 ^ (prefixWord ++ tailWord_4140727).sum := by decide
  have hdescent : baseEnd_4140727 < baseStart_4140727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140767 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 3]
def baseStart_4140767 : Nat := 118140960795 + 4140767 * 2 ^ 59
def prefixEnd_4140767 : Nat := 4983230072969 + 3 ^ 40 * 4140767 * 2
def baseEnd_4140767 : Nat := 2126203749275905963769465

theorem tailTrace_4140767 : CollatzResearch.WordTrace tailWord_4140767 prefixEnd_4140767 2126203749275905963769465 := by
  unfold tailWord_4140767
  simp only [CollatzResearch.WordTrace]
  refine ⟨151026179789715820546700555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100684119859810547031133703 151026179789715820546700555)
  ·
    refine ⟨226539269684573730820050833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151026179789715820546700555 226539269684573730820050833)
    ·
      refine ⟨169904452263430298115038125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226539269684573730820050833 169904452263430298115038125)
      ·
        refine ⟨63714169598786361793139297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169904452263430298115038125 63714169598786361793139297)
        ·
          refine ⟨47785627199089771344854473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63714169598786361793139297 47785627199089771344854473)
          ·
            refine ⟨35839220399317328508640855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47785627199089771344854473 35839220399317328508640855)
            ·
              refine ⟨53758830598975992762961283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35839220399317328508640855 53758830598975992762961283)
              ·
                refine ⟨80638245898463989144441925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53758830598975992762961283 80638245898463989144441925)
                ·
                  refine ⟨15119671105961997964582861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80638245898463989144441925 15119671105961997964582861)
                  ·
                    refine ⟨5669876664735749236718573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15119671105961997964582861 5669876664735749236718573)
                    ·
                      refine ⟨2126203749275905963769465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5669876664735749236718573 2126203749275905963769465)
                      ·
                        rfl

theorem cell23_4140767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_4140767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140767 prefixEnd_4140767 := by exact prefixLift 4140767
  have htrace : WordTrace (prefixWord ++ tailWord_4140767) baseStart_4140767 baseEnd_4140767 := by
    simpa [prefixWord, tailWord_4140767, baseEnd_4140767] using wordTrace_append hprefix tailTrace_4140767
  have hstable : (prefixWord ++ tailWord_4140767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140767).length < 2 ^ (prefixWord ++ tailWord_4140767).sum := by decide
  have hdescent : baseEnd_4140767 < baseStart_4140767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140824 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 4, 4, 2]
def baseStart_4140824 : Nat := 118140960795 + 4140824 * 2 ^ 59
def prefixEnd_4140824 : Nat := 4983230072969 + 3 ^ 40 * 4140824 * 2
def baseEnd_4140824 : Nat := 2126233017673212240756703

theorem tailTrace_4140824 : CollatzResearch.WordTrace tailWord_4140824 prefixEnd_4140824 2126233017673212240756703 := by
  unfold tailWord_4140824
  simp only [CollatzResearch.WordTrace]
  refine ⟨75514129375254659640762763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100685505833672879521017017 75514129375254659640762763)
  ·
    refine ⟨113271194062881989461144145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75514129375254659640762763 113271194062881989461144145)
    ·
      refine ⟨84953395547161492095858109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113271194062881989461144145 84953395547161492095858109)
      ·
        refine ⟨31857523330185559535946791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84953395547161492095858109 31857523330185559535946791)
        ·
          refine ⟨47786284995278339303920187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31857523330185559535946791 47786284995278339303920187)
          ·
            refine ⟨71679427492917508955880281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47786284995278339303920187 71679427492917508955880281)
            ·
              refine ⟨53759570619688131716910211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71679427492917508955880281 53759570619688131716910211)
              ·
                refine ⟨80639355929532197575365317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53759570619688131716910211 80639355929532197575365317)
                ·
                  refine ⟨15119879236787287045380997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80639355929532197575365317 15119879236787287045380997)
                  ·
                    refine ⟨2834977356897616321008937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15119879236787287045380997 2834977356897616321008937)
                    ·
                      refine ⟨2126233017673212240756703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2834977356897616321008937 2126233017673212240756703)
                      ·
                        rfl

theorem cell23_4140824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_4140824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140824 prefixEnd_4140824 := by exact prefixLift 4140824
  have htrace : WordTrace (prefixWord ++ tailWord_4140824) baseStart_4140824 baseEnd_4140824 := by
    simpa [prefixWord, tailWord_4140824, baseEnd_4140824] using wordTrace_append hprefix tailTrace_4140824
  have hstable : (prefixWord ++ tailWord_4140824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140824).length < 2 ^ (prefixWord ++ tailWord_4140824).sum := by decide
  have hdescent : baseEnd_4140824 < baseStart_4140824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140847 : List Nat := [1, 1, 2, 1, 2, 1, 2, 7, 6]
def baseStart_4140847 : Nat := 118140960795 + 4140847 * 2 ^ 59
def prefixEnd_4140847 : Nat := 4983230072969 + 3 ^ 40 * 4140847 * 2
def baseEnd_4140847 : Nat := 236249425303140627863233

theorem tailTrace_4140847 : CollatzResearch.WordTrace tailWord_4140847 prefixEnd_4140847 236249425303140627863233 := by
  unfold tailWord_4140847
  simp only [CollatzResearch.WordTrace]
  refine ⟨151029097629425994209612795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100686065086283996139741863 151029097629425994209612795)
  ·
    refine ⟨226543646444138991314419193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151029097629425994209612795 226543646444138991314419193)
    ·
      refine ⟨169907734833104243485814395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226543646444138991314419193 169907734833104243485814395)
      ·
        refine ⟨254861602249656365228721593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169907734833104243485814395 254861602249656365228721593)
        ·
          refine ⟨191146201687242273921541195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254861602249656365228721593 191146201687242273921541195)
          ·
            refine ⟨286719302530863410882311793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191146201687242273921541195 286719302530863410882311793)
            ·
              refine ⟨215039476898147558161733845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286719302530863410882311793 215039476898147558161733845)
              ·
                refine ⟨5039987739800333394415637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 215039476898147558161733845 5039987739800333394415637)
                ·
                  refine ⟨236249425303140627863233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5039987739800333394415637 236249425303140627863233)
                  ·
                    rfl

theorem cell23_4140847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 6].length) (baseStart_4140847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140847 prefixEnd_4140847 := by exact prefixLift 4140847
  have htrace : WordTrace (prefixWord ++ tailWord_4140847) baseStart_4140847 baseEnd_4140847 := by
    simpa [prefixWord, tailWord_4140847, baseEnd_4140847] using wordTrace_append hprefix tailTrace_4140847
  have hstable : (prefixWord ++ tailWord_4140847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140847).length < 2 ^ (prefixWord ++ tailWord_4140847).sum := by decide
  have hdescent : baseEnd_4140847 < baseStart_4140847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140861 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 2, 2, 3]
def baseStart_4140861 : Nat := 118140960795 + 4140861 * 2 ^ 59
def prefixEnd_4140861 : Nat := 4983230072969 + 3 ^ 40 * 4140861 * 2
def baseEnd_4140861 : Nat := 2126252016457428595994033

theorem tailTrace_4140861 : CollatzResearch.WordTrace tailWord_4140861 prefixEnd_4140861 2126252016457428595994033 := by
  unfold tailWord_4140861
  simp only [CollatzResearch.WordTrace]
  refine ⟨151029608251375274600622437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100686405500916849733748291 151029608251375274600622437)
  ·
    refine ⟨28318051547132863987616707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151029608251375274600622437 28318051547132863987616707)
    ·
      refine ⟨42477077320699295981425061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28318051547132863987616707 42477077320699295981425061)
      ·
        refine ⟨7964451997631117996517199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42477077320699295981425061 7964451997631117996517199)
        ·
          refine ⟨11946677996446676994775799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7964451997631117996517199 11946677996446676994775799)
          ·
            refine ⟨17920016994670015492163699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11946677996446676994775799 17920016994670015492163699)
            ·
              refine ⟨26880025492005023238245549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17920016994670015492163699 26880025492005023238245549)
              ·
                refine ⟨10080009559501883714342081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26880025492005023238245549 10080009559501883714342081)
                ·
                  refine ⟨7560007169626412785756561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10080009559501883714342081 7560007169626412785756561)
                  ·
                    refine ⟨5670005377219809589317421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7560007169626412785756561 5670005377219809589317421)
                    ·
                      refine ⟨2126252016457428595994033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5670005377219809589317421 2126252016457428595994033)
                      ·
                        rfl

theorem cell23_4140861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_4140861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140861 prefixEnd_4140861 := by exact prefixLift 4140861
  have htrace : WordTrace (prefixWord ++ tailWord_4140861) baseStart_4140861 baseEnd_4140861 := by
    simpa [prefixWord, tailWord_4140861, baseEnd_4140861] using wordTrace_append hprefix tailTrace_4140861
  have hstable : (prefixWord ++ tailWord_4140861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140861).length < 2 ^ (prefixWord ++ tailWord_4140861).sum := by decide
  have hdescent : baseEnd_4140861 < baseStart_4140861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140885 : List Nat := [1, 3, 2, 2, 2, 4, 2, 2, 1, 4]
def baseStart_4140885 : Nat := 118140960795 + 4140885 * 2 ^ 59
def prefixEnd_4140885 : Nat := 4983230072969 + 3 ^ 40 * 4140885 * 2
def baseEnd_4140885 : Nat := 708754779997712167364641

theorem tailTrace_4140885 : CollatzResearch.WordTrace tailWord_4140885 prefixEnd_4140885 708754779997712167364641 := by
  unfold tailWord_4140885
  simp only [CollatzResearch.WordTrace]
  refine ⟨151030483603288326699496109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100686989068858884466330739 151030483603288326699496109)
  ·
    refine ⟨56636431351233122512311041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151030483603288326699496109 56636431351233122512311041)
    ·
      refine ⟨42477323513424841884233281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56636431351233122512311041 42477323513424841884233281)
      ·
        refine ⟨31857992635068631413174961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42477323513424841884233281 31857992635068631413174961)
        ·
          refine ⟨23893494476301473559881221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31857992635068631413174961 23893494476301473559881221)
          ·
            refine ⟨4480030214306526292477729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23893494476301473559881221 4480030214306526292477729)
            ·
              refine ⟨3360022660729894719358297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4480030214306526292477729 3360022660729894719358297)
              ·
                refine ⟨2520016995547421039518723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3360022660729894719358297 2520016995547421039518723)
                ·
                  refine ⟨3780025493321131559278085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2520016995547421039518723 3780025493321131559278085)
                  ·
                    refine ⟨708754779997712167364641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3780025493321131559278085 708754779997712167364641)
                    ·
                      rfl

theorem cell23_4140885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_4140885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140885 prefixEnd_4140885 := by exact prefixLift 4140885
  have htrace : WordTrace (prefixWord ++ tailWord_4140885) baseStart_4140885 baseEnd_4140885 := by
    simpa [prefixWord, tailWord_4140885, baseEnd_4140885] using wordTrace_append hprefix tailTrace_4140885
  have hstable : (prefixWord ++ tailWord_4140885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140885).length < 2 ^ (prefixWord ++ tailWord_4140885).sum := by decide
  have hdescent : baseEnd_4140885 < baseStart_4140885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140927 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 6]
def baseStart_4140927 : Nat := 118140960795 + 4140927 * 2 ^ 59
def prefixEnd_4140927 : Nat := 4983230072969 + 3 ^ 40 * 4140927 * 2
def baseEnd_4140927 : Nat := 2126285906180625337768729

theorem tailTrace_4140927 : CollatzResearch.WordTrace tailWord_4140927 prefixEnd_4140927 2126285906180625337768729 := by
  unfold tailWord_4140927
  simp only [CollatzResearch.WordTrace]
  refine ⟨151032015469136167872525035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100688010312757445248350023 151032015469136167872525035)
  ·
    refine ⟨226548023203704251808787553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151032015469136167872525035 226548023203704251808787553)
    ·
      refine ⟨169911017402778188856590665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226548023203704251808787553 169911017402778188856590665)
      ·
        refine ⟨127433263052083641642442999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169911017402778188856590665 127433263052083641642442999)
        ·
          refine ⟨191149894578125462463664499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127433263052083641642442999 191149894578125462463664499)
          ·
            refine ⟨286724841867188193695496749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191149894578125462463664499 286724841867188193695496749)
            ·
              refine ⟨107521815700195572635811281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286724841867188193695496749 107521815700195572635811281)
              ·
                refine ⟨80641361775146679476858461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107521815700195572635811281 80641361775146679476858461)
                ·
                  refine ⟨30240510665680004803821923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80641361775146679476858461 30240510665680004803821923)
                  ·
                    refine ⟨45360765998520007205732885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30240510665680004803821923 45360765998520007205732885)
                    ·
                      refine ⟨2126285906180625337768729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45360765998520007205732885 2126285906180625337768729)
                      ·
                        rfl

theorem cell23_4140927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_4140927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140927 prefixEnd_4140927 := by exact prefixLift 4140927
  have htrace : WordTrace (prefixWord ++ tailWord_4140927) baseStart_4140927 baseEnd_4140927 := by
    simpa [prefixWord, tailWord_4140927, baseEnd_4140927] using wordTrace_append hprefix tailTrace_4140927
  have hstable : (prefixWord ++ tailWord_4140927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140927).length < 2 ^ (prefixWord ++ tailWord_4140927).sum := by decide
  have hdescent : baseEnd_4140927 < baseStart_4140927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140931 : List Nat := [1, 1, 1, 3, 4, 3, 1, 3, 1, 1, 4]
def baseStart_4140931 : Nat := 118140960795 + 4140931 * 2 ^ 59
def prefixEnd_4140931 : Nat := 4983230072969 + 3 ^ 40 * 4140931 * 2
def baseEnd_4140931 : Nat := 2126287960103243322118711

theorem tailTrace_4140931 : CollatzResearch.WordTrace tailWord_4140931 prefixEnd_4140931 2126287960103243322118711 := by
  unfold tailWord_4140931
  simp only [CollatzResearch.WordTrace]
  refine ⟨151032161361121676555670647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100688107574081117703780431 151032161361121676555670647)
  ·
    refine ⟨226548242041682514833505971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151032161361121676555670647 226548242041682514833505971)
    ·
      refine ⟨339822363062523772250258957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226548242041682514833505971 339822363062523772250258957)
      ·
        refine ⟨127433386148446414593847109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339822363062523772250258957 127433386148446414593847109)
        ·
          refine ⟨23893759902833702736346333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127433386148446414593847109 23893759902833702736346333)
          ·
            refine ⟨8960159963562638526129875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23893759902833702736346333 8960159963562638526129875)
            ·
              refine ⟨13440239945343957789194813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8960159963562638526129875 13440239945343957789194813)
              ·
                refine ⟨5040089979503984170948055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13440239945343957789194813 5040089979503984170948055)
                ·
                  refine ⟨7560134969255976256422083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040089979503984170948055 7560134969255976256422083)
                  ·
                    refine ⟨11340202453883964384633125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7560134969255976256422083 11340202453883964384633125)
                    ·
                      refine ⟨2126287960103243322118711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11340202453883964384633125 2126287960103243322118711)
                      ·
                        rfl

theorem cell23_4140931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_4140931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140931 prefixEnd_4140931 := by exact prefixLift 4140931
  have htrace : WordTrace (prefixWord ++ tailWord_4140931) baseStart_4140931 baseEnd_4140931 := by
    simpa [prefixWord, tailWord_4140931, baseEnd_4140931] using wordTrace_append hprefix tailTrace_4140931
  have hstable : (prefixWord ++ tailWord_4140931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140931).length < 2 ^ (prefixWord ++ tailWord_4140931).sum := by decide
  have hdescent : baseEnd_4140931 < baseStart_4140931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140937 : List Nat := [1, 2, 1, 1, 5, 1, 12]
def baseStart_4140937 : Nat := 118140960795 + 4140937 * 2 ^ 59
def prefixEnd_4140937 : Nat := 4983230072969 + 3 ^ 40 * 4140937 * 2
def baseEnd_4140937 : Nat := 26250506678853954304243

theorem tailTrace_4140937 : CollatzResearch.WordTrace tailWord_4140937 prefixEnd_4140937 26250506678853954304243 := by
  unfold tailWord_4140937
  simp only [CollatzResearch.WordTrace]
  refine ⟨151032380199099939580389065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100688253466066626386926043 151032380199099939580389065)
  ·
    refine ⟨113274285149324954685291799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151032380199099939580389065 113274285149324954685291799)
    ·
      refine ⟨169911427723987432027937699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113274285149324954685291799 169911427723987432027937699)
      ·
        refine ⟨254867141585981148041906549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169911427723987432027937699 254867141585981148041906549)
        ·
          refine ⟨23893794523685732628928739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254867141585981148041906549 23893794523685732628928739)
          ·
            refine ⟨35840691785528598943393109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23893794523685732628928739 35840691785528598943393109)
            ·
              refine ⟨26250506678853954304243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 35840691785528598943393109 26250506678853954304243)
              ·
                rfl

theorem cell23_4140937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 12].length) (baseStart_4140937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140937 prefixEnd_4140937 := by exact prefixLift 4140937
  have htrace : WordTrace (prefixWord ++ tailWord_4140937) baseStart_4140937 baseEnd_4140937 := by
    simpa [prefixWord, tailWord_4140937, baseEnd_4140937] using wordTrace_append hprefix tailTrace_4140937
  have hstable : (prefixWord ++ tailWord_4140937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140937).length < 2 ^ (prefixWord ++ tailWord_4140937).sum := by decide
  have hdescent : baseEnd_4140937 < baseStart_4140937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140961 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 1, 1, 6]
def baseStart_4140961 : Nat := 118140960795 + 4140961 * 2 ^ 59
def prefixEnd_4140961 : Nat := 4983230072969 + 3 ^ 40 * 4140961 * 2
def baseEnd_4140961 : Nat := 2126303364522878204743573

theorem tailTrace_4140961 : CollatzResearch.WordTrace tailWord_4140961 prefixEnd_4140961 2126303364522878204743573 := by
  unfold tailWord_4140961
  simp only [CollatzResearch.WordTrace]
  refine ⟨151033255551012991679262737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100688837034008661119508491 151033255551012991679262737)
  ·
    refine ⟨113274941663259743759447053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151033255551012991679262737 113274941663259743759447053)
    ·
      refine ⟨42478103123722403909792645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113274941663259743759447053 42478103123722403909792645)
      ·
        refine ⟨7964644335697950733086121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42478103123722403909792645 7964644335697950733086121)
        ·
          refine ⟨5973483251773463049814591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7964644335697950733086121 5973483251773463049814591)
          ·
            refine ⟨8960224877660194574721887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5973483251773463049814591 8960224877660194574721887)
            ·
              refine ⟨13440337316490291862082831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8960224877660194574721887 13440337316490291862082831)
              ·
                refine ⟨20160505974735437793124247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13440337316490291862082831 20160505974735437793124247)
                ·
                  refine ⟨30240758962103156689686371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20160505974735437793124247 30240758962103156689686371)
                  ·
                    refine ⟨45361138443154735034529557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30240758962103156689686371 45361138443154735034529557)
                    ·
                      refine ⟨2126303364522878204743573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45361138443154735034529557 2126303364522878204743573)
                      ·
                        rfl

theorem cell23_4140961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_4140961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140961 prefixEnd_4140961 := by exact prefixLift 4140961
  have htrace : WordTrace (prefixWord ++ tailWord_4140961) baseStart_4140961 baseEnd_4140961 := by
    simpa [prefixWord, tailWord_4140961, baseEnd_4140961] using wordTrace_append hprefix tailTrace_4140961
  have hstable : (prefixWord ++ tailWord_4140961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140961).length < 2 ^ (prefixWord ++ tailWord_4140961).sum := by decide
  have hdescent : baseEnd_4140961 < baseStart_4140961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140988 : List Nat := [2, 2, 2, 5, 2, 1, 9]
def baseStart_4140988 : Nat := 118140960795 + 4140988 * 2 ^ 59
def prefixEnd_4140988 : Nat := 4983230072969 + 3 ^ 40 * 4140988 * 2
def baseEnd_4140988 : Nat := 26250829981488266655629

theorem tailTrace_4140988 : CollatzResearch.WordTrace tailWord_4140988 prefixEnd_4140988 26250829981488266655629 := by
  unfold tailWord_4140988
  simp only [CollatzResearch.WordTrace]
  refine ⟨75517120160957587645247809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100689493547943450193663745 75517120160957587645247809)
  ·
    refine ⟨56637840120718190733935857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75517120160957587645247809 56637840120718190733935857)
    ·
      refine ⟨42478380090538643050451893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56637840120718190733935857 42478380090538643050451893)
      ·
        refine ⟨3982348133487997785979865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42478380090538643050451893 3982348133487997785979865)
        ·
          refine ⟨2986761100115998339484899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3982348133487997785979865 2986761100115998339484899)
          ·
            refine ⟨4480141650173997509227349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2986761100115998339484899 4480141650173997509227349)
            ·
              refine ⟨26250829981488266655629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4480141650173997509227349 26250829981488266655629)
              ·
                rfl

theorem cell23_4140988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 9].length) (baseStart_4140988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4140988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4140988 prefixEnd_4140988 := by exact prefixLift 4140988
  have htrace : WordTrace (prefixWord ++ tailWord_4140988) baseStart_4140988 baseEnd_4140988 := by
    simpa [prefixWord, tailWord_4140988, baseEnd_4140988] using wordTrace_append hprefix tailTrace_4140988
  have hstable : (prefixWord ++ tailWord_4140988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140988).length < 2 ^ (prefixWord ++ tailWord_4140988).sum := by decide
  have hdescent : baseEnd_4140988 < baseStart_4140988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141038 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 3, 4, 2]
def baseStart_4141038 : Nat := 118140960795 + 4141038 * 2 ^ 59
def prefixEnd_4141038 : Nat := 4983230072969 + 3 ^ 40 * 4141038 * 2
def baseEnd_4141038 : Nat := 2126342902533274403480719

theorem tailTrace_4141038 : CollatzResearch.WordTrace tailWord_4141038 prefixEnd_4141038 2126342902533274403480719 := by
  unfold tailWord_4141038
  simp only [CollatzResearch.WordTrace]
  refine ⟨18879507996466754228726971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100690709314489355886543845 18879507996466754228726971)
  ·
    refine ⟨28319261994700131343090457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18879507996466754228726971 28319261994700131343090457)
    ·
      refine ⟨21239446496025098507317843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28319261994700131343090457 21239446496025098507317843)
      ·
        refine ⟨31859169744037647760976765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21239446496025098507317843 31859169744037647760976765)
        ·
          refine ⟨11947188654014117910366287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31859169744037647760976765 11947188654014117910366287)
          ·
            refine ⟨17920782981021176865549431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11947188654014117910366287 17920782981021176865549431)
            ·
              refine ⟨26881174471531765298324147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17920782981021176865549431 26881174471531765298324147)
              ·
                refine ⟨40321761707297647947486221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26881174471531765298324147 40321761707297647947486221)
                ·
                  refine ⟨15120660640236617980307333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40321761707297647947486221 15120660640236617980307333)
                  ·
                    refine ⟨2835123870044365871307625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15120660640236617980307333 2835123870044365871307625)
                    ·
                      refine ⟨2126342902533274403480719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2835123870044365871307625 2126342902533274403480719)
                      ·
                        rfl

theorem cell23_4141038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_4141038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141038 prefixEnd_4141038 := by exact prefixLift 4141038
  have htrace : WordTrace (prefixWord ++ tailWord_4141038) baseStart_4141038 baseEnd_4141038 := by
    simpa [prefixWord, tailWord_4141038, baseEnd_4141038] using wordTrace_append hprefix tailTrace_4141038
  have hstable : (prefixWord ++ tailWord_4141038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141038).length < 2 ^ (prefixWord ++ tailWord_4141038).sum := by decide
  have hdescent : baseEnd_4141038 < baseStart_4141038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141081 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 4, 5, 2]
def baseStart_4141081 : Nat := 118140960795 + 4141081 * 2 ^ 59
def prefixEnd_4141081 : Nat := 4983230072969 + 3 ^ 40 * 4141081 * 2
def baseEnd_4141081 : Nat := 2126364982201417735243021

theorem tailTrace_4141081 : CollatzResearch.WordTrace tailWord_4141081 prefixEnd_4141081 2126364982201417735243021 := by
  unfold tailWord_4141081
  simp only [CollatzResearch.WordTrace]
  refine ⟨151037632310578252173631097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100691754873718834782420731 151037632310578252173631097)
  ·
    refine ⟨113278224232933689130223323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151037632310578252173631097 113278224232933689130223323)
    ·
      refine ⟨169917336349400533695334985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113278224232933689130223323 169917336349400533695334985)
      ·
        refine ⟨127438002262050400271501239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169917336349400533695334985 127438002262050400271501239)
        ·
          refine ⟨191157003393075600407251859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127438002262050400271501239 191157003393075600407251859)
          ·
            refine ⟨286735505089613400610877789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191157003393075600407251859 286735505089613400610877789)
            ·
              refine ⟨107525814408605025229079171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286735505089613400610877789 107525814408605025229079171)
              ·
                refine ⟨161288721612907537843618757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107525814408605025229079171 161288721612907537843618757)
                ·
                  refine ⟨30241635302420163345678517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161288721612907537843618757 30241635302420163345678517)
                  ·
                    refine ⟨2835153309601890313657361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30241635302420163345678517 2835153309601890313657361)
                    ·
                      refine ⟨2126364982201417735243021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2835153309601890313657361 2126364982201417735243021)
                      ·
                        rfl

theorem cell23_4141081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 5, 2].length) (baseStart_4141081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141081 prefixEnd_4141081 := by exact prefixLift 4141081
  have htrace : WordTrace (prefixWord ++ tailWord_4141081) baseStart_4141081 baseEnd_4141081 := by
    simpa [prefixWord, tailWord_4141081, baseEnd_4141081] using wordTrace_append hprefix tailTrace_4141081
  have hstable : (prefixWord ++ tailWord_4141081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141081).length < 2 ^ (prefixWord ++ tailWord_4141081).sum := by decide
  have hdescent : baseEnd_4141081 < baseStart_4141081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141111 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 4]
def baseStart_4141111 : Nat := 118140960795 + 4141111 * 2 ^ 59
def prefixEnd_4141111 : Nat := 4983230072969 + 3 ^ 40 * 4141111 * 2
def baseEnd_4141111 : Nat := 2126380386621052617867883

theorem tailTrace_4141111 : CollatzResearch.WordTrace tailWord_4141111 prefixEnd_4141111 2126380386621052617867883 := by
  unfold tailWord_4141111
  simp only [CollatzResearch.WordTrace]
  refine ⟨151038726500469567297223187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100692484333646378198148791 151038726500469567297223187)
  ·
    refine ⟨226558089750704350945834781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151038726500469567297223187 226558089750704350945834781)
    ·
      refine ⟨84959283656514131604688043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226558089750704350945834781 84959283656514131604688043)
      ·
        refine ⟨127438925484771197407032065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84959283656514131604688043 127438925484771197407032065)
        ·
          refine ⟨95579194113578398055274049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127438925484771197407032065 95579194113578398055274049)
          ·
            refine ⟨71684395585183798541455537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95579194113578398055274049 71684395585183798541455537)
            ·
              refine ⟨53763296688887848906091653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71684395585183798541455537 53763296688887848906091653)
              ·
                refine ⟨10080618129166471669892185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53763296688887848906091653 10080618129166471669892185)
                ·
                  refine ⟨7560463596874853752419139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10080618129166471669892185 7560463596874853752419139)
                  ·
                    refine ⟨11340695395312280628628709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7560463596874853752419139 11340695395312280628628709)
                    ·
                      refine ⟨2126380386621052617867883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11340695395312280628628709 2126380386621052617867883)
                      ·
                        rfl

theorem cell23_4141111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_4141111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141111 prefixEnd_4141111 := by exact prefixLift 4141111
  have htrace : WordTrace (prefixWord ++ tailWord_4141111) baseStart_4141111 baseEnd_4141111 := by
    simpa [prefixWord, tailWord_4141111, baseEnd_4141111] using wordTrace_append hprefix tailTrace_4141111
  have hstable : (prefixWord ++ tailWord_4141111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141111).length < 2 ^ (prefixWord ++ tailWord_4141111).sum := by decide
  have hdescent : baseEnd_4141111 < baseStart_4141111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141131 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 3]
def baseStart_4141131 : Nat := 118140960795 + 4141131 * 2 ^ 59
def prefixEnd_4141131 : Nat := 4983230072969 + 3 ^ 40 * 4141131 * 2
def baseEnd_4141131 : Nat := 2126390656234142539617791

theorem tailTrace_4141131 : CollatzResearch.WordTrace tailWord_4141131 prefixEnd_4141131 2126390656234142539617791 := by
  unfold tailWord_4141131
  simp only [CollatzResearch.WordTrace]
  refine ⟨151039455960397110712951247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100692970640264740475300831 151039455960397110712951247)
  ·
    refine ⟨226559183940595666069426871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151039455960397110712951247 226559183940595666069426871)
    ·
      refine ⟨339838775910893499104140307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226559183940595666069426871 339838775910893499104140307)
      ·
        refine ⟨509758163866340248656210461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339838775910893499104140307 509758163866340248656210461)
        ·
          refine ⟨191159311449877593246078923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 509758163866340248656210461 191159311449877593246078923)
          ·
            refine ⟨286738967174816389869118385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191159311449877593246078923 286738967174816389869118385)
            ·
              refine ⟨215054225381112292401838789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286738967174816389869118385 215054225381112292401838789)
              ·
                refine ⟨40322667258958554825344773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215054225381112292401838789 40322667258958554825344773)
                ·
                  refine ⟨7560500111054729029752145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40322667258958554825344773 7560500111054729029752145)
                  ·
                    refine ⟨5670375083291046772314109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7560500111054729029752145 5670375083291046772314109)
                    ·
                      refine ⟨2126390656234142539617791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5670375083291046772314109 2126390656234142539617791)
                      ·
                        rfl

theorem cell23_4141131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 3].length) (baseStart_4141131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141131 prefixEnd_4141131 := by exact prefixLift 4141131
  have htrace : WordTrace (prefixWord ++ tailWord_4141131) baseStart_4141131 baseEnd_4141131 := by
    simpa [prefixWord, tailWord_4141131, baseEnd_4141131] using wordTrace_append hprefix tailTrace_4141131
  have hstable : (prefixWord ++ tailWord_4141131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141131).length < 2 ^ (prefixWord ++ tailWord_4141131).sum := by decide
  have hdescent : baseEnd_4141131 < baseStart_4141131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141148 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_4141148 : Nat := 118140960795 + 4141148 * 2 ^ 59
def prefixEnd_4141148 : Nat := 4983230072969 + 3 ^ 40 * 4141148 * 2
def baseEnd_4141148 : Nat := 2126399385405268973105213

theorem tailTrace_4141148 : CollatzResearch.WordTrace tailWord_4141148 prefixEnd_4141148 2126399385405268973105213 := by
  unfold tailWord_4141148
  simp only [CollatzResearch.WordTrace]
  refine ⟨75520038000667761308160049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100693384000890348410880065 75520038000667761308160049)
  ·
    refine ⟨56640028500500820981120037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75520038000667761308160049 56640028500500820981120037)
    ·
      refine ⟨10620005343843903933960007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56640028500500820981120037 10620005343843903933960007)
      ·
        refine ⟨15930008015765855900940011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10620005343843903933960007 15930008015765855900940011)
        ·
          refine ⟨23895012023648783851410017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15930008015765855900940011 23895012023648783851410017)
          ·
            refine ⟨17921259017736587888557513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23895012023648783851410017 17921259017736587888557513)
            ·
              refine ⟨13440944263302440916418135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17921259017736587888557513 13440944263302440916418135)
              ·
                refine ⟨20161416394953661374627203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13440944263302440916418135 20161416394953661374627203)
                ·
                  refine ⟨30242124592430492061940805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20161416394953661374627203 30242124592430492061940805)
                  ·
                    refine ⟨5670398361080717261613901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30242124592430492061940805 5670398361080717261613901)
                    ·
                      refine ⟨2126399385405268973105213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5670398361080717261613901 2126399385405268973105213)
                      ·
                        rfl

theorem cell23_4141148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_4141148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141148 prefixEnd_4141148 := by exact prefixLift 4141148
  have htrace : WordTrace (prefixWord ++ tailWord_4141148) baseStart_4141148 baseEnd_4141148 := by
    simpa [prefixWord, tailWord_4141148, baseEnd_4141148] using wordTrace_append hprefix tailTrace_4141148
  have hstable : (prefixWord ++ tailWord_4141148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141148).length < 2 ^ (prefixWord ++ tailWord_4141148).sum := by decide
  have hdescent : baseEnd_4141148 < baseStart_4141148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141155 : List Nat := [1, 1, 1, 5, 1, 1, 5, 3, 1, 4]
def baseStart_4141155 : Nat := 118140960795 + 4141155 * 2 ^ 59
def prefixEnd_4141155 : Nat := 4983230072969 + 3 ^ 40 * 4141155 * 2
def baseEnd_4141155 : Nat := 708800993256616815239227

theorem tailTrace_4141155 : CollatzResearch.WordTrace tailWord_4141155 prefixEnd_4141155 708800993256616815239227 := by
  unfold tailWord_4141155
  simp only [CollatzResearch.WordTrace]
  refine ⟨151040331312310162811824919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100693554208206775207883279 151040331312310162811824919)
  ·
    refine ⟨226560496968465244217737379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151040331312310162811824919 226560496968465244217737379)
    ·
      refine ⟨339840745452697866326606069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226560496968465244217737379 339840745452697866326606069)
      ·
        refine ⟨31860069886190424968119319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 339840745452697866326606069 31860069886190424968119319)
        ·
          refine ⟨47790104829285637452178979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31860069886190424968119319 47790104829285637452178979)
          ·
            refine ⟨71685157243928456178268469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47790104829285637452178979 71685157243928456178268469)
            ·
              refine ⟨6720483491618292766712669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71685157243928456178268469 6720483491618292766712669)
              ·
                refine ⟨2520181309356859787517251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6720483491618292766712669 2520181309356859787517251)
                ·
                  refine ⟨3780271964035289681275877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2520181309356859787517251 3780271964035289681275877)
                  ·
                    refine ⟨708800993256616815239227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3780271964035289681275877 708800993256616815239227)
                    ·
                      rfl

theorem cell23_4141155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 1, 4].length) (baseStart_4141155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141155 prefixEnd_4141155 := by exact prefixLift 4141155
  have htrace : WordTrace (prefixWord ++ tailWord_4141155) baseStart_4141155 baseEnd_4141155 := by
    simpa [prefixWord, tailWord_4141155, baseEnd_4141155] using wordTrace_append hprefix tailTrace_4141155
  have hstable : (prefixWord ++ tailWord_4141155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141155).length < 2 ^ (prefixWord ++ tailWord_4141155).sum := by decide
  have hdescent : baseEnd_4141155 < baseStart_4141155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141205 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 2, 3, 2]
def baseStart_4141205 : Nat := 118140960795 + 4141205 * 2 ^ 59
def prefixEnd_4141205 : Nat := 4983230072969 + 3 ^ 40 * 4141205 * 2
def baseEnd_4141205 : Nat := 2126428653802575250092451

theorem tailTrace_4141205 : CollatzResearch.WordTrace tailWord_4141205 prefixEnd_4141205 2126428653802575250092451 := by
  unfold tailWord_4141205
  simp only [CollatzResearch.WordTrace]
  refine ⟨151042154962129021351145069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100694769974752680900763379 151042154962129021351145069)
  ·
    refine ⟨56640808110798383006679401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151042154962129021351145069 56640808110798383006679401)
    ·
      refine ⟨42480606083098787255009551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56640808110798383006679401 42480606083098787255009551)
      ·
        refine ⟨63720909124648180882514327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42480606083098787255009551 63720909124648180882514327)
        ·
          refine ⟨95581363686972271323771491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63720909124648180882514327 95581363686972271323771491)
          ·
            refine ⟨143372045530458406985657237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95581363686972271323771491 143372045530458406985657237)
            ·
              refine ⟨6720564634240237827452683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 143372045530458406985657237 6720564634240237827452683)
              ·
                refine ⟨10080846951360356741179025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6720564634240237827452683 10080846951360356741179025)
                ·
                  refine ⟨7560635213520267555884269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10080846951360356741179025 7560635213520267555884269)
                  ·
                    refine ⟨2835238205070100333456601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7560635213520267555884269 2835238205070100333456601)
                    ·
                      refine ⟨2126428653802575250092451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2835238205070100333456601 2126428653802575250092451)
                      ·
                        rfl

theorem cell23_4141205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_4141205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141205 prefixEnd_4141205 := by exact prefixLift 4141205
  have htrace : WordTrace (prefixWord ++ tailWord_4141205) baseStart_4141205 baseEnd_4141205 := by
    simpa [prefixWord, tailWord_4141205, baseEnd_4141205] using wordTrace_append hprefix tailTrace_4141205
  have hstable : (prefixWord ++ tailWord_4141205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141205).length < 2 ^ (prefixWord ++ tailWord_4141205).sum := by decide
  have hdescent : baseEnd_4141205 < baseStart_4141205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141212 : List Nat := [2, 2, 3, 2, 1, 1, 2, 5, 1, 1, 3]
def baseStart_4141212 : Nat := 118140960795 + 4141212 * 2 ^ 59
def prefixEnd_4141212 : Nat := 4983230072969 + 3 ^ 40 * 4141212 * 2
def baseEnd_4141212 : Nat := 2126432248167156722704919

theorem tailTrace_4141212 : CollatzResearch.WordTrace tailWord_4141212 prefixEnd_4141212 2126432248167156722704919 := by
  unfold tailWord_4141212
  simp only [CollatzResearch.WordTrace]
  refine ⟨75521205136551830773324945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100694940182069107697766593 75521205136551830773324945)
  ·
    refine ⟨56640903852413873079993709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75521205136551830773324945 56640903852413873079993709)
    ·
      refine ⟨21240338944655202404997641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56640903852413873079993709 21240338944655202404997641)
      ·
        refine ⟨15930254208491401803748231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21240338944655202404997641 15930254208491401803748231)
        ·
          refine ⟨23895381312737102705622347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15930254208491401803748231 23895381312737102705622347)
          ·
            refine ⟨35843071969105654058433521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23895381312737102705622347 35843071969105654058433521)
            ·
              refine ⟨26882303976829240543825141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35843071969105654058433521 26882303976829240543825141)
              ·
                refine ⟨2520215997827741300983607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26882303976829240543825141 2520215997827741300983607)
                ·
                  refine ⟨3780323996741611951475411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2520215997827741300983607 3780323996741611951475411)
                  ·
                    refine ⟨5670485995112417927213117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3780323996741611951475411 5670485995112417927213117)
                    ·
                      refine ⟨2126432248167156722704919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5670485995112417927213117 2126432248167156722704919)
                      ·
                        rfl

theorem cell23_4141212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_4141212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141212 prefixEnd_4141212 := by exact prefixLift 4141212
  have htrace : WordTrace (prefixWord ++ tailWord_4141212) baseStart_4141212 baseEnd_4141212 := by
    simpa [prefixWord, tailWord_4141212, baseEnd_4141212] using wordTrace_append hprefix tailTrace_4141212
  have hstable : (prefixWord ++ tailWord_4141212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141212).length < 2 ^ (prefixWord ++ tailWord_4141212).sum := by decide
  have hdescent : baseEnd_4141212 < baseStart_4141212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141229 : List Nat := [1, 5, 2, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_4141229 : Nat := 118140960795 + 4141229 * 2 ^ 59
def prefixEnd_4141229 : Nat := 4983230072969 + 3 ^ 40 * 4141229 * 2
def baseEnd_4141229 : Nat := 2126440977338283156192341

theorem tailTrace_4141229 : CollatzResearch.WordTrace tailWord_4141229 prefixEnd_4141229 2126440977338283156192341 := by
  unfold tailWord_4141229
  simp only [CollatzResearch.WordTrace]
  refine ⟨151043030314042073450018741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100695353542694715633345827 151043030314042073450018741)
  ·
    refine ⟨14160284091941444385939257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151043030314042073450018741 14160284091941444385939257)
    ·
      refine ⟨10620213068956083289454443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14160284091941444385939257 10620213068956083289454443)
      ·
        refine ⟨15930319603434124934181665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10620213068956083289454443 15930319603434124934181665)
        ·
          refine ⟨11947739702575593700636249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15930319603434124934181665 11947739702575593700636249)
          ·
            refine ⟨8960804776931695275477187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11947739702575593700636249 8960804776931695275477187)
            ·
              refine ⟨13441207165397542913215781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8960804776931695275477187 13441207165397542913215781)
              ·
                refine ⟨2520226343512039296227959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13441207165397542913215781 2520226343512039296227959)
                ·
                  refine ⟨3780339515268058944341939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2520226343512039296227959 3780339515268058944341939)
                  ·
                    refine ⟨5670509272902088416512909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3780339515268058944341939 5670509272902088416512909)
                    ·
                      refine ⟨2126440977338283156192341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5670509272902088416512909 2126440977338283156192341)
                      ·
                        rfl

theorem cell23_4141229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_4141229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141229 prefixEnd_4141229 := by exact prefixLift 4141229
  have htrace : WordTrace (prefixWord ++ tailWord_4141229) baseStart_4141229 baseEnd_4141229 := by
    simpa [prefixWord, tailWord_4141229, baseEnd_4141229] using wordTrace_append hprefix tailTrace_4141229
  have hstable : (prefixWord ++ tailWord_4141229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141229).length < 2 ^ (prefixWord ++ tailWord_4141229).sum := by decide
  have hdescent : baseEnd_4141229 < baseStart_4141229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141231 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 4]
def baseStart_4141231 : Nat := 118140960795 + 4141231 * 2 ^ 59
def prefixEnd_4141231 : Nat := 4983230072969 + 3 ^ 40 * 4141231 * 2
def baseEnd_4141231 : Nat := 2126442004299592148367331

theorem tailTrace_4141231 : CollatzResearch.WordTrace tailWord_4141231 prefixEnd_4141231 2126442004299592148367331 := by
  unfold tailWord_4141231
  simp only [CollatzResearch.WordTrace]
  refine ⟨151043103260034827791591547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100695402173356551861061031 151043103260034827791591547)
  ·
    refine ⟨226564654890052241687387321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151043103260034827791591547 226564654890052241687387321)
    ·
      refine ⟨169923491167539181265540491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226564654890052241687387321 169923491167539181265540491)
      ·
        refine ⟨254885236751308771898310737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169923491167539181265540491 254885236751308771898310737)
        ·
          refine ⟨191163927563481578923733053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254885236751308771898310737 191163927563481578923733053)
          ·
            refine ⟨71686472836305592096399895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191163927563481578923733053 71686472836305592096399895)
            ·
              refine ⟨107529709254458388144599843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71686472836305592096399895 107529709254458388144599843)
              ·
                refine ⟨161294563881687582216899765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107529709254458388144599843 161294563881687582216899765)
                ·
                  refine ⟨15121365363908210832834353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161294563881687582216899765 15121365363908210832834353)
                  ·
                    refine ⟨11341024022931158124625765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15121365363908210832834353 11341024022931158124625765)
                    ·
                      refine ⟨2126442004299592148367331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11341024022931158124625765 2126442004299592148367331)
                      ·
                        rfl

theorem cell23_4141231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_4141231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141231 prefixEnd_4141231 := by exact prefixLift 4141231
  have htrace : WordTrace (prefixWord ++ tailWord_4141231) baseStart_4141231 baseEnd_4141231 := by
    simpa [prefixWord, tailWord_4141231, baseEnd_4141231] using wordTrace_append hprefix tailTrace_4141231
  have hstable : (prefixWord ++ tailWord_4141231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141231).length < 2 ^ (prefixWord ++ tailWord_4141231).sum := by decide
  have hdescent : baseEnd_4141231 < baseStart_4141231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141235 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 3, 2, 2]
def baseStart_4141235 : Nat := 118140960795 + 4141235 * 2 ^ 59
def prefixEnd_4141235 : Nat := 4983230072969 + 3 ^ 40 * 4141235 * 2
def baseEnd_4141235 : Nat := 2126444058222210132717313

theorem tailTrace_4141235 : CollatzResearch.WordTrace tailWord_4141235 prefixEnd_4141235 2126444058222210132717313 := by
  unfold tailWord_4141235
  simp only [CollatzResearch.WordTrace]
  refine ⟨151043249152020336474737159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100695499434680224316491439 151043249152020336474737159)
  ·
    refine ⟨226564873728030504712105739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151043249152020336474737159 226564873728030504712105739)
    ·
      refine ⟨339847310592045757068158609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226564873728030504712105739 339847310592045757068158609)
      ·
        refine ⟨254885482944034317801118957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339847310592045757068158609 254885482944034317801118957)
        ·
          refine ⟨95582056104012869175419609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254885482944034317801118957 95582056104012869175419609)
          ·
            refine ⟨71686542078009651881564707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95582056104012869175419609 71686542078009651881564707)
            ·
              refine ⟨107529813117014477822347061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71686542078009651881564707 107529813117014477822347061)
              ·
                refine ⟨10080919979720107295845037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107529813117014477822347061 10080919979720107295845037)
                ·
                  refine ⟨3780344992395040235941889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10080919979720107295845037 3780344992395040235941889)
                  ·
                    refine ⟨2835258744296280176956417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3780344992395040235941889 2835258744296280176956417)
                    ·
                      refine ⟨2126444058222210132717313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2835258744296280176956417 2126444058222210132717313)
                      ·
                        rfl

theorem cell23_4141235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 2, 2].length) (baseStart_4141235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141235 prefixEnd_4141235 := by exact prefixLift 4141235
  have htrace : WordTrace (prefixWord ++ tailWord_4141235) baseStart_4141235 baseEnd_4141235 := by
    simpa [prefixWord, tailWord_4141235, baseEnd_4141235] using wordTrace_append hprefix tailTrace_4141235
  have hstable : (prefixWord ++ tailWord_4141235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141235).length < 2 ^ (prefixWord ++ tailWord_4141235).sum := by decide
  have hdescent : baseEnd_4141235 < baseStart_4141235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141248 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 4]
def baseStart_4141248 : Nat := 118140960795 + 4141248 * 2 ^ 59
def prefixEnd_4141248 : Nat := 4983230072969 + 3 ^ 40 * 4141248 * 2
def baseEnd_4141248 : Nat := 2126450733470718581854753

theorem tailTrace_4141248 : CollatzResearch.WordTrace tailWord_4141248 prefixEnd_4141248 2126450733470718581854753 := by
  unfold tailWord_4141248
  simp only [CollatzResearch.WordTrace]
  refine ⟨75521861650486619847480199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100695815533982159796640265 75521861650486619847480199)
  ·
    refine ⟨113282792475729929771220299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75521861650486619847480199 113282792475729929771220299)
    ·
      refine ⟨169924188713594894656830449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113282792475729929771220299 169924188713594894656830449)
      ·
        refine ⟨127443141535196170992622837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169924188713594894656830449 127443141535196170992622837)
        ·
          refine ⟨11947794518924641030558391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127443141535196170992622837 11947794518924641030558391)
          ·
            refine ⟨17921691778386961545837587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11947794518924641030558391 17921691778386961545837587)
            ·
              refine ⟨26882537667580442318756381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17921691778386961545837587 26882537667580442318756381)
              ·
                refine ⟨10080951625342665869533643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26882537667580442318756381 10080951625342665869533643)
                ·
                  refine ⟨15121427438013998804300465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10080951625342665869533643 15121427438013998804300465)
                  ·
                    refine ⟨11341070578510499103225349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15121427438013998804300465 11341070578510499103225349)
                    ·
                      refine ⟨2126450733470718581854753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11341070578510499103225349 2126450733470718581854753)
                      ·
                        rfl

theorem cell23_4141248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_4141248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141248 prefixEnd_4141248 := by exact prefixLift 4141248
  have htrace : WordTrace (prefixWord ++ tailWord_4141248) baseStart_4141248 baseEnd_4141248 := by
    simpa [prefixWord, tailWord_4141248, baseEnd_4141248] using wordTrace_append hprefix tailTrace_4141248
  have hstable : (prefixWord ++ tailWord_4141248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141248).length < 2 ^ (prefixWord ++ tailWord_4141248).sum := by decide
  have hdescent : baseEnd_4141248 < baseStart_4141248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141252 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_4141252 : Nat := 118140960795 + 4141252 * 2 ^ 59
def prefixEnd_4141252 : Nat := 4983230072969 + 3 ^ 40 * 4141252 * 2
def baseEnd_4141252 : Nat := 2126452787393336566204735

theorem tailTrace_4141252 : CollatzResearch.WordTrace tailWord_4141252 prefixEnd_4141252 2126452787393336566204735 := by
  unfold tailWord_4141252
  simp only [CollatzResearch.WordTrace]
  refine ⟨75521934596479374189053005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100695912795305832252070673 75521934596479374189053005)
  ·
    refine ⟨28320725473679765320894877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75521934596479374189053005 28320725473679765320894877)
    ·
      refine ⟨10620272052629911995335579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28320725473679765320894877 10620272052629911995335579)
      ·
        refine ⟨15930408078944867993003369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10620272052629911995335579 15930408078944867993003369)
        ·
          refine ⟨11947806059208650994752527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15930408078944867993003369 11947806059208650994752527)
          ·
            refine ⟨17921709088812976492128791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11947806059208650994752527 17921709088812976492128791)
            ·
              refine ⟨26882563633219464738193187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17921709088812976492128791 26882563633219464738193187)
              ·
                refine ⟨40323845449829197107289781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26882563633219464738193187 40323845449829197107289781)
                ·
                  refine ⟨3780360510921487228808417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40323845449829197107289781 3780360510921487228808417)
                  ·
                    refine ⟨2835270383191115421606313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3780360510921487228808417 2835270383191115421606313)
                    ·
                      refine ⟨2126452787393336566204735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2835270383191115421606313 2126452787393336566204735)
                      ·
                        rfl

theorem cell23_4141252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_4141252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141252 prefixEnd_4141252 := by exact prefixLift 4141252
  have htrace : WordTrace (prefixWord ++ tailWord_4141252) baseStart_4141252 baseEnd_4141252 := by
    simpa [prefixWord, tailWord_4141252, baseEnd_4141252] using wordTrace_append hprefix tailTrace_4141252
  have hstable : (prefixWord ++ tailWord_4141252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141252).length < 2 ^ (prefixWord ++ tailWord_4141252).sum := by decide
  have hdescent : baseEnd_4141252 < baseStart_4141252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141258 : List Nat := [3, 1, 2, 1, 3, 1, 5, 7]
def baseStart_4141258 : Nat := 118140960795 + 4141258 * 2 ^ 59
def prefixEnd_4141258 : Nat := 4983230072969 + 3 ^ 40 * 4141258 * 2
def baseEnd_4141258 : Nat := 78757624751009760841841

theorem tailTrace_4141258 : CollatzResearch.WordTrace tailWord_4141258 prefixEnd_4141258 78757624751009760841841 := by
  unfold tailWord_4141258
  simp only [CollatzResearch.WordTrace]
  refine ⟨37761022007734252850706107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100696058687291340935216285 37761022007734252850706107)
  ·
    refine ⟨56641533011601379276059161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37761022007734252850706107 56641533011601379276059161)
    ·
      refine ⟨42481149758701034457044371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56641533011601379276059161 42481149758701034457044371)
      ·
        refine ⟨63721724638051551685566557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42481149758701034457044371 63721724638051551685566557)
        ·
          refine ⟨23895646739269331882087459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63721724638051551685566557 23895646739269331882087459)
          ·
            refine ⟨35843470108903997823131189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23895646739269331882087459 35843470108903997823131189)
            ·
              refine ⟨3360325322709749795918549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35843470108903997823131189 3360325322709749795918549)
              ·
                refine ⟨78757624751009760841841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3360325322709749795918549 78757624751009760841841)
                ·
                  rfl

theorem cell23_4141258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 7].length) (baseStart_4141258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141258 prefixEnd_4141258 := by exact prefixLift 4141258
  have htrace : WordTrace (prefixWord ++ tailWord_4141258) baseStart_4141258 baseEnd_4141258 := by
    simpa [prefixWord, tailWord_4141258, baseEnd_4141258] using wordTrace_append hprefix tailTrace_4141258
  have hstable : (prefixWord ++ tailWord_4141258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141258).length < 2 ^ (prefixWord ++ tailWord_4141258).sum := by decide
  have hdescent : baseEnd_4141258 < baseStart_4141258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141269 : List Nat := [1, 3, 2, 4, 2, 2, 2, 1, 1, 1, 4]
def baseStart_4141269 : Nat := 118140960795 + 4141269 * 2 ^ 59
def prefixEnd_4141269 : Nat := 4983230072969 + 3 ^ 40 * 4141269 * 2
def baseEnd_4141269 : Nat := 2126461516564462999692157

theorem tailTrace_4141269 : CollatzResearch.WordTrace tailWord_4141269 prefixEnd_4141269 2126461516564462999692157 := by
  unfold tailWord_4141269
  simp only [CollatzResearch.WordTrace]
  refine ⟨151044489233897160281474861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100696326155931440187649907 151044489233897160281474861)
  ·
    refine ⟨56641683462711435105553073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151044489233897160281474861 56641683462711435105553073)
    ·
      refine ⟨42481262597033576329164805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56641683462711435105553073 42481262597033576329164805)
      ·
        refine ⟨7965236736943795561718401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42481262597033576329164805 7965236736943795561718401)
        ·
          refine ⟨5973927552707846671288801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7965236736943795561718401 5973927552707846671288801)
          ·
            refine ⟨4480445664530885003466601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5973927552707846671288801 4480445664530885003466601)
            ·
              refine ⟨3360334248398163752599951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4480445664530885003466601 3360334248398163752599951)
              ·
                refine ⟨5040501372597245628899927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3360334248398163752599951 5040501372597245628899927)
                ·
                  refine ⟨7560752058895868443349891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040501372597245628899927 7560752058895868443349891)
                  ·
                    refine ⟨11341128088343802665024837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7560752058895868443349891 11341128088343802665024837)
                    ·
                      refine ⟨2126461516564462999692157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11341128088343802665024837 2126461516564462999692157)
                      ·
                        rfl

theorem cell23_4141269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_4141269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141269 prefixEnd_4141269 := by exact prefixLift 4141269
  have htrace : WordTrace (prefixWord ++ tailWord_4141269) baseStart_4141269 baseEnd_4141269 := by
    simpa [prefixWord, tailWord_4141269, baseEnd_4141269] using wordTrace_append hprefix tailTrace_4141269
  have hstable : (prefixWord ++ tailWord_4141269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141269).length < 2 ^ (prefixWord ++ tailWord_4141269).sum := by decide
  have hdescent : baseEnd_4141269 < baseStart_4141269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141272 : List Nat := [2, 1, 2, 2, 4, 1, 4, 1, 1, 2, 3]
def baseStart_4141272 : Nat := 118140960795 + 4141272 * 2 ^ 59
def prefixEnd_4141272 : Nat := 4983230072969 + 3 ^ 40 * 4141272 * 2
def baseEnd_4141272 : Nat := 2126463057006426487954643

theorem tailTrace_4141272 : CollatzResearch.WordTrace tailWord_4141272 prefixEnd_4141272 2126463057006426487954643 := by
  unfold tailWord_4141272
  simp only [CollatzResearch.WordTrace]
  refine ⟨75522299326443145896917035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100696399101924194529222713 75522299326443145896917035)
  ·
    refine ⟨113283448989664718845375553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75522299326443145896917035 113283448989664718845375553)
    ·
      refine ⟨84962586742248539134031665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113283448989664718845375553 84962586742248539134031665)
      ·
        refine ⟨63721940056686404350523749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84962586742248539134031665 63721940056686404350523749)
        ·
          refine ⟨11947863760628700815723203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63721940056686404350523749 11947863760628700815723203)
          ·
            refine ⟨17921795640943051223584805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11947863760628700815723203 17921795640943051223584805)
            ·
              refine ⟨3360336682676822104422151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17921795640943051223584805 3360336682676822104422151)
              ·
                refine ⟨5040505024015233156633227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3360336682676822104422151 5040505024015233156633227)
                ·
                  refine ⟨7560757536022849734949841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040505024015233156633227 7560757536022849734949841)
                  ·
                    refine ⟨5670568152017137301212381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7560757536022849734949841 5670568152017137301212381)
                    ·
                      refine ⟨2126463057006426487954643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5670568152017137301212381 2126463057006426487954643)
                      ·
                        rfl

theorem cell23_4141272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_4141272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141272 prefixEnd_4141272 := by exact prefixLift 4141272
  have htrace : WordTrace (prefixWord ++ tailWord_4141272) baseStart_4141272 baseEnd_4141272 := by
    simpa [prefixWord, tailWord_4141272, baseEnd_4141272] using wordTrace_append hprefix tailTrace_4141272
  have hstable : (prefixWord ++ tailWord_4141272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141272).length < 2 ^ (prefixWord ++ tailWord_4141272).sum := by decide
  have hdescent : baseEnd_4141272 < baseStart_4141272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141302 : List Nat := [5, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_4141302 : Nat := 118140960795 + 4141302 * 2 ^ 59
def prefixEnd_4141302 : Nat := 4983230072969 + 3 ^ 40 * 4141302 * 2
def baseEnd_4141302 : Nat := 2126478461426061370579505

theorem tailTrace_4141302 : CollatzResearch.WordTrace tailWord_4141302 prefixEnd_4141302 2126478461426061370579505 := by
  unfold tailWord_4141302
  simp only [CollatzResearch.WordTrace]
  refine ⟨9440355802673600432339135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100697128561851737944950773 9440355802673600432339135)
  ·
    refine ⟨14160533704010400648508703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9440355802673600432339135 14160533704010400648508703)
    ·
      refine ⟨21240800556015600972763055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14160533704010400648508703 21240800556015600972763055)
      ·
        refine ⟨31861200834023401459144583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21240800556015600972763055 31861200834023401459144583)
        ·
          refine ⟨47791801251035102188716875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31861200834023401459144583 47791801251035102188716875)
          ·
            refine ⟨71687701876552653283075313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47791801251035102188716875 71687701876552653283075313)
            ·
              refine ⟨53765776407414489962306485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71687701876552653283075313 53765776407414489962306485)
              ·
                refine ⟨5040541538195108433966233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53765776407414489962306485 5040541538195108433966233)
                ·
                  refine ⟨3780406153646331325474675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5040541538195108433966233 3780406153646331325474675)
                  ·
                    refine ⟨5670609230469496988212013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3780406153646331325474675 5670609230469496988212013)
                    ·
                      refine ⟨2126478461426061370579505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5670609230469496988212013 2126478461426061370579505)
                      ·
                        rfl

theorem cell23_4141302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_4141302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141302 prefixEnd_4141302 := by exact prefixLift 4141302
  have htrace : WordTrace (prefixWord ++ tailWord_4141302) baseStart_4141302 baseEnd_4141302 := by
    simpa [prefixWord, tailWord_4141302, baseEnd_4141302] using wordTrace_append hprefix tailTrace_4141302
  have hstable : (prefixWord ++ tailWord_4141302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141302).length < 2 ^ (prefixWord ++ tailWord_4141302).sum := by decide
  have hdescent : baseEnd_4141302 < baseStart_4141302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141331 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 9]
def baseStart_4141331 : Nat := 118140960795 + 4141331 * 2 ^ 59
def prefixEnd_4141331 : Nat := 4983230072969 + 3 ^ 40 * 4141331 * 2
def baseEnd_4141331 : Nat := 236277039151671306346319

theorem tailTrace_4141331 : CollatzResearch.WordTrace tailWord_4141331 prefixEnd_4141331 236277039151671306346319 := by
  unfold tailWord_4141331
  simp only [CollatzResearch.WordTrace]
  refine ⟨151046750559672544870231847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100697833706448363246821231 151046750559672544870231847)
  ·
    refine ⟨226570125839508817305347771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151046750559672544870231847 226570125839508817305347771)
    ·
      refine ⟨339855188759263225958021657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226570125839508817305347771 339855188759263225958021657)
      ·
        refine ⟨254891391569447419468516243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339855188759263225958021657 254891391569447419468516243)
        ·
          refine ⟨382337087354171129202774365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254891391569447419468516243 382337087354171129202774365)
          ·
            refine ⟨143376407757814173451040387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382337087354171129202774365 143376407757814173451040387)
            ·
              refine ⟨215064611636721260176560581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143376407757814173451040387 215064611636721260176560581)
              ·
                refine ⟨40324614681885236283105109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215064611636721260176560581 40324614681885236283105109)
                ·
                  refine ⟨236277039151671306346319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40324614681885236283105109 236277039151671306346319)
                  ·
                    rfl

theorem cell23_4141331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 9].length) (baseStart_4141331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141331 prefixEnd_4141331 := by exact prefixLift 4141331
  have htrace : WordTrace (prefixWord ++ tailWord_4141331) baseStart_4141331 baseEnd_4141331 := by
    simpa [prefixWord, tailWord_4141331, baseEnd_4141331] using wordTrace_append hprefix tailTrace_4141331
  have hstable : (prefixWord ++ tailWord_4141331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141331).length < 2 ^ (prefixWord ++ tailWord_4141331).sum := by decide
  have hdescent : baseEnd_4141331 < baseStart_4141331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141359 : List Nat := [1, 1, 2, 1, 2, 1, 8, 1, 2, 2, 2]
def baseStart_4141359 : Nat := 118140960795 + 4141359 * 2 ^ 59
def prefixEnd_4141359 : Nat := 4983230072969 + 3 ^ 40 * 4141359 * 2
def baseEnd_4141359 : Nat := 2126507729823367647566743

theorem tailTrace_4141359 : CollatzResearch.WordTrace tailWord_4141359 prefixEnd_4141359 2126507729823367647566743 := by
  unfold tailWord_4141359
  simp only [CollatzResearch.WordTrace]
  refine ⟨151047771803571105652251131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100698514535714070434834087 151047771803571105652251131)
  ·
    refine ⟨226571657705356658478376697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151047771803571105652251131 226571657705356658478376697)
    ·
      refine ⟨169928743279017493858782523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226571657705356658478376697 169928743279017493858782523)
      ·
        refine ⟨254893114918526240788173785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169928743279017493858782523 254893114918526240788173785)
        ·
          refine ⟨191169836188894680591130339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254893114918526240788173785 191169836188894680591130339)
          ·
            refine ⟨286754754283342020886695509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191169836188894680591130339 286754754283342020886695509)
            ·
              refine ⟨3360407276757914307265963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 286754754283342020886695509 3360407276757914307265963)
              ·
                refine ⟨5040610915136871460898945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3360407276757914307265963 5040610915136871460898945)
                ·
                  refine ⟨3780458186352653595674209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5040610915136871460898945 3780458186352653595674209)
                  ·
                    refine ⟨2835343639764490196755657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3780458186352653595674209 2835343639764490196755657)
                    ·
                      refine ⟨2126507729823367647566743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2835343639764490196755657 2126507729823367647566743)
                      ·
                        rfl

theorem cell23_4141359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 2, 2, 2].length) (baseStart_4141359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141359 prefixEnd_4141359 := by exact prefixLift 4141359
  have htrace : WordTrace (prefixWord ++ tailWord_4141359) baseStart_4141359 baseEnd_4141359 := by
    simpa [prefixWord, tailWord_4141359, baseEnd_4141359] using wordTrace_append hprefix tailTrace_4141359
  have hstable : (prefixWord ++ tailWord_4141359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141359).length < 2 ^ (prefixWord ++ tailWord_4141359).sum := by decide
  have hdescent : baseEnd_4141359 < baseStart_4141359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141388 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 3, 2, 5]
def baseStart_4141388 : Nat := 118140960795 + 4141388 * 2 ^ 59
def prefixEnd_4141388 : Nat := 4983230072969 + 3 ^ 40 * 4141388 * 2
def baseEnd_4141388 : Nat := 2126522620762348034104109

theorem tailTrace_4141388 : CollatzResearch.WordTrace tailWord_4141388 prefixEnd_4141388 2126522620762348034104109 := by
  unfold tailWord_4141388
  simp only [CollatzResearch.WordTrace]
  refine ⟨75524414760233021802528409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100699219680310695736704545 75524414760233021802528409)
  ·
    refine ⟨56643311070174766351896307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75524414760233021802528409 56643311070174766351896307)
    ·
      refine ⟨84964966605262149527844461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56643311070174766351896307 84964966605262149527844461)
      ·
        refine ⟨31861862476973306072941673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84964966605262149527844461 31861862476973306072941673)
        ·
          refine ⟨23896396857729979554706255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31861862476973306072941673 23896396857729979554706255)
          ·
            refine ⟨35844595286594969332059383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23896396857729979554706255 35844595286594969332059383)
            ·
              refine ⟨53766892929892453998089075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35844595286594969332059383 53766892929892453998089075)
              ·
                refine ⟨80650339394838680997133613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53766892929892453998089075 80650339394838680997133613)
                ·
                  refine ⟨30243877273064505373925105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80650339394838680997133613 30243877273064505373925105)
                  ·
                    refine ⟨22682907954798379030443829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30243877273064505373925105 22682907954798379030443829)
                    ·
                      refine ⟨2126522620762348034104109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22682907954798379030443829 2126522620762348034104109)
                      ·
                        rfl

theorem cell23_4141388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_4141388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141388 prefixEnd_4141388 := by exact prefixLift 4141388
  have htrace : WordTrace (prefixWord ++ tailWord_4141388) baseStart_4141388 baseEnd_4141388 := by
    simpa [prefixWord, tailWord_4141388, baseEnd_4141388] using wordTrace_append hprefix tailTrace_4141388
  have hstable : (prefixWord ++ tailWord_4141388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141388).length < 2 ^ (prefixWord ++ tailWord_4141388).sum := by decide
  have hdescent : baseEnd_4141388 < baseStart_4141388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141435 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 3]
def baseStart_4141435 : Nat := 118140960795 + 4141435 * 2 ^ 59
def prefixEnd_4141435 : Nat := 4983230072969 + 3 ^ 40 * 4141435 * 2
def baseEnd_4141435 : Nat := 2126546754353109350216393

theorem tailTrace_4141435 : CollatzResearch.WordTrace tailWord_4141435 prefixEnd_4141435 2126546754353109350216393 := by
  unfold tailWord_4141435
  simp only [CollatzResearch.WordTrace]
  refine ⟨151050543751295770632017759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100700362500863847088011839 151050543751295770632017759)
  ·
    refine ⟨226575815626943655948026639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151050543751295770632017759 226575815626943655948026639)
    ·
      refine ⟨339863723440415483922039959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226575815626943655948026639 339863723440415483922039959)
      ·
        refine ⟨509795585160623225883059939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339863723440415483922039959 509795585160623225883059939)
        ·
          refine ⟨764693377740934838824589909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509795585160623225883059939 764693377740934838824589909)
          ·
            refine ⟨8961250520401580142475663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 764693377740934838824589909 8961250520401580142475663)
            ·
              refine ⟨13441875780602370213713495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8961250520401580142475663 13441875780602370213713495)
              ·
                refine ⟨20162813670903555320570243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13441875780602370213713495 20162813670903555320570243)
                ·
                  refine ⟨30244220506355332980855365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20162813670903555320570243 30244220506355332980855365)
                  ·
                    refine ⟨5670791344941624933910381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30244220506355332980855365 5670791344941624933910381)
                    ·
                      refine ⟨2126546754353109350216393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5670791344941624933910381 2126546754353109350216393)
                      ·
                        rfl

theorem cell23_4141435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 3].length) (baseStart_4141435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141435 prefixEnd_4141435 := by exact prefixLift 4141435
  have htrace : WordTrace (prefixWord ++ tailWord_4141435) baseStart_4141435 baseEnd_4141435 := by
    simpa [prefixWord, tailWord_4141435, baseEnd_4141435] using wordTrace_append hprefix tailTrace_4141435
  have hstable : (prefixWord ++ tailWord_4141435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141435).length < 2 ^ (prefixWord ++ tailWord_4141435).sum := by decide
  have hdescent : baseEnd_4141435 < baseStart_4141435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141472 : List Nat := [2, 1, 1, 4, 1, 4, 3, 1, 6]
def baseStart_4141472 : Nat := 118140960795 + 4141472 * 2 ^ 59
def prefixEnd_4141472 : Nat := 4983230072969 + 3 ^ 40 * 4141472 * 2
def baseEnd_4141472 : Nat := 236285083681925078383747

theorem tailTrace_4141472 : CollatzResearch.WordTrace tailWord_4141472 prefixEnd_4141472 236285083681925078383747 := by
  unfold tailWord_4141472
  simp only [CollatzResearch.WordTrace]
  refine ⟨75525946626080862975557335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100701262168107817300743113 75525946626080862975557335)
  ·
    refine ⟨113288919939121294463336003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75525946626080862975557335 113288919939121294463336003)
    ·
      refine ⟨169933379908681941695004005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113288919939121294463336003 169933379908681941695004005)
      ·
        refine ⟨31862508732877864067813251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169933379908681941695004005 31862508732877864067813251)
        ·
          refine ⟨47793763099316796101719877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31862508732877864067813251 47793763099316796101719877)
          ·
            refine ⟨8961330581121899269072477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47793763099316796101719877 8961330581121899269072477)
            ·
              refine ⟨3360498967920712225902179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8961330581121899269072477 3360498967920712225902179)
              ·
                refine ⟨5040748451881068338853269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3360498967920712225902179 5040748451881068338853269)
                ·
                  refine ⟨236285083681925078383747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5040748451881068338853269 236285083681925078383747)
                  ·
                    rfl

theorem cell23_4141472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 6].length) (baseStart_4141472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141472 prefixEnd_4141472 := by exact prefixLift 4141472
  have htrace : WordTrace (prefixWord ++ tailWord_4141472) baseStart_4141472 baseEnd_4141472 := by
    simpa [prefixWord, tailWord_4141472, baseEnd_4141472] using wordTrace_append hprefix tailTrace_4141472
  have hstable : (prefixWord ++ tailWord_4141472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141472).length < 2 ^ (prefixWord ++ tailWord_4141472).sum := by decide
  have hdescent : baseEnd_4141472 < baseStart_4141472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141493 : List Nat := [1, 3, 3, 2, 4, 1, 1, 3, 1, 4]
def baseStart_4141493 : Nat := 118140960795 + 4141493 * 2 ^ 59
def prefixEnd_4141493 : Nat := 4983230072969 + 3 ^ 40 * 4141493 * 2
def baseEnd_4141493 : Nat := 708858845410356707763709

theorem tailTrace_4141493 : CollatzResearch.WordTrace tailWord_4141493 prefixEnd_4141493 708858845410356707763709 := by
  unfold tailWord_4141493
  simp only [CollatzResearch.WordTrace]
  refine ⟨151052659185085646537629133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100701772790057097691752755 151052659185085646537629133)
  ·
    refine ⟨56644747194407117451610925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151052659185085646537629133 56644747194407117451610925)
    ·
      refine ⟨21241780197902669044354097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56644747194407117451610925 21241780197902669044354097)
      ·
        refine ⟨15931335148427001783265573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21241780197902669044354097 15931335148427001783265573)
        ·
          refine ⟨2987125340330062834362295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15931335148427001783265573 2987125340330062834362295)
          ·
            refine ⟨4480688010495094251543443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2987125340330062834362295 4480688010495094251543443)
            ·
              refine ⟨6721032015742641377315165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4480688010495094251543443 6721032015742641377315165)
              ·
                refine ⟨2520387005903490516493187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6721032015742641377315165 2520387005903490516493187)
                ·
                  refine ⟨3780580508855235774739781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2520387005903490516493187 3780580508855235774739781)
                  ·
                    refine ⟨708858845410356707763709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3780580508855235774739781 708858845410356707763709)
                    ·
                      rfl

theorem cell23_4141493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_4141493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141493 prefixEnd_4141493 := by exact prefixLift 4141493
  have htrace : WordTrace (prefixWord ++ tailWord_4141493) baseStart_4141493 baseEnd_4141493 := by
    simpa [prefixWord, tailWord_4141493, baseEnd_4141493] using wordTrace_append hprefix tailTrace_4141493
  have hstable : (prefixWord ++ tailWord_4141493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141493).length < 2 ^ (prefixWord ++ tailWord_4141493).sum := by decide
  have hdescent : baseEnd_4141493 < baseStart_4141493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141502 : List Nat := [4, 2, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_4141502 : Nat := 118140960795 + 4141502 * 2 ^ 59
def prefixEnd_4141502 : Nat := 4983230072969 + 3 ^ 40 * 4141502 * 2
def baseEnd_4141502 : Nat := 708860385852320196026195

theorem tailTrace_4141502 : CollatzResearch.WordTrace tailWord_4141502 prefixEnd_4141502 708860385852320196026195 := by
  unfold tailWord_4141502
  simp only [CollatzResearch.WordTrace]
  refine ⟨18881623430256630134338345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100701991628035360716471173 18881623430256630134338345)
  ·
    refine ⟨14161217572692472600753759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18881623430256630134338345 14161217572692472600753759)
    ·
      refine ⟨21241826359038708901130639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14161217572692472600753759 21241826359038708901130639)
      ·
        refine ⟨31862739538558063351695959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21241826359038708901130639 31862739538558063351695959)
        ·
          refine ⟨47794109307837095027543939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31862739538558063351695959 47794109307837095027543939)
          ·
            refine ⟨71691163961755642541315909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47794109307837095027543939 71691163961755642541315909)
            ·
              refine ⟨13442093242829182976496733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71691163961755642541315909 13442093242829182976496733)
              ·
                refine ⟨5040784966060943616186275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13442093242829182976496733 5040784966060943616186275)
                ·
                  refine ⟨7561177449091415424279413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040784966060943616186275 7561177449091415424279413)
                  ·
                    refine ⟨708860385852320196026195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7561177449091415424279413 708860385852320196026195)
                    ·
                      rfl

theorem cell23_4141502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_4141502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141502 prefixEnd_4141502 := by exact prefixLift 4141502
  have htrace : WordTrace (prefixWord ++ tailWord_4141502) baseStart_4141502 baseEnd_4141502 := by
    simpa [prefixWord, tailWord_4141502, baseEnd_4141502] using wordTrace_append hprefix tailTrace_4141502
  have hstable : (prefixWord ++ tailWord_4141502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141502).length < 2 ^ (prefixWord ++ tailWord_4141502).sum := by decide
  have hdescent : baseEnd_4141502 < baseStart_4141502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141516 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 3, 1, 3]
def baseStart_4141516 : Nat := 118140960795 + 4141516 * 2 ^ 59
def prefixEnd_4141516 : Nat := 4983230072969 + 3 ^ 40 * 4141516 * 2
def baseEnd_4141516 : Nat := 2126588346286123533303521

theorem tailTrace_4141516 : CollatzResearch.WordTrace tailWord_4141516 prefixEnd_4141516 2126588346286123533303521 := by
  unfold tailWord_4141516
  simp only [CollatzResearch.WordTrace]
  refine ⟨75526749032001160732858201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100702332042668214310477601 75526749032001160732858201)
  ·
    refine ⟨56645061774000870549643651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75526749032001160732858201 56645061774000870549643651)
    ·
      refine ⟨84967592661001305824465477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56645061774000870549643651 84967592661001305824465477)
      ·
        refine ⟨15931423623937744842087277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84967592661001305824465477 15931423623937744842087277)
        ·
          refine ⟨5974283858976654315782729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15931423623937744842087277 5974283858976654315782729)
          ·
            refine ⟨4480712894232490736837047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5974283858976654315782729 4480712894232490736837047)
            ·
              refine ⟨6721069341348736105255571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4480712894232490736837047 6721069341348736105255571)
              ·
                refine ⟨10081604012023104157883357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6721069341348736105255571 10081604012023104157883357)
                ·
                  refine ⟨3780601504508664059206259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10081604012023104157883357 3780601504508664059206259)
                  ·
                    refine ⟨5670902256762996088809389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3780601504508664059206259 5670902256762996088809389)
                    ·
                      refine ⟨2126588346286123533303521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5670902256762996088809389 2126588346286123533303521)
                      ·
                        rfl

theorem cell23_4141516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_4141516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141516 prefixEnd_4141516 := by exact prefixLift 4141516
  have htrace : WordTrace (prefixWord ++ tailWord_4141516) baseStart_4141516 baseEnd_4141516 := by
    simpa [prefixWord, tailWord_4141516, baseEnd_4141516] using wordTrace_append hprefix tailTrace_4141516
  have hstable : (prefixWord ++ tailWord_4141516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141516).length < 2 ^ (prefixWord ++ tailWord_4141516).sum := by decide
  have hdescent : baseEnd_4141516 < baseStart_4141516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141535 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 6]
def baseStart_4141535 : Nat := 118140960795 + 4141535 * 2 ^ 59
def prefixEnd_4141535 : Nat := 4983230072969 + 3 ^ 40 * 4141535 * 2
def baseEnd_4141535 : Nat := 2126598102418558958965933

theorem tailTrace_4141535 : CollatzResearch.WordTrace tailWord_4141535 prefixEnd_4141535 2126598102418558958965933 := by
  unfold tailWord_4141535
  simp only [CollatzResearch.WordTrace]
  refine ⟨151054191050933487710658059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100702794033955658473772039 151054191050933487710658059)
  ·
    refine ⟨226581286576400231565987089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151054191050933487710658059 226581286576400231565987089)
    ·
      refine ⟨169935964932300173674490317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226581286576400231565987089 169935964932300173674490317)
      ·
        refine ⟨63725986849612565127933869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169935964932300173674490317 63725986849612565127933869)
        ·
          refine ⟨23897245068604711922975201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63725986849612565127933869 23897245068604711922975201)
          ·
            refine ⟨17922933801453533942231401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23897245068604711922975201 17922933801453533942231401)
            ·
              refine ⟨13442200351090150456673551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17922933801453533942231401 13442200351090150456673551)
              ·
                refine ⟨20163300526635225685010327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13442200351090150456673551 20163300526635225685010327)
                ·
                  refine ⟨30244950789952838527515491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20163300526635225685010327 30244950789952838527515491)
                  ·
                    refine ⟨45367426184929257791273237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30244950789952838527515491 45367426184929257791273237)
                    ·
                      refine ⟨2126598102418558958965933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45367426184929257791273237 2126598102418558958965933)
                      ·
                        rfl

theorem cell23_4141535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_4141535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141535 prefixEnd_4141535 := by exact prefixLift 4141535
  have htrace : WordTrace (prefixWord ++ tailWord_4141535) baseStart_4141535 baseEnd_4141535 := by
    simpa [prefixWord, tailWord_4141535, baseEnd_4141535] using wordTrace_append hprefix tailTrace_4141535
  have hstable : (prefixWord ++ tailWord_4141535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141535).length < 2 ^ (prefixWord ++ tailWord_4141535).sum := by decide
  have hdescent : baseEnd_4141535 < baseStart_4141535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141573 : List Nat := [1, 3, 1, 1, 2, 2, 6, 2, 1, 2, 2]
def baseStart_4141573 : Nat := 118140960795 + 4141573 * 2 ^ 59
def prefixEnd_4141573 : Nat := 4983230072969 + 3 ^ 40 * 4141573 * 2
def baseEnd_4141573 : Nat := 2126617614683429810290759

theorem tailTrace_4141573 : CollatzResearch.WordTrace tailWord_4141573 prefixEnd_4141573 2126617614683429810290759 := by
  unfold tailWord_4141573
  simp only [CollatzResearch.WordTrace]
  refine ⟨151055577024795820200541373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100703718016530546800360915 151055577024795820200541373)
  ·
    refine ⟨56645841384298432575203015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151055577024795820200541373 56645841384298432575203015)
    ·
      refine ⟨84968762076447648862804523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56645841384298432575203015 84968762076447648862804523)
      ·
        refine ⟨127453143114671473294206785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84968762076447648862804523 127453143114671473294206785)
        ·
          refine ⟨95589857336003604970655089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127453143114671473294206785 95589857336003604970655089)
          ·
            refine ⟨71692393002002703727991317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95589857336003604970655089 71692393002002703727991317)
            ·
              refine ⟨3360580921968876737249593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71692393002002703727991317 3360580921968876737249593)
              ·
                refine ⟨2520435691476657552937195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3360580921968876737249593 2520435691476657552937195)
                ·
                  refine ⟨3780653537214986329405793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2520435691476657552937195 3780653537214986329405793)
                  ·
                    refine ⟨2835490152911239747054345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3780653537214986329405793 2835490152911239747054345)
                    ·
                      refine ⟨2126617614683429810290759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2835490152911239747054345 2126617614683429810290759)
                      ·
                        rfl

theorem cell23_4141573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 1, 2, 2].length) (baseStart_4141573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141573 prefixEnd_4141573 := by exact prefixLift 4141573
  have htrace : WordTrace (prefixWord ++ tailWord_4141573) baseStart_4141573 baseEnd_4141573 := by
    simpa [prefixWord, tailWord_4141573, baseEnd_4141573] using wordTrace_append hprefix tailTrace_4141573
  have hstable : (prefixWord ++ tailWord_4141573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141573).length < 2 ^ (prefixWord ++ tailWord_4141573).sum := by decide
  have hdescent : baseEnd_4141573 < baseStart_4141573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141589 : List Nat := [1, 3, 2, 1, 3, 1, 1, 5, 2, 1, 3]
def baseStart_4141589 : Nat := 118140960795 + 4141589 * 2 ^ 59
def prefixEnd_4141589 : Nat := 4983230072969 + 3 ^ 40 * 4141589 * 2
def baseEnd_4141589 : Nat := 2126625830373901747690685

theorem tailTrace_4141589 : CollatzResearch.WordTrace tailWord_4141589 prefixEnd_4141589 2126625830373901747690685 := by
  unfold tailWord_4141589
  simp only [CollatzResearch.WordTrace]
  refine ⟨151056160592737854933123821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100704107061825236622082547 151056160592737854933123821)
  ·
    refine ⟨56646060222276695599921433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151056160592737854933123821 56646060222276695599921433)
    ·
      refine ⟨42484545166707521699941075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56646060222276695599921433 42484545166707521699941075)
      ·
        refine ⟨63726817750061282549911613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42484545166707521699941075 63726817750061282549911613)
        ·
          refine ⟨23897556656272980956216855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63726817750061282549911613 23897556656272980956216855)
          ·
            refine ⟨35846334984409471434325283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23897556656272980956216855 35846334984409471434325283)
            ·
              refine ⟨53769502476614207151487925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35846334984409471434325283 53769502476614207151487925)
              ·
                refine ⟨5040890857182581920451993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53769502476614207151487925 5040890857182581920451993)
                ·
                  refine ⟨3780668142886936440338995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5040890857182581920451993 3780668142886936440338995)
                  ·
                    refine ⟨5671002214330404660508493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3780668142886936440338995 5671002214330404660508493)
                    ·
                      refine ⟨2126625830373901747690685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5671002214330404660508493 2126625830373901747690685)
                      ·
                        rfl

theorem cell23_4141589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_4141589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141589 prefixEnd_4141589 := by exact prefixLift 4141589
  have htrace : WordTrace (prefixWord ++ tailWord_4141589) baseStart_4141589 baseEnd_4141589 := by
    simpa [prefixWord, tailWord_4141589, baseEnd_4141589] using wordTrace_append hprefix tailTrace_4141589
  have hstable : (prefixWord ++ tailWord_4141589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141589).length < 2 ^ (prefixWord ++ tailWord_4141589).sum := by decide
  have hdescent : baseEnd_4141589 < baseStart_4141589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141599 : List Nat := [1, 1, 2, 4, 1, 1, 1, 6, 1, 3, 2]
def baseStart_4141599 : Nat := 118140960795 + 4141599 * 2 ^ 59
def prefixEnd_4141599 : Nat := 4983230072969 + 3 ^ 40 * 4141599 * 2
def baseEnd_4141599 : Nat := 2126630965180446708565639

theorem tailTrace_4141599 : CollatzResearch.WordTrace tailWord_4141599 prefixEnd_4141599 2126630965180446708565639 := by
  unfold tailWord_4141599
  simp only [CollatzResearch.WordTrace]
  refine ⟨151056525322701626640987851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100704350215134417760658567 151056525322701626640987851)
  ·
    refine ⟨226584787984052439961481777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151056525322701626640987851 226584787984052439961481777)
    ·
      refine ⟨169938590988039329971111333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226584787984052439961481777 169938590988039329971111333)
      ·
        refine ⟨31863485810257374369583375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169938590988039329971111333 31863485810257374369583375)
        ·
          refine ⟨47795228715386061554375063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31863485810257374369583375 47795228715386061554375063)
          ·
            refine ⟨71692843073079092331562595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47795228715386061554375063 71692843073079092331562595)
            ·
              refine ⟨107539264609618638497343893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71692843073079092331562595 107539264609618638497343893)
              ·
                refine ⟨5040903028575873679562995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107539264609618638497343893 5040903028575873679562995)
                ·
                  refine ⟨7561354542863810519344493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040903028575873679562995 7561354542863810519344493)
                  ·
                    refine ⟨2835507953573928944754185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7561354542863810519344493 2835507953573928944754185)
                    ·
                      refine ⟨2126630965180446708565639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2835507953573928944754185 2126630965180446708565639)
                      ·
                        rfl

theorem cell23_4141599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_4141599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141599 prefixEnd_4141599 := by exact prefixLift 4141599
  have htrace : WordTrace (prefixWord ++ tailWord_4141599) baseStart_4141599 baseEnd_4141599 := by
    simpa [prefixWord, tailWord_4141599, baseEnd_4141599] using wordTrace_append hprefix tailTrace_4141599
  have hstable : (prefixWord ++ tailWord_4141599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141599).length < 2 ^ (prefixWord ++ tailWord_4141599).sum := by decide
  have hdescent : baseEnd_4141599 < baseStart_4141599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141607 : List Nat := [1, 1, 7, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_4141607 : Nat := 118140960795 + 4141607 * 2 ^ 59
def prefixEnd_4141607 : Nat := 4983230072969 + 3 ^ 40 * 4141607 * 2
def baseEnd_4141607 : Nat := 2126635073025682677265603

theorem tailTrace_4141607 : CollatzResearch.WordTrace tailWord_4141607 prefixEnd_4141607 2126635073025682677265603 := by
  unfold tailWord_4141607
  simp only [CollatzResearch.WordTrace]
  refine ⟨151056817106672644007279075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100704544737781762671519383 151056817106672644007279075)
  ·
    refine ⟨226585225660008966010918613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151056817106672644007279075 226585225660008966010918613)
    ·
      refine ⟨5310591226406460140880905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 226585225660008966010918613 5310591226406460140880905)
      ·
        refine ⟨3982943419804845105660679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5310591226406460140880905 3982943419804845105660679)
        ·
          refine ⟨5974415129707267658491019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3982943419804845105660679 5974415129707267658491019)
          ·
            refine ⟨8961622694560901487736529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5974415129707267658491019 8961622694560901487736529)
            ·
              refine ⟨6721217020920676115802397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8961622694560901487736529 6721217020920676115802397)
              ·
                refine ⟨2520456382845253543425899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6721217020920676115802397 2520456382845253543425899)
                ·
                  refine ⟨3780684574267880315138849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2520456382845253543425899 3780684574267880315138849)
                  ·
                    refine ⟨2835513430700910236354137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3780684574267880315138849 2835513430700910236354137)
                    ·
                      refine ⟨2126635073025682677265603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2835513430700910236354137 2126635073025682677265603)
                      ·
                        rfl

theorem cell23_4141607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_4141607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141607 prefixEnd_4141607 := by exact prefixLift 4141607
  have htrace : WordTrace (prefixWord ++ tailWord_4141607) baseStart_4141607 baseEnd_4141607 := by
    simpa [prefixWord, tailWord_4141607, baseEnd_4141607] using wordTrace_append hprefix tailTrace_4141607
  have hstable : (prefixWord ++ tailWord_4141607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141607).length < 2 ^ (prefixWord ++ tailWord_4141607).sum := by decide
  have hdescent : baseEnd_4141607 < baseStart_4141607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141616 : List Nat := [2, 1, 1, 1, 2, 3, 6, 1, 1, 3, 2]
def baseStart_4141616 : Nat := 118140960795 + 4141616 * 2 ^ 59
def prefixEnd_4141616 : Nat := 4983230072969 + 3 ^ 40 * 4141616 * 2
def baseEnd_4141616 : Nat := 2126639694351573142053061

theorem tailTrace_4141616 : CollatzResearch.WordTrace tailWord_4141616 prefixEnd_4141616 2126639694351573142053061 := by
  unfold tailWord_4141616
  simp only [CollatzResearch.WordTrace]
  refine ⟨75528572681820019272178351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100704763575760025696237801 75528572681820019272178351)
  ·
    refine ⟨113292859022730028908267527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75528572681820019272178351 113292859022730028908267527)
    ·
      refine ⟨169939288534095043362401291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113292859022730028908267527 169939288534095043362401291)
      ·
        refine ⟨254908932801142565043601937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169939288534095043362401291 254908932801142565043601937)
        ·
          refine ⟨191181699600856923782701453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254908932801142565043601937 191181699600856923782701453)
          ·
            refine ⟨71693137350321346418513045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191181699600856923782701453 71693137350321346418513045)
            ·
              refine ⟨3360615813296313113367799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71693137350321346418513045 3360615813296313113367799)
              ·
                refine ⟨5040923719944469670051699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3360615813296313113367799 5040923719944469670051699)
                ·
                  refine ⟨7561385579916704505077549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040923719944469670051699 7561385579916704505077549)
                  ·
                    refine ⟨2835519592468764189404081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7561385579916704505077549 2835519592468764189404081)
                    ·
                      refine ⟨2126639694351573142053061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2835519592468764189404081 2126639694351573142053061)
                      ·
                        rfl

theorem cell23_4141616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 1, 3, 2].length) (baseStart_4141616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141616 prefixEnd_4141616 := by exact prefixLift 4141616
  have htrace : WordTrace (prefixWord ++ tailWord_4141616) baseStart_4141616 baseEnd_4141616 := by
    simpa [prefixWord, tailWord_4141616, baseEnd_4141616] using wordTrace_append hprefix tailTrace_4141616
  have hstable : (prefixWord ++ tailWord_4141616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141616).length < 2 ^ (prefixWord ++ tailWord_4141616).sum := by decide
  have hdescent : baseEnd_4141616 < baseStart_4141616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141642 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_4141642 : Nat := 118140960795 + 4141642 * 2 ^ 59
def prefixEnd_4141642 : Nat := 4983230072969 + 3 ^ 40 * 4141642 * 2
def baseEnd_4141642 : Nat := 2126653044848590040327941

theorem tailTrace_4141642 : CollatzResearch.WordTrace tailWord_4141642 prefixEnd_4141642 2126653044848590040327941 := by
  unfold tailWord_4141642
  simp only [CollatzResearch.WordTrace]
  refine ⟨37764523415386461246200795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100705395774363896656535453 37764523415386461246200795)
  ·
    refine ⟨56646785123079691869301193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37764523415386461246200795 56646785123079691869301193)
    ·
      refine ⟨42485088842309768901975895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56646785123079691869301193 42485088842309768901975895)
      ·
        refine ⟨63727633263464653352963843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42485088842309768901975895 63727633263464653352963843)
        ·
          refine ⟨95591449895196980029445765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63727633263464653352963843 95591449895196980029445765)
          ·
            refine ⟨17923396855349433755521081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95591449895196980029445765 17923396855349433755521081)
            ·
              refine ⟨13442547641512075316640811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17923396855349433755521081 13442547641512075316640811)
              ·
                refine ⟨20163821462268112974961217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13442547641512075316640811 20163821462268112974961217)
                ·
                  refine ⟨15122866096701084731220913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20163821462268112974961217 15122866096701084731220913)
                  ·
                    refine ⟨11342149572525813548415685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15122866096701084731220913 11342149572525813548415685)
                    ·
                      refine ⟨2126653044848590040327941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11342149572525813548415685 2126653044848590040327941)
                      ·
                        rfl

theorem cell23_4141642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_4141642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141642 prefixEnd_4141642 := by exact prefixLift 4141642
  have htrace : WordTrace (prefixWord ++ tailWord_4141642) baseStart_4141642 baseEnd_4141642 := by
    simpa [prefixWord, tailWord_4141642, baseEnd_4141642] using wordTrace_append hprefix tailTrace_4141642
  have hstable : (prefixWord ++ tailWord_4141642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141642).length < 2 ^ (prefixWord ++ tailWord_4141642).sum := by decide
  have hdescent : baseEnd_4141642 < baseStart_4141642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141646 : List Nat := [4, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2]
def baseStart_4141646 : Nat := 118140960795 + 4141646 * 2 ^ 59
def prefixEnd_4141646 : Nat := 4983230072969 + 3 ^ 40 * 4141646 * 2
def baseEnd_4141646 : Nat := 2126655098771208024677923

theorem tailTrace_4141646 : CollatzResearch.WordTrace tailWord_4141646 prefixEnd_4141646 2126655098771208024677923 := by
  unfold tailWord_4141646
  simp only [CollatzResearch.WordTrace]
  refine ⟨18882279944191419208493599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100705493035687569111965861 18882279944191419208493599)
  ·
    refine ⟨28323419916287128812740399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18882279944191419208493599 28323419916287128812740399)
    ·
      refine ⟨42485129874430693219110599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28323419916287128812740399 42485129874430693219110599)
      ·
        refine ⟨63727694811646039828665899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42485129874430693219110599 63727694811646039828665899)
        ·
          refine ⟨95591542217469059742998849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63727694811646039828665899 95591542217469059742998849)
          ·
            refine ⟨71693656663101794807249137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95591542217469059742998849 71693656663101794807249137)
            ·
              refine ⟨53770242497326346105436853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71693656663101794807249137 53770242497326346105436853)
              ·
                refine ⟨5040960234124344947384705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53770242497326346105436853 5040960234124344947384705)
                ·
                  refine ⟨3780720175593258710538529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5040960234124344947384705 3780720175593258710538529)
                  ·
                    refine ⟨2835540131694944032903897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3780720175593258710538529 2835540131694944032903897)
                    ·
                      refine ⟨2126655098771208024677923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2835540131694944032903897 2126655098771208024677923)
                      ·
                        rfl

theorem cell23_4141646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_4141646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141646 prefixEnd_4141646 := by exact prefixLift 4141646
  have htrace : WordTrace (prefixWord ++ tailWord_4141646) baseStart_4141646 baseEnd_4141646 := by
    simpa [prefixWord, tailWord_4141646, baseEnd_4141646] using wordTrace_append hprefix tailTrace_4141646
  have hstable : (prefixWord ++ tailWord_4141646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141646).length < 2 ^ (prefixWord ++ tailWord_4141646).sum := by decide
  have hdescent : baseEnd_4141646 < baseStart_4141646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141652 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 7]
def baseStart_4141652 : Nat := 118140960795 + 4141652 * 2 ^ 59
def prefixEnd_4141652 : Nat := 4983230072969 + 3 ^ 40 * 4141652 * 2
def baseEnd_4141652 : Nat := 236295353295015000133655

theorem tailTrace_4141652 : CollatzResearch.WordTrace tailWord_4141652 prefixEnd_4141652 236295353295015000133655 := by
  unfold tailWord_4141652
  simp only [CollatzResearch.WordTrace]
  refine ⟨75529229195754808346333605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100705638927673077795111473 75529229195754808346333605)
  ·
    refine ⟨14161730474204026564937551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75529229195754808346333605 14161730474204026564937551)
    ·
      refine ⟨21242595711306039847406327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14161730474204026564937551 21242595711306039847406327)
      ·
        refine ⟨31863893566959059771109491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21242595711306039847406327 31863893566959059771109491)
        ·
          refine ⟨47795840350438589656664237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31863893566959059771109491 47795840350438589656664237)
          ·
            refine ⟨17923440131414471121249089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47795840350438589656664237 17923440131414471121249089)
            ·
              refine ⟨13442580098560853340936817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17923440131414471121249089 13442580098560853340936817)
              ·
                refine ⟨10081935073920640005702613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13442580098560853340936817 10081935073920640005702613)
                ·
                  refine ⟨236295353295015000133655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10081935073920640005702613 236295353295015000133655)
                  ·
                    rfl

theorem cell23_4141652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_4141652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141652 prefixEnd_4141652 := by exact prefixLift 4141652
  have htrace : WordTrace (prefixWord ++ tailWord_4141652) baseStart_4141652 baseEnd_4141652 := by
    simpa [prefixWord, tailWord_4141652, baseEnd_4141652] using wordTrace_append hprefix tailTrace_4141652
  have hstable : (prefixWord ++ tailWord_4141652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141652).length < 2 ^ (prefixWord ++ tailWord_4141652).sum := by decide
  have hdescent : baseEnd_4141652 < baseStart_4141652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141666 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_4141666 : Nat := 118140960795 + 4141666 * 2 ^ 59
def prefixEnd_4141666 : Nat := 4983230072969 + 3 ^ 40 * 4141666 * 2
def baseEnd_4141666 : Nat := 2126665368384297946427831

theorem tailTrace_4141666 : CollatzResearch.WordTrace tailWord_4141666 prefixEnd_4141666 2126665368384297946427831 := by
  unfold tailWord_4141666
  simp only [CollatzResearch.WordTrace]
  refine ⟨37764742253364724270919213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100705979342305931389117901 37764742253364724270919213)
  ·
    refine ⟨14161778345011771601594705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37764742253364724270919213 14161778345011771601594705)
    ·
      refine ⟨10621333758758828701196029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14161778345011771601594705 10621333758758828701196029)
      ·
        refine ⟨3983000159534560762948511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10621333758758828701196029 3983000159534560762948511)
        ·
          refine ⟨5974500239301841144422767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3983000159534560762948511 5974500239301841144422767)
          ·
            refine ⟨8961750358952761716634151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5974500239301841144422767 8961750358952761716634151)
            ·
              refine ⟨13442625538429142574951227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8961750358952761716634151 13442625538429142574951227)
              ·
                refine ⟨20163938307643713862426841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13442625538429142574951227 20163938307643713862426841)
                ·
                  refine ⟨15122953730732785396820131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20163938307643713862426841 15122953730732785396820131)
                  ·
                    refine ⟨22684430596099178095230197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15122953730732785396820131 22684430596099178095230197)
                    ·
                      refine ⟨2126665368384297946427831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22684430596099178095230197 2126665368384297946427831)
                      ·
                        rfl

theorem cell23_4141666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_4141666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141666 prefixEnd_4141666 := by exact prefixLift 4141666
  have htrace : WordTrace (prefixWord ++ tailWord_4141666) baseStart_4141666 baseEnd_4141666 := by
    simpa [prefixWord, tailWord_4141666, baseEnd_4141666] using wordTrace_append hprefix tailTrace_4141666
  have hstable : (prefixWord ++ tailWord_4141666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141666).length < 2 ^ (prefixWord ++ tailWord_4141666).sum := by decide
  have hdescent : baseEnd_4141666 < baseStart_4141666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141686 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 7]
def baseStart_4141686 : Nat := 118140960795 + 4141686 * 2 ^ 59
def prefixEnd_4141686 : Nat := 4983230072969 + 3 ^ 40 * 4141686 * 2
def baseEnd_4141686 : Nat := 236297293110820874241971

theorem tailTrace_4141686 : CollatzResearch.WordTrace tailWord_4141686 prefixEnd_4141686 236297293110820874241971 := by
  unfold tailWord_4141686
  simp only [CollatzResearch.WordTrace]
  refine ⟨9441231154586652531212807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100706465648924293666269941 9441231154586652531212807)
  ·
    refine ⟨14161846731879978796819211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9441231154586652531212807 14161846731879978796819211)
    ·
      refine ⟨21242770097819968195228817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14161846731879978796819211 21242770097819968195228817)
      ·
        refine ⟨15932077573364976146421613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21242770097819968195228817 15932077573364976146421613)
        ·
          refine ⟨5974529090011866054908105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15932077573364976146421613 5974529090011866054908105)
          ·
            refine ⟨4480896817508899541181079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5974529090011866054908105 4480896817508899541181079)
            ·
              refine ⟨6721345226263349311771619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4480896817508899541181079 6721345226263349311771619)
              ·
                refine ⟨10082017839395023967657429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6721345226263349311771619 10082017839395023967657429)
                ·
                  refine ⟨236297293110820874241971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10082017839395023967657429 236297293110820874241971)
                  ·
                    rfl

theorem cell23_4141686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_4141686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141686 prefixEnd_4141686 := by exact prefixLift 4141686
  have htrace : WordTrace (prefixWord ++ tailWord_4141686) baseStart_4141686 baseEnd_4141686 := by
    simpa [prefixWord, tailWord_4141686, baseEnd_4141686] using wordTrace_append hprefix tailTrace_4141686
  have hstable : (prefixWord ++ tailWord_4141686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141686).length < 2 ^ (prefixWord ++ tailWord_4141686).sum := by decide
  have hdescent : baseEnd_4141686 < baseStart_4141686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141695 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 2, 8]
def baseStart_4141695 : Nat := 118140960795 + 4141695 * 2 ^ 59
def prefixEnd_4141695 : Nat := 4983230072969 + 3 ^ 40 * 4141695 * 2
def baseEnd_4141695 : Nat := 708893419774426110988399

theorem tailTrace_4141695 : CollatzResearch.WordTrace tailWord_4141695 prefixEnd_4141695 708893419774426110988399 := by
  unfold tailWord_4141695
  simp only [CollatzResearch.WordTrace]
  refine ⟨151060026730353835036482539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100706684486902556690988359 151060026730353835036482539)
  ·
    refine ⟨226590040095530752554723809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151060026730353835036482539 226590040095530752554723809)
    ·
      refine ⟨169942530071648064416042857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226590040095530752554723809 169942530071648064416042857)
      ·
        refine ⟨127456897553736048312032143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169942530071648064416042857 127456897553736048312032143)
        ·
          refine ⟨191185346330604072468048215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127456897553736048312032143 191185346330604072468048215)
          ·
            refine ⟨286778019495906108702072323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191185346330604072468048215 286778019495906108702072323)
            ·
              refine ⟨430167029243859163053108485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286778019495906108702072323 430167029243859163053108485)
              ·
                refine ⟨80656317983223593072457841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 430167029243859163053108485 80656317983223593072457841)
                ·
                  refine ⟨60492238487417694804343381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80656317983223593072457841 60492238487417694804343381)
                  ·
                    refine ⟨708893419774426110988399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60492238487417694804343381 708893419774426110988399)
                    ·
                      rfl

theorem cell23_4141695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 8].length) (baseStart_4141695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141695 prefixEnd_4141695 := by exact prefixLift 4141695
  have htrace : WordTrace (prefixWord ++ tailWord_4141695) baseStart_4141695 baseEnd_4141695 := by
    simpa [prefixWord, tailWord_4141695, baseEnd_4141695] using wordTrace_append hprefix tailTrace_4141695
  have hstable : (prefixWord ++ tailWord_4141695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141695).length < 2 ^ (prefixWord ++ tailWord_4141695).sum := by decide
  have hdescent : baseEnd_4141695 < baseStart_4141695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141716 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_4141716 : Nat := 118140960795 + 4141716 * 2 ^ 59
def prefixEnd_4141716 : Nat := 4983230072969 + 3 ^ 40 * 4141716 * 2
def baseEnd_4141716 : Nat := 708897014139007583600867

theorem tailTrace_4141716 : CollatzResearch.WordTrace tailWord_4141716 prefixEnd_4141716 708897014139007583600867 := by
  unfold tailWord_4141716
  simp only [CollatzResearch.WordTrace]
  refine ⟨75530396331638877811498501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100707195108851837081998001 75530396331638877811498501)
  ·
    refine ⟨14161949312182289589655969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75530396331638877811498501 14161949312182289589655969)
    ·
      refine ⟨10621461984136717192241977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14161949312182289589655969 10621461984136717192241977)
      ·
        refine ⟨7966096488102537894181483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10621461984136717192241977 7966096488102537894181483)
        ·
          refine ⟨11949144732153806841272225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7966096488102537894181483 11949144732153806841272225)
          ·
            refine ⟨8961858549115355130954169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11949144732153806841272225 8961858549115355130954169)
            ·
              refine ⟨6721393911836516348215627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8961858549115355130954169 6721393911836516348215627)
              ·
                refine ⟨10082090867754774522323441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6721393911836516348215627 10082090867754774522323441)
                ·
                  refine ⟨7561568150816080891742581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10082090867754774522323441 7561568150816080891742581)
                  ·
                    refine ⟨708897014139007583600867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7561568150816080891742581 708897014139007583600867)
                    ·
                      rfl

theorem cell23_4141716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_4141716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141716 prefixEnd_4141716 := by exact prefixLift 4141716
  have htrace : WordTrace (prefixWord ++ tailWord_4141716) baseStart_4141716 baseEnd_4141716 := by
    simpa [prefixWord, tailWord_4141716, baseEnd_4141716] using wordTrace_append hprefix tailTrace_4141716
  have hstable : (prefixWord ++ tailWord_4141716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141716).length < 2 ^ (prefixWord ++ tailWord_4141716).sum := by decide
  have hdescent : baseEnd_4141716 < baseStart_4141716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141719 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 4]
def baseStart_4141719 : Nat := 118140960795 + 4141719 * 2 ^ 59
def prefixEnd_4141719 : Nat := 4983230072969 + 3 ^ 40 * 4141719 * 2
def baseEnd_4141719 : Nat := 2126692582858986239065087

theorem tailTrace_4141719 : CollatzResearch.WordTrace tailWord_4141719 prefixEnd_4141719 2126692582858986239065087 := by
  unfold tailWord_4141719
  simp only [CollatzResearch.WordTrace]
  refine ⟨151060902082266887135356211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100707268054844591423570807 151060902082266887135356211)
  ·
    refine ⟨226591353123400330703034317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151060902082266887135356211 226591353123400330703034317)
    ·
      refine ⟨84971757421275124013637869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226591353123400330703034317 84971757421275124013637869)
      ·
        refine ⟨31864409032978171505114201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84971757421275124013637869 31864409032978171505114201)
        ·
          refine ⟨23898306774733628628835651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31864409032978171505114201 23898306774733628628835651)
          ·
            refine ⟨35847460162100442943253477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23898306774733628628835651 35847460162100442943253477)
            ·
              refine ⟨6721398780393833051860027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35847460162100442943253477 6721398780393833051860027)
              ·
                refine ⟨10082098170590749577790041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6721398780393833051860027 10082098170590749577790041)
                ·
                  refine ⟨7561573627943062183342531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10082098170590749577790041 7561573627943062183342531)
                  ·
                    refine ⟨11342360441914593275013797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7561573627943062183342531 11342360441914593275013797)
                    ·
                      refine ⟨2126692582858986239065087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11342360441914593275013797 2126692582858986239065087)
                      ·
                        rfl

theorem cell23_4141719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_4141719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141719 prefixEnd_4141719 := by exact prefixLift 4141719
  have htrace : WordTrace (prefixWord ++ tailWord_4141719) baseStart_4141719 baseEnd_4141719 := by
    simpa [prefixWord, tailWord_4141719, baseEnd_4141719] using wordTrace_append hprefix tailTrace_4141719
  have hstable : (prefixWord ++ tailWord_4141719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141719).length < 2 ^ (prefixWord ++ tailWord_4141719).sum := by decide
  have hdescent : baseEnd_4141719 < baseStart_4141719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141732 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_4141732 : Nat := 118140960795 + 4141732 * 2 ^ 59
def prefixEnd_4141732 : Nat := 4983230072969 + 3 ^ 40 * 4141732 * 2
def baseEnd_4141732 : Nat := 2126699258107494688202527

theorem tailTrace_4141732 : CollatzResearch.WordTrace tailWord_4141732 prefixEnd_4141732 2126699258107494688202527 := by
  unfold tailWord_4141732
  simp only [CollatzResearch.WordTrace]
  refine ⟨75530688115609895177789725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100707584154146526903719633 75530688115609895177789725)
  ·
    refine ⟨28324008043353710691671147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75530688115609895177789725 28324008043353710691671147)
    ·
      refine ⟨42486012065030566037506721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28324008043353710691671147 42486012065030566037506721)
      ·
        refine ⟨31864509048772924528130041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42486012065030566037506721 31864509048772924528130041)
        ·
          refine ⟨23898381786579693396097531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31864509048772924528130041 23898381786579693396097531)
          ·
            refine ⟨35847572679869540094146297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23898381786579693396097531 35847572679869540094146297)
            ·
              refine ⟨26885679509902155070609723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35847572679869540094146297 26885679509902155070609723)
              ·
                refine ⟨40328519264853232605914585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26885679509902155070609723 40328519264853232605914585)
                ·
                  refine ⟨30246389448639924454435939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40328519264853232605914585 30246389448639924454435939)
                  ·
                    refine ⟨45369584172959886681653909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30246389448639924454435939 45369584172959886681653909)
                    ·
                      refine ⟨2126699258107494688202527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45369584172959886681653909 2126699258107494688202527)
                      ·
                        rfl

theorem cell23_4141732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_4141732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141732 prefixEnd_4141732 := by exact prefixLift 4141732
  have htrace : WordTrace (prefixWord ++ tailWord_4141732) baseStart_4141732 baseEnd_4141732 := by
    simpa [prefixWord, tailWord_4141732, baseEnd_4141732] using wordTrace_append hprefix tailTrace_4141732
  have hstable : (prefixWord ++ tailWord_4141732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141732).length < 2 ^ (prefixWord ++ tailWord_4141732).sum := by decide
  have hdescent : baseEnd_4141732 < baseStart_4141732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141752 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 4, 5, 3]
def baseStart_4141752 : Nat := 118140960795 + 4141752 * 2 ^ 59
def prefixEnd_4141752 : Nat := 4983230072969 + 3 ^ 40 * 4141752 * 2
def baseEnd_4141752 : Nat := 2126709527720584609952435

theorem tailTrace_4141752 : CollatzResearch.WordTrace tailWord_4141752 prefixEnd_4141752 2126709527720584609952435 := by
  unfold tailWord_4141752
  simp only [CollatzResearch.WordTrace]
  refine ⟨75531052845573666885653755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100708070460764889180871673 75531052845573666885653755)
  ·
    refine ⟨113296579268360500328480633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75531052845573666885653755 113296579268360500328480633)
    ·
      refine ⟨84972434451270375246360475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113296579268360500328480633 84972434451270375246360475)
      ·
        refine ⟨127458651676905562869540713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84972434451270375246360475 127458651676905562869540713)
        ·
          refine ⟨95593988757679172152155535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127458651676905562869540713 95593988757679172152155535)
          ·
            refine ⟨143390983136518758228233303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95593988757679172152155535 143390983136518758228233303)
            ·
              refine ⟨215086474704778137342349955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143390983136518758228233303 215086474704778137342349955)
              ·
                refine ⟨322629712057167206013524933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215086474704778137342349955 322629712057167206013524933)
                ·
                  refine ⟨60493071010718851127535925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 322629712057167206013524933 60493071010718851127535925)
                  ·
                    refine ⟨5671225407254892293206493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60493071010718851127535925 5671225407254892293206493)
                    ·
                      refine ⟨2126709527720584609952435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5671225407254892293206493 2126709527720584609952435)
                      ·
                        rfl

theorem cell23_4141752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_4141752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141752 prefixEnd_4141752 := by exact prefixLift 4141752
  have htrace : WordTrace (prefixWord ++ tailWord_4141752) baseStart_4141752 baseEnd_4141752 := by
    simpa [prefixWord, tailWord_4141752, baseEnd_4141752] using wordTrace_append hprefix tailTrace_4141752
  have hstable : (prefixWord ++ tailWord_4141752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141752).length < 2 ^ (prefixWord ++ tailWord_4141752).sum := by decide
  have hdescent : baseEnd_4141752 < baseStart_4141752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141773 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_4141773 : Nat := 118140960795 + 4141773 * 2 ^ 59
def prefixEnd_4141773 : Nat := 4983230072969 + 3 ^ 40 * 4141773 * 2
def baseEnd_4141773 : Nat := 2126720310814329027789839

theorem tailTrace_4141773 : CollatzResearch.WordTrace tailWord_4141773 prefixEnd_4141773 2126720310814329027789839 := by
  unfold tailWord_4141773
  simp only [CollatzResearch.WordTrace]
  refine ⟨151062871624071254357821973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100708581082714169571881315 151062871624071254357821973)
  ·
    refine ⟨7081072107378340048022905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151062871624071254357821973 7081072107378340048022905)
    ·
      refine ⟨5310804080533755036017179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7081072107378340048022905 5310804080533755036017179)
      ·
        refine ⟨7966206120800632554025769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5310804080533755036017179 7966206120800632554025769)
        ·
          refine ⟨5974654590600474415519327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7966206120800632554025769 5974654590600474415519327)
          ·
            refine ⟨8961981885900711623278991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5974654590600474415519327 8961981885900711623278991)
            ·
              refine ⟨13442972828851067434918487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8961981885900711623278991 13442972828851067434918487)
              ·
                refine ⟨20164459243276601152377731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13442972828851067434918487 20164459243276601152377731)
                ·
                  refine ⟨30246688864914901728566597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20164459243276601152377731 30246688864914901728566597)
                  ·
                    refine ⟨5671254162171544074106237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30246688864914901728566597 5671254162171544074106237)
                    ·
                      refine ⟨2126720310814329027789839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5671254162171544074106237 2126720310814329027789839)
                      ·
                        rfl

theorem cell23_4141773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_4141773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141773 prefixEnd_4141773 := by exact prefixLift 4141773
  have htrace : WordTrace (prefixWord ++ tailWord_4141773) baseStart_4141773 baseEnd_4141773 := by
    simpa [prefixWord, tailWord_4141773, baseEnd_4141773] using wordTrace_append hprefix tailTrace_4141773
  have hstable : (prefixWord ++ tailWord_4141773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141773).length < 2 ^ (prefixWord ++ tailWord_4141773).sum := by decide
  have hdescent : baseEnd_4141773 < baseStart_4141773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141780 : List Nat := [2, 4, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_4141780 : Nat := 118140960795 + 4141780 * 2 ^ 59
def prefixEnd_4141780 : Nat := 4983230072969 + 3 ^ 40 * 4141780 * 2
def baseEnd_4141780 : Nat := 708907968392970166800769

theorem tailTrace_4141780 : CollatzResearch.WordTrace tailWord_4141780 prefixEnd_4141780 708907968392970166800769 := by
  unfold tailWord_4141780
  simp only [CollatzResearch.WordTrace]
  refine ⟨75531563467522947276663397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100708751290030596368884529 75531563467522947276663397)
  ·
    refine ⟨14162168150160552614374387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75531563467522947276663397 14162168150160552614374387)
    ·
      refine ⟨21243252225240828921561581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14162168150160552614374387 21243252225240828921561581)
      ·
        refine ⟨7966219584465310845585593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21243252225240828921561581 7966219584465310845585593)
        ·
          refine ⟨5974664688348983134189195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7966219584465310845585593 5974664688348983134189195)
          ·
            refine ⟨8961997032523474701283793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5974664688348983134189195 8961997032523474701283793)
            ·
              refine ⟨6721497774392606025962845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8961997032523474701283793 6721497774392606025962845)
              ·
                refine ⟨2520561665397227259736067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6721497774392606025962845 2520561665397227259736067)
                ·
                  refine ⟨3780842498095840889604101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2520561665397227259736067 3780842498095840889604101)
                  ·
                    refine ⟨708907968392970166800769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3780842498095840889604101 708907968392970166800769)
                    ·
                      rfl

theorem cell23_4141780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_4141780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141780 prefixEnd_4141780 := by exact prefixLift 4141780
  have htrace : WordTrace (prefixWord ++ tailWord_4141780) baseStart_4141780 baseEnd_4141780 := by
    simpa [prefixWord, tailWord_4141780, baseEnd_4141780] using wordTrace_append hprefix tailTrace_4141780
  have hstable : (prefixWord ++ tailWord_4141780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141780).length < 2 ^ (prefixWord ++ tailWord_4141780).sum := by decide
  have hdescent : baseEnd_4141780 < baseStart_4141780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141829 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 3, 2, 3]
def baseStart_4141829 : Nat := 118140960795 + 4141829 * 2 ^ 59
def prefixEnd_4141829 : Nat := 4983230072969 + 3 ^ 40 * 4141829 * 2
def baseEnd_4141829 : Nat := 2126749065730980808689581

theorem tailTrace_4141829 : CollatzResearch.WordTrace tailWord_4141829 prefixEnd_4141829 2126749065730980808689581 := by
  unfold tailWord_4141829
  simp only [CollatzResearch.WordTrace]
  refine ⟨151064914111868375921860541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100709942741245583947907027 151064914111868375921860541)
  ·
    refine ⟨56649342791950640970697703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151064914111868375921860541 56649342791950640970697703)
    ·
      refine ⟨84974014187925961456046555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56649342791950640970697703 84974014187925961456046555)
      ·
        refine ⟨127461021281888942184069833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84974014187925961456046555 127461021281888942184069833)
        ·
          refine ⟨95595765961416706638052375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127461021281888942184069833 95595765961416706638052375)
          ·
            refine ⟨143393648942125059957078563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95595765961416706638052375 143393648942125059957078563)
            ·
              refine ⟨215090473413187589935617845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143393648942125059957078563 215090473413187589935617845)
              ·
                refine ⟨20164731882486336556464173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215090473413187589935617845 20164731882486336556464173)
                ·
                  refine ⟨7561774455932376208674065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20164731882486336556464173 7561774455932376208674065)
                  ·
                    refine ⟨5671330841949282156505549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7561774455932376208674065 5671330841949282156505549)
                    ·
                      refine ⟨2126749065730980808689581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5671330841949282156505549 2126749065730980808689581)
                      ·
                        rfl

theorem cell23_4141829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_4141829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141829 prefixEnd_4141829 := by exact prefixLift 4141829
  have htrace : WordTrace (prefixWord ++ tailWord_4141829) baseStart_4141829 baseEnd_4141829 := by
    simpa [prefixWord, tailWord_4141829, baseEnd_4141829] using wordTrace_append hprefix tailTrace_4141829
  have hstable : (prefixWord ++ tailWord_4141829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141829).length < 2 ^ (prefixWord ++ tailWord_4141829).sum := by decide
  have hdescent : baseEnd_4141829 < baseStart_4141829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141870 : List Nat := [4, 1, 3, 2, 1, 1, 4, 1, 2, 4]
def baseStart_4141870 : Nat := 118140960795 + 4141870 * 2 ^ 59
def prefixEnd_4141870 : Nat := 4983230072969 + 3 ^ 40 * 4141870 * 2
def baseEnd_4141870 : Nat := 708923372812605049425631

theorem tailTrace_4141870 : CollatzResearch.WordTrace tailWord_4141870 prefixEnd_4141870 708923372812605049425631 := by
  unfold tailWord_4141870
  simp only [CollatzResearch.WordTrace]
  refine ⟨18883301188089979990512883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100710939669813226616068709 18883301188089979990512883)
  ·
    refine ⟨28324951782134969985769325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18883301188089979990512883 28324951782134969985769325)
    ·
      refine ⟨10621856918300613744663497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28324951782134969985769325 10621856918300613744663497)
      ·
        refine ⟨7966392688725460308497623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10621856918300613744663497 7966392688725460308497623)
        ·
          refine ⟨11949589033088190462746435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7966392688725460308497623 11949589033088190462746435)
          ·
            refine ⟨17924383549632285694119653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11949589033088190462746435 17924383549632285694119653)
            ·
              refine ⟨3360821915556053567647435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17924383549632285694119653 3360821915556053567647435)
              ·
                refine ⟨5041232873334080351471153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3360821915556053567647435 5041232873334080351471153)
                ·
                  refine ⟨3780924655000560263603365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5041232873334080351471153 3780924655000560263603365)
                  ·
                    refine ⟨708923372812605049425631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3780924655000560263603365 708923372812605049425631)
                    ·
                      rfl

theorem cell23_4141870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_4141870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141870 prefixEnd_4141870 := by exact prefixLift 4141870
  have htrace : WordTrace (prefixWord ++ tailWord_4141870) baseStart_4141870 baseEnd_4141870 := by
    simpa [prefixWord, tailWord_4141870, baseEnd_4141870] using wordTrace_append hprefix tailTrace_4141870
  have hstable : (prefixWord ++ tailWord_4141870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141870).length < 2 ^ (prefixWord ++ tailWord_4141870).sum := by decide
  have hdescent : baseEnd_4141870 < baseStart_4141870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141909 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 2, 6]
def baseStart_4141909 : Nat := 118140960795 + 4141909 * 2 ^ 59
def prefixEnd_4141909 : Nat := 4983230072969 + 3 ^ 40 * 4141909 * 2
def baseEnd_4141909 : Nat := 708930048061113498563071

theorem tailTrace_4141909 : CollatzResearch.WordTrace tailWord_4141909 prefixEnd_4141909 708930048061113498563071 := by
  unfold tailWord_4141909
  simp only [CollatzResearch.WordTrace]
  refine ⟨151067831951578549584772781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100711887967719033056515187 151067831951578549584772781)
  ·
    refine ⟨56650436981841956094289793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151067831951578549584772781 56650436981841956094289793)
    ·
      refine ⟨42487827736381467070717345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56650436981841956094289793 42487827736381467070717345)
      ·
        refine ⟨31865870802286100303038009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42487827736381467070717345 31865870802286100303038009)
        ·
          refine ⟨23899403101714575227278507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31865870802286100303038009 23899403101714575227278507)
          ·
            refine ⟨35849104652571862840917761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23899403101714575227278507 35849104652571862840917761)
            ·
              refine ⟨26886828489428897130688321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35849104652571862840917761 26886828489428897130688321)
              ·
                refine ⟨20165121367071672848016241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26886828489428897130688321 20165121367071672848016241)
                ·
                  refine ⟨15123841025303754636012181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20165121367071672848016241 15123841025303754636012181)
                  ·
                    refine ⟨708930048061113498563071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15123841025303754636012181 708930048061113498563071)
                    ·
                      rfl

theorem cell23_4141909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_4141909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141909 prefixEnd_4141909 := by exact prefixLift 4141909
  have htrace : WordTrace (prefixWord ++ tailWord_4141909) baseStart_4141909 baseEnd_4141909 := by
    simpa [prefixWord, tailWord_4141909, baseEnd_4141909] using wordTrace_append hprefix tailTrace_4141909
  have hstable : (prefixWord ++ tailWord_4141909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141909).length < 2 ^ (prefixWord ++ tailWord_4141909).sum := by decide
  have hdescent : baseEnd_4141909 < baseStart_4141909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141916 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_4141916 : Nat := 118140960795 + 4141916 * 2 ^ 59
def prefixEnd_4141916 : Nat := 4983230072969 + 3 ^ 40 * 4141916 * 2
def baseEnd_4141916 : Nat := 2126793738547921968301681

theorem tailTrace_4141916 : CollatzResearch.WordTrace tailWord_4141916 prefixEnd_4141916 2126793738547921968301681 := by
  unfold tailWord_4141916
  simp only [CollatzResearch.WordTrace]
  refine ⟨75534043631276594890138801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100712058175035459853518401 75534043631276594890138801)
  ·
    refine ⟨56650532723457446167604101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75534043631276594890138801 56650532723457446167604101)
    ·
      refine ⟨10621974885648271156425769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56650532723457446167604101 10621974885648271156425769)
      ·
        refine ⟨7966481164236203367319327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10621974885648271156425769 7966481164236203367319327)
        ·
          refine ⟨11949721746354305050978991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7966481164236203367319327 11949721746354305050978991)
          ·
            refine ⟨17924582619531457576468487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11949721746354305050978991 17924582619531457576468487)
            ·
              refine ⟨26886873929297186364702731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17924582619531457576468487 26886873929297186364702731)
              ·
                refine ⟨40330310893945779547054097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26886873929297186364702731 40330310893945779547054097)
                ·
                  refine ⟨30247733170459334660290573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40330310893945779547054097 30247733170459334660290573)
                  ·
                    refine ⟨11342899938922250497608965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30247733170459334660290573 11342899938922250497608965)
                    ·
                      refine ⟨2126793738547921968301681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11342899938922250497608965 2126793738547921968301681)
                      ·
                        rfl

theorem cell23_4141916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_4141916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141916 prefixEnd_4141916 := by exact prefixLift 4141916
  have htrace : WordTrace (prefixWord ++ tailWord_4141916) baseStart_4141916 baseEnd_4141916 := by
    simpa [prefixWord, tailWord_4141916, baseEnd_4141916] using wordTrace_append hprefix tailTrace_4141916
  have hstable : (prefixWord ++ tailWord_4141916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141916).length < 2 ^ (prefixWord ++ tailWord_4141916).sum := by decide
  have hdescent : baseEnd_4141916 < baseStart_4141916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141919 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 3]
def baseStart_4141919 : Nat := 118140960795 + 4141919 * 2 ^ 59
def prefixEnd_4141919 : Nat := 4983230072969 + 3 ^ 40 * 4141919 * 2
def baseEnd_4141919 : Nat := 2126795278989885456564167

theorem tailTrace_4141919 : CollatzResearch.WordTrace tailWord_4141919 prefixEnd_4141919 2126795278989885456564167 := by
  unfold tailWord_4141919
  simp only [CollatzResearch.WordTrace]
  refine ⟨151068196681542321292636811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100712131121028214195091207 151068196681542321292636811)
  ·
    refine ⟨226602295022313481938955217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151068196681542321292636811 226602295022313481938955217)
    ·
      refine ⟨169951721266735111454216413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226602295022313481938955217 169951721266735111454216413)
      ·
        refine ⟨63731895475025666795331155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169951721266735111454216413 63731895475025666795331155)
        ·
          refine ⟨95597843212538500192996733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63731895475025666795331155 95597843212538500192996733)
          ·
            refine ⟨35849191204701937572373775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95597843212538500192996733 35849191204701937572373775)
            ·
              refine ⟨53773786807052906358560663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35849191204701937572373775 53773786807052906358560663)
              ·
                refine ⟨80660680210579359537840995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53773786807052906358560663 80660680210579359537840995)
                ·
                  refine ⟨120991020315869039306761493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80660680210579359537840995 120991020315869039306761493)
                  ·
                    refine ⟨5671454077306361217504445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120991020315869039306761493 5671454077306361217504445)
                    ·
                      refine ⟨2126795278989885456564167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5671454077306361217504445 2126795278989885456564167)
                      ·
                        rfl

theorem cell23_4141919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_4141919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141919 prefixEnd_4141919 := by exact prefixLift 4141919
  have htrace : WordTrace (prefixWord ++ tailWord_4141919) baseStart_4141919 baseEnd_4141919 := by
    simpa [prefixWord, tailWord_4141919, baseEnd_4141919] using wordTrace_append hprefix tailTrace_4141919
  have hstable : (prefixWord ++ tailWord_4141919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141919).length < 2 ^ (prefixWord ++ tailWord_4141919).sum := by decide
  have hdescent : baseEnd_4141919 < baseStart_4141919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141933 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 6, 2, 2]
def baseStart_4141933 : Nat := 118140960795 + 4141933 * 2 ^ 59
def prefixEnd_4141933 : Nat := 4983230072969 + 3 ^ 40 * 4141933 * 2
def baseEnd_4141933 : Nat := 2126802467719048401789103

theorem tailTrace_4141933 : CollatzResearch.WordTrace tailWord_4141933 prefixEnd_4141933 2126802467719048401789103 := by
  unfold tailWord_4141933
  simp only [CollatzResearch.WordTrace]
  refine ⟨151068707303491601683646453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100712471535661067789097635 151068707303491601683646453)
  ·
    refine ⟨14162691309702337657841855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151068707303491601683646453 14162691309702337657841855)
    ·
      refine ⟨21244036964553506486762783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14162691309702337657841855 21244036964553506486762783)
      ·
        refine ⟨31866055446830259730144175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21244036964553506486762783 31866055446830259730144175)
        ·
          refine ⟨47799083170245389595216263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31866055446830259730144175 47799083170245389595216263)
          ·
            refine ⟨71698624755368084392824395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47799083170245389595216263 71698624755368084392824395)
            ·
              refine ⟨107547937133052126589236593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71698624755368084392824395 107547937133052126589236593)
              ·
                refine ⟨80660952849789094941927445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107547937133052126589236593 80660952849789094941927445)
                ·
                  refine ⟨3780982164833863825402849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80660952849789094941927445 3780982164833863825402849)
                  ·
                    refine ⟨2835736623625397869052137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3780982164833863825402849 2835736623625397869052137)
                    ·
                      refine ⟨2126802467719048401789103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2835736623625397869052137 2126802467719048401789103)
                      ·
                        rfl

theorem cell23_4141933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_4141933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141933 prefixEnd_4141933 := by exact prefixLift 4141933
  have htrace : WordTrace (prefixWord ++ tailWord_4141933) baseStart_4141933 baseEnd_4141933 := by
    simpa [prefixWord, tailWord_4141933, baseEnd_4141933] using wordTrace_append hprefix tailTrace_4141933
  have hstable : (prefixWord ++ tailWord_4141933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141933).length < 2 ^ (prefixWord ++ tailWord_4141933).sum := by decide
  have hdescent : baseEnd_4141933 < baseStart_4141933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141954 : List Nat := [3, 4, 2, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_4141954 : Nat := 118140960795 + 4141954 * 2 ^ 59
def prefixEnd_4141954 : Nat := 4983230072969 + 3 ^ 40 * 4141954 * 2
def baseEnd_4141954 : Nat := 2126813250812792819626507

theorem tailTrace_4141954 : CollatzResearch.WordTrace tailWord_4141954 prefixEnd_4141954 2126813250812792819626507 := by
  unfold tailWord_4141954
  simp only [CollatzResearch.WordTrace]
  refine ⟨37767368309103880567540229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100712982157610348180107277 37767368309103880567540229)
  ·
    refine ⟨7081381557956977606413793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37767368309103880567540229 7081381557956977606413793)
    ·
      refine ⟨5311036168467733204810345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7081381557956977606413793 5311036168467733204810345)
      ·
        refine ⟨3983277126350799903607759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5311036168467733204810345 3983277126350799903607759)
        ·
          refine ⟨5974915689526199855411639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3983277126350799903607759 5974915689526199855411639)
          ·
            refine ⟨8962373534289299783117459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5974915689526199855411639 8962373534289299783117459)
            ·
              refine ⟨13443560301433949674676189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8962373534289299783117459 13443560301433949674676189)
              ·
                refine ⟨5041335113037731128003571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13443560301433949674676189 5041335113037731128003571)
                ·
                  refine ⟨7562002669556596692005357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5041335113037731128003571 7562002669556596692005357)
                  ·
                    refine ⟨2835751001083723759502009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7562002669556596692005357 2835751001083723759502009)
                    ·
                      refine ⟨2126813250812792819626507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2835751001083723759502009 2126813250812792819626507)
                      ·
                        rfl

theorem cell23_4141954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_4141954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141954 prefixEnd_4141954 := by exact prefixLift 4141954
  have htrace : WordTrace (prefixWord ++ tailWord_4141954) baseStart_4141954 baseEnd_4141954 := by
    simpa [prefixWord, tailWord_4141954, baseEnd_4141954] using wordTrace_append hprefix tailTrace_4141954
  have hstable : (prefixWord ++ tailWord_4141954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141954).length < 2 ^ (prefixWord ++ tailWord_4141954).sum := by decide
  have hdescent : baseEnd_4141954 < baseStart_4141954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141969 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 4, 5]
def baseStart_4141969 : Nat := 118140960795 + 4141969 * 2 ^ 59
def prefixEnd_4141969 : Nat := 4983230072969 + 3 ^ 40 * 4141969 * 2
def baseEnd_4141969 : Nat := 708940317674203420312979

theorem tailTrace_4141969 : CollatzResearch.WordTrace tailWord_4141969 prefixEnd_4141969 708940317674203420312979 := by
  unfold tailWord_4141969
  simp only [CollatzResearch.WordTrace]
  refine ⟨151070020331361179831956961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100713346887574119887971307 151070020331361179831956961)
  ·
    refine ⟨113302515248520884873967721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151070020331361179831956961 113302515248520884873967721)
    ·
      refine ⟨84976886436390663655475791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113302515248520884873967721 84976886436390663655475791)
      ·
        refine ⟨127465329654585995483213687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84976886436390663655475791 127465329654585995483213687)
        ·
          refine ⟨191197994481878993224820531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127465329654585995483213687 191197994481878993224820531)
          ·
            refine ⟨286796991722818489837230797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191197994481878993224820531 286796991722818489837230797)
            ·
              refine ⟨107548871896056933688961549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286796991722818489837230797 107548871896056933688961549)
              ·
                refine ⟨40330826961021350133360581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107548871896056933688961549 40330826961021350133360581)
                ·
                  refine ⟨7562030055191503150005109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40330826961021350133360581 7562030055191503150005109)
                  ·
                    refine ⟨708940317674203420312979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7562030055191503150005109 708940317674203420312979)
                    ·
                      rfl

theorem cell23_4141969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_4141969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141969 prefixEnd_4141969 := by exact prefixLift 4141969
  have htrace : WordTrace (prefixWord ++ tailWord_4141969) baseStart_4141969 baseEnd_4141969 := by
    simpa [prefixWord, tailWord_4141969, baseEnd_4141969] using wordTrace_append hprefix tailTrace_4141969
  have hstable : (prefixWord ++ tailWord_4141969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141969).length < 2 ^ (prefixWord ++ tailWord_4141969).sum := by decide
  have hdescent : baseEnd_4141969 < baseStart_4141969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141986 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_4141986 : Nat := 118140960795 + 4141986 * 2 ^ 59
def prefixEnd_4141986 : Nat := 4983230072969 + 3 ^ 40 * 4141986 * 2
def baseEnd_4141986 : Nat := 708943227397912231475453

theorem tailTrace_4141986 : CollatzResearch.WordTrace tailWord_4141986 prefixEnd_4141986 708943227397912231475453 := by
  unfold tailWord_4141986
  simp only [CollatzResearch.WordTrace]
  refine ⟨37767660093074897933831453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100713760248199727823550541 37767660093074897933831453)
  ·
    refine ⟨14162872534903086725186795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37767660093074897933831453 14162872534903086725186795)
    ·
      refine ⟨21244308802354630087780193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14162872534903086725186795 21244308802354630087780193)
      ·
        refine ⟨15933231601765972565835145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21244308802354630087780193 15933231601765972565835145)
        ·
          refine ⟨11949923701324479424376359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15933231601765972565835145 11949923701324479424376359)
          ·
            refine ⟨17924885551986719136564539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11949923701324479424376359 17924885551986719136564539)
            ·
              refine ⟨26887328327980078704846809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17924885551986719136564539 26887328327980078704846809)
              ·
                refine ⟨20165496245985059028635107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26887328327980078704846809 20165496245985059028635107)
                ·
                  refine ⟨30248244368977588542952661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20165496245985059028635107 30248244368977588542952661)
                  ·
                    refine ⟨708943227397912231475453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30248244368977588542952661 708943227397912231475453)
                    ·
                      rfl

theorem cell23_4141986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_4141986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4141986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4141986 prefixEnd_4141986 := by exact prefixLift 4141986
  have htrace : WordTrace (prefixWord ++ tailWord_4141986) baseStart_4141986 baseEnd_4141986 := by
    simpa [prefixWord, tailWord_4141986, baseEnd_4141986] using wordTrace_append hprefix tailTrace_4141986
  have hstable : (prefixWord ++ tailWord_4141986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141986).length < 2 ^ (prefixWord ++ tailWord_4141986).sum := by decide
  have hdescent : baseEnd_4141986 < baseStart_4141986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142019 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 4]
def baseStart_4142019 : Nat := 118140960795 + 4142019 * 2 ^ 59
def prefixEnd_4142019 : Nat := 4983230072969 + 3 ^ 40 * 4142019 * 2
def baseEnd_4142019 : Nat := 2126846627055335065313707

theorem tailTrace_4142019 : CollatzResearch.WordTrace tailWord_4142019 prefixEnd_4142019 2126846627055335065313707 := by
  unfold tailWord_4142019
  simp only [CollatzResearch.WordTrace]
  refine ⟨151071843981180038371277111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100714562654120025580851407 151071843981180038371277111)
  ·
    refine ⟨226607765971770057556915667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151071843981180038371277111 226607765971770057556915667)
    ·
      refine ⟨339911648957655086335373501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226607765971770057556915667 339911648957655086335373501)
      ·
        refine ⟨127466868359120657375765063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339911648957655086335373501 127466868359120657375765063)
        ·
          refine ⟨191200302538680986063647595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127466868359120657375765063 191200302538680986063647595)
          ·
            refine ⟨286800453808021479095471393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191200302538680986063647595 286800453808021479095471393)
            ·
              refine ⟨215100340356016109321603545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286800453808021479095471393 215100340356016109321603545)
              ·
                refine ⟨161325255267012081991202659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215100340356016109321603545 161325255267012081991202659)
                ·
                  refine ⟨241987882900518122986803989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161325255267012081991202659 241987882900518122986803989)
                  ·
                    refine ⟨11343182010961787015006437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 241987882900518122986803989 11343182010961787015006437)
                    ·
                      refine ⟨2126846627055335065313707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11343182010961787015006437 2126846627055335065313707)
                      ·
                        rfl

theorem cell23_4142019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_4142019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142019 prefixEnd_4142019 := by exact prefixLift 4142019
  have htrace : WordTrace (prefixWord ++ tailWord_4142019) baseStart_4142019 baseEnd_4142019 := by
    simpa [prefixWord, tailWord_4142019, baseEnd_4142019] using wordTrace_append hprefix tailTrace_4142019
  have hstable : (prefixWord ++ tailWord_4142019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142019).length < 2 ^ (prefixWord ++ tailWord_4142019).sum := by decide
  have hdescent : baseEnd_4142019 < baseStart_4142019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142020 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 2, 5]
def baseStart_4142020 : Nat := 118140960795 + 4142020 * 2 ^ 59
def prefixEnd_4142020 : Nat := 4983230072969 + 3 ^ 40 * 4142020 * 2
def baseEnd_4142020 : Nat := 708949046845329853800401

theorem tailTrace_4142020 : CollatzResearch.WordTrace tailWord_4142020 prefixEnd_4142020 708949046845329853800401 := by
  unfold tailWord_4142020
  simp only [CollatzResearch.WordTrace]
  refine ⟨75535940227088207771031757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100714586969450943694709009 75535940227088207771031757)
  ·
    refine ⟨28325977585158077914136909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75535940227088207771031757 28325977585158077914136909)
    ·
      refine ⟨10622241594434279217801341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28325977585158077914136909 10622241594434279217801341)
      ·
        refine ⟨3983340597912854706675503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10622241594434279217801341 3983340597912854706675503)
        ·
          refine ⟨5975010896869282060013255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3983340597912854706675503 5975010896869282060013255)
          ·
            refine ⟨8962516345303923090019883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5975010896869282060013255 8962516345303923090019883)
            ·
              refine ⟨13443774517955884635029825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8962516345303923090019883 13443774517955884635029825)
              ·
                refine ⟨10082830888466913476272369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13443774517955884635029825 10082830888466913476272369)
                ·
                  refine ⟨7562123166350185107204277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10082830888466913476272369 7562123166350185107204277)
                  ·
                    refine ⟨708949046845329853800401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7562123166350185107204277 708949046845329853800401)
                    ·
                      rfl

theorem cell23_4142020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_4142020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142020 prefixEnd_4142020 := by exact prefixLift 4142020
  have htrace : WordTrace (prefixWord ++ tailWord_4142020) baseStart_4142020 baseEnd_4142020 := by
    simpa [prefixWord, tailWord_4142020, baseEnd_4142020] using wordTrace_append hprefix tailTrace_4142020
  have hstable : (prefixWord ++ tailWord_4142020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142020).length < 2 ^ (prefixWord ++ tailWord_4142020).sum := by decide
  have hdescent : baseEnd_4142020 < baseStart_4142020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142056 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_4142056 : Nat := 118140960795 + 4142056 * 2 ^ 59
def prefixEnd_4142056 : Nat := 4983230072969 + 3 ^ 40 * 4142056 * 2
def baseEnd_4142056 : Nat := 2126865625839551420551037

theorem tailTrace_4142056 : CollatzResearch.WordTrace tailWord_4142056 prefixEnd_4142056 2126865625839551420551037 := by
  unfold tailWord_4142056
  simp only [CollatzResearch.WordTrace]
  refine ⟨75536596741022996845187011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100715462321363995793582681 75536596741022996845187011)
  ·
    refine ⟨113304895111534495267780517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75536596741022996845187011 113304895111534495267780517)
    ·
      refine ⟨21244667833412717862708847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113304895111534495267780517 21244667833412717862708847)
      ·
        refine ⟨31867001750119076794063271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21244667833412717862708847 31867001750119076794063271)
        ·
          refine ⟨47800502625178615191094907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31867001750119076794063271 47800502625178615191094907)
          ·
            refine ⟨71700753937767922786642361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47800502625178615191094907 71700753937767922786642361)
            ·
              refine ⟨53775565453325942089981771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71700753937767922786642361 53775565453325942089981771)
              ·
                refine ⟨80663348179988913134972657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53775565453325942089981771 80663348179988913134972657)
                ·
                  refine ⟨60497511134991684851229493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80663348179988913134972657 60497511134991684851229493)
                  ·
                    refine ⟨5671641668905470454802765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60497511134991684851229493 5671641668905470454802765)
                    ·
                      refine ⟨2126865625839551420551037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5671641668905470454802765 2126865625839551420551037)
                      ·
                        rfl

theorem cell23_4142056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_4142056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142056 prefixEnd_4142056 := by exact prefixLift 4142056
  have htrace : WordTrace (prefixWord ++ tailWord_4142056) baseStart_4142056 baseEnd_4142056 := by
    simpa [prefixWord, tailWord_4142056, baseEnd_4142056] using wordTrace_append hprefix tailTrace_4142056
  have hstable : (prefixWord ++ tailWord_4142056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142056).length < 2 ^ (prefixWord ++ tailWord_4142056).sum := by decide
  have hdescent : baseEnd_4142056 < baseStart_4142056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142113 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_4142113 : Nat := 118140960795 + 4142113 * 2 ^ 59
def prefixEnd_4142113 : Nat := 4983230072969 + 3 ^ 40 * 4142113 * 2
def baseEnd_4142113 : Nat := 2126894894236857697538275

theorem tailTrace_4142113 : CollatzResearch.WordTrace tailWord_4142113 prefixEnd_4142113 2126894894236857697538275 := by
  unfold tailWord_4142113
  simp only [CollatzResearch.WordTrace]
  refine ⟨151075272442839492425198993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100716848295226328283465995 151075272442839492425198993)
  ·
    refine ⟨113306454332129619318899245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151075272442839492425198993 113306454332129619318899245)
    ·
      refine ⟨42489920374548607244587217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113306454332129619318899245 42489920374548607244587217)
      ·
        refine ⟨31867440280911455433440413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42489920374548607244587217 31867440280911455433440413)
        ·
          refine ⟨11950290105341795787540155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31867440280911455433440413 11950290105341795787540155)
          ·
            refine ⟨17925435158012693681310233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11950290105341795787540155 17925435158012693681310233)
            ·
              refine ⟨13444076368509520260982675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17925435158012693681310233 13444076368509520260982675)
              ·
                refine ⟨20166114552764280391474013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13444076368509520260982675 20166114552764280391474013)
                ·
                  refine ⟨7562292957286605146802755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20166114552764280391474013 7562292957286605146802755)
                  ·
                    refine ⟨11343439435929907720204133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7562292957286605146802755 11343439435929907720204133)
                    ·
                      refine ⟨2126894894236857697538275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11343439435929907720204133 2126894894236857697538275)
                      ·
                        rfl

theorem cell23_4142113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_4142113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142113 prefixEnd_4142113 := by exact prefixLift 4142113
  have htrace : WordTrace (prefixWord ++ tailWord_4142113) baseStart_4142113 baseEnd_4142113 := by
    simpa [prefixWord, tailWord_4142113, baseEnd_4142113] using wordTrace_append hprefix tailTrace_4142113
  have hstable : (prefixWord ++ tailWord_4142113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142113).length < 2 ^ (prefixWord ++ tailWord_4142113).sum := by decide
  have hdescent : baseEnd_4142113 < baseStart_4142113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142130 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2]
def baseStart_4142130 : Nat := 118140960795 + 4142130 * 2 ^ 59
def prefixEnd_4142130 : Nat := 4983230072969 + 3 ^ 40 * 4142130 * 2
def baseEnd_4142130 : Nat := 2126903623407984131025697

theorem tailTrace_4142130 : CollatzResearch.WordTrace tailWord_4142130 prefixEnd_4142130 2126903623407984131025697 := by
  unfold tailWord_4142130
  simp only [CollatzResearch.WordTrace]
  refine ⟨37768973120944476082141961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100717261655851936219045229 37768973120944476082141961)
  ·
    refine ⟨28326729840708357061606471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37768973120944476082141961 28326729840708357061606471)
    ·
      refine ⟨42490094761062535592409707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28326729840708357061606471 42490094761062535592409707)
      ·
        refine ⟨63735142141593803388614561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42490094761062535592409707 63735142141593803388614561)
        ·
          refine ⟨47801356606195352541460921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63735142141593803388614561 47801356606195352541460921)
          ·
            refine ⟨35851017454646514406095691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47801356606195352541460921 35851017454646514406095691)
            ·
              refine ⟨53776526181969771609143537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35851017454646514406095691 53776526181969771609143537)
              ·
                refine ⟨40332394636477328706857653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53776526181969771609143537 40332394636477328706857653)
                ·
                  refine ⟨3781161997169749566267905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40332394636477328706857653 3781161997169749566267905)
                  ·
                    refine ⟨2835871497877312174700929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3781161997169749566267905 2835871497877312174700929)
                    ·
                      refine ⟨2126903623407984131025697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2835871497877312174700929 2126903623407984131025697)
                      ·
                        rfl

theorem cell23_4142130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_4142130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142130 prefixEnd_4142130 := by exact prefixLift 4142130
  have htrace : WordTrace (prefixWord ++ tailWord_4142130) baseStart_4142130 baseEnd_4142130 := by
    simpa [prefixWord, tailWord_4142130, baseEnd_4142130] using wordTrace_append hprefix tailTrace_4142130
  have hstable : (prefixWord ++ tailWord_4142130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142130).length < 2 ^ (prefixWord ++ tailWord_4142130).sum := by decide
  have hdescent : baseEnd_4142130 < baseStart_4142130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142136 : List Nat := [2, 1, 2, 1, 5, 2, 10]
def baseStart_4142136 : Nat := 118140960795 + 4142136 * 2 ^ 59
def prefixEnd_4142136 : Nat := 4983230072969 + 3 ^ 40 * 4142136 * 2
def baseEnd_4142136 : Nat := 26258107460393964290749

theorem tailTrace_4142136 : CollatzResearch.WordTrace tailWord_4142136 prefixEnd_4142136 26258107460393964290749 := by
  unfold tailWord_4142136
  simp only [CollatzResearch.WordTrace]
  refine ⟨75538055660878083676643131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100717407547837444902190841 75538055660878083676643131)
  ·
    refine ⟨113307083491317125514964697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75538055660878083676643131 113307083491317125514964697)
    ·
      refine ⟨84980312618487844136223523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113307083491317125514964697 84980312618487844136223523)
      ·
        refine ⟨127470468927731766204335285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84980312618487844136223523 127470468927731766204335285)
        ·
          refine ⟨11950356461974853081656433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127470468927731766204335285 11950356461974853081656433)
          ·
            refine ⟨8962767346481139811242325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11950356461974853081656433 8962767346481139811242325)
            ·
              refine ⟨26258107460393964290749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8962767346481139811242325 26258107460393964290749)
              ·
                rfl

theorem cell23_4142136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 10].length) (baseStart_4142136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142136 prefixEnd_4142136 := by exact prefixLift 4142136
  have htrace : WordTrace (prefixWord ++ tailWord_4142136) baseStart_4142136 baseEnd_4142136 := by
    simpa [prefixWord, tailWord_4142136, baseEnd_4142136] using wordTrace_append hprefix tailTrace_4142136
  have hstable : (prefixWord ++ tailWord_4142136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142136).length < 2 ^ (prefixWord ++ tailWord_4142136).sum := by decide
  have hdescent : baseEnd_4142136 < baseStart_4142136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142140 : List Nat := [2, 2, 2, 2, 2, 2, 3, 2, 2, 4]
def baseStart_4142140 : Nat := 118140960795 + 4142140 * 2 ^ 59
def prefixEnd_4142140 : Nat := 4983230072969 + 3 ^ 40 * 4142140 * 2
def baseEnd_4142140 : Nat := 708969586071509697300217

theorem tailTrace_4142140 : CollatzResearch.WordTrace tailWord_4142140 prefixEnd_4142140 708969586071509697300217 := by
  unfold tailWord_4142140
  simp only [CollatzResearch.WordTrace]
  refine ⟨75538128606870838018215937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100717504809161117357621249 75538128606870838018215937)
  ·
    refine ⟨56653596455153128513661953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75538128606870838018215937 56653596455153128513661953)
    ·
      refine ⟨42490197341364846385246465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56653596455153128513661953 42490197341364846385246465)
      ·
        refine ⟨31867648006023634788934849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42490197341364846385246465 31867648006023634788934849)
        ·
          refine ⟨23900736004517726091701137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31867648006023634788934849 23900736004517726091701137)
          ·
            refine ⟨17925552003388294568775853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23900736004517726091701137 17925552003388294568775853)
            ·
              refine ⟨6722082001270610463290945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17925552003388294568775853 6722082001270610463290945)
              ·
                refine ⟨5041561500952957847468209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6722082001270610463290945 5041561500952957847468209)
                ·
                  refine ⟨3781171125714718385601157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5041561500952957847468209 3781171125714718385601157)
                  ·
                    refine ⟨708969586071509697300217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3781171125714718385601157 708969586071509697300217)
                    ·
                      rfl

theorem cell23_4142140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_4142140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142140 prefixEnd_4142140 := by exact prefixLift 4142140
  have htrace : WordTrace (prefixWord ++ tailWord_4142140) baseStart_4142140 baseEnd_4142140 := by
    simpa [prefixWord, tailWord_4142140, baseEnd_4142140] using wordTrace_append hprefix tailTrace_4142140
  have hstable : (prefixWord ++ tailWord_4142140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142140).length < 2 ^ (prefixWord ++ tailWord_4142140).sum := by decide
  have hdescent : baseEnd_4142140 < baseStart_4142140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142147 : List Nat := [1, 1, 1, 3, 1, 2, 3, 6, 1, 2, 2]
def baseStart_4142147 : Nat := 118140960795 + 4142147 * 2 ^ 59
def prefixEnd_4142147 : Nat := 4983230072969 + 3 ^ 40 * 4142147 * 2
def baseEnd_4142147 : Nat := 2126912352579110564513119

theorem tailTrace_4142147 : CollatzResearch.WordTrace tailWord_4142147 prefixEnd_4142147 2126912352579110564513119 := by
  unfold tailWord_4142147
  simp only [CollatzResearch.WordTrace]
  refine ⟨151076512524716316231936695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100717675016477544154624463 151076512524716316231936695)
  ·
    refine ⟨226614768787074474347905043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151076512524716316231936695 226614768787074474347905043)
    ·
      refine ⟨339922153180611711521857565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226614768787074474347905043 339922153180611711521857565)
      ·
        refine ⟨127470807442729391820696587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339922153180611711521857565 127470807442729391820696587)
        ·
          refine ⟨191206211164094087731044881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127470807442729391820696587 191206211164094087731044881)
          ·
            refine ⟨143404658373070565798283661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191206211164094087731044881 143404658373070565798283661)
            ·
              refine ⟨53776746889901462174356373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143404658373070565798283661 53776746889901462174356373)
              ·
                refine ⟨2520785010464131039422955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53776746889901462174356373 2520785010464131039422955)
                ·
                  refine ⟨3781177515696196559134433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2520785010464131039422955 3781177515696196559134433)
                  ·
                    refine ⟨2835883136772147419350825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3781177515696196559134433 2835883136772147419350825)
                    ·
                      refine ⟨2126912352579110564513119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2835883136772147419350825 2126912352579110564513119)
                      ·
                        rfl

theorem cell23_4142147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 1, 2, 2].length) (baseStart_4142147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142147 prefixEnd_4142147 := by exact prefixLift 4142147
  have htrace : WordTrace (prefixWord ++ tailWord_4142147) baseStart_4142147 baseEnd_4142147 := by
    simpa [prefixWord, tailWord_4142147, baseEnd_4142147] using wordTrace_append hprefix tailTrace_4142147
  have hstable : (prefixWord ++ tailWord_4142147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142147).length < 2 ^ (prefixWord ++ tailWord_4142147).sum := by decide
  have hdescent : baseEnd_4142147 < baseStart_4142147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142150 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_4142150 : Nat := 118140960795 + 4142150 * 2 ^ 59
def prefixEnd_4142150 : Nat := 4983230072969 + 3 ^ 40 * 4142150 * 2
def baseEnd_4142150 : Nat := 2126913893021074052775605

theorem tailTrace_4142150 : CollatzResearch.WordTrace tailWord_4142150 prefixEnd_4142150 2126913893021074052775605 := by
  unfold tailWord_4142150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4721144435740795242009247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100717747962470298496197269 4721144435740795242009247)
  ·
    refine ⟨7081716653611192863013871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4721144435740795242009247 7081716653611192863013871)
    ·
      refine ⟨10622574980416789294520807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7081716653611192863013871 10622574980416789294520807)
      ·
        refine ⟨15933862470625183941781211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10622574980416789294520807 15933862470625183941781211)
        ·
          refine ⟨23900793705937775912671817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15933862470625183941781211 23900793705937775912671817)
          ·
            refine ⟨17925595279453331934503863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23900793705937775912671817 17925595279453331934503863)
            ·
              refine ⟨26888392919179997901755795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17925595279453331934503863 26888392919179997901755795)
              ·
                refine ⟨40332589378769996852633693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26888392919179997901755795 40332589378769996852633693)
                ·
                  refine ⟨15124721017038748819737635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40332589378769996852633693 15124721017038748819737635)
                  ·
                    refine ⟨22687081525558123229606453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15124721017038748819737635 22687081525558123229606453)
                    ·
                      refine ⟨2126913893021074052775605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22687081525558123229606453 2126913893021074052775605)
                      ·
                        rfl

theorem cell23_4142150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_4142150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142150 prefixEnd_4142150 := by exact prefixLift 4142150
  have htrace : WordTrace (prefixWord ++ tailWord_4142150) baseStart_4142150 baseEnd_4142150 := by
    simpa [prefixWord, tailWord_4142150, baseEnd_4142150] using wordTrace_append hprefix tailTrace_4142150
  have hstable : (prefixWord ++ tailWord_4142150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142150).length < 2 ^ (prefixWord ++ tailWord_4142150).sum := by decide
  have hdescent : baseEnd_4142150 < baseStart_4142150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142163 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 6, 1, 3]
def baseStart_4142163 : Nat := 118140960795 + 4142163 * 2 ^ 59
def prefixEnd_4142163 : Nat := 4983230072969 + 3 ^ 40 * 4142163 * 2
def baseEnd_4142163 : Nat := 2126920568269582501913045

theorem tailTrace_4142163 : CollatzResearch.WordTrace tailWord_4142163 prefixEnd_4142163 2126920568269582501913045 := by
  unfold tailWord_4142163
  simp only [CollatzResearch.WordTrace]
  refine ⟨151077096092658350964519143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100718064061772233976346095 151077096092658350964519143)
  ·
    refine ⟨226615644138987526446778715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151077096092658350964519143 226615644138987526446778715)
    ·
      refine ⟨339923466208481289670168073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226615644138987526446778715 339923466208481289670168073)
      ·
        refine ⟨254942599656360967252626055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339923466208481289670168073 254942599656360967252626055)
        ·
          refine ⟨382413899484541450878939083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254942599656360967252626055 382413899484541450878939083)
          ·
            refine ⟨573620849226812176318408625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382413899484541450878939083 573620849226812176318408625)
            ·
              refine ⟨430215636920109132238806469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573620849226812176318408625 430215636920109132238806469)
              ·
                refine ⟨80665431922520462294776213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 430215636920109132238806469 80665431922520462294776213)
                ·
                  refine ⟨3781192121368146670067635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80665431922520462294776213 3781192121368146670067635)
                  ·
                    refine ⟨5671788182052220005101453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3781192121368146670067635 5671788182052220005101453)
                    ·
                      refine ⟨2126920568269582501913045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5671788182052220005101453 2126920568269582501913045)
                      ·
                        rfl

theorem cell23_4142163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 1, 3].length) (baseStart_4142163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142163 prefixEnd_4142163 := by exact prefixLift 4142163
  have htrace : WordTrace (prefixWord ++ tailWord_4142163) baseStart_4142163 baseEnd_4142163 := by
    simpa [prefixWord, tailWord_4142163, baseEnd_4142163] using wordTrace_append hprefix tailTrace_4142163
  have hstable : (prefixWord ++ tailWord_4142163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142163).length < 2 ^ (prefixWord ++ tailWord_4142163).sum := by decide
  have hdescent : baseEnd_4142163 < baseStart_4142163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142176 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 5]
def baseStart_4142176 : Nat := 118140960795 + 4142176 * 2 ^ 59
def prefixEnd_4142176 : Nat := 4983230072969 + 3 ^ 40 * 4142176 * 2
def baseEnd_4142176 : Nat := 2126927243518090951050485

theorem tailTrace_4142176 : CollatzResearch.WordTrace tailWord_4142176 prefixEnd_4142176 2126927243518090951050485 := by
  unfold tailWord_4142176
  simp only [CollatzResearch.WordTrace]
  refine ⟨75538785120805627092371191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100718380161074169456494921 75538785120805627092371191)
  ·
    refine ⟨113308177681208440638556787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75538785120805627092371191 113308177681208440638556787)
    ·
      refine ⟨169962266521812660957835181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113308177681208440638556787 169962266521812660957835181)
      ·
        refine ⟨63735849945679747859188193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169962266521812660957835181 63735849945679747859188193)
        ·
          refine ⟨47801887459259810894391145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63735849945679747859188193 47801887459259810894391145)
          ·
            refine ⟨35851415594444858170793359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47801887459259810894391145 35851415594444858170793359)
            ·
              refine ⟨53777123391667287256190039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35851415594444858170793359 53777123391667287256190039)
              ·
                refine ⟨80665685087500930884285059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53777123391667287256190039 80665685087500930884285059)
                ·
                  refine ⟨120998527631251396326427589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80665685087500930884285059 120998527631251396326427589)
                  ·
                    refine ⟨22687223930859636811205173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120998527631251396326427589 22687223930859636811205173)
                    ·
                      refine ⟨2126927243518090951050485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22687223930859636811205173 2126927243518090951050485)
                      ·
                        rfl

theorem cell23_4142176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_4142176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142176 prefixEnd_4142176 := by exact prefixLift 4142176
  have htrace : WordTrace (prefixWord ++ tailWord_4142176) baseStart_4142176 baseEnd_4142176 := by
    simpa [prefixWord, tailWord_4142176, baseEnd_4142176] using wordTrace_append hprefix tailTrace_4142176
  have hstable : (prefixWord ++ tailWord_4142176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142176).length < 2 ^ (prefixWord ++ tailWord_4142176).sum := by decide
  have hdescent : baseEnd_4142176 < baseStart_4142176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142270 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_4142270 : Nat := 118140960795 + 4142270 * 2 ^ 59
def prefixEnd_4142270 : Nat := 4983230072969 + 3 ^ 40 * 4142270 * 2
def baseEnd_4142270 : Nat := 2126975510699613583275053

theorem tailTrace_4142270 : CollatzResearch.WordTrace tailWord_4142270 prefixEnd_4142270 2126975510699613583275053 := by
  unfold tailWord_4142270
  simp only [CollatzResearch.WordTrace]
  refine ⟨18885124837908838529833033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100720665802180472159109509 18885124837908838529833033)
  ·
    refine ⟨14163843628431628897374775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18885124837908838529833033 14163843628431628897374775)
    ·
      refine ⟨21245765442647443346062163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14163843628431628897374775 21245765442647443346062163)
      ·
        refine ⟨31868648163971165019093245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21245765442647443346062163 31868648163971165019093245)
        ·
          refine ⟨11950743061489186882159967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31868648163971165019093245 11950743061489186882159967)
          ·
            refine ⟨17926114592233780323239951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11950743061489186882159967 17926114592233780323239951)
            ·
              refine ⟨26889171888350670484859927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17926114592233780323239951 26889171888350670484859927)
              ·
                refine ⟨40333757832526005727289891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26889171888350670484859927 40333757832526005727289891)
                ·
                  refine ⟨60500636748789008590934837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40333757832526005727289891 60500636748789008590934837)
                  ·
                    refine ⟨5671934695198969555400141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60500636748789008590934837 5671934695198969555400141)
                    ·
                      refine ⟨2126975510699613583275053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5671934695198969555400141 2126975510699613583275053)
                      ·
                        rfl

theorem cell23_4142270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_4142270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142270 prefixEnd_4142270 := by exact prefixLift 4142270
  have htrace : WordTrace (prefixWord ++ tailWord_4142270) baseStart_4142270 baseEnd_4142270 := by
    simpa [prefixWord, tailWord_4142270, baseEnd_4142270] using wordTrace_append hprefix tailTrace_4142270
  have hstable : (prefixWord ++ tailWord_4142270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142270).length < 2 ^ (prefixWord ++ tailWord_4142270).sum := by decide
  have hdescent : baseEnd_4142270 < baseStart_4142270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142313 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 5, 4, 3]
def baseStart_4142313 : Nat := 118140960795 + 4142313 * 2 ^ 59
def prefixEnd_4142313 : Nat := 4983230072969 + 3 ^ 40 * 4142313 * 2
def baseEnd_4142313 : Nat := 2126997590367756915037355

theorem tailTrace_4142313 : CollatzResearch.WordTrace tailWord_4142313 prefixEnd_4142313 2126997590367756915037355 := by
  unfold tailWord_4142313
  simp only [CollatzResearch.WordTrace]
  refine ⟨151082567042114926582479593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100721711361409951054986395 151082567042114926582479593)
  ·
    refine ⟨113311925281586194936859695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151082567042114926582479593 113311925281586194936859695)
    ·
      refine ⟨169967887922379292405289543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113311925281586194936859695 169967887922379292405289543)
      ·
        refine ⟨254951831883568938607934315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169967887922379292405289543 254951831883568938607934315)
        ·
          refine ⟨382427747825353407911901473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254951831883568938607934315 382427747825353407911901473)
          ·
            refine ⟨286820810869015055933926105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382427747825353407911901473 286820810869015055933926105)
            ·
              refine ⟨215115608151761291950444579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286820810869015055933926105 215115608151761291950444579)
              ·
                refine ⟨322673412227641937925666869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215115608151761291950444579 322673412227641937925666869)
                ·
                  refine ⟨30250632396341431680531269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 322673412227641937925666869 30250632396341431680531269)
                  ·
                    refine ⟨5671993574314018440099613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30250632396341431680531269 5671993574314018440099613)
                    ·
                      refine ⟨2126997590367756915037355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5671993574314018440099613 2126997590367756915037355)
                      ·
                        rfl

theorem cell23_4142313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 4, 3].length) (baseStart_4142313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142313 prefixEnd_4142313 := by exact prefixLift 4142313
  have htrace : WordTrace (prefixWord ++ tailWord_4142313) baseStart_4142313 baseEnd_4142313 := by
    simpa [prefixWord, tailWord_4142313, baseEnd_4142313] using wordTrace_append hprefix tailTrace_4142313
  have hstable : (prefixWord ++ tailWord_4142313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142313).length < 2 ^ (prefixWord ++ tailWord_4142313).sum := by decide
  have hdescent : baseEnd_4142313 < baseStart_4142313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142363 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 5, 5]
def baseStart_4142363 : Nat := 118140960795 + 4142363 * 2 ^ 59
def prefixEnd_4142363 : Nat := 4983230072969 + 3 ^ 40 * 4142363 * 2
def baseEnd_4142363 : Nat := 709007754800160573137375

theorem tailTrace_4142363 : CollatzResearch.WordTrace tailWord_4142363 prefixEnd_4142363 709007754800160573137375 := by
  unfold tailWord_4142363
  simp only [CollatzResearch.WordTrace]
  refine ⟨151084390691933785121799743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100722927127955856747866495 151084390691933785121799743)
  ·
    refine ⟨226626586037900677682699615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151084390691933785121799743 226626586037900677682699615)
    ·
      refine ⟨339939879056851016524049423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226626586037900677682699615 339939879056851016524049423)
      ·
        refine ⟨509909818585276524786074135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339939879056851016524049423 509909818585276524786074135)
        ·
          refine ⟨764864727877914787179111203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509909818585276524786074135 764864727877914787179111203)
          ·
            refine ⟨1147297091816872180768666805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764864727877914787179111203 1147297091816872180768666805)
            ·
              refine ⟨107559102357831766947062513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1147297091816872180768666805 107559102357831766947062513)
              ·
                refine ⟨80669326768373825210296885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107559102357831766947062513 80669326768373825210296885)
                ·
                  refine ⟨7562749384535046113465333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80669326768373825210296885 7562749384535046113465333)
                  ·
                    refine ⟨709007754800160573137375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7562749384535046113465333 709007754800160573137375)
                    ·
                      rfl

theorem cell23_4142363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 5].length) (baseStart_4142363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142363 prefixEnd_4142363 := by exact prefixLift 4142363
  have htrace : WordTrace (prefixWord ++ tailWord_4142363) baseStart_4142363 baseEnd_4142363 := by
    simpa [prefixWord, tailWord_4142363, baseEnd_4142363] using wordTrace_append hprefix tailTrace_4142363
  have hstable : (prefixWord ++ tailWord_4142363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142363).length < 2 ^ (prefixWord ++ tailWord_4142363).sum := by decide
  have hdescent : baseEnd_4142363 < baseStart_4142363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142383 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 4]
def baseStart_4142383 : Nat := 118140960795 + 4142383 * 2 ^ 59
def prefixEnd_4142383 : Nat := 4983230072969 + 3 ^ 40 * 4142383 * 2
def baseEnd_4142383 : Nat := 2127033534013571641162033

theorem tailTrace_4142383 : CollatzResearch.WordTrace tailWord_4142383 prefixEnd_4142383 2127033534013571641162033 := by
  unfold tailWord_4142383
  simp only [CollatzResearch.WordTrace]
  refine ⟨151085120151861328537527803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100723413434574219025018535 151085120151861328537527803)
  ·
    refine ⟨226627680227791992806291705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151085120151861328537527803 226627680227791992806291705)
    ·
      refine ⟨169970760170843994604718779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226627680227791992806291705 169970760170843994604718779)
      ·
        refine ⟨254956140256265991907078169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169970760170843994604718779 254956140256265991907078169)
        ·
          refine ⟨191217105192199493930308627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254956140256265991907078169 191217105192199493930308627)
          ·
            refine ⟨286825657788299240895462941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191217105192199493930308627 286825657788299240895462941)
            ·
              refine ⟨107559621670612215335798603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286825657788299240895462941 107559621670612215335798603)
              ·
                refine ⟨161339432505918323003697905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107559621670612215335798603 161339432505918323003697905)
                ·
                  refine ⟨121004574379438742252773429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161339432505918323003697905 121004574379438742252773429)
                  ·
                    refine ⟨11344178848072382086197509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121004574379438742252773429 11344178848072382086197509)
                    ·
                      refine ⟨2127033534013571641162033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11344178848072382086197509 2127033534013571641162033)
                      ·
                        rfl

theorem cell23_4142383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_4142383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142383 prefixEnd_4142383 := by exact prefixLift 4142383
  have htrace : WordTrace (prefixWord ++ tailWord_4142383) baseStart_4142383 baseEnd_4142383 := by
    simpa [prefixWord, tailWord_4142383, baseEnd_4142383] using wordTrace_append hprefix tailTrace_4142383
  have hstable : (prefixWord ++ tailWord_4142383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142383).length < 2 ^ (prefixWord ++ tailWord_4142383).sum := by decide
  have hdescent : baseEnd_4142383 < baseStart_4142383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142400 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 4]
def baseStart_4142400 : Nat := 118140960795 + 4142400 * 2 ^ 59
def prefixEnd_4142400 : Nat := 4983230072969 + 3 ^ 40 * 4142400 * 2
def baseEnd_4142400 : Nat := 2127042263184698074649455

theorem tailTrace_4142400 : CollatzResearch.WordTrace tailWord_4142400 prefixEnd_4142400 2127042263184698074649455 := by
  unfold tailWord_4142400
  simp only [CollatzResearch.WordTrace]
  refine ⟨75542870096399870220448327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100723826795199826960597769 75542870096399870220448327)
  ·
    refine ⟨113314305144599805330672491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75542870096399870220448327 113314305144599805330672491)
    ·
      refine ⟨169971457716899707996008737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113314305144599805330672491 169971457716899707996008737)
      ·
        refine ⟨127478593287674780997006553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169971457716899707996008737 127478593287674780997006553)
        ·
          refine ⟨95608944965756085747754915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127478593287674780997006553 95608944965756085747754915)
          ·
            refine ⟨143413417448634128621632373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95608944965756085747754915 143413417448634128621632373)
            ·
              refine ⟨13445007885809449558278035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143413417448634128621632373 13445007885809449558278035)
              ·
                refine ⟨20167511828714174337417053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13445007885809449558278035 20167511828714174337417053)
                ·
                  refine ⟨7562816935767815376531395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20167511828714174337417053 7562816935767815376531395)
                  ·
                    refine ⟨11344225403651723064797093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7562816935767815376531395 11344225403651723064797093)
                    ·
                      refine ⟨2127042263184698074649455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11344225403651723064797093 2127042263184698074649455)
                      ·
                        rfl

theorem cell23_4142400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_4142400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142400 prefixEnd_4142400 := by exact prefixLift 4142400
  have htrace : WordTrace (prefixWord ++ tailWord_4142400) baseStart_4142400 baseEnd_4142400 := by
    simpa [prefixWord, tailWord_4142400, baseEnd_4142400] using wordTrace_append hprefix tailTrace_4142400
  have hstable : (prefixWord ++ tailWord_4142400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142400).length < 2 ^ (prefixWord ++ tailWord_4142400).sum := by decide
  have hdescent : baseEnd_4142400 < baseStart_4142400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142410 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 6, 4]
def baseStart_4142410 : Nat := 118140960795 + 4142410 * 2 ^ 59
def prefixEnd_4142410 : Nat := 4983230072969 + 3 ^ 40 * 4142410 * 2
def baseEnd_4142410 : Nat := 709015799330414345174803

theorem tailTrace_4142410 : CollatzResearch.WordTrace tailWord_4142410 prefixEnd_4142410 709015799330414345174803 := by
  unfold tailWord_4142410
  simp only [CollatzResearch.WordTrace]
  refine ⟨37771526230690878037190171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100724069948509008099173789 37771526230690878037190171)
  ·
    refine ⟨56657289346036317055785257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37771526230690878037190171 56657289346036317055785257)
    ·
      refine ⟨42492967009527237791838943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56657289346036317055785257 42492967009527237791838943)
      ·
        refine ⟨63739450514290856687758415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42492967009527237791838943 63739450514290856687758415)
        ·
          refine ⟨95609175771436285031637623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63739450514290856687758415 95609175771436285031637623)
          ·
            refine ⟨143413763657154427547456435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95609175771436285031637623 143413763657154427547456435)
            ·
              refine ⟨215120645485731641321184653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143413763657154427547456435 215120645485731641321184653)
              ·
                refine ⟨80670242057149365495444245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215120645485731641321184653 80670242057149365495444245)
                ·
                  refine ⟨3781417596428876507598949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80670242057149365495444245 3781417596428876507598949)
                  ·
                    refine ⟨709015799330414345174803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3781417596428876507598949 709015799330414345174803)
                    ·
                      rfl

theorem cell23_4142410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_4142410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142410 prefixEnd_4142410 := by exact prefixLift 4142410
  have htrace : WordTrace (prefixWord ++ tailWord_4142410) baseStart_4142410 baseEnd_4142410 := by
    simpa [prefixWord, tailWord_4142410, baseEnd_4142410] using wordTrace_append hprefix tailTrace_4142410
  have hstable : (prefixWord ++ tailWord_4142410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142410).length < 2 ^ (prefixWord ++ tailWord_4142410).sum := by decide
  have hdescent : baseEnd_4142410 < baseStart_4142410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142423 : List Nat := [1, 1, 3, 2, 3, 13]
def baseStart_4142423 : Nat := 118140960795 + 4142423 * 2 ^ 59
def prefixEnd_4142423 : Nat := 4983230072969 + 3 ^ 40 * 4142423 * 2
def baseEnd_4142423 : Nat := 8753308943373462899843

theorem tailTrace_4142423 : CollatzResearch.WordTrace tailWord_4142423 prefixEnd_4142423 8753308943373462899843 := by
  unfold tailWord_4142423
  simp only [CollatzResearch.WordTrace]
  refine ⟨151086579071716415368983923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100724386047810943579322615 151086579071716415368983923)
  ·
    refine ⟨226629868607574623053475885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151086579071716415368983923 226629868607574623053475885)
    ·
      refine ⟨84986200727840483645053457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226629868607574623053475885 84986200727840483645053457)
      ·
        refine ⟨63739650545880362733790093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84986200727840483645053457 63739650545880362733790093)
        ·
          refine ⟨23902368954705136025171285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63739650545880362733790093 23902368954705136025171285)
          ·
            refine ⟨8753308943373462899843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 23902368954705136025171285 8753308943373462899843)
            ·
              rfl

theorem cell23_4142423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 13].length) (baseStart_4142423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142423 prefixEnd_4142423 := by exact prefixLift 4142423
  have htrace : WordTrace (prefixWord ++ tailWord_4142423) baseStart_4142423 baseEnd_4142423 := by
    simpa [prefixWord, tailWord_4142423, baseEnd_4142423] using wordTrace_append hprefix tailTrace_4142423
  have hstable : (prefixWord ++ tailWord_4142423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142423).length < 2 ^ (prefixWord ++ tailWord_4142423).sum := by decide
  have hdescent : baseEnd_4142423 < baseStart_4142423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142467 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 3]
def baseStart_4142467 : Nat := 118140960795 + 4142467 * 2 ^ 59
def prefixEnd_4142467 : Nat := 4983230072969 + 3 ^ 40 * 4142467 * 2
def baseEnd_4142467 : Nat := 2127076666388549312511647

theorem tailTrace_4142467 : CollatzResearch.WordTrace tailWord_4142467 prefixEnd_4142467 2127076666388549312511647 := by
  unfold tailWord_4142467
  simp only [CollatzResearch.WordTrace]
  refine ⟨151088183883557010883585655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100725455922371340589057103 151088183883557010883585655)
  ·
    refine ⟨226632275825335516325378483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151088183883557010883585655 226632275825335516325378483)
    ·
      refine ⟨339948413738003274488067725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226632275825335516325378483 339948413738003274488067725)
      ·
        refine ⟨127480655151751227933025397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339948413738003274488067725 127480655151751227933025397)
        ·
          refine ⟨11951311420476677618721131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127480655151751227933025397 11951311420476677618721131)
          ·
            refine ⟨17926967130715016428081697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11951311420476677618721131 17926967130715016428081697)
            ·
              refine ⟨13445225348036262321061273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17926967130715016428081697 13445225348036262321061273)
              ·
                refine ⟨10083919011027196740795955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13445225348036262321061273 10083919011027196740795955)
                ·
                  refine ⟨15125878516540795111193933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10083919011027196740795955 15125878516540795111193933)
                  ·
                    refine ⟨5672204443702798166697725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15125878516540795111193933 5672204443702798166697725)
                    ·
                      refine ⟨2127076666388549312511647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5672204443702798166697725 2127076666388549312511647)
                      ·
                        rfl

theorem cell23_4142467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_4142467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142467 prefixEnd_4142467 := by exact prefixLift 4142467
  have htrace : WordTrace (prefixWord ++ tailWord_4142467) baseStart_4142467 baseEnd_4142467 := by
    simpa [prefixWord, tailWord_4142467, baseEnd_4142467] using wordTrace_append hprefix tailTrace_4142467
  have hstable : (prefixWord ++ tailWord_4142467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142467).length < 2 ^ (prefixWord ++ tailWord_4142467).sum := by decide
  have hdescent : baseEnd_4142467 < baseStart_4142467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142468 : List Nat := [2, 3, 2, 1, 1, 4, 2, 3, 1, 2, 2]
def baseStart_4142468 : Nat := 118140960795 + 4142468 * 2 ^ 59
def prefixEnd_4142468 : Nat := 4983230072969 + 3 ^ 40 * 4142468 * 2
def baseEnd_4142468 : Nat := 2127077179869203808599143

theorem tailTrace_4142468 : CollatzResearch.WordTrace tailWord_4142468 prefixEnd_4142468 2127077179869203808599143 := by
  unfold tailWord_4142468
  simp only [CollatzResearch.WordTrace]
  refine ⟨75544110178276694027186029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100725480237702258702914705 75544110178276694027186029)
  ·
    refine ⟨28329041316853760260194761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75544110178276694027186029 28329041316853760260194761)
    ·
      refine ⟨21246780987640320195146071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28329041316853760260194761 21246780987640320195146071)
      ·
        refine ⟨31870171481460480292719107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21246780987640320195146071 31870171481460480292719107)
        ·
          refine ⟨47805257222190720439078661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31870171481460480292719107 47805257222190720439078661)
          ·
            refine ⟨8963485729160760082327249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47805257222190720439078661 8963485729160760082327249)
            ·
              refine ⟨6722614296870570061745437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8963485729160760082327249 6722614296870570061745437)
              ·
                refine ⟨2520980361326463773154539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6722614296870570061745437 2520980361326463773154539)
                ·
                  refine ⟨3781470541989695659731809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2520980361326463773154539 3781470541989695659731809)
                  ·
                    refine ⟨2836102906492271744798857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3781470541989695659731809 2836102906492271744798857)
                    ·
                      refine ⟨2127077179869203808599143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2836102906492271744798857 2127077179869203808599143)
                      ·
                        rfl

theorem cell23_4142468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_4142468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142468 prefixEnd_4142468 := by exact prefixLift 4142468
  have htrace : WordTrace (prefixWord ++ tailWord_4142468) baseStart_4142468 baseEnd_4142468 := by
    simpa [prefixWord, tailWord_4142468, baseEnd_4142468] using wordTrace_append hprefix tailTrace_4142468
  have hstable : (prefixWord ++ tailWord_4142468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142468).length < 2 ^ (prefixWord ++ tailWord_4142468).sum := by decide
  have hdescent : baseEnd_4142468 < baseStart_4142468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142471 : List Nat := [1, 1, 4, 2, 2, 4, 2, 1, 1, 2, 3]
def baseStart_4142471 : Nat := 118140960795 + 4142471 * 2 ^ 59
def prefixEnd_4142471 : Nat := 4983230072969 + 3 ^ 40 * 4142471 * 2
def baseEnd_4142471 : Nat := 2127078720311167296861629

theorem tailTrace_4142471 : CollatzResearch.WordTrace tailWord_4142471 prefixEnd_4142471 2127078720311167296861629 := by
  unfold tailWord_4142471
  simp only [CollatzResearch.WordTrace]
  refine ⟨151088329775542519566731267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100725553183695013044487511 151088329775542519566731267)
  ·
    refine ⟨226632494663313779350096901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151088329775542519566731267 226632494663313779350096901)
    ·
      refine ⟨42493592749371333628143169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226632494663313779350096901 42493592749371333628143169)
      ·
        refine ⟨31870194562028500221107377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42493592749371333628143169 31870194562028500221107377)
        ·
          refine ⟨23902645921521375165830533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31870194562028500221107377 23902645921521375165830533)
          ·
            refine ⟨4481746110285257843593225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23902645921521375165830533 4481746110285257843593225)
            ·
              refine ⟨3361309582713943382694919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4481746110285257843593225 3361309582713943382694919)
              ·
                refine ⟨5041964374070915074042379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3361309582713943382694919 5041964374070915074042379)
                ·
                  refine ⟨7562946561106372611063569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5041964374070915074042379 7562946561106372611063569)
                  ·
                    refine ⟨5672209920829779458297677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7562946561106372611063569 5672209920829779458297677)
                    ·
                      refine ⟨2127078720311167296861629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5672209920829779458297677 2127078720311167296861629)
                      ·
                        rfl

theorem cell23_4142471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_4142471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142471 prefixEnd_4142471 := by exact prefixLift 4142471
  have htrace : WordTrace (prefixWord ++ tailWord_4142471) baseStart_4142471 baseEnd_4142471 := by
    simpa [prefixWord, tailWord_4142471, baseEnd_4142471] using wordTrace_append hprefix tailTrace_4142471
  have hstable : (prefixWord ++ tailWord_4142471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142471).length < 2 ^ (prefixWord ++ tailWord_4142471).sum := by decide
  have hdescent : baseEnd_4142471 < baseStart_4142471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142478 : List Nat := [4, 1, 1, 4, 3, 1, 1, 2, 2, 4]
def baseStart_4142478 : Nat := 118140960795 + 4142478 * 2 ^ 59
def prefixEnd_4142478 : Nat := 4983230072969 + 3 ^ 40 * 4142478 * 2
def baseEnd_4142478 : Nat := 709027438225249589824699

theorem tailTrace_4142478 : CollatzResearch.WordTrace tailWord_4142478 prefixEnd_4142478 709027438225249589824699 := by
  unfold tailWord_4142478
  simp only [CollatzResearch.WordTrace]
  refine ⟨18886073135814644970279511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100725723391011439841490725 18886073135814644970279511)
  ·
    refine ⟨28329109703721967455419267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18886073135814644970279511 28329109703721967455419267)
    ·
      refine ⟨42493664555582951183128901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28329109703721967455419267 42493664555582951183128901)
      ·
        refine ⟨7967562104171803346836669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42493664555582951183128901 7967562104171803346836669)
        ·
          refine ⟨2987835789064426255063751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7967562104171803346836669 2987835789064426255063751)
          ·
            refine ⟨4481753683596639382595627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2987835789064426255063751 4481753683596639382595627)
            ·
              refine ⟨6722630525394959073893441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4481753683596639382595627 6722630525394959073893441)
              ·
                refine ⟨5041972894046219305420081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6722630525394959073893441 5041972894046219305420081)
                ·
                  refine ⟨3781479670534664479065061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5041972894046219305420081 3781479670534664479065061)
                  ·
                    refine ⟨709027438225249589824699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3781479670534664479065061 709027438225249589824699)
                    ·
                      rfl

theorem cell23_4142478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_4142478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142478 prefixEnd_4142478 := by exact prefixLift 4142478
  have htrace : WordTrace (prefixWord ++ tailWord_4142478) baseStart_4142478 baseEnd_4142478 := by
    simpa [prefixWord, tailWord_4142478, baseEnd_4142478] using wordTrace_append hprefix tailTrace_4142478
  have hstable : (prefixWord ++ tailWord_4142478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142478).length < 2 ^ (prefixWord ++ tailWord_4142478).sum := by decide
  have hdescent : baseEnd_4142478 < baseStart_4142478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142520 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 1, 4, 4]
def baseStart_4142520 : Nat := 118140960795 + 4142520 * 2 ^ 59
def prefixEnd_4142520 : Nat := 4983230072969 + 3 ^ 40 * 4142520 * 2
def baseEnd_4142520 : Nat := 2127103880863237605148903

theorem tailTrace_4142520 : CollatzResearch.WordTrace tailWord_4142520 prefixEnd_4142520 2127103880863237605148903 := by
  unfold tailWord_4142520
  simp only [CollatzResearch.WordTrace]
  refine ⟨75545058476182500467632507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100726744634910000623510009 75545058476182500467632507)
  ·
    refine ⟨113317587714273750701448761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75545058476182500467632507 113317587714273750701448761)
    ·
      refine ⟨84988190785705313026086571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113317587714273750701448761 84988190785705313026086571)
      ·
        refine ⟨127482286178557969539129857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84988190785705313026086571 127482286178557969539129857)
        ·
          refine ⟨95611714633918477154347393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127482286178557969539129857 95611714633918477154347393)
          ·
            refine ⟨71708785975438857865760545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95611714633918477154347393 71708785975438857865760545)
            ·
              refine ⟨53781589481579143399320409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71708785975438857865760545 53781589481579143399320409)
              ·
                refine ⟨40336192111184357549490307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53781589481579143399320409 40336192111184357549490307)
                ·
                  refine ⟨60504288166776536324235461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40336192111184357549490307 60504288166776536324235461)
                  ·
                    refine ⟨11344554031270600560794149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60504288166776536324235461 11344554031270600560794149)
                    ·
                      refine ⟨2127103880863237605148903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11344554031270600560794149 2127103880863237605148903)
                      ·
                        rfl

theorem cell23_4142520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_4142520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142520 prefixEnd_4142520 := by exact prefixLift 4142520
  have htrace : WordTrace (prefixWord ++ tailWord_4142520) baseStart_4142520 baseEnd_4142520 := by
    simpa [prefixWord, tailWord_4142520, baseEnd_4142520] using wordTrace_append hprefix tailTrace_4142520
  have hstable : (prefixWord ++ tailWord_4142520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142520).length < 2 ^ (prefixWord ++ tailWord_4142520).sum := by decide
  have hdescent : baseEnd_4142520 < baseStart_4142520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142560 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 1, 7]
def baseStart_4142560 : Nat := 118140960795 + 4142560 * 2 ^ 59
def prefixEnd_4142560 : Nat := 4983230072969 + 3 ^ 40 * 4142560 * 2
def baseEnd_4142560 : Nat := 709041473363139149549573

theorem tailTrace_4142560 : CollatzResearch.WordTrace tailWord_4142560 prefixEnd_4142560 709041473363139149549573 := by
  unfold tailWord_4142560
  simp only [CollatzResearch.WordTrace]
  refine ⟨75545787936110043883360567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100727717248146725177814089 75545787936110043883360567)
  ·
    refine ⟨113318681904165065825040851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75545787936110043883360567 113318681904165065825040851)
    ·
      refine ⟨169978022856247598737561277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113318681904165065825040851 169978022856247598737561277)
      ·
        refine ⟨63741758571092849526585479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169978022856247598737561277 63741758571092849526585479)
        ·
          refine ⟨95612637856639274289878219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63741758571092849526585479 95612637856639274289878219)
          ·
            refine ⟨143418956784958911434817329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95612637856639274289878219 143418956784958911434817329)
            ·
              refine ⟨107564217588719183576112997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143418956784958911434817329 107564217588719183576112997)
              ·
                refine ⟨20168290797884846920521187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107564217588719183576112997 20168290797884846920521187)
                ·
                  refine ⟨30252436196827270380781781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20168290797884846920521187 30252436196827270380781781)
                  ·
                    refine ⟨709041473363139149549573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30252436196827270380781781 709041473363139149549573)
                    ·
                      rfl

theorem cell23_4142560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 1, 7].length) (baseStart_4142560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142560 prefixEnd_4142560 := by exact prefixLift 4142560
  have htrace : WordTrace (prefixWord ++ tailWord_4142560) baseStart_4142560 baseEnd_4142560 := by
    simpa [prefixWord, tailWord_4142560, baseEnd_4142560] using wordTrace_append hprefix tailTrace_4142560
  have hstable : (prefixWord ++ tailWord_4142560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142560).length < 2 ^ (prefixWord ++ tailWord_4142560).sum := by decide
  have hdescent : baseEnd_4142560 < baseStart_4142560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142577 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 2, 5]
def baseStart_4142577 : Nat := 118140960795 + 4142577 * 2 ^ 59
def prefixEnd_4142577 : Nat := 4983230072969 + 3 ^ 40 * 4142577 * 2
def baseEnd_4142577 : Nat := 709044383086847960712047

theorem tailTrace_4142577 : CollatzResearch.WordTrace tailWord_4142577 prefixEnd_4142577 709044383086847960712047 := by
  unfold tailWord_4142577
  simp only [CollatzResearch.WordTrace]
  refine ⟨151092195913158499670089985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100728130608772333113393323 151092195913158499670089985)
  ·
    refine ⟨113319146934868874752567489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151092195913158499670089985 113319146934868874752567489)
    ·
      refine ⟨84989360201151656064425617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113319146934868874752567489 84989360201151656064425617)
      ·
        refine ⟨63742020150863742048319213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84989360201151656064425617 63742020150863742048319213)
        ·
          refine ⟨23903257556573903268119705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63742020150863742048319213 23903257556573903268119705)
          ·
            refine ⟨17927443167430427451089779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23903257556573903268119705 17927443167430427451089779)
            ·
              refine ⟨26891164751145641176634669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17927443167430427451089779 26891164751145641176634669)
              ·
                refine ⟨10084186781679615441238001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26891164751145641176634669 10084186781679615441238001)
                ·
                  refine ⟨7563140086259711580928501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10084186781679615441238001 7563140086259711580928501)
                  ·
                    refine ⟨709044383086847960712047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7563140086259711580928501 709044383086847960712047)
                    ·
                      rfl

theorem cell23_4142577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_4142577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142577 prefixEnd_4142577 := by exact prefixLift 4142577
  have htrace : WordTrace (prefixWord ++ tailWord_4142577) baseStart_4142577 baseEnd_4142577 := by
    simpa [prefixWord, tailWord_4142577, baseEnd_4142577] using wordTrace_append hprefix tailTrace_4142577
  have hstable : (prefixWord ++ tailWord_4142577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142577).length < 2 ^ (prefixWord ++ tailWord_4142577).sum := by decide
  have hdescent : baseEnd_4142577 < baseStart_4142577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142624 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 5, 4]
def baseStart_4142624 : Nat := 118140960795 + 4142624 * 2 ^ 59
def prefixEnd_4142624 : Nat := 4983230072969 + 3 ^ 40 * 4142624 * 2
def baseEnd_4142624 : Nat := 709052427617101732749475

theorem tailTrace_4142624 : CollatzResearch.WordTrace tailWord_4142624 prefixEnd_4142624 709052427617101732749475 := by
  unfold tailWord_4142624
  simp only [CollatzResearch.WordTrace]
  refine ⟨75546955071994113348525463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100729273429325484464700617 75546955071994113348525463)
  ·
    refine ⟨113320432607991170022788195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75546955071994113348525463 113320432607991170022788195)
    ·
      refine ⟨169980648911986755034182293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113320432607991170022788195 169980648911986755034182293)
      ·
        refine ⟨7967842917749379142227295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 169980648911986755034182293 7967842917749379142227295)
        ·
          refine ⟨11951764376624068713340943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7967842917749379142227295 11951764376624068713340943)
          ·
            refine ⟨17927646564936103070011415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11951764376624068713340943 17927646564936103070011415)
            ·
              refine ⟨26891469847404154605017123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17927646564936103070011415 26891469847404154605017123)
              ·
                refine ⟨40337204771106231907525685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26891469847404154605017123 40337204771106231907525685)
                ·
                  refine ⟨3781612947291209241330533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40337204771106231907525685 3781612947291209241330533)
                  ·
                    refine ⟨709052427617101732749475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3781612947291209241330533 709052427617101732749475)
                    ·
                      rfl

theorem cell23_4142624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 5, 4].length) (baseStart_4142624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142624 prefixEnd_4142624 := by exact prefixLift 4142624
  have htrace : WordTrace (prefixWord ++ tailWord_4142624) baseStart_4142624 baseEnd_4142624 := by
    simpa [prefixWord, tailWord_4142624, baseEnd_4142624] using wordTrace_append hprefix tailTrace_4142624
  have hstable : (prefixWord ++ tailWord_4142624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142624).length < 2 ^ (prefixWord ++ tailWord_4142624).sum := by decide
  have hdescent : baseEnd_4142624 < baseStart_4142624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142634 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_4142634 : Nat := 118140960795 + 4142634 * 2 ^ 59
def prefixEnd_4142634 : Nat := 4983230072969 + 3 ^ 40 * 4142634 * 2
def baseEnd_4142634 : Nat := 2127162417657850159123379

theorem tailTrace_4142634 : CollatzResearch.WordTrace tailWord_4142634 prefixEnd_4142634 2127162417657850159123379 := by
  unfold tailWord_4142634
  simp only [CollatzResearch.WordTrace]
  refine ⟨37773568718487999601228739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100729516582634665603276637 37773568718487999601228739)
  ·
    refine ⟨56660353077731999401843109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37773568718487999601228739 56660353077731999401843109)
    ·
      refine ⟨10623816202074749887845583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56660353077731999401843109 10623816202074749887845583)
      ·
        refine ⟨15935724303112124831768375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10623816202074749887845583 15935724303112124831768375)
        ·
          refine ⟨23903586454668187247652563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15935724303112124831768375 23903586454668187247652563)
          ·
            refine ⟨35855379682002280871478845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23903586454668187247652563 35855379682002280871478845)
            ·
              refine ⟨13445767380750855326804567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35855379682002280871478845 13445767380750855326804567)
              ·
                refine ⟨20168651071126282990206851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13445767380750855326804567 20168651071126282990206851)
                ·
                  refine ⟨30252976606689424485310277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20168651071126282990206851 30252976606689424485310277)
                  ·
                    refine ⟨5672433113754267090995677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30252976606689424485310277 5672433113754267090995677)
                    ·
                      refine ⟨2127162417657850159123379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5672433113754267090995677 2127162417657850159123379)
                      ·
                        rfl

theorem cell23_4142634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_4142634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142634 prefixEnd_4142634 := by exact prefixLift 4142634
  have htrace : WordTrace (prefixWord ++ tailWord_4142634) baseStart_4142634 baseEnd_4142634 := by
    simpa [prefixWord, tailWord_4142634, baseEnd_4142634] using wordTrace_append hprefix tailTrace_4142634
  have hstable : (prefixWord ++ tailWord_4142634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142634).length < 2 ^ (prefixWord ++ tailWord_4142634).sum := by decide
  have hdescent : baseEnd_4142634 < baseStart_4142634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142657 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_4142657 : Nat := 118140960795 + 4142657 * 2 ^ 59
def prefixEnd_4142657 : Nat := 4983230072969 + 3 ^ 40 * 4142657 * 2
def baseEnd_4142657 : Nat := 2127174227712903569135773

theorem tailTrace_4142657 : CollatzResearch.WordTrace tailWord_4142657 prefixEnd_4142657 2127174227712903569135773 := by
  unfold tailWord_4142657
  simp only [CollatzResearch.WordTrace]
  refine ⟨151095113752868673333002225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100730075835245782222001483 151095113752868673333002225)
  ·
    refine ⟨113321335314651504999751669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151095113752868673333002225 113321335314651504999751669)
    ·
      refine ⟨10623875185748578593726719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113321335314651504999751669 10623875185748578593726719)
      ·
        refine ⟨15935812778622867890590079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10623875185748578593726719 15935812778622867890590079)
        ·
          refine ⟨23903719167934301835885119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15935812778622867890590079 23903719167934301835885119)
          ·
            refine ⟨35855578751901452753827679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23903719167934301835885119 35855578751901452753827679)
            ·
              refine ⟨53783368127852179130741519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35855578751901452753827679 53783368127852179130741519)
              ·
                refine ⟨80675052191778268696112279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53783368127852179130741519 80675052191778268696112279)
                ·
                  refine ⟨121012578287667403044168419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80675052191778268696112279 121012578287667403044168419)
                  ·
                    refine ⟨181518867431501104566252629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121012578287667403044168419 181518867431501104566252629)
                    ·
                      refine ⟨2127174227712903569135773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 181518867431501104566252629 2127174227712903569135773)
                      ·
                        rfl

theorem cell23_4142657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_4142657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142657 prefixEnd_4142657 := by exact prefixLift 4142657
  have htrace : WordTrace (prefixWord ++ tailWord_4142657) baseStart_4142657 baseEnd_4142657 := by
    simpa [prefixWord, tailWord_4142657, baseEnd_4142657] using wordTrace_append hprefix tailTrace_4142657
  have hstable : (prefixWord ++ tailWord_4142657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142657).length < 2 ^ (prefixWord ++ tailWord_4142657).sum := by decide
  have hdescent : baseEnd_4142657 < baseStart_4142657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142697 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 1, 6]
def baseStart_4142697 : Nat := 118140960795 + 4142697 * 2 ^ 59
def prefixEnd_4142697 : Nat := 4983230072969 + 3 ^ 40 * 4142697 * 2
def baseEnd_4142697 : Nat := 709064922313027804211863

theorem tailTrace_4142697 : CollatzResearch.WordTrace tailWord_4142697 prefixEnd_4142697 709064922313027804211863 := by
  unfold tailWord_4142697
  simp only [CollatzResearch.WordTrace]
  refine ⟨151096572672723760164458345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100731048448482506776305563 151096572672723760164458345)
  ·
    refine ⟨113322429504542820123343759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151096572672723760164458345 113322429504542820123343759)
    ·
      refine ⟨169983644256814230185015639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113322429504542820123343759 169983644256814230185015639)
      ·
        refine ⟨254975466385221345277523459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169983644256814230185015639 254975466385221345277523459)
        ·
          refine ⟨382463199577832017916285189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254975466385221345277523459 382463199577832017916285189)
          ·
            refine ⟨71711849920843503359303473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 382463199577832017916285189 71711849920843503359303473)
            ·
              refine ⟨53783887440632627519477605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71711849920843503359303473 53783887440632627519477605)
              ·
                refine ⟨10084478895118617659902051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53783887440632627519477605 10084478895118617659902051)
                ·
                  refine ⟨15126718342677926489853077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10084478895118617659902051 15126718342677926489853077)
                  ·
                    refine ⟨709064922313027804211863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15126718342677926489853077 709064922313027804211863)
                    ·
                      rfl

theorem cell23_4142697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 6].length) (baseStart_4142697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142697 prefixEnd_4142697 := by exact prefixLift 4142697
  have htrace : WordTrace (prefixWord ++ tailWord_4142697) baseStart_4142697 baseEnd_4142697 := by
    simpa [prefixWord, tailWord_4142697, baseEnd_4142697] using wordTrace_append hprefix tailTrace_4142697
  have hstable : (prefixWord ++ tailWord_4142697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142697).length < 2 ^ (prefixWord ++ tailWord_4142697).sum := by decide
  have hdescent : baseEnd_4142697 < baseStart_4142697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142707 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 3]
def baseStart_4142707 : Nat := 118140960795 + 4142707 * 2 ^ 59
def prefixEnd_4142707 : Nat := 4983230072969 + 3 ^ 40 * 4142707 * 2
def baseEnd_4142707 : Nat := 2127199901745628373510543

theorem tailTrace_4142707 : CollatzResearch.WordTrace tailWord_4142707 prefixEnd_4142707 2127199901745628373510543 := by
  unfold tailWord_4142707
  simp only [CollatzResearch.WordTrace]
  refine ⟨151096937402687531872322375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100731291601791687914881583 151096937402687531872322375)
  ·
    refine ⟨226645406104031297808483563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151096937402687531872322375 226645406104031297808483563)
    ·
      refine ⟨339968109156046946712725345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226645406104031297808483563 339968109156046946712725345)
      ·
        refine ⟨254976081867035210034544009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339968109156046946712725345 254976081867035210034544009)
        ·
          refine ⟨191232061400276407525908007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254976081867035210034544009 191232061400276407525908007)
          ·
            refine ⟨286848092100414611288862011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191232061400276407525908007 286848092100414611288862011)
            ·
              refine ⟨430272138150621916933293017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286848092100414611288862011 430272138150621916933293017)
              ·
                refine ⟨322704103612966437699969763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430272138150621916933293017 322704103612966437699969763)
                ·
                  refine ⟨484056155419449656549954645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322704103612966437699969763 484056155419449656549954645)
                  ·
                    refine ⟨5672533071321675662694781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 484056155419449656549954645 5672533071321675662694781)
                    ·
                      refine ⟨2127199901745628373510543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5672533071321675662694781 2127199901745628373510543)
                      ·
                        rfl

theorem cell23_4142707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 3].length) (baseStart_4142707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142707 prefixEnd_4142707 := by exact prefixLift 4142707
  have htrace : WordTrace (prefixWord ++ tailWord_4142707) baseStart_4142707 baseEnd_4142707 := by
    simpa [prefixWord, tailWord_4142707, baseEnd_4142707] using wordTrace_append hprefix tailTrace_4142707
  have hstable : (prefixWord ++ tailWord_4142707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142707).length < 2 ^ (prefixWord ++ tailWord_4142707).sum := by decide
  have hdescent : baseEnd_4142707 < baseStart_4142707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142727 : List Nat := [1, 1, 4, 2, 1, 3, 1, 10]
def baseStart_4142727 : Nat := 118140960795 + 4142727 * 2 ^ 59
def prefixEnd_4142727 : Nat := 4983230072969 + 3 ^ 40 * 4142727 * 2
def baseEnd_4142727 : Nat := 78785561902174751676313

theorem tailTrace_4142727 : CollatzResearch.WordTrace tailWord_4142727 prefixEnd_4142727 78785561902174751676313 := by
  unfold tailWord_4142727
  simp only [CollatzResearch.WordTrace]
  refine ⟨151097666862615075288050435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100731777908410050192033623 151097666862615075288050435)
  ·
    refine ⟨226646500293922612932075653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151097666862615075288050435 226646500293922612932075653)
    ·
      refine ⟨42496218805110489924764185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226646500293922612932075653 42496218805110489924764185)
      ·
        refine ⟨31872164103832867443573139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42496218805110489924764185 31872164103832867443573139)
        ·
          refine ⟨47808246155749301165359709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31872164103832867443573139 47808246155749301165359709)
          ·
            refine ⟨17928092308405987937009891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47808246155749301165359709 17928092308405987937009891)
            ·
              refine ⟨26892138462608981905514837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17928092308405987937009891 26892138462608981905514837)
              ·
                refine ⟨78785561902174751676313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26892138462608981905514837 78785561902174751676313)
                ·
                  rfl

theorem cell23_4142727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 10].length) (baseStart_4142727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142727 prefixEnd_4142727 := by exact prefixLift 4142727
  have htrace : WordTrace (prefixWord ++ tailWord_4142727) baseStart_4142727 baseEnd_4142727 := by
    simpa [prefixWord, tailWord_4142727, baseEnd_4142727] using wordTrace_append hprefix tailTrace_4142727
  have hstable : (prefixWord ++ tailWord_4142727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142727).length < 2 ^ (prefixWord ++ tailWord_4142727).sum := by decide
  have hdescent : baseEnd_4142727 < baseStart_4142727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142734 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_4142734 : Nat := 118140960795 + 4142734 * 2 ^ 59
def prefixEnd_4142734 : Nat := 4983230072969 + 3 ^ 40 * 4142734 * 2
def baseEnd_4142734 : Nat := 2127213765723299767872919

theorem tailTrace_4142734 : CollatzResearch.WordTrace tailWord_4142734 prefixEnd_4142734 2127213765723299767872919 := by
  unfold tailWord_4142734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18887240271698714435444407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100731948115726476989036837 18887240271698714435444407)
  ·
    refine ⟨28330860407548071653166611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18887240271698714435444407 28330860407548071653166611)
    ·
      refine ⟨42496290611322107479749917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28330860407548071653166611 42496290611322107479749917)
      ·
        refine ⟨15936108979245790304906219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42496290611322107479749917 15936108979245790304906219)
        ·
          refine ⟨23904163468868685457359329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15936108979245790304906219 23904163468868685457359329)
          ·
            refine ⟨17928122601651514093019497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23904163468868685457359329 17928122601651514093019497)
            ·
              refine ⟨13446091951238635569764623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17928122601651514093019497 13446091951238635569764623)
              ·
                refine ⟨20169137926857953354646935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13446091951238635569764623 20169137926857953354646935)
                ·
                  refine ⟨30253706890286930031970403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20169137926857953354646935 30253706890286930031970403)
                  ·
                    refine ⟨45380560335430395047955605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30253706890286930031970403 45380560335430395047955605)
                    ·
                      refine ⟨2127213765723299767872919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45380560335430395047955605 2127213765723299767872919)
                      ·
                        rfl

theorem cell23_4142734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_4142734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142734 prefixEnd_4142734 := by exact prefixLift 4142734
  have htrace : WordTrace (prefixWord ++ tailWord_4142734) baseStart_4142734 baseEnd_4142734 := by
    simpa [prefixWord, tailWord_4142734, baseEnd_4142734] using wordTrace_append hprefix tailTrace_4142734
  have hstable : (prefixWord ++ tailWord_4142734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142734).length < 2 ^ (prefixWord ++ tailWord_4142734).sum := by decide
  have hdescent : baseEnd_4142734 < baseStart_4142734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142766 : List Nat := [4, 1, 4, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_4142766 : Nat := 118140960795 + 4142766 * 2 ^ 59
def prefixEnd_4142766 : Nat := 4983230072969 + 3 ^ 40 * 4142766 * 2
def baseEnd_4142766 : Nat := 2127230197104243642672773

theorem tailTrace_4142766 : CollatzResearch.WordTrace tailWord_4142766 prefixEnd_4142766 2127230197104243642672773 := by
  unfold tailWord_4142766
  simp only [CollatzResearch.WordTrace]
  refine ⟨18887386163684223118590019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100732726206315856632480101 18887386163684223118590019)
  ·
    refine ⟨28331079245526334677885029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18887386163684223118590019 28331079245526334677885029)
    ·
      refine ⟨5312077358536187752103443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28331079245526334677885029 5312077358536187752103443)
      ·
        refine ⟨7968116037804281628155165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5312077358536187752103443 7968116037804281628155165)
        ·
          refine ⟨2988043514176605610558187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7968116037804281628155165 2988043514176605610558187)
          ·
            refine ⟨4482065271264908415837281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2988043514176605610558187 4482065271264908415837281)
            ·
              refine ⟨3361548953448681311877961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4482065271264908415837281 3361548953448681311877961)
              ·
                refine ⟨2521161715086510983908471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3361548953448681311877961 2521161715086510983908471)
                ·
                  refine ⟨3781742572629766475862707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521161715086510983908471 3781742572629766475862707)
                  ·
                    refine ⟨5672613858944649713794061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3781742572629766475862707 5672613858944649713794061)
                    ·
                      refine ⟨2127230197104243642672773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5672613858944649713794061 2127230197104243642672773)
                      ·
                        rfl

theorem cell23_4142766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_4142766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142766 prefixEnd_4142766 := by exact prefixLift 4142766
  have htrace : WordTrace (prefixWord ++ tailWord_4142766) baseStart_4142766 baseEnd_4142766 := by
    simpa [prefixWord, tailWord_4142766, baseEnd_4142766] using wordTrace_append hprefix tailTrace_4142766
  have hstable : (prefixWord ++ tailWord_4142766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142766).length < 2 ^ (prefixWord ++ tailWord_4142766).sum := by decide
  have hdescent : baseEnd_4142766 < baseStart_4142766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142781 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 5, 3, 2]
def baseStart_4142781 : Nat := 118140960795 + 4142781 * 2 ^ 59
def prefixEnd_4142781 : Nat := 4983230072969 + 3 ^ 40 * 4142781 * 2
def baseEnd_4142781 : Nat := 2127237899314061083985203

theorem tailTrace_4142781 : CollatzResearch.WordTrace tailWord_4142781 prefixEnd_4142781 2127237899314061083985203 := by
  unfold tailWord_4142781
  simp only [CollatzResearch.WordTrace]
  refine ⟨151099636404419442510516197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100733090936279628340344131 151099636404419442510516197)
  ·
    refine ⟨28331181825828645470721787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151099636404419442510516197 28331181825828645470721787)
    ·
      refine ⟨42496772738742968206082681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28331181825828645470721787 42496772738742968206082681)
      ·
        refine ⟨31872579554057226154562011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42496772738742968206082681 31872579554057226154562011)
        ·
          refine ⟨47808869331085839231843017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31872579554057226154562011 47808869331085839231843017)
          ·
            refine ⟨35856651998314379423882263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47808869331085839231843017 35856651998314379423882263)
            ·
              refine ⟨53784977997471569135823395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35856651998314379423882263 53784977997471569135823395)
              ·
                refine ⟨80677466996207353703735093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53784977997471569135823395 80677466996207353703735093)
                ·
                  refine ⟨7563512530894439409725165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80677466996207353703735093 7563512530894439409725165)
                  ·
                    refine ⟨2836317199085414778646937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7563512530894439409725165 2836317199085414778646937)
                    ·
                      refine ⟨2127237899314061083985203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2836317199085414778646937 2127237899314061083985203)
                      ·
                        rfl

theorem cell23_4142781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_4142781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142781 prefixEnd_4142781 := by exact prefixLift 4142781
  have htrace : WordTrace (prefixWord ++ tailWord_4142781) baseStart_4142781 baseEnd_4142781 := by
    simpa [prefixWord, tailWord_4142781, baseEnd_4142781] using wordTrace_append hprefix tailTrace_4142781
  have hstable : (prefixWord ++ tailWord_4142781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142781).length < 2 ^ (prefixWord ++ tailWord_4142781).sum := by decide
  have hdescent : baseEnd_4142781 < baseStart_4142781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142788 : List Nat := [2, 3, 3, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_4142788 : Nat := 118140960795 + 4142788 * 2 ^ 59
def prefixEnd_4142788 : Nat := 4983230072969 + 3 ^ 40 * 4142788 * 2
def baseEnd_4142788 : Nat := 2127241493678642556597671

theorem tailTrace_4142788 : CollatzResearch.WordTrace tailWord_4142788 prefixEnd_4142788 2127241493678642556597671 := by
  unfold tailWord_4142788
  simp only [CollatzResearch.WordTrace]
  refine ⟨75549945857697041353010509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100733261143596055137347345 75549945857697041353010509)
  ·
    refine ⟨28331229696636390507378941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75549945857697041353010509 28331229696636390507378941)
    ·
      refine ⟨10624211136238646440267103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28331229696636390507378941 10624211136238646440267103)
      ·
        refine ⟨15936316704357969660400655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10624211136238646440267103 15936316704357969660400655)
        ·
          refine ⟨23904475056536954490600983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15936316704357969660400655 23904475056536954490600983)
          ·
            refine ⟨35856712584805431735901475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23904475056536954490600983 35856712584805431735901475)
            ·
              refine ⟨53785068877208147603852213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35856712584805431735901475 53785068877208147603852213)
              ·
                refine ⟨5042350207238263837861145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53785068877208147603852213 5042350207238263837861145)
                ·
                  refine ⟨3781762655428697878395859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5042350207238263837861145 3781762655428697878395859)
                  ·
                    refine ⟨5672643983143046817593789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3781762655428697878395859 5672643983143046817593789)
                    ·
                      refine ⟨2127241493678642556597671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5672643983143046817593789 2127241493678642556597671)
                      ·
                        rfl

theorem cell23_4142788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_4142788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142788 prefixEnd_4142788 := by exact prefixLift 4142788
  have htrace : WordTrace (prefixWord ++ tailWord_4142788) baseStart_4142788 baseEnd_4142788 := by
    simpa [prefixWord, tailWord_4142788, baseEnd_4142788] using wordTrace_append hprefix tailTrace_4142788
  have hstable : (prefixWord ++ tailWord_4142788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142788).length < 2 ^ (prefixWord ++ tailWord_4142788).sum := by decide
  have hdescent : baseEnd_4142788 < baseStart_4142788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142798 : List Nat := [4, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2]
def baseStart_4142798 : Nat := 118140960795 + 4142798 * 2 ^ 59
def prefixEnd_4142798 : Nat := 4983230072969 + 3 ^ 40 * 4142798 * 2
def baseEnd_4142798 : Nat := 2127246628485187517472625

theorem tailTrace_4142798 : CollatzResearch.WordTrace tailWord_4142798 prefixEnd_4142798 2127246628485187517472625 := by
  unfold tailWord_4142798
  simp only [CollatzResearch.WordTrace]
  refine ⟨18887532055669731801735631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100733504296905236275923365 18887532055669731801735631)
  ·
    refine ⟨28331298083504597702603447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18887532055669731801735631 28331298083504597702603447)
    ·
      refine ⟨42496947125256896553905171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28331298083504597702603447 42496947125256896553905171)
      ·
        refine ⟨63745420687885344830857757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42496947125256896553905171 63745420687885344830857757)
        ·
          refine ⟨23904532757957004311571659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63745420687885344830857757 23904532757957004311571659)
          ·
            refine ⟨35856799136935506467357489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23904532757957004311571659 35856799136935506467357489)
            ·
              refine ⟨26892599352701629850518117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35856799136935506467357489 26892599352701629850518117)
              ·
                refine ⟨5042362378631555596972147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26892599352701629850518117 5042362378631555596972147)
                ·
                  refine ⟨7563543567947333395458221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5042362378631555596972147 7563543567947333395458221)
                  ·
                    refine ⟨2836328837980250023296833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7563543567947333395458221 2836328837980250023296833)
                    ·
                      refine ⟨2127246628485187517472625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2836328837980250023296833 2127246628485187517472625)
                      ·
                        rfl

theorem cell23_4142798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_4142798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142798 prefixEnd_4142798 := by exact prefixLift 4142798
  have htrace : WordTrace (prefixWord ++ tailWord_4142798) baseStart_4142798 baseEnd_4142798 := by
    simpa [prefixWord, tailWord_4142798, baseEnd_4142798] using wordTrace_append hprefix tailTrace_4142798
  have hstable : (prefixWord ++ tailWord_4142798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142798).length < 2 ^ (prefixWord ++ tailWord_4142798).sum := by decide
  have hdescent : baseEnd_4142798 < baseStart_4142798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142806 : List Nat := [5, 2, 1, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_4142806 : Nat := 118140960795 + 4142806 * 2 ^ 59
def prefixEnd_4142806 : Nat := 4983230072969 + 3 ^ 40 * 4142806 * 2
def baseEnd_4142806 : Nat := 2127250736330423486172589

theorem tailTrace_4142806 : CollatzResearch.WordTrace tailWord_4142806 prefixEnd_4142806 2127250736330423486172589 := by
  unfold tailWord_4142806
  simp only [CollatzResearch.WordTrace]
  refine ⟨9443784264333054486261017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100733698819552581186784181 9443784264333054486261017)
  ·
    refine ⟨7082838198249790864695763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9443784264333054486261017 7082838198249790864695763)
    ·
      refine ⟨10624257297374686297043645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7082838198249790864695763 10624257297374686297043645)
      ·
        refine ⟨3984096486515507361391367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10624257297374686297043645 3984096486515507361391367)
        ·
          refine ⟨5976144729773261042087051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3984096486515507361391367 5976144729773261042087051)
          ·
            refine ⟨8964217094659891563130577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5976144729773261042087051 8964217094659891563130577)
            ·
              refine ⟨6723162820994918672347933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8964217094659891563130577 6723162820994918672347933)
              ·
                refine ⟨2521186057873094502130475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6723162820994918672347933 2521186057873094502130475)
                ·
                  refine ⟨3781779086809641753195713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521186057873094502130475 3781779086809641753195713)
                  ·
                    refine ⟨2836334315107231314896785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3781779086809641753195713 2836334315107231314896785)
                    ·
                      refine ⟨2127250736330423486172589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2836334315107231314896785 2127250736330423486172589)
                      ·
                        rfl

theorem cell23_4142806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_4142806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142806 prefixEnd_4142806 := by exact prefixLift 4142806
  have htrace : WordTrace (prefixWord ++ tailWord_4142806) baseStart_4142806 baseEnd_4142806 := by
    simpa [prefixWord, tailWord_4142806, baseEnd_4142806] using wordTrace_append hprefix tailTrace_4142806
  have hstable : (prefixWord ++ tailWord_4142806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142806).length < 2 ^ (prefixWord ++ tailWord_4142806).sum := by decide
  have hdescent : baseEnd_4142806 < baseStart_4142806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142881 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 2, 5]
def baseStart_4142881 : Nat := 118140960795 + 4142881 * 2 ^ 59
def prefixEnd_4142881 : Nat := 4983230072969 + 3 ^ 40 * 4142881 * 2
def baseEnd_4142881 : Nat := 709096415793170230911581

theorem tailTrace_4142881 : CollatzResearch.WordTrace tailWord_4142881 prefixEnd_4142881 709096415793170230911581 := by
  unfold tailWord_4142881
  simp only [CollatzResearch.WordTrace]
  refine ⟨151103283704057159589156497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100735522469371439726104331 151103283704057159589156497)
  ·
    refine ⟨113327462778042869691867373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151103283704057159589156497 113327462778042869691867373)
    ·
      refine ⟨42497798541766076134450265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113327462778042869691867373 42497798541766076134450265)
      ·
        refine ⟨31873348906324557100837699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42497798541766076134450265 31873348906324557100837699)
        ·
          refine ⟨47810023359486835651256549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31873348906324557100837699 47810023359486835651256549)
          ·
            refine ⟨8964379379903781684610603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47810023359486835651256549 8964379379903781684610603)
            ·
              refine ⟨13446569069855672526915905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8964379379903781684610603 13446569069855672526915905)
              ·
                refine ⟨10084926802391754395186929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13446569069855672526915905 10084926802391754395186929)
                ·
                  refine ⟨7563695101793815796390197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10084926802391754395186929 7563695101793815796390197)
                  ·
                    refine ⟨709096415793170230911581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7563695101793815796390197 709096415793170230911581)
                    ·
                      rfl

theorem cell23_4142881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_4142881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142881 prefixEnd_4142881 := by exact prefixLift 4142881
  have htrace : WordTrace (prefixWord ++ tailWord_4142881) baseStart_4142881 baseEnd_4142881 := by
    simpa [prefixWord, tailWord_4142881, baseEnd_4142881] using wordTrace_append hprefix tailTrace_4142881
  have hstable : (prefixWord ++ tailWord_4142881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142881).length < 2 ^ (prefixWord ++ tailWord_4142881).sum := by decide
  have hdescent : baseEnd_4142881 < baseStart_4142881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142928 : List Nat := [2, 1, 1, 1, 1, 4, 1, 7, 1, 4]
def baseStart_4142928 : Nat := 118140960795 + 4142928 * 2 ^ 59
def prefixEnd_4142928 : Nat := 4983230072969 + 3 ^ 40 * 4142928 * 2
def baseEnd_4142928 : Nat := 709104460323424002949009

theorem tailTrace_4142928 : CollatzResearch.WordTrace tailWord_4142928 prefixEnd_4142928 709104460323424002949009 := by
  unfold tailWord_4142928
  simp only [CollatzResearch.WordTrace]
  refine ⟨75552498967443443308058719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100736665289924591077411625 75552498967443443308058719)
  ·
    refine ⟨113328748451165164962088079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75552498967443443308058719 113328748451165164962088079)
    ·
      refine ⟨169993122676747747443132119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113328748451165164962088079 169993122676747747443132119)
      ·
        refine ⟨254989684015121621164698179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169993122676747747443132119 254989684015121621164698179)
        ·
          refine ⟨382484526022682431747047269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254989684015121621164698179 382484526022682431747047269)
          ·
            refine ⟨71715848629252955952571363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 382484526022682431747047269 71715848629252955952571363)
            ·
              refine ⟨107573772943879433928857045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71715848629252955952571363 107573772943879433928857045)
              ·
                refine ⟨2521260303372174232707587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 107573772943879433928857045 2521260303372174232707587)
                ·
                  refine ⟨3781890455058261349061381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521260303372174232707587 3781890455058261349061381)
                  ·
                    refine ⟨709104460323424002949009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3781890455058261349061381 709104460323424002949009)
                    ·
                      rfl

theorem cell23_4142928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 1, 4].length) (baseStart_4142928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142928 prefixEnd_4142928 := by exact prefixLift 4142928
  have htrace : WordTrace (prefixWord ++ tailWord_4142928) baseStart_4142928 baseEnd_4142928 := by
    simpa [prefixWord, tailWord_4142928, baseEnd_4142928] using wordTrace_append hprefix tailTrace_4142928
  have hstable : (prefixWord ++ tailWord_4142928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142928).length < 2 ^ (prefixWord ++ tailWord_4142928).sum := by decide
  have hdescent : baseEnd_4142928 < baseStart_4142928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142958 : List Nat := [4, 1, 2, 3, 1, 1, 2, 3, 6]
def baseStart_4142958 : Nat := 118140960795 + 4142958 * 2 ^ 59
def prefixEnd_4142958 : Nat := 4983230072969 + 3 ^ 40 * 4142958 * 2
def baseEnd_4142958 : Nat := 236369865043322987941321

theorem tailTrace_4142958 : CollatzResearch.WordTrace tailWord_4142958 prefixEnd_4142958 236369865043322987941321 := by
  unfold tailWord_4142958
  simp only [CollatzResearch.WordTrace]
  refine ⟨18888261515597275217463691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100737394749852134493139685 18888261515597275217463691)
  ·
    refine ⟨28332392273395912826195537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18888261515597275217463691 28332392273395912826195537)
    ·
      refine ⟨21249294205046934619646653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28332392273395912826195537 21249294205046934619646653)
      ·
        refine ⟨7968485326892600482367495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21249294205046934619646653 7968485326892600482367495)
        ·
          refine ⟨11952727990338900723551243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7968485326892600482367495 11952727990338900723551243)
          ·
            refine ⟨17929091985508351085326865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11952727990338900723551243 17929091985508351085326865)
            ·
              refine ⟨13446818989131263313995149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17929091985508351085326865 13446818989131263313995149)
              ·
                refine ⟨5042557120924223742748181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13446818989131263313995149 5042557120924223742748181)
                ·
                  refine ⟨236369865043322987941321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5042557120924223742748181 236369865043322987941321)
                  ·
                    rfl

theorem cell23_4142958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_4142958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142958 prefixEnd_4142958 := by exact prefixLift 4142958
  have htrace : WordTrace (prefixWord ++ tailWord_4142958) baseStart_4142958 baseEnd_4142958 := by
    simpa [prefixWord, tailWord_4142958, baseEnd_4142958] using wordTrace_append hprefix tailTrace_4142958
  have hstable : (prefixWord ++ tailWord_4142958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142958).length < 2 ^ (prefixWord ++ tailWord_4142958).sum := by decide
  have hdescent : baseEnd_4142958 < baseStart_4142958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142971 : List Nat := [1, 1, 1, 1, 1, 5, 1, 6, 1, 5]
def baseStart_4142971 : Nat := 118140960795 + 4142971 * 2 ^ 59
def prefixEnd_4142971 : Nat := 4983230072969 + 3 ^ 40 * 4142971 * 2
def baseEnd_4142971 : Nat := 709111820212805113536443

theorem tailTrace_4142971 : CollatzResearch.WordTrace tailWord_4142971 prefixEnd_4142971 709111820212805113536443 := by
  unfold tailWord_4142971
  simp only [CollatzResearch.WordTrace]
  refine ⟨151106566273731104959932767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100737710849154069973288511 151106566273731104959932767)
  ·
    refine ⟨226659849410596657439899151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151106566273731104959932767 226659849410596657439899151)
    ·
      refine ⟨339989774115894986159848727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226659849410596657439899151 339989774115894986159848727)
      ·
        refine ⟨509984661173842479239773091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339989774115894986159848727 509984661173842479239773091)
        ·
          refine ⟨764976991760763718859659637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509984661173842479239773091 764976991760763718859659637)
          ·
            refine ⟨71716592977571598643093091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 764976991760763718859659637 71716592977571598643093091)
            ·
              refine ⟨107574889466357397964639637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71716592977571598643093091 107574889466357397964639637)
              ·
                refine ⟨5042572943735503029592483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107574889466357397964639637 5042572943735503029592483)
                ·
                  refine ⟨7563859415603254544388725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5042572943735503029592483 7563859415603254544388725)
                  ·
                    refine ⟨709111820212805113536443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7563859415603254544388725 709111820212805113536443)
                    ·
                      rfl

theorem cell23_4142971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 5].length) (baseStart_4142971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4142971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4142971 prefixEnd_4142971 := by exact prefixLift 4142971
  have htrace : WordTrace (prefixWord ++ tailWord_4142971) baseStart_4142971 baseEnd_4142971 := by
    simpa [prefixWord, tailWord_4142971, baseEnd_4142971] using wordTrace_append hprefix tailTrace_4142971
  have hstable : (prefixWord ++ tailWord_4142971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142971).length < 2 ^ (prefixWord ++ tailWord_4142971).sum := by decide
  have hdescent : baseEnd_4142971 < baseStart_4142971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143002 : List Nat := [3, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3]
def baseStart_4143002 : Nat := 118140960795 + 4143002 * 2 ^ 59
def prefixEnd_4143002 : Nat := 4983230072969 + 3 ^ 40 * 4143002 * 2
def baseEnd_4143002 : Nat := 2127351378538704719321687

theorem tailTrace_4143002 : CollatzResearch.WordTrace tailWord_4143002 prefixEnd_4143002 2127351378538704719321687 := by
  unfold tailWord_4143002
  simp only [CollatzResearch.WordTrace]
  refine ⟨37776924234154699313577815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100738464624412531502874173 37776924234154699313577815)
  ·
    refine ⟨56665386351232048970366723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37776924234154699313577815 56665386351232048970366723)
    ·
      refine ⟨84998079526848073455550085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56665386351232048970366723 84998079526848073455550085)
      ·
        refine ⟨15937139911284013772915641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84998079526848073455550085 15937139911284013772915641)
        ·
          refine ⟨11952854933463010329686731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15937139911284013772915641 11952854933463010329686731)
          ·
            refine ⟨17929282400194515494530097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11952854933463010329686731 17929282400194515494530097)
            ·
              refine ⟨13446961800145886620897573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17929282400194515494530097 13446961800145886620897573)
              ·
                refine ⟨2521305337527353741418295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13446961800145886620897573 2521305337527353741418295)
                ·
                  refine ⟨3781958006291030612127443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521305337527353741418295 3781958006291030612127443)
                  ·
                    refine ⟨5672937009436545918191165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3781958006291030612127443 5672937009436545918191165)
                    ·
                      refine ⟨2127351378538704719321687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5672937009436545918191165 2127351378538704719321687)
                      ·
                        rfl

theorem cell23_4143002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_4143002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143002 prefixEnd_4143002 := by exact prefixLift 4143002
  have htrace : WordTrace (prefixWord ++ tailWord_4143002) baseStart_4143002 baseEnd_4143002 := by
    simpa [prefixWord, tailWord_4143002, baseEnd_4143002] using wordTrace_append hprefix tailTrace_4143002
  have hstable : (prefixWord ++ tailWord_4143002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143002).length < 2 ^ (prefixWord ++ tailWord_4143002).sum := by decide
  have hdescent : baseEnd_4143002 < baseStart_4143002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143025 : List Nat := [1, 2, 2, 4, 2, 2, 2, 2, 1, 1, 4]
def baseStart_4143025 : Nat := 118140960795 + 4143025 * 2 ^ 59
def prefixEnd_4143025 : Nat := 4983230072969 + 3 ^ 40 * 4143025 * 2
def baseEnd_4143025 : Nat := 2127363188593758129334081

theorem tailTrace_4143025 : CollatzResearch.WordTrace tailWord_4143025 prefixEnd_4143025 2127363188593758129334081 := by
  unfold tailWord_4143025
  simp only [CollatzResearch.WordTrace]
  refine ⟨151108535815535472182398529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100739023877023648121599019 151108535815535472182398529)
  ·
    refine ⟨113331401861651604136798897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151108535815535472182398529 113331401861651604136798897)
    ·
      refine ⟨84998551396238703102599173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113331401861651604136798897 84998551396238703102599173)
      ·
        refine ⟨15937228386794756831737345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84998551396238703102599173 15937228386794756831737345)
        ·
          refine ⟨11952921290096067623803009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15937228386794756831737345 11952921290096067623803009)
          ·
            refine ⟨8964690967572050717852257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11952921290096067623803009 8964690967572050717852257)
            ·
              refine ⟨6723518225679038038389193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8964690967572050717852257 6723518225679038038389193)
              ·
                refine ⟨5042638669259278528791895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6723518225679038038389193 5042638669259278528791895)
                ·
                  refine ⟨7563958003888917793187843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5042638669259278528791895 7563958003888917793187843)
                  ·
                    refine ⟨11345937005833376689781765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7563958003888917793187843 11345937005833376689781765)
                    ·
                      refine ⟨2127363188593758129334081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11345937005833376689781765 2127363188593758129334081)
                      ·
                        rfl

theorem cell23_4143025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_4143025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143025 prefixEnd_4143025 := by exact prefixLift 4143025
  have htrace : WordTrace (prefixWord ++ tailWord_4143025) baseStart_4143025 baseEnd_4143025 := by
    simpa [prefixWord, tailWord_4143025, baseEnd_4143025] using wordTrace_append hprefix tailTrace_4143025
  have hstable : (prefixWord ++ tailWord_4143025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143025).length < 2 ^ (prefixWord ++ tailWord_4143025).sum := by decide
  have hdescent : baseEnd_4143025 < baseStart_4143025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143036 : List Nat := [2, 2, 2, 5, 1, 2, 1, 3, 1, 1, 3]
def baseStart_4143036 : Nat := 118140960795 + 4143036 * 2 ^ 59
def prefixEnd_4143036 : Nat := 4983230072969 + 3 ^ 40 * 4143036 * 2
def baseEnd_4143036 : Nat := 2127368836880957586296531

theorem tailTrace_4143036 : CollatzResearch.WordTrace tailWord_4143036 prefixEnd_4143036 2127368836880957586296531 := by
  unfold tailWord_4143036
  simp only [CollatzResearch.WordTrace]
  refine ⟨75554468509247810530524481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100739291345663747374032641 75554468509247810530524481)
  ·
    refine ⟨56665851381935857897893361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75554468509247810530524481 56665851381935857897893361)
    ·
      refine ⟨42499388536451893423420021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56665851381935857897893361 42499388536451893423420021)
      ·
        refine ⟨3984317675292365008445627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42499388536451893423420021 3984317675292365008445627)
        ·
          refine ⟨5976476512938547512668441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3984317675292365008445627 5976476512938547512668441)
          ·
            refine ⟨4482357384703910634501331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5976476512938547512668441 4482357384703910634501331)
            ·
              refine ⟨6723536077055865951751997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4482357384703910634501331 6723536077055865951751997)
              ·
                refine ⟨2521326028895949731906999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6723536077055865951751997 2521326028895949731906999)
                ·
                  refine ⟨3781989043343924597860499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521326028895949731906999 3781989043343924597860499)
                  ·
                    refine ⟨5672983565015886896790749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3781989043343924597860499 5672983565015886896790749)
                    ·
                      refine ⟨2127368836880957586296531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5672983565015886896790749 2127368836880957586296531)
                      ·
                        rfl

theorem cell23_4143036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_4143036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143036 prefixEnd_4143036 := by exact prefixLift 4143036
  have htrace : WordTrace (prefixWord ++ tailWord_4143036) baseStart_4143036 baseEnd_4143036 := by
    simpa [prefixWord, tailWord_4143036, baseEnd_4143036] using wordTrace_append hprefix tailTrace_4143036
  have hstable : (prefixWord ++ tailWord_4143036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143036).length < 2 ^ (prefixWord ++ tailWord_4143036).sum := by decide
  have hdescent : baseEnd_4143036 < baseStart_4143036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143069 : List Nat := [1, 4, 3, 1, 3, 2, 2, 1, 2, 4]
def baseStart_4143069 : Nat := 118140960795 + 4143069 * 2 ^ 59
def prefixEnd_4143069 : Nat := 4983230072969 + 3 ^ 40 * 4143069 * 2
def baseEnd_4143069 : Nat := 709128593914185319061293

theorem tailTrace_4143069 : CollatzResearch.WordTrace tailWord_4143069 prefixEnd_4143069 709128593914185319061293 := by
  unfold tailWord_4143069
  simp only [CollatzResearch.WordTrace]
  refine ⟨151110140627376067697000261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100740093751584045131333507 151110140627376067697000261)
  ·
    refine ⟨28333151367633012693187549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151110140627376067697000261 28333151367633012693187549)
    ·
      refine ⟨10624931762862379759945331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28333151367633012693187549 10624931762862379759945331)
      ·
        refine ⟨15937397644293569639917997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10624931762862379759945331 15937397644293569639917997)
        ·
          refine ⟨5976524116610088614969249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15937397644293569639917997 5976524116610088614969249)
          ·
            refine ⟨4482393087457566461226937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5976524116610088614969249 4482393087457566461226937)
            ·
              refine ⟨3361794815593174845920203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4482393087457566461226937 3361794815593174845920203)
              ·
                refine ⟨5042692223389762268880305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3361794815593174845920203 5042692223389762268880305)
                ·
                  refine ⟨3782019167542321701660229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5042692223389762268880305 3782019167542321701660229)
                  ·
                    refine ⟨709128593914185319061293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3782019167542321701660229 709128593914185319061293)
                    ·
                      rfl

theorem cell23_4143069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_4143069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143069 prefixEnd_4143069 := by exact prefixLift 4143069
  have htrace : WordTrace (prefixWord ++ tailWord_4143069) baseStart_4143069 baseEnd_4143069 := by
    simpa [prefixWord, tailWord_4143069, baseEnd_4143069] using wordTrace_append hprefix tailTrace_4143069
  have hstable : (prefixWord ++ tailWord_4143069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143069).length < 2 ^ (prefixWord ++ tailWord_4143069).sum := by decide
  have hdescent : baseEnd_4143069 < baseStart_4143069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143079 : List Nat := [1, 1, 5, 2, 4, 1, 1, 2, 1, 2, 3]
def baseStart_4143079 : Nat := 118140960795 + 4143079 * 2 ^ 59
def prefixEnd_4143079 : Nat := 4983230072969 + 3 ^ 40 * 4143079 * 2
def baseEnd_4143079 : Nat := 2127390916549100918058833

theorem tailTrace_4143079 : CollatzResearch.WordTrace tailWord_4143079 prefixEnd_4143079 2127390916549100918058833 := by
  unfold tailWord_4143079
  simp only [CollatzResearch.WordTrace]
  refine ⟨151110505357339839404864291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100740336904893226269909527 151110505357339839404864291)
  ·
    refine ⟨226665758036009759107296437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151110505357339839404864291 226665758036009759107296437)
    ·
      refine ⟨21249914815875914916309041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226665758036009759107296437 21249914815875914916309041)
      ·
        refine ⟨15937436111906936187231781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21249914815875914916309041 15937436111906936187231781)
        ·
          refine ⟨2988269270982550535105959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15937436111906936187231781 2988269270982550535105959)
          ·
            refine ⟨4482403906473825802658939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2988269270982550535105959 4482403906473825802658939)
            ·
              refine ⟨6723605859710738703988409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4482403906473825802658939 6723605859710738703988409)
              ·
                refine ⟨5042704394783054027991307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6723605859710738703988409 5042704394783054027991307)
                ·
                  refine ⟨7564056592174581041986961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5042704394783054027991307 7564056592174581041986961)
                  ·
                    refine ⟨5673042444130935781490221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7564056592174581041986961 5673042444130935781490221)
                    ·
                      refine ⟨2127390916549100918058833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5673042444130935781490221 2127390916549100918058833)
                      ·
                        rfl

theorem cell23_4143079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_4143079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143079 prefixEnd_4143079 := by exact prefixLift 4143079
  have htrace : WordTrace (prefixWord ++ tailWord_4143079) baseStart_4143079 baseEnd_4143079 := by
    simpa [prefixWord, tailWord_4143079, baseEnd_4143079] using wordTrace_append hprefix tailTrace_4143079
  have hstable : (prefixWord ++ tailWord_4143079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143079).length < 2 ^ (prefixWord ++ tailWord_4143079).sum := by decide
  have hdescent : baseEnd_4143079 < baseStart_4143079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143118 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3]
def baseStart_4143118 : Nat := 118140960795 + 4143118 * 2 ^ 59
def prefixEnd_4143118 : Nat := 4983230072969 + 3 ^ 40 * 4143118 * 2
def baseEnd_4143118 : Nat := 2127410942294626265471153

theorem tailTrace_4143118 : CollatzResearch.WordTrace tailWord_4143118 prefixEnd_4143118 2127410942294626265471153 := by
  unfold tailWord_4143118
  simp only [CollatzResearch.WordTrace]
  refine ⟨18888990975524818633191751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100741285202799032710356005 18888990975524818633191751)
  ·
    refine ⟨28333486463287227949787627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18888990975524818633191751 28333486463287227949787627)
    ·
      refine ⟨42500229694930841924681441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28333486463287227949787627 42500229694930841924681441)
      ·
        refine ⟨31875172271198131443511081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42500229694930841924681441 31875172271198131443511081)
        ·
          refine ⟨23906379203398598582633311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31875172271198131443511081 23906379203398598582633311)
          ·
            refine ⟨35859568805097897873949967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23906379203398598582633311 35859568805097897873949967)
            ·
              refine ⟨53789353207646846810924951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35859568805097897873949967 53789353207646846810924951)
              ·
                refine ⟨80684029811470270216387427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53789353207646846810924951 80684029811470270216387427)
                ·
                  refine ⟨121026044717205405324581141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80684029811470270216387427 121026044717205405324581141)
                  ·
                    refine ⟨5673095846119003374589741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121026044717205405324581141 5673095846119003374589741)
                    ·
                      refine ⟨2127410942294626265471153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5673095846119003374589741 2127410942294626265471153)
                      ·
                        rfl

theorem cell23_4143118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_4143118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143118 prefixEnd_4143118 := by exact prefixLift 4143118
  have htrace : WordTrace (prefixWord ++ tailWord_4143118) baseStart_4143118 baseEnd_4143118 := by
    simpa [prefixWord, tailWord_4143118, baseEnd_4143118] using wordTrace_append hprefix tailTrace_4143118
  have hstable : (prefixWord ++ tailWord_4143118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143118).length < 2 ^ (prefixWord ++ tailWord_4143118).sum := by decide
  have hdescent : baseEnd_4143118 < baseStart_4143118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143128 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 2, 2, 4]
def baseStart_4143128 : Nat := 118140960795 + 4143128 * 2 ^ 59
def prefixEnd_4143128 : Nat := 4983230072969 + 3 ^ 40 * 4143128 * 2
def baseEnd_4143128 : Nat := 2127416077101171226346107

theorem tailTrace_4143128 : CollatzResearch.WordTrace tailWord_4143128 prefixEnd_4143128 2127416077101171226346107 := by
  unfold tailWord_4143128
  simp only [CollatzResearch.WordTrace]
  refine ⟨75556146267081160386699019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100741528356108213848932025 75556146267081160386699019)
  ·
    refine ⟨113334219400621740580048529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75556146267081160386699019 113334219400621740580048529)
    ·
      refine ⟨85000664550466305435036397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113334219400621740580048529 85000664550466305435036397)
      ·
        refine ⟨31875249206424864538138649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85000664550466305435036397 31875249206424864538138649)
        ·
          refine ⟨23906436904818648403603987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31875249206424864538138649 23906436904818648403603987)
          ·
            refine ⟨35859655357227972605405981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23906436904818648403603987 35859655357227972605405981)
            ·
              refine ⟨13447370758960489727027243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35859655357227972605405981 13447370758960489727027243)
              ·
                refine ⟨20171056138440734590540865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13447370758960489727027243 20171056138440734590540865)
                ·
                  refine ⟨15128292103830550942905649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20171056138440734590540865 15128292103830550942905649)
                  ·
                    refine ⟨11346219077872913207179237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15128292103830550942905649 11346219077872913207179237)
                    ·
                      refine ⟨2127416077101171226346107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11346219077872913207179237 2127416077101171226346107)
                      ·
                        rfl

theorem cell23_4143128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_4143128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143128 prefixEnd_4143128 := by exact prefixLift 4143128
  have htrace : WordTrace (prefixWord ++ tailWord_4143128) baseStart_4143128 baseEnd_4143128 := by
    simpa [prefixWord, tailWord_4143128, baseEnd_4143128] using wordTrace_append hprefix tailTrace_4143128
  have hstable : (prefixWord ++ tailWord_4143128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143128).length < 2 ^ (prefixWord ++ tailWord_4143128).sum := by decide
  have hdescent : baseEnd_4143128 < baseStart_4143128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143132 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 1, 4, 2]
def baseStart_4143132 : Nat := 118140960795 + 4143132 * 2 ^ 59
def prefixEnd_4143132 : Nat := 4983230072969 + 3 ^ 40 * 4143132 * 2
def baseEnd_4143132 : Nat := 2127418131023789210696089

theorem tailTrace_4143132 : CollatzResearch.WordTrace tailWord_4143132 prefixEnd_4143132 2127418131023789210696089 := by
  unfold tailWord_4143132
  simp only [CollatzResearch.WordTrace]
  refine ⟨75556219213073914728271825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100741625617431886304362433 75556219213073914728271825)
  ·
    refine ⟨56667164409805436046203869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75556219213073914728271825 56667164409805436046203869)
    ·
      refine ⟨21250186653677038517326451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56667164409805436046203869 21250186653677038517326451)
      ·
        refine ⟨31875279980515557775989677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21250186653677038517326451 31875279980515557775989677)
        ·
          refine ⟨11953229992693334165996129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31875279980515557775989677 11953229992693334165996129)
          ·
            refine ⟨8964922494520000624497097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11953229992693334165996129 8964922494520000624497097)
            ·
              refine ⟨6723691870890000468372823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8964922494520000624497097 6723691870890000468372823)
              ·
                refine ⟨10085537806335000702559235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6723691870890000468372823 10085537806335000702559235)
                ·
                  refine ⟨15128306709502501053838853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10085537806335000702559235 15128306709502501053838853)
                  ·
                    refine ⟨2836557508031718947594785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15128306709502501053838853 2836557508031718947594785)
                    ·
                      refine ⟨2127418131023789210696089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2836557508031718947594785 2127418131023789210696089)
                      ·
                        rfl

theorem cell23_4143132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_4143132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143132 prefixEnd_4143132 := by exact prefixLift 4143132
  have htrace : WordTrace (prefixWord ++ tailWord_4143132) baseStart_4143132 baseEnd_4143132 := by
    simpa [prefixWord, tailWord_4143132, baseEnd_4143132] using wordTrace_append hprefix tailTrace_4143132
  have hstable : (prefixWord ++ tailWord_4143132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143132).length < 2 ^ (prefixWord ++ tailWord_4143132).sum := by decide
  have hdescent : baseEnd_4143132 < baseStart_4143132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143138 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 7]
def baseStart_4143138 : Nat := 118140960795 + 4143138 * 2 ^ 59
def prefixEnd_4143138 : Nat := 4983230072969 + 3 ^ 40 * 4143138 * 2
def baseEnd_4143138 : Nat := 236380134656412909691229

theorem tailTrace_4143138 : CollatzResearch.WordTrace tailWord_4143138 prefixEnd_4143138 236380134656412909691229 := by
  unfold tailWord_4143138
  simp only [CollatzResearch.WordTrace]
  refine ⟨37778164316031523120315517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100741771509417394987508045 37778164316031523120315517)
  ·
    refine ⟨14166811618511821170118319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37778164316031523120315517 14166811618511821170118319)
    ·
      refine ⟨21250217427767731755177479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14166811618511821170118319 21250217427767731755177479)
      ·
        refine ⟨31875326141651597632766219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21250217427767731755177479 31875326141651597632766219)
        ·
          refine ⟨47812989212477396449149329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31875326141651597632766219 47812989212477396449149329)
          ·
            refine ⟨35859741909358047336861997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47812989212477396449149329 35859741909358047336861997)
            ·
              refine ⟨13447403216009267751323249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35859741909358047336861997 13447403216009267751323249)
              ·
                refine ⟨10085552412006950813492437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13447403216009267751323249 10085552412006950813492437)
                ·
                  refine ⟨236380134656412909691229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10085552412006950813492437 236380134656412909691229)
                  ·
                    rfl

theorem cell23_4143138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_4143138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143138 prefixEnd_4143138 := by exact prefixLift 4143138
  have htrace : WordTrace (prefixWord ++ tailWord_4143138) baseStart_4143138 baseEnd_4143138 := by
    simpa [prefixWord, tailWord_4143138, baseEnd_4143138] using wordTrace_append hprefix tailTrace_4143138
  have hstable : (prefixWord ++ tailWord_4143138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143138).length < 2 ^ (prefixWord ++ tailWord_4143138).sum := by decide
  have hdescent : baseEnd_4143138 < baseStart_4143138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143222 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_4143222 : Nat := 118140960795 + 4143222 * 2 ^ 59
def prefixEnd_4143222 : Nat := 4983230072969 + 3 ^ 40 * 4143222 * 2
def baseEnd_4143222 : Nat := 2127464344282693858570675

theorem tailTrace_4143222 : CollatzResearch.WordTrace tailWord_4143222 prefixEnd_4143222 2127464344282693858570675 := by
  unfold tailWord_4143222
  simp only [CollatzResearch.WordTrace]
  refine ⟨9444732562238860926707495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100743813997214516551546613 9444732562238860926707495)
  ·
    refine ⟨14167098843358291390061243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9444732562238860926707495 14167098843358291390061243)
    ·
      refine ⟨21250648265037437085091865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14167098843358291390061243 21250648265037437085091865)
      ·
        refine ⟨15937986198778077813818899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21250648265037437085091865 15937986198778077813818899)
        ·
          refine ⟨23906979298167116720728349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15937986198778077813818899 23906979298167116720728349)
          ·
            refine ⟨8965117236812668770273131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23906979298167116720728349 8965117236812668770273131)
            ·
              refine ⟨13447675855219003155409697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8965117236812668770273131 13447675855219003155409697)
              ·
                refine ⟨10085756891414252366557273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13447675855219003155409697 10085756891414252366557273)
                ·
                  refine ⟨7564317668560689274917955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10085756891414252366557273 7564317668560689274917955)
                  ·
                    refine ⟨11346476502841033912376933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7564317668560689274917955 11346476502841033912376933)
                    ·
                      refine ⟨2127464344282693858570675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11346476502841033912376933 2127464344282693858570675)
                      ·
                        rfl

theorem cell23_4143222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_4143222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143222 prefixEnd_4143222 := by exact prefixLift 4143222
  have htrace : WordTrace (prefixWord ++ tailWord_4143222) baseStart_4143222 baseEnd_4143222 := by
    simpa [prefixWord, tailWord_4143222, baseEnd_4143222] using wordTrace_append hprefix tailTrace_4143222
  have hstable : (prefixWord ++ tailWord_4143222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143222).length < 2 ^ (prefixWord ++ tailWord_4143222).sum := by decide
  have hdescent : baseEnd_4143222 < baseStart_4143222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143225 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 4, 2, 3]
def baseStart_4143225 : Nat := 118140960795 + 4143225 * 2 ^ 59
def prefixEnd_4143225 : Nat := 4983230072969 + 3 ^ 40 * 4143225 * 2
def baseEnd_4143225 : Nat := 2127465884724657346833161

theorem tailTrace_4143225 : CollatzResearch.WordTrace tailWord_4143225 prefixEnd_4143225 2127465884724657346833161 := by
  unfold tailWord_4143225
  simp only [CollatzResearch.WordTrace]
  refine ⟨151115830414810906339679129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100743886943207270893119419 151115830414810906339679129)
  ·
    refine ⟨113336872811108179754759347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151115830414810906339679129 113336872811108179754759347)
    ·
      refine ⟨170005309216662269632139021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113336872811108179754759347 170005309216662269632139021)
      ·
        refine ⟨63751990956248351112052133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170005309216662269632139021 63751990956248351112052133)
        ·
          refine ⟨11953498304296565833509775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63751990956248351112052133 11953498304296565833509775)
          ·
            refine ⟨17930247456444848750264663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11953498304296565833509775 17930247456444848750264663)
            ·
              refine ⟨26895371184667273125396995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17930247456444848750264663 26895371184667273125396995)
              ·
                refine ⟨40343056777000909688095493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26895371184667273125396995 40343056777000909688095493)
                ·
                  refine ⟨7564323145687670566517905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40343056777000909688095493 7564323145687670566517905)
                  ·
                    refine ⟨5673242359265752924888429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7564323145687670566517905 5673242359265752924888429)
                    ·
                      refine ⟨2127465884724657346833161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5673242359265752924888429 2127465884724657346833161)
                      ·
                        rfl

theorem cell23_4143225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_4143225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143225 prefixEnd_4143225 := by exact prefixLift 4143225
  have htrace : WordTrace (prefixWord ++ tailWord_4143225) baseStart_4143225 baseEnd_4143225 := by
    simpa [prefixWord, tailWord_4143225, baseEnd_4143225] using wordTrace_append hprefix tailTrace_4143225
  have hstable : (prefixWord ++ tailWord_4143225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143225).length < 2 ^ (prefixWord ++ tailWord_4143225).sum := by decide
  have hdescent : baseEnd_4143225 < baseStart_4143225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143228 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 8]
def baseStart_4143228 : Nat := 118140960795 + 4143228 * 2 ^ 59
def prefixEnd_4143228 : Nat := 4983230072969 + 3 ^ 40 * 4143228 * 2
def baseEnd_4143228 : Nat := 236385269462957870566183

theorem tailTrace_4143228 : CollatzResearch.WordTrace tailWord_4143228 prefixEnd_4143228 236385269462957870566183 := by
  unfold tailWord_4143228
  simp only [CollatzResearch.WordTrace]
  refine ⟨75557969916900018926019169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100743959889200025234692225 75557969916900018926019169)
  ·
    refine ⟨56668477437675014194514377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75557969916900018926019169 56668477437675014194514377)
    ·
      refine ⟨42501358078256260645885783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56668477437675014194514377 42501358078256260645885783)
      ·
        refine ⟨63752037117384390968828675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42501358078256260645885783 63752037117384390968828675)
        ·
          refine ⟨95628055676076586453243013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63752037117384390968828675 95628055676076586453243013)
          ·
            refine ⟨17930260439264359959983065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95628055676076586453243013 17930260439264359959983065)
            ·
              refine ⟨13447695329448269969987299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17930260439264359959983065 13447695329448269969987299)
              ·
                refine ⟨20171542994172404954980949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13447695329448269969987299 20171542994172404954980949)
                ·
                  refine ⟨236385269462957870566183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20171542994172404954980949 236385269462957870566183)
                  ·
                    rfl

theorem cell23_4143228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 8].length) (baseStart_4143228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143228 prefixEnd_4143228 := by exact prefixLift 4143228
  have htrace : WordTrace (prefixWord ++ tailWord_4143228) baseStart_4143228 baseEnd_4143228 := by
    simpa [prefixWord, tailWord_4143228, baseEnd_4143228] using wordTrace_append hprefix tailTrace_4143228
  have hstable : (prefixWord ++ tailWord_4143228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143228).length < 2 ^ (prefixWord ++ tailWord_4143228).sum := by decide
  have hdescent : baseEnd_4143228 < baseStart_4143228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143282 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2]
def baseStart_4143282 : Nat := 118140960795 + 4143282 * 2 ^ 59
def prefixEnd_4143282 : Nat := 4983230072969 + 3 ^ 40 * 4143282 * 2
def baseEnd_4143282 : Nat := 2127495153121963623820399

theorem tailTrace_4143282 : CollatzResearch.WordTrace tailWord_4143282 prefixEnd_4143282 2127495153121963623820399 := by
  unfold tailWord_4143282
  simp only [CollatzResearch.WordTrace]
  refine ⟨37779477343901101268626025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100745272917069603383002733 37779477343901101268626025)
  ·
    refine ⟨28334608007925825951469519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37779477343901101268626025 28334608007925825951469519)
    ·
      refine ⟨42501912011888738927204279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28334608007925825951469519 42501912011888738927204279)
      ·
        refine ⟨63752868017833108390806419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42501912011888738927204279 63752868017833108390806419)
        ·
          refine ⟨95629302026749662586209629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63752868017833108390806419 95629302026749662586209629)
          ·
            refine ⟨35860988260031123469828611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95629302026749662586209629 35860988260031123469828611)
            ·
              refine ⟨53791482390046685204742917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35860988260031123469828611 53791482390046685204742917)
              ·
                refine ⟨10085902948133753475889297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53791482390046685204742917 10085902948133753475889297)
                ·
                  refine ⟨7564427211100315106916973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10085902948133753475889297 7564427211100315106916973)
                  ·
                    refine ⟨2836660204162618165093865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7564427211100315106916973 2836660204162618165093865)
                    ·
                      refine ⟨2127495153121963623820399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2836660204162618165093865 2127495153121963623820399)
                      ·
                        rfl

theorem cell23_4143282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_4143282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143282 prefixEnd_4143282 := by exact prefixLift 4143282
  have htrace : WordTrace (prefixWord ++ tailWord_4143282) baseStart_4143282 baseEnd_4143282 := by
    simpa [prefixWord, tailWord_4143282, baseEnd_4143282] using wordTrace_append hprefix tailTrace_4143282
  have hstable : (prefixWord ++ tailWord_4143282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143282).length < 2 ^ (prefixWord ++ tailWord_4143282).sum := by decide
  have hdescent : baseEnd_4143282 < baseStart_4143282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143288 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 3, 6]
def baseStart_4143288 : Nat := 118140960795 + 4143288 * 2 ^ 59
def prefixEnd_4143288 : Nat := 4983230072969 + 3 ^ 40 * 4143288 * 2
def baseEnd_4143288 : Nat := 709166078001963533448457

theorem tailTrace_4143288 : CollatzResearch.WordTrace tailWord_4143288 prefixEnd_4143288 709166078001963533448457 := by
  unfold tailWord_4143288
  simp only [CollatzResearch.WordTrace]
  refine ⟨75559064106791334049611259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100745418809055112066148345 75559064106791334049611259)
  ·
    refine ⟨113338596160187001074416889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75559064106791334049611259 113338596160187001074416889)
    ·
      refine ⟨85003947120140250805812667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113338596160187001074416889 85003947120140250805812667)
      ·
        refine ⟨127505920680210376208719001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85003947120140250805812667 127505920680210376208719001)
        ·
          refine ⟨95629440510157782156539251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127505920680210376208719001 95629440510157782156539251)
          ·
            refine ⟨143444160765236673234808877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95629440510157782156539251 143444160765236673234808877)
            ·
              refine ⟨53791560286963752463053329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143444160765236673234808877 53791560286963752463053329)
              ·
                refine ⟨40343670215222814347289997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53791560286963752463053329 40343670215222814347289997)
                ·
                  refine ⟨15128876330708555380233749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40343670215222814347289997 15128876330708555380233749)
                  ·
                    refine ⟨709166078001963533448457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15128876330708555380233749 709166078001963533448457)
                    ·
                      rfl

theorem cell23_4143288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_4143288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143288 prefixEnd_4143288 := by exact prefixLift 4143288
  have htrace : WordTrace (prefixWord ++ tailWord_4143288) baseStart_4143288 baseEnd_4143288 := by
    simpa [prefixWord, tailWord_4143288, baseEnd_4143288] using wordTrace_append hprefix tailTrace_4143288
  have hstable : (prefixWord ++ tailWord_4143288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143288).length < 2 ^ (prefixWord ++ tailWord_4143288).sum := by decide
  have hdescent : baseEnd_4143288 < baseStart_4143288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143289 : List Nat := [1, 2, 1, 4, 1, 2, 3, 4, 1, 1, 3]
def baseStart_4143289 : Nat := 118140960795 + 4143289 * 2 ^ 59
def prefixEnd_4143289 : Nat := 4983230072969 + 3 ^ 40 * 4143289 * 2
def baseEnd_4143289 : Nat := 2127498747486545096432867

theorem tailTrace_4143289 : CollatzResearch.WordTrace tailWord_4143289 prefixEnd_4143289 2127498747486545096432867 := by
  unfold tailWord_4143289
  simp only [CollatzResearch.WordTrace]
  refine ⟨151118164686579045270008921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100745443124386030180005947 151118164686579045270008921)
  ·
    refine ⟨113338623514934283952506691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151118164686579045270008921 113338623514934283952506691)
    ·
      refine ⟨170007935272401425928760037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113338623514934283952506691 170007935272401425928760037)
      ·
        refine ⟨31876487863575267361642507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170007935272401425928760037 31876487863575267361642507)
        ·
          refine ⟨47814731795362901042463761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31876487863575267361642507 47814731795362901042463761)
          ·
            refine ⟨35861048846522175781847821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47814731795362901042463761 35861048846522175781847821)
            ·
              refine ⟨13447893317445815918192933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35861048846522175781847821 13447893317445815918192933)
              ·
                refine ⟨2521479997021090484661175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13447893317445815918192933 2521479997021090484661175)
                ·
                  refine ⟨3782219995531635726991763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521479997021090484661175 3782219995531635726991763)
                  ·
                    refine ⟨5673329993297453590487645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3782219995531635726991763 5673329993297453590487645)
                    ·
                      refine ⟨2127498747486545096432867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5673329993297453590487645 2127498747486545096432867)
                      ·
                        rfl

theorem cell23_4143289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_4143289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143289 prefixEnd_4143289 := by exact prefixLift 4143289
  have htrace : WordTrace (prefixWord ++ tailWord_4143289) baseStart_4143289 baseEnd_4143289 := by
    simpa [prefixWord, tailWord_4143289, baseEnd_4143289] using wordTrace_append hprefix tailTrace_4143289
  have hstable : (prefixWord ++ tailWord_4143289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143289).length < 2 ^ (prefixWord ++ tailWord_4143289).sum := by decide
  have hdescent : baseEnd_4143289 < baseStart_4143289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143295 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 2, 6, 2]
def baseStart_4143295 : Nat := 118140960795 + 4143295 * 2 ^ 59
def prefixEnd_4143295 : Nat := 4983230072969 + 3 ^ 40 * 4143295 * 2
def baseEnd_4143295 : Nat := 2127501828370472072957839

theorem tailTrace_4143295 : CollatzResearch.WordTrace tailWord_4143295 prefixEnd_4143295 2127501828370472072957839 := by
  unfold tailWord_4143295
  simp only [CollatzResearch.WordTrace]
  refine ⟨151118383524557308294727339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100745589016371538863151559 151118383524557308294727339)
  ·
    refine ⟨226677575286835962442091009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151118383524557308294727339 226677575286835962442091009)
    ·
      refine ⟨170008181465126971831568257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226677575286835962442091009 170008181465126971831568257)
      ·
        refine ⟨127506136098845228873676193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170008181465126971831568257 127506136098845228873676193)
        ·
          refine ⟨95629602074133921655257145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127506136098845228873676193 95629602074133921655257145)
          ·
            refine ⟨71722201555600441241442859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95629602074133921655257145 71722201555600441241442859)
            ·
              refine ⟨107583302333400661862164289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71722201555600441241442859 107583302333400661862164289)
              ·
                refine ⟨80687476750050496396623217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107583302333400661862164289 80687476750050496396623217)
                ·
                  refine ⟨60515607562537872297467413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80687476750050496396623217 60515607562537872297467413)
                  ·
                    refine ⟨2836669104493962763943785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60515607562537872297467413 2836669104493962763943785)
                    ·
                      refine ⟨2127501828370472072957839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2836669104493962763943785 2127501828370472072957839)
                      ·
                        rfl

theorem cell23_4143295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 6, 2].length) (baseStart_4143295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143295 prefixEnd_4143295 := by exact prefixLift 4143295
  have htrace : WordTrace (prefixWord ++ tailWord_4143295) baseStart_4143295 baseEnd_4143295 := by
    simpa [prefixWord, tailWord_4143295, baseEnd_4143295] using wordTrace_append hprefix tailTrace_4143295
  have hstable : (prefixWord ++ tailWord_4143295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143295).length < 2 ^ (prefixWord ++ tailWord_4143295).sum := by decide
  have hdescent : baseEnd_4143295 < baseStart_4143295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143335 : List Nat := [1, 1, 5, 3, 1, 2, 10]
def baseStart_4143335 : Nat := 118140960795 + 4143335 * 2 ^ 59
def prefixEnd_4143335 : Nat := 4983230072969 + 3 ^ 40 * 4143335 * 2
def baseEnd_4143335 : Nat := 26265708241933974277255

theorem tailTrace_4143335 : CollatzResearch.WordTrace tailWord_4143335 prefixEnd_4143335 26265708241933974277255 := by
  unfold tailWord_4143335
  simp only [CollatzResearch.WordTrace]
  refine ⟨151119842444412395126183459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100746561629608263417455639 151119842444412395126183459)
  ·
    refine ⟨226679763666618592689275189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151119842444412395126183459 226679763666618592689275189)
    ·
      refine ⟨21251227843745493064619549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226679763666618592689275189 21251227843745493064619549)
      ·
        refine ⟨7969210441404559899232331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21251227843745493064619549 7969210441404559899232331)
        ·
          refine ⟨11953815662106839848848497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7969210441404559899232331 11953815662106839848848497)
          ·
            refine ⟨8965361746580129886636373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11953815662106839848848497 8965361746580129886636373)
            ·
              refine ⟨26265708241933974277255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8965361746580129886636373 26265708241933974277255)
              ·
                rfl

theorem cell23_4143335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 10].length) (baseStart_4143335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143335 prefixEnd_4143335 := by exact prefixLift 4143335
  have htrace : WordTrace (prefixWord ++ tailWord_4143335) baseStart_4143335 baseEnd_4143335 := by
    simpa [prefixWord, tailWord_4143335, baseEnd_4143335] using wordTrace_append hprefix tailTrace_4143335
  have hstable : (prefixWord ++ tailWord_4143335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143335).length < 2 ^ (prefixWord ++ tailWord_4143335).sum := by decide
  have hdescent : baseEnd_4143335 < baseStart_4143335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143345 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 3, 3, 3]
def baseStart_4143345 : Nat := 118140960795 + 4143345 * 2 ^ 59
def prefixEnd_4143345 : Nat := 4983230072969 + 3 ^ 40 * 4143345 * 2
def baseEnd_4143345 : Nat := 2127527502403196877332609

theorem tailTrace_4143345 : CollatzResearch.WordTrace tailWord_4143345 prefixEnd_4143345 2127527502403196877332609 := by
  unfold tailWord_4143345
  simp only [CollatzResearch.WordTrace]
  refine ⟨151120207174376166834047489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100746804782917444556031659 151120207174376166834047489)
  ·
    refine ⟨113340155380782125125535617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151120207174376166834047489 113340155380782125125535617)
    ·
      refine ⟨85005116535586593844151713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113340155380782125125535617 85005116535586593844151713)
      ·
        refine ⟨63753837401689945383113785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85005116535586593844151713 63753837401689945383113785)
        ·
          refine ⟨47815378051267459037335339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63753837401689945383113785 47815378051267459037335339)
          ·
            refine ⟨71723067076901188556003009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47815378051267459037335339 71723067076901188556003009)
            ·
              refine ⟨53792300307675891417002257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71723067076901188556003009 53792300307675891417002257)
              ·
                refine ⟨40344225230756918562751693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53792300307675891417002257 40344225230756918562751693)
                ·
                  refine ⟨15129084461533844461031885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40344225230756918562751693 15129084461533844461031885)
                  ·
                    refine ⟨5673406673075191672886957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15129084461533844461031885 5673406673075191672886957)
                    ·
                      refine ⟨2127527502403196877332609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5673406673075191672886957 2127527502403196877332609)
                      ·
                        rfl

theorem cell23_4143345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_4143345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143345 prefixEnd_4143345 := by exact prefixLift 4143345
  have htrace : WordTrace (prefixWord ++ tailWord_4143345) baseStart_4143345 baseEnd_4143345 := by
    simpa [prefixWord, tailWord_4143345, baseEnd_4143345] using wordTrace_append hprefix tailTrace_4143345
  have hstable : (prefixWord ++ tailWord_4143345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143345).length < 2 ^ (prefixWord ++ tailWord_4143345).sum := by decide
  have hdescent : baseEnd_4143345 < baseStart_4143345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143346 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 3, 2, 2]
def baseStart_4143346 : Nat := 118140960795 + 4143346 * 2 ^ 59
def prefixEnd_4143346 : Nat := 4983230072969 + 3 ^ 40 * 4143346 * 2
def baseEnd_4143346 : Nat := 2127528015883851373420105

theorem tailTrace_4143346 : CollatzResearch.WordTrace tailWord_4143346 prefixEnd_4143346 2127528015883851373420105 := by
  unfold tailWord_4143346
  simp only [CollatzResearch.WordTrace]
  refine ⟨37780060911843136001208473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100746829098248362669889261 37780060911843136001208473)
  ·
    refine ⟨28335045683882352000906355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37780060911843136001208473 28335045683882352000906355)
    ·
      refine ⟨42502568525823528001359533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28335045683882352000906355 42502568525823528001359533)
      ·
        refine ⟨15938463197183823000509825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42502568525823528001359533 15938463197183823000509825)
        ·
          refine ⟨11953847397887867250382369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15938463197183823000509825 11953847397887867250382369)
          ·
            refine ⟨8965385548415900437786777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11953847397887867250382369 8965385548415900437786777)
            ·
              refine ⟨6724039161311925328340083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8965385548415900437786777 6724039161311925328340083)
              ·
                refine ⟨10086058741967887992510125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6724039161311925328340083 10086058741967887992510125)
                ·
                  refine ⟨3782272028237957997191297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10086058741967887992510125 3782272028237957997191297)
                  ·
                    refine ⟨2836704021178468497893473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3782272028237957997191297 2836704021178468497893473)
                    ·
                      refine ⟨2127528015883851373420105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2836704021178468497893473 2127528015883851373420105)
                      ·
                        rfl

theorem cell23_4143346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_4143346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143346 prefixEnd_4143346 := by exact prefixLift 4143346
  have htrace : WordTrace (prefixWord ++ tailWord_4143346) baseStart_4143346 baseEnd_4143346 := by
    simpa [prefixWord, tailWord_4143346, baseEnd_4143346] using wordTrace_append hprefix tailTrace_4143346
  have hstable : (prefixWord ++ tailWord_4143346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143346).length < 2 ^ (prefixWord ++ tailWord_4143346).sum := by decide
  have hdescent : baseEnd_4143346 < baseStart_4143346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143415 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 4]
def baseStart_4143415 : Nat := 118140960795 + 4143415 * 2 ^ 59
def prefixEnd_4143415 : Nat := 4983230072969 + 3 ^ 40 * 4143415 * 2
def baseEnd_4143415 : Nat := 2127563446049011603457287

theorem tailTrace_4143415 : CollatzResearch.WordTrace tailWord_4143415 prefixEnd_4143415 2127563446049011603457287 := by
  unfold tailWord_4143415
  simp only [CollatzResearch.WordTrace]
  refine ⟨151122760284122568789095699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100748506856081712526063799 151122760284122568789095699)
  ·
    refine ⟨226684140426183853183643549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151122760284122568789095699 226684140426183853183643549)
    ·
      refine ⟨85006552659818944943866331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226684140426183853183643549 85006552659818944943866331)
      ·
        refine ⟨127509828989728417415799497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85006552659818944943866331 127509828989728417415799497)
        ·
          refine ⟨95632371742296313061849623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127509828989728417415799497 95632371742296313061849623)
          ·
            refine ⟨143448557613444469592774435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95632371742296313061849623 143448557613444469592774435)
            ·
              refine ⟨215172836420166704389161653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143448557613444469592774435 215172836420166704389161653)
              ·
                refine ⟨20172453414390628536483905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215172836420166704389161653 20172453414390628536483905)
                ·
                  refine ⟨15129340060792971402362929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20172453414390628536483905 15129340060792971402362929)
                  ·
                    refine ⟨11347005045594728551772197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15129340060792971402362929 11347005045594728551772197)
                    ·
                      refine ⟨2127563446049011603457287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11347005045594728551772197 2127563446049011603457287)
                      ·
                        rfl

theorem cell23_4143415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_4143415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143415 prefixEnd_4143415 := by exact prefixLift 4143415
  have htrace : WordTrace (prefixWord ++ tailWord_4143415) baseStart_4143415 baseEnd_4143415 := by
    simpa [prefixWord, tailWord_4143415, baseEnd_4143415] using wordTrace_append hprefix tailTrace_4143415
  have hstable : (prefixWord ++ tailWord_4143415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143415).length < 2 ^ (prefixWord ++ tailWord_4143415).sum := by decide
  have hdescent : baseEnd_4143415 < baseStart_4143415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143422 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_4143422 : Nat := 118140960795 + 4143422 * 2 ^ 59
def prefixEnd_4143422 : Nat := 4983230072969 + 3 ^ 40 * 4143422 * 2
def baseEnd_4143422 : Nat := 2127567040413593076069755

theorem tailTrace_4143422 : CollatzResearch.WordTrace tailWord_4143422 prefixEnd_4143422 2127567040413593076069755 := by
  unfold tailWord_4143422
  simp only [CollatzResearch.WordTrace]
  refine ⟨18890376949387151123075065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100748677063398139323067013 18890376949387151123075065)
  ·
    refine ⟨14167782712040363342306299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18890376949387151123075065 14167782712040363342306299)
    ·
      refine ⟨21251674068060545013459449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14167782712040363342306299 21251674068060545013459449)
      ·
        refine ⟨15938755551045408760094587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21251674068060545013459449 15938755551045408760094587)
        ·
          refine ⟨23908133326568113140141881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15938755551045408760094587 23908133326568113140141881)
          ·
            refine ⟨17931099994926084855106411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23908133326568113140141881 17931099994926084855106411)
            ·
              refine ⟨26896649992389127282659617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17931099994926084855106411 26896649992389127282659617)
              ·
                refine ⟨20172487494291845461994713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26896649992389127282659617 20172487494291845461994713)
                ·
                  refine ⟨15129365620718884096496035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20172487494291845461994713 15129365620718884096496035)
                  ·
                    refine ⟨22694048431078326144744053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15129365620718884096496035 22694048431078326144744053)
                    ·
                      refine ⟨2127567040413593076069755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22694048431078326144744053 2127567040413593076069755)
                      ·
                        rfl

theorem cell23_4143422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_4143422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143422 prefixEnd_4143422 := by exact prefixLift 4143422
  have htrace : WordTrace (prefixWord ++ tailWord_4143422) baseStart_4143422 baseEnd_4143422 := by
    simpa [prefixWord, tailWord_4143422, baseEnd_4143422] using wordTrace_append hprefix tailTrace_4143422
  have hstable : (prefixWord ++ tailWord_4143422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143422).length < 2 ^ (prefixWord ++ tailWord_4143422).sum := by decide
  have hdescent : baseEnd_4143422 < baseStart_4143422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143435 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 3]
def baseStart_4143435 : Nat := 118140960795 + 4143435 * 2 ^ 59
def prefixEnd_4143435 : Nat := 4983230072969 + 3 ^ 40 * 4143435 * 2
def baseEnd_4143435 : Nat := 2127573715662101525207195

theorem tailTrace_4143435 : CollatzResearch.WordTrace tailWord_4143435 prefixEnd_4143435 2127573715662101525207195 := by
  unfold tailWord_4143435
  simp only [CollatzResearch.WordTrace]
  refine ⟨151123489744050112204823759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100748993162700074803215839 151123489744050112204823759)
  ·
    refine ⟨226685234616075168307235639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151123489744050112204823759 226685234616075168307235639)
    ·
      refine ⟨340027851924112752460853459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226685234616075168307235639 340027851924112752460853459)
      ·
        refine ⟨510041777886169128691280189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340027851924112752460853459 510041777886169128691280189)
        ·
          refine ⟨191265666707313423259230071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510041777886169128691280189 191265666707313423259230071)
          ·
            refine ⟨286898500060970134888845107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191265666707313423259230071 286898500060970134888845107)
            ·
              refine ⟨430347750091455202333267661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286898500060970134888845107 430347750091455202333267661)
              ·
                refine ⟨161380406284295700874975373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 430347750091455202333267661 161380406284295700874975373)
                ·
                  refine ⟨60517652356610887828115765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161380406284295700874975373 60517652356610887828115765)
                  ·
                    refine ⟨5673529908432270733885853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60517652356610887828115765 5673529908432270733885853)
                    ·
                      refine ⟨2127573715662101525207195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5673529908432270733885853 2127573715662101525207195)
                      ·
                        rfl

theorem cell23_4143435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 3].length) (baseStart_4143435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143435 prefixEnd_4143435 := by exact prefixLift 4143435
  have htrace : WordTrace (prefixWord ++ tailWord_4143435) baseStart_4143435 baseEnd_4143435 := by
    simpa [prefixWord, tailWord_4143435, baseEnd_4143435] using wordTrace_append hprefix tailTrace_4143435
  have hstable : (prefixWord ++ tailWord_4143435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143435).length < 2 ^ (prefixWord ++ tailWord_4143435).sum := by decide
  have hdescent : baseEnd_4143435 < baseStart_4143435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143465 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 1, 2, 5]
def baseStart_4143465 : Nat := 118140960795 + 4143465 * 2 ^ 59
def prefixEnd_4143465 : Nat := 4983230072969 + 3 ^ 40 * 4143465 * 2
def baseEnd_4143465 : Nat := 2127589120081736407832057

theorem tailTrace_4143465 : CollatzResearch.WordTrace tailWord_4143465 prefixEnd_4143465 2127589120081736407832057 := by
  unfold tailWord_4143465
  simp only [CollatzResearch.WordTrace]
  refine ⟨151124583933941427328415849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100749722622627618218943899 151124583933941427328415849)
  ·
    refine ⟨113343437950456070496311887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151124583933941427328415849 113343437950456070496311887)
    ·
      refine ⟨170015156925684105744467831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113343437950456070496311887 170015156925684105744467831)
      ·
        refine ⟨255022735388526158616701747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170015156925684105744467831 255022735388526158616701747)
        ·
          refine ⟨382534103082789237925052621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255022735388526158616701747 382534103082789237925052621)
          ·
            refine ⟨143450288656045964221894733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382534103082789237925052621 143450288656045964221894733)
            ·
              refine ⟨53793858246017236583210525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143450288656045964221894733 53793858246017236583210525)
              ·
                refine ⟨20172696842256463718703947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53793858246017236583210525 20172696842256463718703947)
                ·
                  refine ⟨30259045263384695578055921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20172696842256463718703947 30259045263384695578055921)
                  ·
                    refine ⟨22694283947538521683541941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30259045263384695578055921 22694283947538521683541941)
                    ·
                      refine ⟨2127589120081736407832057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22694283947538521683541941 2127589120081736407832057)
                      ·
                        rfl

theorem cell23_4143465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_4143465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143465 prefixEnd_4143465 := by exact prefixLift 4143465
  have htrace : WordTrace (prefixWord ++ tailWord_4143465) baseStart_4143465 baseEnd_4143465 := by
    simpa [prefixWord, tailWord_4143465, baseEnd_4143465] using wordTrace_append hprefix tailTrace_4143465
  have hstable : (prefixWord ++ tailWord_4143465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143465).length < 2 ^ (prefixWord ++ tailWord_4143465).sum := by decide
  have hdescent : baseEnd_4143465 < baseStart_4143465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143475 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 4]
def baseStart_4143475 : Nat := 118140960795 + 4143475 * 2 ^ 59
def prefixEnd_4143475 : Nat := 4983230072969 + 3 ^ 40 * 4143475 * 2
def baseEnd_4143475 : Nat := 2127594254888281368707011

theorem tailTrace_4143475 : CollatzResearch.WordTrace tailWord_4143475 prefixEnd_4143475 2127594254888281368707011 := by
  unfold tailWord_4143475
  simp only [CollatzResearch.WordTrace]
  refine ⟨151124948663905199036279879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100749965775936799357519919 151124948663905199036279879)
  ·
    refine ⟨226687422995857798554419819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151124948663905199036279879 226687422995857798554419819)
    ·
      refine ⟨340031134493786697831629729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226687422995857798554419819 340031134493786697831629729)
      ·
        refine ⟨255023350870340023373722297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340031134493786697831629729 255023350870340023373722297)
        ·
          refine ⟨191267513152755017530291723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255023350870340023373722297 191267513152755017530291723)
          ·
            refine ⟨286901269729132526295437585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191267513152755017530291723 286901269729132526295437585)
            ·
              refine ⟨215175952296849394721578189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286901269729132526295437585 215175952296849394721578189)
              ·
                refine ⟨80690982111318523020591821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215175952296849394721578189 80690982111318523020591821)
                ·
                  refine ⟨30259118291744446132721933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80690982111318523020591821 30259118291744446132721933)
                  ·
                    refine ⟨11347169359404167299770725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30259118291744446132721933 11347169359404167299770725)
                    ·
                      refine ⟨2127594254888281368707011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11347169359404167299770725 2127594254888281368707011)
                      ·
                        rfl

theorem cell23_4143475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_4143475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143475 prefixEnd_4143475 := by exact prefixLift 4143475
  have htrace : WordTrace (prefixWord ++ tailWord_4143475) baseStart_4143475 baseEnd_4143475 := by
    simpa [prefixWord, tailWord_4143475, baseEnd_4143475] using wordTrace_append hprefix tailTrace_4143475
  have hstable : (prefixWord ++ tailWord_4143475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143475).length < 2 ^ (prefixWord ++ tailWord_4143475).sum := by decide
  have hdescent : baseEnd_4143475 < baseStart_4143475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143489 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 2, 5]
def baseStart_4143489 : Nat := 118140960795 + 4143489 * 2 ^ 59
def prefixEnd_4143489 : Nat := 4983230072969 + 3 ^ 40 * 4143489 * 2
def baseEnd_4143489 : Nat := 709200481205814771310649

theorem tailTrace_4143489 : CollatzResearch.WordTrace tailWord_4143489 prefixEnd_4143489 709200481205814771310649 := by
  unfold tailWord_4143489
  simp only [CollatzResearch.WordTrace]
  refine ⟨151125459285854479427289521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100750306190569652951526347 151125459285854479427289521)
  ·
    refine ⟨113344094464390859570467141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151125459285854479427289521 113344094464390859570467141)
    ·
      refine ⟨21252017712073286169462589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113344094464390859570467141 21252017712073286169462589)
      ·
        refine ⟨7969506642027482313548471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21252017712073286169462589 7969506642027482313548471)
        ·
          refine ⟨11954259963041223470322707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7969506642027482313548471 11954259963041223470322707)
          ·
            refine ⟨17931389944561835205484061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11954259963041223470322707 17931389944561835205484061)
            ·
              refine ⟨6724271229210688202056523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17931389944561835205484061 6724271229210688202056523)
              ·
                refine ⟨10086406843816032303084785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6724271229210688202056523 10086406843816032303084785)
                ·
                  refine ⟨7564805132862024227313589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10086406843816032303084785 7564805132862024227313589)
                  ·
                    refine ⟨709200481205814771310649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7564805132862024227313589 709200481205814771310649)
                    ·
                      rfl

theorem cell23_4143489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_4143489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143489 prefixEnd_4143489 := by exact prefixLift 4143489
  have htrace : WordTrace (prefixWord ++ tailWord_4143489) baseStart_4143489 baseEnd_4143489 := by
    simpa [prefixWord, tailWord_4143489, baseEnd_4143489] using wordTrace_append hprefix tailTrace_4143489
  have hstable : (prefixWord ++ tailWord_4143489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143489).length < 2 ^ (prefixWord ++ tailWord_4143489).sum := by decide
  have hdescent : baseEnd_4143489 < baseStart_4143489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143492 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_4143492 : Nat := 118140960795 + 4143492 * 2 ^ 59
def prefixEnd_4143492 : Nat := 4983230072969 + 3 ^ 40 * 4143492 * 2
def baseEnd_4143492 : Nat := 2127602984059407802194433

theorem tailTrace_4143492 : CollatzResearch.WordTrace tailWord_4143492 prefixEnd_4143492 2127602984059407802194433 := by
  unfold tailWord_4143492
  simp only [CollatzResearch.WordTrace]
  refine ⟨75562784352421805469824365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100750379136562407293099153 75562784352421805469824365)
  ·
    refine ⟨28336044132158177051184137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75562784352421805469824365 28336044132158177051184137)
    ·
      refine ⟨21252033099118632788388103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28336044132158177051184137 21252033099118632788388103)
      ·
        refine ⟨31878049648677949182582155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21252033099118632788388103 31878049648677949182582155)
        ·
          refine ⟨47817074473016923773873233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31878049648677949182582155 47817074473016923773873233)
          ·
            refine ⟨35862805854762692830404925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47817074473016923773873233 35862805854762692830404925)
            ·
              refine ⟨13448552195536009811401847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35862805854762692830404925 13448552195536009811401847)
              ·
                refine ⟨20172828293304014717102771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13448552195536009811401847 20172828293304014717102771)
                ·
                  refine ⟨30259242439956022075654157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20172828293304014717102771 30259242439956022075654157)
                  ·
                    refine ⟨11347215914983508278370309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30259242439956022075654157 11347215914983508278370309)
                    ·
                      refine ⟨2127602984059407802194433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11347215914983508278370309 2127602984059407802194433)
                      ·
                        rfl

theorem cell23_4143492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_4143492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143492 prefixEnd_4143492 := by exact prefixLift 4143492
  have htrace : WordTrace (prefixWord ++ tailWord_4143492) baseStart_4143492 baseEnd_4143492 := by
    simpa [prefixWord, tailWord_4143492, baseEnd_4143492] using wordTrace_append hprefix tailTrace_4143492
  have hstable : (prefixWord ++ tailWord_4143492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143492).length < 2 ^ (prefixWord ++ tailWord_4143492).sum := by decide
  have hdescent : baseEnd_4143492 < baseStart_4143492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143519 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 3, 4]
def baseStart_4143519 : Nat := 118140960795 + 4143519 * 2 ^ 59
def prefixEnd_4143519 : Nat := 4983230072969 + 3 ^ 40 * 4143519 * 2
def baseEnd_4143519 : Nat := 709205616012359732185603

theorem tailTrace_4143519 : CollatzResearch.WordTrace tailWord_4143519 prefixEnd_4143519 709205616012359732185603 := by
  unfold tailWord_4143519
  simp only [CollatzResearch.WordTrace]
  refine ⟨151126553475745794550881611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100751035650497196367254407 151126553475745794550881611)
  ·
    refine ⟨226689830213618691826322417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151126553475745794550881611 226689830213618691826322417)
    ·
      refine ⟨170017372660214018869741813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226689830213618691826322417 170017372660214018869741813)
      ·
        refine ⟨15939128686895064269038295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170017372660214018869741813 15939128686895064269038295)
        ·
          refine ⟨23908693030342596403557443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15939128686895064269038295 23908693030342596403557443)
          ·
            refine ⟨35863039545513894605336165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23908693030342596403557443 35863039545513894605336165)
            ·
              refine ⟨6724319914783855238500531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35863039545513894605336165 6724319914783855238500531)
              ·
                refine ⟨10086479872175782857750797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6724319914783855238500531 10086479872175782857750797)
                ·
                  refine ⟨3782429952065918571656549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10086479872175782857750797 3782429952065918571656549)
                  ·
                    refine ⟨709205616012359732185603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3782429952065918571656549 709205616012359732185603)
                    ·
                      rfl

theorem cell23_4143519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 4].length) (baseStart_4143519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143519 prefixEnd_4143519 := by exact prefixLift 4143519
  have htrace : WordTrace (prefixWord ++ tailWord_4143519) baseStart_4143519 baseEnd_4143519 := by
    simpa [prefixWord, tailWord_4143519, baseEnd_4143519] using wordTrace_append hprefix tailTrace_4143519
  have hstable : (prefixWord ++ tailWord_4143519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143519).length < 2 ^ (prefixWord ++ tailWord_4143519).sum := by decide
  have hdescent : baseEnd_4143519 < baseStart_4143519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143522 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_4143522 : Nat := 118140960795 + 4143522 * 2 ^ 59
def prefixEnd_4143522 : Nat := 4983230072969 + 3 ^ 40 * 4143522 * 2
def baseEnd_4143522 : Nat := 2127618388479042684819295

theorem tailTrace_4143522 : CollatzResearch.WordTrace tailWord_4143522 prefixEnd_4143522 2127618388479042684819295 := by
  unfold tailWord_4143522
  simp only [CollatzResearch.WordTrace]
  refine ⟨37781665723683731515810205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100751108596489950708827213 37781665723683731515810205)
  ·
    refine ⟨14168124646381399318428827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37781665723683731515810205 14168124646381399318428827)
    ·
      refine ⟨21252186969572098977643241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14168124646381399318428827 21252186969572098977643241)
      ·
        refine ⟨15939140227179074233232431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21252186969572098977643241 15939140227179074233232431)
        ·
          refine ⟨23908710340768611349848647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15939140227179074233232431 23908710340768611349848647)
          ·
            refine ⟨35863065511152917024772971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23908710340768611349848647 35863065511152917024772971)
            ·
              refine ⟨53794598266729375537159457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35863065511152917024772971 53794598266729375537159457)
              ·
                refine ⟨40345948700047031652869593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53794598266729375537159457 40345948700047031652869593)
                ·
                  refine ⟨30259461525035273739652195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40345948700047031652869593 30259461525035273739652195)
                  ·
                    refine ⟨45389192287552910609478293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30259461525035273739652195 45389192287552910609478293)
                    ·
                      refine ⟨2127618388479042684819295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45389192287552910609478293 2127618388479042684819295)
                      ·
                        rfl

theorem cell23_4143522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_4143522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143522 prefixEnd_4143522 := by exact prefixLift 4143522
  have htrace : WordTrace (prefixWord ++ tailWord_4143522) baseStart_4143522 baseEnd_4143522 := by
    simpa [prefixWord, tailWord_4143522, baseEnd_4143522] using wordTrace_append hprefix tailTrace_4143522
  have hstable : (prefixWord ++ tailWord_4143522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143522).length < 2 ^ (prefixWord ++ tailWord_4143522).sum := by decide
  have hdescent : baseEnd_4143522 < baseStart_4143522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143570 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 3, 4]
def baseStart_4143570 : Nat := 118140960795 + 4143570 * 2 ^ 59
def prefixEnd_4143570 : Nat := 4983230072969 + 3 ^ 40 * 4143570 * 2
def baseEnd_4143570 : Nat := 709214345183486165673025

theorem tailTrace_4143570 : CollatzResearch.WordTrace tailWord_4143570 prefixEnd_4143570 709214345183486165673025 := by
  unfold tailWord_4143570
  simp only [CollatzResearch.WordTrace]
  refine ⟨37782103399640257565247041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100752275732374020173992109 37782103399640257565247041)
  ·
    refine ⟨28336577549730193173935281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37782103399640257565247041 28336577549730193173935281)
    ·
      refine ⟨21252433162297644880451461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28336577549730193173935281 21252433162297644880451461)
      ·
        refine ⟨3984831217930808415084649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21252433162297644880451461 3984831217930808415084649)
        ·
          refine ⟨2988623413448106311313487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3984831217930808415084649 2988623413448106311313487)
          ·
            refine ⟨4482935120172159466970231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2988623413448106311313487 4482935120172159466970231)
            ·
              refine ⟨6724402680258239200455347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4482935120172159466970231 6724402680258239200455347)
              ·
                refine ⟨10086604020387358800683021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6724402680258239200455347 10086604020387358800683021)
                ·
                  refine ⟨3782476507645259550256133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10086604020387358800683021 3782476507645259550256133)
                  ·
                    refine ⟨709214345183486165673025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3782476507645259550256133 709214345183486165673025)
                    ·
                      rfl

theorem cell23_4143570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_4143570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143570 prefixEnd_4143570 := by exact prefixLift 4143570
  have htrace : WordTrace (prefixWord ++ tailWord_4143570) baseStart_4143570 baseEnd_4143570 := by
    simpa [prefixWord, tailWord_4143570, baseEnd_4143570] using wordTrace_append hprefix tailTrace_4143570
  have hstable : (prefixWord ++ tailWord_4143570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143570).length < 2 ^ (prefixWord ++ tailWord_4143570).sum := by decide
  have hdescent : baseEnd_4143570 < baseStart_4143570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143626 : List Nat := [3, 1, 2, 2, 2, 1, 4, 2, 2, 4]
def baseStart_4143626 : Nat := 118140960795 + 4143626 * 2 ^ 59
def prefixEnd_4143626 : Nat := 4983230072969 + 3 ^ 40 * 4143626 * 2
def baseEnd_4143626 : Nat := 709223930155703425972939

theorem tailTrace_4143626 : CollatzResearch.WordTrace tailWord_4143626 prefixEnd_4143626 709223930155703425972939 := by
  unfold tailWord_4143626
  simp only [CollatzResearch.WordTrace]
  refine ⟨37782614021589537956256683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100753637390905434550017821 37782614021589537956256683)
  ·
    refine ⟨56673921032384306934385025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37782614021589537956256683 56673921032384306934385025)
    ·
      refine ⟨42505440774288230200788769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56673921032384306934385025 42505440774288230200788769)
      ·
        refine ⟨31879080580716172650591577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42505440774288230200788769 31879080580716172650591577)
        ·
          refine ⟨23909310435537129487943683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31879080580716172650591577 23909310435537129487943683)
          ·
            refine ⟨35863965653305694231915525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23909310435537129487943683 35863965653305694231915525)
            ·
              refine ⟨6724493559994817668484161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35863965653305694231915525 6724493559994817668484161)
              ·
                refine ⟨5043370169996113251363121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6724493559994817668484161 5043370169996113251363121)
                ·
                  refine ⟨3782527627497084938522341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5043370169996113251363121 3782527627497084938522341)
                  ·
                    refine ⟨709223930155703425972939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3782527627497084938522341 709223930155703425972939)
                    ·
                      rfl

theorem cell23_4143626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_4143626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143626 prefixEnd_4143626 := by exact prefixLift 4143626
  have htrace : WordTrace (prefixWord ++ tailWord_4143626) baseStart_4143626 baseEnd_4143626 := by
    simpa [prefixWord, tailWord_4143626, baseEnd_4143626] using wordTrace_append hprefix tailTrace_4143626
  have hstable : (prefixWord ++ tailWord_4143626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143626).length < 2 ^ (prefixWord ++ tailWord_4143626).sum := by decide
  have hdescent : baseEnd_4143626 < baseStart_4143626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143642 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6]
def baseStart_4143642 : Nat := 118140960795 + 4143642 * 2 ^ 59
def prefixEnd_4143642 : Nat := 4983230072969 + 3 ^ 40 * 4143642 * 2
def baseEnd_4143642 : Nat := 2127680006157582215318743

theorem tailTrace_4143642 : CollatzResearch.WordTrace tailWord_4143642 prefixEnd_4143642 2127680006157582215318743 := by
  unfold tailWord_4143642
  simp only [CollatzResearch.WordTrace]
  refine ⟨37782759913575046639402295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100754026436200124371739453 37782759913575046639402295)
  ·
    refine ⟨56674139870362569959103443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37782759913575046639402295 56674139870362569959103443)
    ·
      refine ⟨85011209805543854938655165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56674139870362569959103443 85011209805543854938655165)
      ·
        refine ⟨31879203677078945601995687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85011209805543854938655165 31879203677078945601995687)
        ·
          refine ⟨47818805515618418402993531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31879203677078945601995687 47818805515618418402993531)
          ·
            refine ⟨71728208273427627604490297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47818805515618418402993531 71728208273427627604490297)
            ·
              refine ⟨53796156205070720703367723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71728208273427627604490297 53796156205070720703367723)
              ·
                refine ⟨80694234307606081055051585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53796156205070720703367723 80694234307606081055051585)
                ·
                  refine ⟨60520675730704560791288689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80694234307606081055051585 60520675730704560791288689)
                  ·
                    refine ⟨45390506798028420593466517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60520675730704560791288689 45390506798028420593466517)
                    ·
                      refine ⟨2127680006157582215318743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45390506798028420593466517 2127680006157582215318743)
                      ·
                        rfl

theorem cell23_4143642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_4143642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143642 prefixEnd_4143642 := by exact prefixLift 4143642
  have htrace : WordTrace (prefixWord ++ tailWord_4143642) baseStart_4143642 baseEnd_4143642 := by
    simpa [prefixWord, tailWord_4143642, baseEnd_4143642] using wordTrace_append hprefix tailTrace_4143642
  have hstable : (prefixWord ++ tailWord_4143642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143642).length < 2 ^ (prefixWord ++ tailWord_4143642).sum := by decide
  have hdescent : baseEnd_4143642 < baseStart_4143642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143656 : List Nat := [2, 1, 5, 2, 1, 2, 3, 7]
def baseStart_4143656 : Nat := 118140960795 + 4143656 * 2 ^ 59
def prefixEnd_4143656 : Nat := 4983230072969 + 3 ^ 40 * 4143656 * 2
def baseEnd_4143656 : Nat := 78803229440249820760877

theorem tailTrace_4143656 : CollatzResearch.WordTrace tailWord_4143656 prefixEnd_4143656 78803229440249820760877 := by
  unfold tailWord_4143656
  simp only [CollatzResearch.WordTrace]
  refine ⟨75565775138124733474309411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100754366850832977965745881 75565775138124733474309411)
  ·
    refine ⟨113348662707187100211464117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75565775138124733474309411 113348662707187100211464117)
    ·
      refine ⟨10626437128798790644824761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113348662707187100211464117 10626437128798790644824761)
      ·
        refine ⟨7969827846599092983618571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10626437128798790644824761 7969827846599092983618571)
        ·
          refine ⟨11954741769898639475427857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7969827846599092983618571 11954741769898639475427857)
          ·
            refine ⟨8966056327423979606570893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11954741769898639475427857 8966056327423979606570893)
            ·
              refine ⟨3362271122783992352464085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8966056327423979606570893 3362271122783992352464085)
              ·
                refine ⟨78803229440249820760877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3362271122783992352464085 78803229440249820760877)
                ·
                  rfl

theorem cell23_4143656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 7].length) (baseStart_4143656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143656 prefixEnd_4143656 := by exact prefixLift 4143656
  have htrace : WordTrace (prefixWord ++ tailWord_4143656) baseStart_4143656 baseEnd_4143656 := by
    simpa [prefixWord, tailWord_4143656, baseEnd_4143656] using wordTrace_append hprefix tailTrace_4143656
  have hstable : (prefixWord ++ tailWord_4143656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143656).length < 2 ^ (prefixWord ++ tailWord_4143656).sum := by decide
  have hdescent : baseEnd_4143656 < baseStart_4143656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143670 : List Nat := [5, 1, 2, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_4143670 : Nat := 118140960795 + 4143670 * 2 ^ 59
def prefixEnd_4143670 : Nat := 4983230072969 + 3 ^ 40 * 4143670 * 2
def baseEnd_4143670 : Nat := 2127694383615908105768615

theorem tailTrace_4143670 : CollatzResearch.WordTrace tailWord_4143670 prefixEnd_4143670 2127694383615908105768615 := by
  unfold tailWord_4143670
  simp only [CollatzResearch.WordTrace]
  refine ⟨9445753806137421708726779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100754707265465831559752309 9445753806137421708726779)
  ·
    refine ⟨14168630709206132563090169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9445753806137421708726779 14168630709206132563090169)
    ·
      refine ⟨10626473031904599422317627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14168630709206132563090169 10626473031904599422317627)
      ·
        refine ⟨15939709547856899133476441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10626473031904599422317627 15939709547856899133476441)
        ·
          refine ⟨11954782160892674350107331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15939709547856899133476441 11954782160892674350107331)
          ·
            refine ⟨17932173241339011525160997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11954782160892674350107331 17932173241339011525160997)
            ·
              refine ⟨3362282482751064660967687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17932173241339011525160997 3362282482751064660967687)
              ·
                refine ⟨5043423724126596991451531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3362282482751064660967687 5043423724126596991451531)
                ·
                  refine ⟨7565135586189895487177297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5043423724126596991451531 7565135586189895487177297)
                  ·
                    refine ⟨5673851689642421615382973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7565135586189895487177297 5673851689642421615382973)
                    ·
                      refine ⟨2127694383615908105768615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5673851689642421615382973 2127694383615908105768615)
                      ·
                        rfl

theorem cell23_4143670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_4143670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143670 prefixEnd_4143670 := by exact prefixLift 4143670
  have htrace : WordTrace (prefixWord ++ tailWord_4143670) baseStart_4143670 baseEnd_4143670 := by
    simpa [prefixWord, tailWord_4143670, baseEnd_4143670] using wordTrace_append hprefix tailTrace_4143670
  have hstable : (prefixWord ++ tailWord_4143670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143670).length < 2 ^ (prefixWord ++ tailWord_4143670).sum := by decide
  have hdescent : baseEnd_4143670 < baseStart_4143670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143684 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_4143684 : Nat := 118140960795 + 4143684 * 2 ^ 59
def prefixEnd_4143684 : Nat := 4983230072969 + 3 ^ 40 * 4143684 * 2
def baseEnd_4143684 : Nat := 2127701572345071050993551

theorem tailTrace_4143684 : CollatzResearch.WordTrace tailWord_4143684 prefixEnd_4143684 2127701572345071050993551 := by
  unfold tailWord_4143684
  simp only [CollatzResearch.WordTrace]
  refine ⟨75566285760074013865319053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100755047680098685153758737 75566285760074013865319053)
  ·
    refine ⟨28337357160027755199494645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75566285760074013865319053 28337357160027755199494645)
    ·
      refine ⟨2656627233752602049952623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28337357160027755199494645 2656627233752602049952623)
      ·
        refine ⟨3984940850628903074928935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2656627233752602049952623 3984940850628903074928935)
        ·
          refine ⟨5977411275943354612393403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3984940850628903074928935 5977411275943354612393403)
          ·
            refine ⟨8966116913915031918590105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5977411275943354612393403 8966116913915031918590105)
            ·
              refine ⟨6724587685436273938942579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8966116913915031918590105 6724587685436273938942579)
              ·
                refine ⟨10086881528154410908413869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6724587685436273938942579 10086881528154410908413869)
                ·
                  refine ⟨3782580573057904090655201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10086881528154410908413869 3782580573057904090655201)
                  ·
                    refine ⟨2836935429793428067991401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3782580573057904090655201 2836935429793428067991401)
                    ·
                      refine ⟨2127701572345071050993551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2836935429793428067991401 2127701572345071050993551)
                      ·
                        rfl

theorem cell23_4143684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_4143684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143684 prefixEnd_4143684 := by exact prefixLift 4143684
  have htrace : WordTrace (prefixWord ++ tailWord_4143684) baseStart_4143684 baseEnd_4143684 := by
    simpa [prefixWord, tailWord_4143684, baseEnd_4143684] using wordTrace_append hprefix tailTrace_4143684
  have hstable : (prefixWord ++ tailWord_4143684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143684).length < 2 ^ (prefixWord ++ tailWord_4143684).sum := by decide
  have hdescent : baseEnd_4143684 < baseStart_4143684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143689 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 2, 8, 2]
def baseStart_4143689 : Nat := 118140960795 + 4143689 * 2 ^ 59
def prefixEnd_4143689 : Nat := 4983230072969 + 3 ^ 40 * 4143689 * 2
def baseEnd_4143689 : Nat := 2127704139748343531431027

theorem tailTrace_4143689 : CollatzResearch.WordTrace tailWord_4143689 prefixEnd_4143689 2127704139748343531431027 := by
  unfold tailWord_4143689
  simp only [CollatzResearch.WordTrace]
  refine ⟨151132753885129913584570121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100755169256753275723046747 151132753885129913584570121)
  ·
    refine ⟨113349565413847435188427591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151132753885129913584570121 113349565413847435188427591)
    ·
      refine ⟨170024348120771152782641387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113349565413847435188427591 170024348120771152782641387)
      ·
        refine ⟨255036522181156729173962081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170024348120771152782641387 255036522181156729173962081)
        ·
          refine ⟨191277391635867546880471561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255036522181156729173962081 191277391635867546880471561)
          ·
            refine ⟨143458043726900660160353671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191277391635867546880471561 143458043726900660160353671)
            ·
              refine ⟨215187065590350990240530507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143458043726900660160353671 215187065590350990240530507)
              ·
                refine ⟨322780598385526485360795761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215187065590350990240530507 322780598385526485360795761)
                ·
                  refine ⟨242085448789144864020596821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322780598385526485360795761 242085448789144864020596821)
                  ·
                    refine ⟨2836938852997791375241369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 242085448789144864020596821 2836938852997791375241369)
                    ·
                      refine ⟨2127704139748343531431027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2836938852997791375241369 2127704139748343531431027)
                      ·
                        rfl

theorem cell23_4143689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 8, 2].length) (baseStart_4143689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143689 prefixEnd_4143689 := by exact prefixLift 4143689
  have htrace : WordTrace (prefixWord ++ tailWord_4143689) baseStart_4143689 baseEnd_4143689 := by
    simpa [prefixWord, tailWord_4143689, baseEnd_4143689] using wordTrace_append hprefix tailTrace_4143689
  have hstable : (prefixWord ++ tailWord_4143689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143689).length < 2 ^ (prefixWord ++ tailWord_4143689).sum := by decide
  have hdescent : baseEnd_4143689 < baseStart_4143689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143700 : List Nat := [2, 4, 1, 1, 1, 4, 3, 1, 2, 1, 3]
def baseStart_4143700 : Nat := 118140960795 + 4143700 * 2 ^ 59
def prefixEnd_4143700 : Nat := 4983230072969 + 3 ^ 40 * 4143700 * 2
def baseEnd_4143700 : Nat := 2127709788035542988393477

theorem tailTrace_4143700 : CollatzResearch.WordTrace tailWord_4143700 prefixEnd_4143700 2127709788035542988393477 := by
  unfold tailWord_4143700
  simp only [CollatzResearch.WordTrace]
  refine ⟨75566577544045031231610277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100755436725393374975480369 75566577544045031231610277)
  ·
    refine ⟨14168733289508443355926927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75566577544045031231610277 14168733289508443355926927)
    ·
      refine ⟨21253099934262665033890391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14168733289508443355926927 21253099934262665033890391)
      ·
        refine ⟨31879649901393997550835587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21253099934262665033890391 31879649901393997550835587)
        ·
          refine ⟨47819474852090996326253381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31879649901393997550835587 47819474852090996326253381)
          ·
            refine ⟨8966151534767061811172509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47819474852090996326253381 8966151534767061811172509)
            ·
              refine ⟨3362306825537648179189691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8966151534767061811172509 3362306825537648179189691)
              ·
                refine ⟨5043460238306472268784537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3362306825537648179189691 5043460238306472268784537)
                ·
                  refine ⟨3782595178729854201588403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5043460238306472268784537 3782595178729854201588403)
                  ·
                    refine ⟨5673892768094781302382605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3782595178729854201588403 5673892768094781302382605)
                    ·
                      refine ⟨2127709788035542988393477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5673892768094781302382605 2127709788035542988393477)
                      ·
                        rfl

theorem cell23_4143700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_4143700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143700 prefixEnd_4143700 := by exact prefixLift 4143700
  have htrace : WordTrace (prefixWord ++ tailWord_4143700) baseStart_4143700 baseEnd_4143700 := by
    simpa [prefixWord, tailWord_4143700, baseEnd_4143700] using wordTrace_append hprefix tailTrace_4143700
  have hstable : (prefixWord ++ tailWord_4143700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143700).length < 2 ^ (prefixWord ++ tailWord_4143700).sum := by decide
  have hdescent : baseEnd_4143700 < baseStart_4143700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143726 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_4143726 : Nat := 118140960795 + 4143726 * 2 ^ 59
def prefixEnd_4143726 : Nat := 4983230072969 + 3 ^ 40 * 4143726 * 2
def baseEnd_4143726 : Nat := 2127723138532559886668357

theorem tailTrace_4143726 : CollatzResearch.WordTrace tailWord_4143726 prefixEnd_4143726 2127723138532559886668357 := by
  unfold tailWord_4143726
  simp only [CollatzResearch.WordTrace]
  refine ⟨18891762923249483612958379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100756068923997245935778021 18891762923249483612958379)
  ·
    refine ⟨28337644384874225419437569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18891762923249483612958379 28337644384874225419437569)
    ·
      refine ⟨21253233288655669064578177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28337644384874225419437569 21253233288655669064578177)
      ·
        refine ⟨15939924966491751798433633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21253233288655669064578177 15939924966491751798433633)
        ·
          refine ⟨11954943724868813848825225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15939924966491751798433633 11954943724868813848825225)
          ·
            refine ⟨8966207793651610386618919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11954943724868813848825225 8966207793651610386618919)
            ·
              refine ⟨13449311690477415579928379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8966207793651610386618919 13449311690477415579928379)
              ·
                refine ⟨20173967535716123369892569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13449311690477415579928379 20173967535716123369892569)
                ·
                  refine ⟨15130475651787092527419427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20173967535716123369892569 15130475651787092527419427)
                  ·
                    refine ⟨22695713477680638791129141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15130475651787092527419427 22695713477680638791129141)
                    ·
                      refine ⟨2127723138532559886668357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22695713477680638791129141 2127723138532559886668357)
                      ·
                        rfl

theorem cell23_4143726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_4143726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143726 prefixEnd_4143726 := by exact prefixLift 4143726
  have htrace : WordTrace (prefixWord ++ tailWord_4143726) baseStart_4143726 baseEnd_4143726 := by
    simpa [prefixWord, tailWord_4143726, baseEnd_4143726] using wordTrace_append hprefix tailTrace_4143726
  have hstable : (prefixWord ++ tailWord_4143726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143726).length < 2 ^ (prefixWord ++ tailWord_4143726).sum := by decide
  have hdescent : baseEnd_4143726 < baseStart_4143726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143739 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 3]
def baseStart_4143739 : Nat := 118140960795 + 4143739 * 2 ^ 59
def prefixEnd_4143739 : Nat := 4983230072969 + 3 ^ 40 * 4143739 * 2
def baseEnd_4143739 : Nat := 2127729813781068335805797

theorem tailTrace_4143739 : CollatzResearch.WordTrace tailWord_4143739 prefixEnd_4143739 2127729813781068335805797 := by
  unfold tailWord_4143739
  simp only [CollatzResearch.WordTrace]
  refine ⟨151134577534948772123890271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100756385023299181415926847 151134577534948772123890271)
  ·
    refine ⟨226701866302423158185835407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151134577534948772123890271 226701866302423158185835407)
    ·
      refine ⟨340052799453634737278753111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226701866302423158185835407 340052799453634737278753111)
      ·
        refine ⟨510079199180452105918129667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340052799453634737278753111 510079199180452105918129667)
        ·
          refine ⟨765118798770678158877194501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510079199180452105918129667 765118798770678158877194501)
          ·
            refine ⟨143459774769502154789473969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 765118798770678158877194501 143459774769502154789473969)
            ·
              refine ⟨107594831077126616092105477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143459774769502154789473969 107594831077126616092105477)
              ·
                refine ⟨20174030826961240517269777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107594831077126616092105477 20174030826961240517269777)
                ·
                  refine ⟨15130523120220930387952333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20174030826961240517269777 15130523120220930387952333)
                  ·
                    refine ⟨5673946170082848895482125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15130523120220930387952333 5673946170082848895482125)
                    ·
                      refine ⟨2127729813781068335805797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5673946170082848895482125 2127729813781068335805797)
                      ·
                        rfl

theorem cell23_4143739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 3].length) (baseStart_4143739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143739 prefixEnd_4143739 := by exact prefixLift 4143739
  have htrace : WordTrace (prefixWord ++ tailWord_4143739) baseStart_4143739 baseEnd_4143739 := by
    simpa [prefixWord, tailWord_4143739, baseEnd_4143739] using wordTrace_append hprefix tailTrace_4143739
  have hstable : (prefixWord ++ tailWord_4143739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143739).length < 2 ^ (prefixWord ++ tailWord_4143739).sum := by decide
  have hdescent : baseEnd_4143739 < baseStart_4143739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143870 : List Nat := [4, 2, 2, 1, 2, 2, 3, 1, 6]
def baseStart_4143870 : Nat := 118140960795 + 4143870 * 2 ^ 59
def prefixEnd_4143870 : Nat := 4983230072969 + 3 ^ 40 * 4143870 * 2
def baseEnd_4143870 : Nat := 236421897749645258140855

theorem tailTrace_4143870 : CollatzResearch.WordTrace tailWord_4143870 prefixEnd_4143870 236421897749645258140855 := by
  unfold tailWord_4143870
  simp only [CollatzResearch.WordTrace]
  refine ⟨18892419437184272687113633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100759570331649454331272709 18892419437184272687113633)
  ·
    refine ⟨14169314577888204515335225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18892419437184272687113633 14169314577888204515335225)
    ·
      refine ⟨10626985933416153386501419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14169314577888204515335225 10626985933416153386501419)
      ·
        refine ⟨15940478900124230079752129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10626985933416153386501419 15940478900124230079752129)
        ·
          refine ⟨11955359175093172559814097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15940478900124230079752129 11955359175093172559814097)
          ·
            refine ⟨8966519381319879419860573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11955359175093172559814097 8966519381319879419860573)
            ·
              refine ⟨3362444767994954782447715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8966519381319879419860573 3362444767994954782447715)
              ·
                refine ⟨5043667151992432173671573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3362444767994954782447715 5043667151992432173671573)
                ·
                  refine ⟨236421897749645258140855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5043667151992432173671573 236421897749645258140855)
                  ·
                    rfl

theorem cell23_4143870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_4143870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143870 prefixEnd_4143870 := by exact prefixLift 4143870
  have htrace : WordTrace (prefixWord ++ tailWord_4143870) baseStart_4143870 baseEnd_4143870 := by
    simpa [prefixWord, tailWord_4143870, baseEnd_4143870] using wordTrace_append hprefix tailTrace_4143870
  have hstable : (prefixWord ++ tailWord_4143870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143870).length < 2 ^ (prefixWord ++ tailWord_4143870).sum := by decide
  have hdescent : baseEnd_4143870 < baseStart_4143870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143899 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 6]
def baseStart_4143899 : Nat := 118140960795 + 4143899 * 2 ^ 59
def prefixEnd_4143899 : Nat := 4983230072969 + 3 ^ 40 * 4143899 * 2
def baseEnd_4143899 : Nat := 2127811970685787709805061

theorem tailTrace_4143899 : CollatzResearch.WordTrace tailWord_4143899 prefixEnd_4143899 2127811970685787709805061 := by
  unfold tailWord_4143899
  simp only [CollatzResearch.WordTrace]
  refine ⟨151140413214369119449714751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100760275476246079633143167 151140413214369119449714751)
  ·
    refine ⟨226710619821553679174572127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151140413214369119449714751 226710619821553679174572127)
    ·
      refine ⟨340065929732330518761858191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226710619821553679174572127 340065929732330518761858191)
      ·
        refine ⟨510098894598495778142787287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340065929732330518761858191 510098894598495778142787287)
        ·
          refine ⟨765148341897743667214180931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510098894598495778142787287 765148341897743667214180931)
          ·
            refine ⟨1147722512846615500821271397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765148341897743667214180931 1147722512846615500821271397)
            ·
              refine ⟨215197971158740406403988387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1147722512846615500821271397 215197971158740406403988387)
              ·
                refine ⟨322796956738110609605982581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215197971158740406403988387 322796956738110609605982581)
                ·
                  refine ⟨30262214694197869650560867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 322796956738110609605982581 30262214694197869650560867)
                  ·
                    refine ⟨45393322041296804475841301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30262214694197869650560867 45393322041296804475841301)
                    ·
                      refine ⟨2127811970685787709805061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45393322041296804475841301 2127811970685787709805061)
                      ·
                        rfl

theorem cell23_4143899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 6].length) (baseStart_4143899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143899 prefixEnd_4143899 := by exact prefixLift 4143899
  have htrace : WordTrace (prefixWord ++ tailWord_4143899) baseStart_4143899 baseEnd_4143899 := by
    simpa [prefixWord, tailWord_4143899, baseEnd_4143899] using wordTrace_append hprefix tailTrace_4143899
  have hstable : (prefixWord ++ tailWord_4143899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143899).length < 2 ^ (prefixWord ++ tailWord_4143899).sum := by decide
  have hdescent : baseEnd_4143899 < baseStart_4143899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143903 : List Nat := [1, 1, 2, 4, 2, 2, 2, 3, 1, 1, 4]
def baseStart_4143903 : Nat := 118140960795 + 4143903 * 2 ^ 59
def prefixEnd_4143903 : Nat := 4983230072969 + 3 ^ 40 * 4143903 * 2
def baseEnd_4143903 : Nat := 2127814024608405694155043

theorem tailTrace_4143903 : CollatzResearch.WordTrace tailWord_4143903 prefixEnd_4143903 2127814024608405694155043 := by
  unfold tailWord_4143903
  simp only [CollatzResearch.WordTrace]
  refine ⟨151140559106354628132860363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100760372737569752088573575 151140559106354628132860363)
  ·
    refine ⟨226710838659531942199290545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151140559106354628132860363 226710838659531942199290545)
    ·
      refine ⟨170033128994648956649467909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226710838659531942199290545 170033128994648956649467909)
      ·
        refine ⟨31881211686496679371775233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170033128994648956649467909 31881211686496679371775233)
        ·
          refine ⟨23910908764872509528831425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31881211686496679371775233 23910908764872509528831425)
          ·
            refine ⟨17933181573654382146623569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23910908764872509528831425 17933181573654382146623569)
            ·
              refine ⟨13449886180240786609967677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17933181573654382146623569 13449886180240786609967677)
              ·
                refine ⟨5043707317590294978737879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13449886180240786609967677 5043707317590294978737879)
                ·
                  refine ⟨7565560976385442468106819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5043707317590294978737879 7565560976385442468106819)
                  ·
                    refine ⟨11348341464578163702160229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7565560976385442468106819 11348341464578163702160229)
                    ·
                      refine ⟨2127814024608405694155043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11348341464578163702160229 2127814024608405694155043)
                      ·
                        rfl

theorem cell23_4143903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_4143903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143903 prefixEnd_4143903 := by exact prefixLift 4143903
  have htrace : WordTrace (prefixWord ++ tailWord_4143903) baseStart_4143903 baseEnd_4143903 := by
    simpa [prefixWord, tailWord_4143903, baseEnd_4143903] using wordTrace_append hprefix tailTrace_4143903
  have hstable : (prefixWord ++ tailWord_4143903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143903).length < 2 ^ (prefixWord ++ tailWord_4143903).sum := by decide
  have hdescent : baseEnd_4143903 < baseStart_4143903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143914 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4143914 : Nat := 118140960795 + 4143914 * 2 ^ 59
def prefixEnd_4143914 : Nat := 4983230072969 + 3 ^ 40 * 4143914 * 2
def baseEnd_4143914 : Nat := 2127819672895605151117493

theorem tailTrace_4143914 : CollatzResearch.WordTrace tailWord_4143914 prefixEnd_4143914 2127819672895605151117493 := by
  unfold tailWord_4143914
  simp only [CollatzResearch.WordTrace]
  refine ⟨37785240077328694252877699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100760640206209851341007197 37785240077328694252877699)
  ·
    refine ⟨56677860115993041379316549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37785240077328694252877699 56677860115993041379316549)
    ·
      refine ⟨10627098771748695258621853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56677860115993041379316549 10627098771748695258621853)
      ·
        refine ⟨3985162039405760721983195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10627098771748695258621853 3985162039405760721983195)
        ·
          refine ⟨5977743059108641082974793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985162039405760721983195 5977743059108641082974793)
          ·
            refine ⟨4483307294331480812231095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5977743059108641082974793 4483307294331480812231095)
            ·
              refine ⟨6724960941497221218346643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4483307294331480812231095 6724960941497221218346643)
              ·
                refine ⟨10087441412245831827519965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6724960941497221218346643 10087441412245831827519965)
                ·
                  refine ⟨3782790529592186935319987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10087441412245831827519965 3782790529592186935319987)
                  ·
                    refine ⟨5674185794388280402979981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3782790529592186935319987 5674185794388280402979981)
                    ·
                      refine ⟨2127819672895605151117493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5674185794388280402979981 2127819672895605151117493)
                      ·
                        rfl

theorem cell23_4143914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4143914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143914 prefixEnd_4143914 := by exact prefixLift 4143914
  have htrace : WordTrace (prefixWord ++ tailWord_4143914) baseStart_4143914 baseEnd_4143914 := by
    simpa [prefixWord, tailWord_4143914, baseEnd_4143914] using wordTrace_append hprefix tailTrace_4143914
  have hstable : (prefixWord ++ tailWord_4143914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143914).length < 2 ^ (prefixWord ++ tailWord_4143914).sum := by decide
  have hdescent : baseEnd_4143914 < baseStart_4143914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143919 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 7]
def baseStart_4143919 : Nat := 118140960795 + 4143919 * 2 ^ 59
def prefixEnd_4143919 : Nat := 4983230072969 + 3 ^ 40 * 4143919 * 2
def baseEnd_4143919 : Nat := 2127822240298877631554969

theorem tailTrace_4143919 : CollatzResearch.WordTrace tailWord_4143919 prefixEnd_4143919 2127822240298877631554969 := by
  unfold tailWord_4143919
  simp only [CollatzResearch.WordTrace]
  refine ⟨151141142674296662865442811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100760761782864441910295207 151141142674296662865442811)
  ·
    refine ⟨226711714011444994298164217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151141142674296662865442811 226711714011444994298164217)
    ·
      refine ⟨170033785508583745723623163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226711714011444994298164217 170033785508583745723623163)
      ·
        refine ⟨255050678262875618585434745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170033785508583745723623163 255050678262875618585434745)
        ·
          refine ⟨191288008697156713939076059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255050678262875618585434745 191288008697156713939076059)
          ·
            refine ⟨286932013045735070908614089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191288008697156713939076059 286932013045735070908614089)
            ·
              refine ⟨215199009784301303181460567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286932013045735070908614089 215199009784301303181460567)
              ·
                refine ⟨322798514676451954772190851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215199009784301303181460567 322798514676451954772190851)
                ·
                  refine ⟨484197772014677932158286277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322798514676451954772190851 484197772014677932158286277)
                  ·
                    refine ⟨90787082252752112279678677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 484197772014677932158286277 90787082252752112279678677)
                    ·
                      refine ⟨2127822240298877631554969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90787082252752112279678677 2127822240298877631554969)
                      ·
                        rfl

theorem cell23_4143919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_4143919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143919 prefixEnd_4143919 := by exact prefixLift 4143919
  have htrace : WordTrace (prefixWord ++ tailWord_4143919) baseStart_4143919 baseEnd_4143919 := by
    simpa [prefixWord, tailWord_4143919, baseEnd_4143919] using wordTrace_append hprefix tailTrace_4143919
  have hstable : (prefixWord ++ tailWord_4143919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143919).length < 2 ^ (prefixWord ++ tailWord_4143919).sum := by decide
  have hdescent : baseEnd_4143919 < baseStart_4143919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143930 : List Nat := [3, 1, 1, 1, 6, 1, 1, 3, 2, 4]
def baseStart_4143930 : Nat := 118140960795 + 4143930 * 2 ^ 59
def prefixEnd_4143930 : Nat := 4983230072969 + 3 ^ 40 * 4143930 * 2
def baseEnd_4143930 : Nat := 709275962862025696172473

theorem tailTrace_4143930 : CollatzResearch.WordTrace tailWord_4143930 prefixEnd_4143930 709275962862025696172473 := by
  unfold tailWord_4143930
  simp only [CollatzResearch.WordTrace]
  refine ⟨37785385969314202936023311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100761029251504541162728829 37785385969314202936023311)
  ·
    refine ⟨56678078953971304404034967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37785385969314202936023311 56678078953971304404034967)
    ·
      refine ⟨85017118430956956606052451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56678078953971304404034967 85017118430956956606052451)
      ·
        refine ⟨127525677646435434909078677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85017118430956956606052451 127525677646435434909078677)
        ·
          refine ⟨5977766139676661011363063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 127525677646435434909078677 5977766139676661011363063)
          ·
            refine ⟨8966649209514991517044595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5977766139676661011363063 8966649209514991517044595)
            ·
              refine ⟨13449973814272487275566893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8966649209514991517044595 13449973814272487275566893)
              ·
                refine ⟨5043740180352182728337585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13449973814272487275566893 5043740180352182728337585)
                ·
                  refine ⟨3782805135264137046253189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5043740180352182728337585 3782805135264137046253189)
                  ·
                    refine ⟨709275962862025696172473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3782805135264137046253189 709275962862025696172473)
                    ·
                      rfl

theorem cell23_4143930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_4143930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143930 prefixEnd_4143930 := by exact prefixLift 4143930
  have htrace : WordTrace (prefixWord ++ tailWord_4143930) baseStart_4143930 baseEnd_4143930 := by
    simpa [prefixWord, tailWord_4143930, baseEnd_4143930] using wordTrace_append hprefix tailTrace_4143930
  have hstable : (prefixWord ++ tailWord_4143930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143930).length < 2 ^ (prefixWord ++ tailWord_4143930).sum := by decide
  have hdescent : baseEnd_4143930 < baseStart_4143930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143936 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 3]
def baseStart_4143936 : Nat := 118140960795 + 4143936 * 2 ^ 59
def prefixEnd_4143936 : Nat := 4983230072969 + 3 ^ 40 * 4143936 * 2
def baseEnd_4143936 : Nat := 2127830969470004065042391

theorem tailTrace_4143936 : CollatzResearch.WordTrace tailWord_4143936 prefixEnd_4143936 2127830969470004065042391 := by
  unfold tailWord_4143936
  simp only [CollatzResearch.WordTrace]
  refine ⟨75570881357617537384405831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100761175143490049845874441 75570881357617537384405831)
  ·
    refine ⟨113356322036426306076608747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75570881357617537384405831 113356322036426306076608747)
    ·
      refine ⟨170034483054639459114913121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113356322036426306076608747 170034483054639459114913121)
      ·
        refine ⟨127525862290979594336184841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170034483054639459114913121 127525862290979594336184841)
        ·
          refine ⟨95644396718234695752138631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127525862290979594336184841 95644396718234695752138631)
          ·
            refine ⟨143466595077352043628207947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95644396718234695752138631 143466595077352043628207947)
            ·
              refine ⟨215199892616028065442311921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143466595077352043628207947 215199892616028065442311921)
              ·
                refine ⟨161399919462021049081733941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215199892616028065442311921 161399919462021049081733941)
                ·
                  refine ⟨15131242449564473351412557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161399919462021049081733941 15131242449564473351412557)
                  ·
                    refine ⟨5674215918586677506779709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15131242449564473351412557 5674215918586677506779709)
                    ·
                      refine ⟨2127830969470004065042391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5674215918586677506779709 2127830969470004065042391)
                      ·
                        rfl

theorem cell23_4143936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_4143936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143936 prefixEnd_4143936 := by exact prefixLift 4143936
  have htrace : WordTrace (prefixWord ++ tailWord_4143936) baseStart_4143936 baseEnd_4143936 := by
    simpa [prefixWord, tailWord_4143936, baseEnd_4143936] using wordTrace_append hprefix tailTrace_4143936
  have hstable : (prefixWord ++ tailWord_4143936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143936).length < 2 ^ (prefixWord ++ tailWord_4143936).sum := by decide
  have hdescent : baseEnd_4143936 < baseStart_4143936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143971 : List Nat := [1, 1, 1, 5, 3, 3, 2, 2, 1, 2, 2]
def baseStart_4143971 : Nat := 118140960795 + 4143971 * 2 ^ 59
def prefixEnd_4143971 : Nat := 4983230072969 + 3 ^ 40 * 4143971 * 2
def baseEnd_4143971 : Nat := 2127848941292911428104731

theorem tailTrace_4143971 : CollatzResearch.WordTrace tailWord_4143971 prefixEnd_4143971 2127848941292911428104731 := by
  unfold tailWord_4143971
  simp only [CollatzResearch.WordTrace]
  refine ⟨151143039270108275746335767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100762026180072183830890511 151143039270108275746335767)
  ·
    refine ⟨226714558905162413619503651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151143039270108275746335767 226714558905162413619503651)
    ·
      refine ⟨340071838357743620429255477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226714558905162413619503651 340071838357743620429255477)
      ·
        refine ⟨31881734846038464415242701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 340071838357743620429255477 31881734846038464415242701)
        ·
          refine ⟨11955650567264424155716013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31881734846038464415242701 11955650567264424155716013)
          ·
            refine ⟨4483368962724159058393505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11955650567264424155716013 4483368962724159058393505)
            ·
              refine ⟨3362526722043119293795129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4483368962724159058393505 3362526722043119293795129)
              ·
                refine ⟨2521895041532339470346347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3362526722043119293795129 2521895041532339470346347)
                ·
                  refine ⟨3782842562298509205519521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521895041532339470346347 3782842562298509205519521)
                  ·
                    refine ⟨2837131921723881904139641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3782842562298509205519521 2837131921723881904139641)
                    ·
                      refine ⟨2127848941292911428104731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2837131921723881904139641 2127848941292911428104731)
                      ·
                        rfl

theorem cell23_4143971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_4143971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143971 prefixEnd_4143971 := by exact prefixLift 4143971
  have htrace : WordTrace (prefixWord ++ tailWord_4143971) baseStart_4143971 baseEnd_4143971 := by
    simpa [prefixWord, tailWord_4143971, baseEnd_4143971] using wordTrace_append hprefix tailTrace_4143971
  have hstable : (prefixWord ++ tailWord_4143971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143971).length < 2 ^ (prefixWord ++ tailWord_4143971).sum := by decide
  have hdescent : baseEnd_4143971 < baseStart_4143971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143986 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 1, 8]
def baseStart_4143986 : Nat := 118140960795 + 4143986 * 2 ^ 59
def prefixEnd_4143986 : Nat := 4983230072969 + 3 ^ 40 * 4143986 * 2
def baseEnd_4143986 : Nat := 709285547834242956472387

theorem tailTrace_4143986 : CollatzResearch.WordTrace tailWord_4143986 prefixEnd_4143986 709285547834242956472387 := by
  unfold tailWord_4143986
  simp only [CollatzResearch.WordTrace]
  refine ⟨37785896591263483327032953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100762390910035955538754541 37785896591263483327032953)
  ·
    refine ⟨28339422443447612495274715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37785896591263483327032953 28339422443447612495274715)
    ·
      refine ⟨42509133665171418742912073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28339422443447612495274715 42509133665171418742912073)
      ·
        refine ⟨31881850248878564057184055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42509133665171418742912073 31881850248878564057184055)
        ·
          refine ⟨47822775373317846085776083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31881850248878564057184055 47822775373317846085776083)
          ·
            refine ⟨71734163059976769128664125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47822775373317846085776083 71734163059976769128664125)
            ·
              refine ⟨26900311147491288423249047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71734163059976769128664125 26900311147491288423249047)
              ·
                refine ⟨40350466721236932634873571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26900311147491288423249047 40350466721236932634873571)
                ·
                  refine ⟨60525700081855398952310357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40350466721236932634873571 60525700081855398952310357)
                  ·
                    refine ⟨709285547834242956472387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60525700081855398952310357 709285547834242956472387)
                    ·
                      rfl

theorem cell23_4143986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_4143986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143986 prefixEnd_4143986 := by exact prefixLift 4143986
  have htrace : WordTrace (prefixWord ++ tailWord_4143986) baseStart_4143986 baseEnd_4143986 := by
    simpa [prefixWord, tailWord_4143986, baseEnd_4143986] using wordTrace_append hprefix tailTrace_4143986
  have hstable : (prefixWord ++ tailWord_4143986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143986).length < 2 ^ (prefixWord ++ tailWord_4143986).sum := by decide
  have hdescent : baseEnd_4143986 < baseStart_4143986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143996 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_4143996 : Nat := 118140960795 + 4143996 * 2 ^ 59
def prefixEnd_4143996 : Nat := 4983230072969 + 3 ^ 40 * 4143996 * 2
def baseEnd_4143996 : Nat := 2127861778309273830292115

theorem tailTrace_4143996 : CollatzResearch.WordTrace tailWord_4143996 prefixEnd_4143996 2127861778309273830292115 := by
  unfold tailWord_4143996
  simp only [CollatzResearch.WordTrace]
  refine ⟨75571975547508852507997921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100762634063345136677330561 75571975547508852507997921)
  ·
    refine ⟨56678981660631639380998441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75571975547508852507997921 56678981660631639380998441)
    ·
      refine ⟨42509236245473729535748831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56678981660631639380998441 42509236245473729535748831)
      ·
        refine ⟨63763854368210594303623247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42509236245473729535748831 63763854368210594303623247)
        ·
          refine ⟨95645781552315891455434871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63763854368210594303623247 95645781552315891455434871)
          ·
            refine ⟨143468672328473837183152307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95645781552315891455434871 143468672328473837183152307)
            ·
              refine ⟨215203008492710755774728461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143468672328473837183152307 215203008492710755774728461)
              ·
                refine ⟨80701128184766533415523173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215203008492710755774728461 80701128184766533415523173)
                ·
                  refine ⟨15131461534643725015410595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80701128184766533415523173 15131461534643725015410595)
                  ·
                    refine ⟨22697192301965587523115893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15131461534643725015410595 22697192301965587523115893)
                    ·
                      refine ⟨2127861778309273830292115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22697192301965587523115893 2127861778309273830292115)
                      ·
                        rfl

theorem cell23_4143996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_4143996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4143996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4143996 prefixEnd_4143996 := by exact prefixLift 4143996
  have htrace : WordTrace (prefixWord ++ tailWord_4143996) baseStart_4143996 baseEnd_4143996 := by
    simpa [prefixWord, tailWord_4143996, baseEnd_4143996] using wordTrace_append hprefix tailTrace_4143996
  have hstable : (prefixWord ++ tailWord_4143996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143996).length < 2 ^ (prefixWord ++ tailWord_4143996).sum := by decide
  have hdescent : baseEnd_4143996 < baseStart_4143996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144033 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 7]
def baseStart_4144033 : Nat := 118140960795 + 4144033 * 2 ^ 59
def prefixEnd_4144033 : Nat := 4983230072969 + 3 ^ 40 * 4144033 * 2
def baseEnd_4144033 : Nat := 236431197454832242836605

theorem tailTrace_4144033 : CollatzResearch.WordTrace tailWord_4144033 prefixEnd_4144033 236431197454832242836605 := by
  unfold tailWord_4144033
  simp only [CollatzResearch.WordTrace]
  refine ⟨151145300595883660335092753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100763533730589106890061835 151145300595883660335092753)
  ·
    refine ⟨113358975446912745251319565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151145300595883660335092753 113358975446912745251319565)
    ·
      refine ⟨42509615792592279469244837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113358975446912745251319565 42509615792592279469244837)
      ·
        refine ⟨7970552961111052400483407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42509615792592279469244837 7970552961111052400483407)
        ·
          refine ⟨11955829441666578600725111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7970552961111052400483407 11955829441666578600725111)
          ·
            refine ⟨17933744162499867901087667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11955829441666578600725111 17933744162499867901087667)
            ·
              refine ⟨26900616243749801851631501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17933744162499867901087667 26900616243749801851631501)
              ·
                refine ⟨10087731091406175694361813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26900616243749801851631501 10087731091406175694361813)
                ·
                  refine ⟨236431197454832242836605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10087731091406175694361813 236431197454832242836605)
                  ·
                    rfl

theorem cell23_4144033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 7].length) (baseStart_4144033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144033 prefixEnd_4144033 := by exact prefixLift 4144033
  have htrace : WordTrace (prefixWord ++ tailWord_4144033) baseStart_4144033 baseEnd_4144033 := by
    simpa [prefixWord, tailWord_4144033, baseEnd_4144033] using wordTrace_append hprefix tailTrace_4144033
  have hstable : (prefixWord ++ tailWord_4144033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144033).length < 2 ^ (prefixWord ++ tailWord_4144033).sum := by decide
  have hdescent : baseEnd_4144033 < baseStart_4144033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144140 : List Nat := [2, 2, 1, 2, 3, 3, 2, 2, 6]
def baseStart_4144140 : Nat := 118140960795 + 4144140 * 2 ^ 59
def prefixEnd_4144140 : Nat := 4983230072969 + 3 ^ 40 * 4144140 * 2
def baseEnd_4144140 : Nat := 236437302169280140765717

theorem tailTrace_4144140 : CollatzResearch.WordTrace tailWord_4144140 prefixEnd_4144140 236437302169280140765717 := by
  unfold tailWord_4144140
  simp only [CollatzResearch.WordTrace]
  refine ⟨75574601603248008804618937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100766135470997345072825249 75574601603248008804618937)
  ·
    refine ⟨56680951202436006603464203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75574601603248008804618937 56680951202436006603464203)
    ·
      refine ⟨85021426803654009905196305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56680951202436006603464203 85021426803654009905196305)
      ·
        refine ⟨63766070102740507428897229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85021426803654009905196305 63766070102740507428897229)
        ·
          refine ⟨23912276288527690285836461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63766070102740507428897229 23912276288527690285836461)
          ·
            refine ⟨8967103608197883857188673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23912276288527690285836461 8967103608197883857188673)
            ·
              refine ⟨6725327706148412892891505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8967103608197883857188673 6725327706148412892891505)
              ·
                refine ⟨5043995779611309669668629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6725327706148412892891505 5043995779611309669668629)
                ·
                  refine ⟨236437302169280140765717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5043995779611309669668629 236437302169280140765717)
                  ·
                    rfl

theorem cell23_4144140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 6].length) (baseStart_4144140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144140 prefixEnd_4144140 := by exact prefixLift 4144140
  have htrace : WordTrace (prefixWord ++ tailWord_4144140) baseStart_4144140 baseEnd_4144140 := by
    simpa [prefixWord, tailWord_4144140, baseEnd_4144140] using wordTrace_append hprefix tailTrace_4144140
  have hstable : (prefixWord ++ tailWord_4144140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144140).length < 2 ^ (prefixWord ++ tailWord_4144140).sum := by decide
  have hdescent : baseEnd_4144140 < baseStart_4144140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144153 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 3, 5]
def baseStart_4144153 : Nat := 118140960795 + 4144153 * 2 ^ 59
def prefixEnd_4144153 : Nat := 4983230072969 + 3 ^ 40 * 4144153 * 2
def baseEnd_4144153 : Nat := 709314131590676572009631

theorem tailTrace_4144153 : CollatzResearch.WordTrace tailWord_4144153 prefixEnd_4144153 709314131590676572009631 := by
  unfold tailWord_4144153
  simp only [CollatzResearch.WordTrace]
  refine ⟨151149677355448920829461113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100766451570299280552974075 151149677355448920829461113)
  ·
    refine ⟨113362258016586690622095835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151149677355448920829461113 113362258016586690622095835)
    ·
      refine ⟨170043387024880035933143753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113362258016586690622095835 170043387024880035933143753)
      ·
        refine ⟨127532540268660026949857815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170043387024880035933143753 127532540268660026949857815)
        ·
          refine ⟨191298810402990040424786723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127532540268660026949857815 191298810402990040424786723)
          ·
            refine ⟨286948215604485060637180085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191298810402990040424786723 286948215604485060637180085)
            ·
              refine ⟨26901395212920474434735633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 286948215604485060637180085 26901395212920474434735633)
              ·
                refine ⟨20176046409690355826051725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26901395212920474434735633 20176046409690355826051725)
                ·
                  refine ⟨7566017403633883434769397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20176046409690355826051725 7566017403633883434769397)
                  ·
                    refine ⟨709314131590676572009631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7566017403633883434769397 709314131590676572009631)
                    ·
                      rfl

theorem cell23_4144153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 5].length) (baseStart_4144153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144153 prefixEnd_4144153 := by exact prefixLift 4144153
  have htrace : WordTrace (prefixWord ++ tailWord_4144153) baseStart_4144153 baseEnd_4144153 := by
    simpa [prefixWord, tailWord_4144153, baseEnd_4144153] using wordTrace_append hprefix tailTrace_4144153
  have hstable : (prefixWord ++ tailWord_4144153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144153).length < 2 ^ (prefixWord ++ tailWord_4144153).sum := by decide
  have hdescent : baseEnd_4144153 < baseStart_4144153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144184 : List Nat := [2, 1, 2, 1, 5, 1, 1, 5, 1, 1, 3]
def baseStart_4144184 : Nat := 118140960795 + 4144184 * 2 ^ 59
def prefixEnd_4144184 : Nat := 4983230072969 + 3 ^ 40 * 4144184 * 2
def baseEnd_4144184 : Nat := 2127958312672319094741251

theorem tailTrace_4144184 : CollatzResearch.WordTrace tailWord_4144184 prefixEnd_4144184 2127958312672319094741251 := by
  unfold tailWord_4144184
  simp only [CollatzResearch.WordTrace]
  refine ⟨75575404009168306561919803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100767205345557742082559737 75575404009168306561919803)
  ·
    refine ⟨113363106013752459842879705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75575404009168306561919803 113363106013752459842879705)
    ·
      refine ⟨85022329510314344882159779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113363106013752459842879705 85022329510314344882159779)
      ·
        refine ⟨127533494265471517323239669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85022329510314344882159779 127533494265471517323239669)
        ·
          refine ⟨11956265087387954749053719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127533494265471517323239669 11956265087387954749053719)
          ·
            refine ⟨17934397631081932123580579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11956265087387954749053719 17934397631081932123580579)
            ·
              refine ⟨26901596446622898185370869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17934397631081932123580579 26901596446622898185370869)
              ·
                refine ⟨2522024666870896704878519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26901596446622898185370869 2522024666870896704878519)
                ·
                  refine ⟨3783037000306345057317779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522024666870896704878519 3783037000306345057317779)
                  ·
                    refine ⟨5674555500459517585976669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3783037000306345057317779 5674555500459517585976669)
                    ·
                      refine ⟨2127958312672319094741251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5674555500459517585976669 2127958312672319094741251)
                      ·
                        rfl

theorem cell23_4144184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 1, 1, 3].length) (baseStart_4144184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144184 prefixEnd_4144184 := by exact prefixLift 4144184
  have htrace : WordTrace (prefixWord ++ tailWord_4144184) baseStart_4144184 baseEnd_4144184 := by
    simpa [prefixWord, tailWord_4144184, baseEnd_4144184] using wordTrace_append hprefix tailTrace_4144184
  have hstable : (prefixWord ++ tailWord_4144184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144184).length < 2 ^ (prefixWord ++ tailWord_4144184).sum := by decide
  have hdescent : baseEnd_4144184 < baseStart_4144184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144200 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 4, 4]
def baseStart_4144200 : Nat := 118140960795 + 4144200 * 2 ^ 59
def prefixEnd_4144200 : Nat := 4983230072969 + 3 ^ 40 * 4144200 * 2
def baseEnd_4144200 : Nat := 709322176120930344047059

theorem tailTrace_4144200 : CollatzResearch.WordTrace tailWord_4144200 prefixEnd_4144200 709322176120930344047059 := by
  unfold tailWord_4144200
  simp only [CollatzResearch.WordTrace]
  refine ⟨75575695793139323928211027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100767594390852431904281369 75575695793139323928211027)
  ·
    refine ⟨113363543689708985892316541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75575695793139323928211027 113363543689708985892316541)
    ·
      refine ⟨42511328883640869709618703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113363543689708985892316541 42511328883640869709618703)
      ·
        refine ⟨63766993325461304564428055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42511328883640869709618703 63766993325461304564428055)
        ·
          refine ⟨95650489988191956846642083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63766993325461304564428055 95650489988191956846642083)
          ·
            refine ⟨143475734982287935269963125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95650489988191956846642083 143475734982287935269963125)
            ·
              refine ⟨13450850154589493931559043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143475734982287935269963125 13450850154589493931559043)
              ·
                refine ⟨20176275231884240897338565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13450850154589493931559043 20176275231884240897338565)
                ·
                  refine ⟨3783051605978295168250981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20176275231884240897338565 3783051605978295168250981)
                  ·
                    refine ⟨709322176120930344047059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3783051605978295168250981 709322176120930344047059)
                    ·
                      rfl

theorem cell23_4144200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_4144200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144200 prefixEnd_4144200 := by exact prefixLift 4144200
  have htrace : WordTrace (prefixWord ++ tailWord_4144200) baseStart_4144200 baseEnd_4144200 := by
    simpa [prefixWord, tailWord_4144200, baseEnd_4144200] using wordTrace_append hprefix tailTrace_4144200
  have hstable : (prefixWord ++ tailWord_4144200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144200).length < 2 ^ (prefixWord ++ tailWord_4144200).sum := by decide
  have hdescent : baseEnd_4144200 < baseStart_4144200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144210 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_4144210 : Nat := 118140960795 + 4144210 * 2 ^ 59
def prefixEnd_4144210 : Nat := 4983230072969 + 3 ^ 40 * 4144210 * 2
def baseEnd_4144210 : Nat := 2127971663169335993016131

theorem tailTrace_4144210 : CollatzResearch.WordTrace tailWord_4144210 prefixEnd_4144210 2127971663169335993016131 := by
  unfold tailWord_4144210
  simp only [CollatzResearch.WordTrace]
  refine ⟨37787939079060604891071521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100767837544161613042857389 37787939079060604891071521)
  ·
    refine ⟨28340954309295453668303641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37787939079060604891071521 28340954309295453668303641)
    ·
      refine ⟨21255715731971590251227731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28340954309295453668303641 21255715731971590251227731)
      ·
        refine ⟨31883573597957385376841597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21255715731971590251227731 31883573597957385376841597)
        ·
          refine ⟨11956340099234019516315599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31883573597957385376841597 11956340099234019516315599)
          ·
            refine ⟨17934510148851029274473399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11956340099234019516315599 17934510148851029274473399)
            ·
              refine ⟨26901765223276543911710099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17934510148851029274473399 26901765223276543911710099)
              ·
                refine ⟨40352647834914815867565149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26901765223276543911710099 40352647834914815867565149)
                ·
                  refine ⟨15132242938093055950336931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40352647834914815867565149 15132242938093055950336931)
                  ·
                    refine ⟨22698364407139583925505397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15132242938093055950336931 22698364407139583925505397)
                    ·
                      refine ⟨2127971663169335993016131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22698364407139583925505397 2127971663169335993016131)
                      ·
                        rfl

theorem cell23_4144210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_4144210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144210 prefixEnd_4144210 := by exact prefixLift 4144210
  have htrace : WordTrace (prefixWord ++ tailWord_4144210) baseStart_4144210 baseEnd_4144210 := by
    simpa [prefixWord, tailWord_4144210, baseEnd_4144210] using wordTrace_append hprefix tailTrace_4144210
  have hstable : (prefixWord ++ tailWord_4144210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144210).length < 2 ^ (prefixWord ++ tailWord_4144210).sum := by decide
  have hdescent : baseEnd_4144210 < baseStart_4144210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144213 : List Nat := [1, 3, 2, 2, 1, 2, 2, 10]
def baseStart_4144213 : Nat := 118140960795 + 4144213 * 2 ^ 59
def prefixEnd_4144213 : Nat := 4983230072969 + 3 ^ 40 * 4144213 * 2
def baseEnd_4144213 : Nat := 78813822355974054862171

theorem tailTrace_4144213 : CollatzResearch.WordTrace tailWord_4144213 prefixEnd_4144213 78813822355974054862171 := by
  unfold tailWord_4144213
  simp only [CollatzResearch.WordTrace]
  refine ⟨151151865735231551076645293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100767910490154367384430195 151151865735231551076645293)
  ·
    refine ⟨56681949650711831653741985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151151865735231551076645293 56681949650711831653741985)
    ·
      refine ⟨42511462238033873740306489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56681949650711831653741985 42511462238033873740306489)
      ·
        refine ⟨31883596678525405305229867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42511462238033873740306489 31883596678525405305229867)
        ·
          refine ⟨47825395017788107957844801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31883596678525405305229867 47825395017788107957844801)
          ·
            refine ⟨35869046263341080968383601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47825395017788107957844801 35869046263341080968383601)
            ·
              refine ⟨26901784697505810726287701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35869046263341080968383601 26901784697505810726287701)
              ·
                refine ⟨78813822355974054862171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26901784697505810726287701 78813822355974054862171)
                ·
                  rfl

theorem cell23_4144213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 10].length) (baseStart_4144213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144213 prefixEnd_4144213 := by exact prefixLift 4144213
  have htrace : WordTrace (prefixWord ++ tailWord_4144213) baseStart_4144213 baseEnd_4144213 := by
    simpa [prefixWord, tailWord_4144213, baseEnd_4144213] using wordTrace_append hprefix tailTrace_4144213
  have hstable : (prefixWord ++ tailWord_4144213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144213).length < 2 ^ (prefixWord ++ tailWord_4144213).sum := by decide
  have hdescent : baseEnd_4144213 < baseStart_4144213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144220 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_4144220 : Nat := 118140960795 + 4144220 * 2 ^ 59
def prefixEnd_4144220 : Nat := 4983230072969 + 3 ^ 40 * 4144220 * 2
def baseEnd_4144220 : Nat := 2127976797975880953891085

theorem tailTrace_4144220 : CollatzResearch.WordTrace tailWord_4144220 prefixEnd_4144220 2127976797975880953891085 := by
  unfold tailWord_4144220
  simp only [CollatzResearch.WordTrace]
  refine ⟨75576060523103095636075057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100768080697470794181433409 75576060523103095636075057)
  ·
    refine ⟨56682045392327321727056293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75576060523103095636075057 56682045392327321727056293)
    ·
      refine ⟨10627883511061372823823055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56682045392327321727056293 10627883511061372823823055)
      ·
        refine ⟨15941825266592059235734583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10627883511061372823823055 15941825266592059235734583)
        ·
          refine ⟨23912737899888088853601875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15941825266592059235734583 23912737899888088853601875)
          ·
            refine ⟨35869106849832133280402813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23912737899888088853601875 35869106849832133280402813)
            ·
              refine ⟨13450915068687049980151055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35869106849832133280402813 13450915068687049980151055)
              ·
                refine ⟨20176372603030574970226583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13450915068687049980151055 20176372603030574970226583)
                ·
                  refine ⟨30264558904545862455339875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20176372603030574970226583 30264558904545862455339875)
                  ·
                    refine ⟨45396838356818793683009813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30264558904545862455339875 45396838356818793683009813)
                    ·
                      refine ⟨2127976797975880953891085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45396838356818793683009813 2127976797975880953891085)
                      ·
                        rfl

theorem cell23_4144220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_4144220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144220 prefixEnd_4144220 := by exact prefixLift 4144220
  have htrace : WordTrace (prefixWord ++ tailWord_4144220) baseStart_4144220 baseEnd_4144220 := by
    simpa [prefixWord, tailWord_4144220, baseEnd_4144220] using wordTrace_append hprefix tailTrace_4144220
  have hstable : (prefixWord ++ tailWord_4144220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144220).length < 2 ^ (prefixWord ++ tailWord_4144220).sum := by decide
  have hdescent : baseEnd_4144220 < baseStart_4144220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144240 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 3]
def baseStart_4144240 : Nat := 118140960795 + 4144240 * 2 ^ 59
def prefixEnd_4144240 : Nat := 4983230072969 + 3 ^ 40 * 4144240 * 2
def baseEnd_4144240 : Nat := 2127987067588970875640993

theorem tailTrace_4144240 : CollatzResearch.WordTrace tailWord_4144240 prefixEnd_4144240 2127987067588970875640993 := by
  unfold tailWord_4144240
  simp only [CollatzResearch.WordTrace]
  refine ⟨75576425253066867343939087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100768567004089156458585449 75576425253066867343939087)
  ·
    refine ⟨113364637879600301015908631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75576425253066867343939087 113364637879600301015908631)
    ·
      refine ⟨170046956819400451523862947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113364637879600301015908631 170046956819400451523862947)
      ·
        refine ⟨255070435229100677285794421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170046956819400451523862947 255070435229100677285794421)
        ·
          refine ⟨23912853302728188495543227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 255070435229100677285794421 23912853302728188495543227)
          ·
            refine ⟨35869279954092282743314841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23912853302728188495543227 35869279954092282743314841)
            ·
              refine ⟨26901959965569212057486131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35869279954092282743314841 26901959965569212057486131)
              ·
                refine ⟨40352939948353818086229197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26901959965569212057486131 40352939948353818086229197)
                ·
                  refine ⟨15132352480632681782335949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40352939948353818086229197 15132352480632681782335949)
                  ·
                    refine ⟨5674632180237255668375981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15132352480632681782335949 5674632180237255668375981)
                    ·
                      refine ⟨2127987067588970875640993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5674632180237255668375981 2127987067588970875640993)
                      ·
                        rfl

theorem cell23_4144240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 3].length) (baseStart_4144240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144240 prefixEnd_4144240 := by exact prefixLift 4144240
  have htrace : WordTrace (prefixWord ++ tailWord_4144240) baseStart_4144240 baseEnd_4144240 := by
    simpa [prefixWord, tailWord_4144240, baseEnd_4144240] using wordTrace_append hprefix tailTrace_4144240
  have hstable : (prefixWord ++ tailWord_4144240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144240).length < 2 ^ (prefixWord ++ tailWord_4144240).sum := by decide
  have hdescent : baseEnd_4144240 < baseStart_4144240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144284 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 3, 3, 2]
def baseStart_4144284 : Nat := 118140960795 + 4144284 * 2 ^ 59
def prefixEnd_4144284 : Nat := 4983230072969 + 3 ^ 40 * 4144284 * 2
def baseEnd_4144284 : Nat := 2128009660737768703490791

theorem tailTrace_4144284 : CollatzResearch.WordTrace tailWord_4144284 prefixEnd_4144284 2128009660737768703490791 := by
  unfold tailWord_4144284
  simp only [CollatzResearch.WordTrace]
  refine ⟨75577227658987165101239953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100769636878649553468319937 75577227658987165101239953)
  ·
    refine ⟨56682920744240373825929965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75577227658987165101239953 56682920744240373825929965)
    ·
      refine ⟨21256095279090140184723737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56682920744240373825929965 21256095279090140184723737)
      ·
        refine ⟨15942071459317605138542803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21256095279090140184723737 15942071459317605138542803)
        ·
          refine ⟨23913107188976407707814205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15942071459317605138542803 23913107188976407707814205)
          ·
            refine ⟨8967415195866152890430327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23913107188976407707814205 8967415195866152890430327)
            ·
              refine ⟨13451122793799229335645491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8967415195866152890430327 13451122793799229335645491)
              ·
                refine ⟨20176684190698844003468237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13451122793799229335645491 20176684190698844003468237)
                ·
                  refine ⟨7566256571512066501300589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20176684190698844003468237 7566256571512066501300589)
                  ·
                    refine ⟨2837346214317024937987721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7566256571512066501300589 2837346214317024937987721)
                    ·
                      refine ⟨2128009660737768703490791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2837346214317024937987721 2128009660737768703490791)
                      ·
                        rfl

theorem cell23_4144284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_4144284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144284 prefixEnd_4144284 := by exact prefixLift 4144284
  have htrace : WordTrace (prefixWord ++ tailWord_4144284) baseStart_4144284 baseEnd_4144284 := by
    simpa [prefixWord, tailWord_4144284, baseEnd_4144284] using wordTrace_append hprefix tailTrace_4144284
  have hstable : (prefixWord ++ tailWord_4144284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144284).length < 2 ^ (prefixWord ++ tailWord_4144284).sum := by decide
  have hdescent : baseEnd_4144284 < baseStart_4144284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144407 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 3]
def baseStart_4144407 : Nat := 118140960795 + 4144407 * 2 ^ 59
def prefixEnd_4144407 : Nat := 4983230072969 + 3 ^ 40 * 4144407 * 2
def baseEnd_4144407 : Nat := 2128072818858271722252725

theorem tailTrace_4144407 : CollatzResearch.WordTrace tailWord_4144407 prefixEnd_4144407 2128072818858271722252725 := by
  unfold tailWord_4144407
  simp only [CollatzResearch.WordTrace]
  refine ⟨151158941496528722209207475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100772627664352481472804983 151158941496528722209207475)
  ·
    refine ⟨226738412244793083313811213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151158941496528722209207475 226738412244793083313811213)
    ·
      refine ⟨85026904591797406242679205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226738412244793083313811213 85026904591797406242679205)
      ·
        refine ⟨15942544610962013670502351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85026904591797406242679205 15942544610962013670502351)
        ·
          refine ⟨23913816916443020505753527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15942544610962013670502351 23913816916443020505753527)
          ·
            refine ⟨35870725374664530758630291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23913816916443020505753527 35870725374664530758630291)
            ·
              refine ⟨53806088061996796137945437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35870725374664530758630291 53806088061996796137945437)
              ·
                refine ⟨20177283023248798551729539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53806088061996796137945437 20177283023248798551729539)
                ·
                  refine ⟨30265924534873197827594309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20177283023248798551729539 30265924534873197827594309)
                  ·
                    refine ⟨5674860850288724592673933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30265924534873197827594309 5674860850288724592673933)
                    ·
                      refine ⟨2128072818858271722252725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5674860850288724592673933 2128072818858271722252725)
                      ·
                        rfl

theorem cell23_4144407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_4144407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144407 prefixEnd_4144407 := by exact prefixLift 4144407
  have htrace : WordTrace (prefixWord ++ tailWord_4144407) baseStart_4144407 baseEnd_4144407 := by
    simpa [prefixWord, tailWord_4144407, baseEnd_4144407] using wordTrace_append hprefix tailTrace_4144407
  have hstable : (prefixWord ++ tailWord_4144407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144407).length < 2 ^ (prefixWord ++ tailWord_4144407).sum := by decide
  have hdescent : baseEnd_4144407 < baseStart_4144407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144424 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_4144424 : Nat := 118140960795 + 4144424 * 2 ^ 59
def prefixEnd_4144424 : Nat := 4983230072969 + 3 ^ 40 * 4144424 * 2
def baseEnd_4144424 : Nat := 2128081548029398155740147

theorem tailTrace_4144424 : CollatzResearch.WordTrace tailWord_4144424 prefixEnd_4144424 2128081548029398155740147 := by
  unfold tailWord_4144424
  simp only [CollatzResearch.WordTrace]
  refine ⟨75579780768733567056288163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100773041024978089408384217 75579780768733567056288163)
  ·
    refine ⟨113369671153100350584432245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75579780768733567056288163 113369671153100350584432245)
    ·
      refine ⟨10628406670603157867290523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113369671153100350584432245 10628406670603157867290523)
      ·
        refine ⟨15942610005904736800935785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10628406670603157867290523 15942610005904736800935785)
        ·
          refine ⟨11956957504428552600701839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15942610005904736800935785 11956957504428552600701839)
          ·
            refine ⟨17935436256642828901052759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11956957504428552600701839 17935436256642828901052759)
            ·
              refine ⟨26903154384964243351579139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17935436256642828901052759 26903154384964243351579139)
              ·
                refine ⟨40354731577446365027368709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26903154384964243351579139 40354731577446365027368709)
                ·
                  refine ⟨7566512170771193442631633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40354731577446365027368709 7566512170771193442631633)
                  ·
                    refine ⟨5674884128078395081973725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7566512170771193442631633 5674884128078395081973725)
                    ·
                      refine ⟨2128081548029398155740147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5674884128078395081973725 2128081548029398155740147)
                      ·
                        rfl

theorem cell23_4144424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_4144424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144424 prefixEnd_4144424 := by exact prefixLift 4144424
  have htrace : WordTrace (prefixWord ++ tailWord_4144424) baseStart_4144424 baseEnd_4144424 := by
    simpa [prefixWord, tailWord_4144424, baseEnd_4144424] using wordTrace_append hprefix tailTrace_4144424
  have hstable : (prefixWord ++ tailWord_4144424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144424).length < 2 ^ (prefixWord ++ tailWord_4144424).sum := by decide
  have hdescent : baseEnd_4144424 < baseStart_4144424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144440 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 2, 9]
def baseStart_4144440 : Nat := 118140960795 + 4144440 * 2 ^ 59
def prefixEnd_4144440 : Nat := 4983230072969 + 3 ^ 40 * 4144440 * 2
def baseEnd_4144440 : Nat := 709363254573290031046691

theorem tailTrace_4144440 : CollatzResearch.WordTrace tailWord_4144440 prefixEnd_4144440 709363254573290031046691 := by
  unfold tailWord_4144440
  simp only [CollatzResearch.WordTrace]
  refine ⟨75580072552704584422579387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100773430070272779230105849 75580072552704584422579387)
  ·
    refine ⟨113370108829056876633869081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75580072552704584422579387 113370108829056876633869081)
    ·
      refine ⟨85027581621792657475401811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113370108829056876633869081 85027581621792657475401811)
      ·
        refine ⟨127541372432688986213102717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85027581621792657475401811 127541372432688986213102717)
        ·
          refine ⟨47828014662258369829913519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127541372432688986213102717 47828014662258369829913519)
          ·
            refine ⟨71742021993387554744870279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47828014662258369829913519 71742021993387554744870279)
            ·
              refine ⟨107613032990081332117305419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71742021993387554744870279 107613032990081332117305419)
              ·
                refine ⟨161419549485121998175958129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107613032990081332117305419 161419549485121998175958129)
                ·
                  refine ⟨121064662113841498631968597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161419549485121998175958129 121064662113841498631968597)
                  ·
                    refine ⟨709363254573290031046691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 121064662113841498631968597 709363254573290031046691)
                    ·
                      rfl

theorem cell23_4144440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_4144440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144440 prefixEnd_4144440 := by exact prefixLift 4144440
  have htrace : WordTrace (prefixWord ++ tailWord_4144440) baseStart_4144440 baseEnd_4144440 := by
    simpa [prefixWord, tailWord_4144440, baseEnd_4144440] using wordTrace_append hprefix tailTrace_4144440
  have hstable : (prefixWord ++ tailWord_4144440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144440).length < 2 ^ (prefixWord ++ tailWord_4144440).sum := by decide
  have hdescent : baseEnd_4144440 < baseStart_4144440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144444 : List Nat := [2, 2, 2, 2, 1, 3, 4, 1, 6]
def baseStart_4144444 : Nat := 118140960795 + 4144444 * 2 ^ 59
def prefixEnd_4144444 : Nat := 4983230072969 + 3 ^ 40 * 4144444 * 2
def baseEnd_4144444 : Nat := 236454646404720897498895

theorem tailTrace_4144444 : CollatzResearch.WordTrace tailWord_4144444 prefixEnd_4144444 236454646404720897498895 := by
  unfold tailWord_4144444
  simp only [CollatzResearch.WordTrace]
  refine ⟨75580145498697338764152193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100773527331596451685536257 75580145498697338764152193)
  ·
    refine ⟨56685109124023004073114145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75580145498697338764152193 56685109124023004073114145)
    ·
      refine ⟨42513831843017253054835609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56685109124023004073114145 42513831843017253054835609)
      ·
        refine ⟨31885373882262939791126707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42513831843017253054835609 31885373882262939791126707)
        ·
          refine ⟨47828060823394409686690061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31885373882262939791126707 47828060823394409686690061)
          ·
            refine ⟨17935522808772903632508773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47828060823394409686690061 17935522808772903632508773)
            ·
              refine ⟨3362910526644919431095395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17935522808772903632508773 3362910526644919431095395)
              ·
                refine ⟨5044365789967379146643093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3362910526644919431095395 5044365789967379146643093)
                ·
                  refine ⟨236454646404720897498895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5044365789967379146643093 236454646404720897498895)
                  ·
                    rfl

theorem cell23_4144444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 6].length) (baseStart_4144444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144444 prefixEnd_4144444 := by exact prefixLift 4144444
  have htrace : WordTrace (prefixWord ++ tailWord_4144444) baseStart_4144444 baseEnd_4144444 := by
    simpa [prefixWord, tailWord_4144444, baseEnd_4144444] using wordTrace_append hprefix tailTrace_4144444
  have hstable : (prefixWord ++ tailWord_4144444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144444).length < 2 ^ (prefixWord ++ tailWord_4144444).sum := by decide
  have hdescent : baseEnd_4144444 < baseStart_4144444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144497 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 1, 1, 5]
def baseStart_4144497 : Nat := 118140960795 + 4144497 * 2 ^ 59
def prefixEnd_4144497 : Nat := 4983230072969 + 3 ^ 40 * 4144497 * 2
def baseEnd_4144497 : Nat := 2128119032117176370127311

theorem tailTrace_4144497 : CollatzResearch.WordTrace tailWord_4144497 prefixEnd_4144497 2128119032117176370127311 := by
  unfold tailWord_4144497
  simp only [CollatzResearch.WordTrace]
  refine ⟨151162224066202667579983745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100774816044135111719989163 151162224066202667579983745)
  ·
    refine ⟨113371668049652000684987809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151162224066202667579983745 113371668049652000684987809)
    ·
      refine ⟨85028751037239000513740857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113371668049652000684987809 85028751037239000513740857)
      ·
        refine ⟨63771563277929250385305643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85028751037239000513740857 63771563277929250385305643)
        ·
          refine ⟨95657344916893875577958465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63771563277929250385305643 95657344916893875577958465)
          ·
            refine ⟨71743008687670406683468849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95657344916893875577958465 71743008687670406683468849)
            ·
              refine ⟨53807256515752805012601637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71743008687670406683468849 53807256515752805012601637)
              ·
                refine ⟨10088860596703650939862807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53807256515752805012601637 10088860596703650939862807)
                ·
                  refine ⟨15133290895055476409794211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10088860596703650939862807 15133290895055476409794211)
                  ·
                    refine ⟨22699936342583214614691317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15133290895055476409794211 22699936342583214614691317)
                    ·
                      refine ⟨2128119032117176370127311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22699936342583214614691317 2128119032117176370127311)
                      ·
                        rfl

theorem cell23_4144497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_4144497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144497 prefixEnd_4144497 := by exact prefixLift 4144497
  have htrace : WordTrace (prefixWord ++ tailWord_4144497) baseStart_4144497 baseEnd_4144497 := by
    simpa [prefixWord, tailWord_4144497, baseEnd_4144497] using wordTrace_append hprefix tailTrace_4144497
  have hstable : (prefixWord ++ tailWord_4144497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144497).length < 2 ^ (prefixWord ++ tailWord_4144497).sum := by decide
  have hdescent : baseEnd_4144497 < baseStart_4144497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
