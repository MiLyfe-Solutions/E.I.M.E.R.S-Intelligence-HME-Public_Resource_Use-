import V185TrunkScan23Chunk0252

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1496813 : List Nat := [1, 5, 1, 2, 1, 4, 2, 2, 1, 1, 3]
def baseStart_1496813 : Nat := 118140960795 + 1496813 * 2 ^ 59
def prefixEnd_1496813 : Nat := 4983230072969 + 3 ^ 40 * 1496813 * 2
def baseEnd_1496813 : Nat := 768584518898357445953789

theorem tailTrace_1496813 : CollatzResearch.WordTrace tailWord_1496813 prefixEnd_1496813 768584518898357445953789 := by
  unfold tailWord_1496813
  simp only [CollatzResearch.WordTrace]
  refine ⟨54593255126309611153343093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36395503417539740768895395 54593255126309611153343093)
  ·
    refine ⟨5118117668091526045625915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54593255126309611153343093 5118117668091526045625915)
    ·
      refine ⟨7677176502137289068438873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5118117668091526045625915 7677176502137289068438873)
      ·
        refine ⟨5757882376602966801329155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7677176502137289068438873 5757882376602966801329155)
        ·
          refine ⟨8636823564904450201993733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5757882376602966801329155 8636823564904450201993733)
          ·
            refine ⟨1619404418419584412873825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8636823564904450201993733 1619404418419584412873825)
            ·
              refine ⟨1214553313814688309655369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1619404418419584412873825 1214553313814688309655369)
              ·
                refine ⟨910914985361016232241527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1214553313814688309655369 910914985361016232241527)
                ·
                  refine ⟨1366372478041524348362291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 910914985361016232241527 1366372478041524348362291)
                  ·
                    refine ⟨2049558717062286522543437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1366372478041524348362291 2049558717062286522543437)
                    ·
                      refine ⟨768584518898357445953789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2049558717062286522543437 768584518898357445953789)
                      ·
                        rfl

theorem cell23_1496813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_1496813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496813 prefixEnd_1496813 := by exact prefixLift 1496813
  have htrace : WordTrace (prefixWord ++ tailWord_1496813) baseStart_1496813 baseEnd_1496813 := by
    simpa [prefixWord, tailWord_1496813, baseEnd_1496813] using wordTrace_append hprefix tailTrace_1496813
  have hstable : (prefixWord ++ tailWord_1496813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496813).length < 2 ^ (prefixWord ++ tailWord_1496813).sum := by decide
  have hdescent : baseEnd_1496813 < baseStart_1496813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496822 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_1496822 : Nat := 118140960795 + 1496822 * 2 ^ 59
def prefixEnd_1496822 : Nat := 4983230072969 + 3 ^ 40 * 1496822 * 2
def baseEnd_1496822 : Nat := 768589140224247910741247

theorem tailTrace_1496822 : CollatzResearch.WordTrace tailWord_1496822 prefixEnd_1496822 768589140224247910741247 := by
  unfold tailWord_1496822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3412098961454812855651295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36395722255518003793613813 3412098961454812855651295)
  ·
    refine ⟨5118148442182219283476943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3412098961454812855651295 5118148442182219283476943)
    ·
      refine ⟨7677222663273328925215415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5118148442182219283476943 7677222663273328925215415)
      ·
        refine ⟨11515833994909993387823123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7677222663273328925215415 11515833994909993387823123)
        ·
          refine ⟨17273750992364990081734685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11515833994909993387823123 17273750992364990081734685)
          ·
            refine ⟨6477656622136871280650507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17273750992364990081734685 6477656622136871280650507)
            ·
              refine ⟨9716484933205306920975761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6477656622136871280650507 9716484933205306920975761)
              ·
                refine ⟨7287363699903980190731821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9716484933205306920975761 7287363699903980190731821)
                ·
                  refine ⟨2732761387463992571524433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7287363699903980190731821 2732761387463992571524433)
                  ·
                    refine ⟨2049571040597994428643325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2732761387463992571524433 2049571040597994428643325)
                    ·
                      refine ⟨768589140224247910741247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2049571040597994428643325 768589140224247910741247)
                      ·
                        rfl

theorem cell23_1496822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_1496822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496822 prefixEnd_1496822 := by exact prefixLift 1496822
  have htrace : WordTrace (prefixWord ++ tailWord_1496822) baseStart_1496822 baseEnd_1496822 := by
    simpa [prefixWord, tailWord_1496822, baseEnd_1496822] using wordTrace_append hprefix tailTrace_1496822
  have hstable : (prefixWord ++ tailWord_1496822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496822).length < 2 ^ (prefixWord ++ tailWord_1496822).sum := by decide
  have hdescent : baseEnd_1496822 < baseStart_1496822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496835 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 3]
def baseStart_1496835 : Nat := 118140960795 + 1496835 * 2 ^ 59
def prefixEnd_1496835 : Nat := 4983230072969 + 3 ^ 40 * 1496835 * 2
def baseEnd_1496835 : Nat := 768595815472756359878687

theorem tailTrace_1496835 : CollatzResearch.WordTrace tailWord_1496835 prefixEnd_1496835 768595815472756359878687 := by
  unfold tailWord_1496835
  simp only [CollatzResearch.WordTrace]
  refine ⟨54594057532229908910643959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36396038354819939273762639 54594057532229908910643959)
  ·
    refine ⟨81891086298344863365965939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54594057532229908910643959 81891086298344863365965939)
    ·
      refine ⟨122836629447517295048948909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81891086298344863365965939 122836629447517295048948909)
      ·
        refine ⟨46063736042818985643355841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122836629447517295048948909 46063736042818985643355841)
        ·
          refine ⟨34547802032114239232516881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46063736042818985643355841 34547802032114239232516881)
          ·
            refine ⟨25910851524085679424387661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34547802032114239232516881 25910851524085679424387661)
            ·
              refine ⟨9716569321532129784145373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25910851524085679424387661 9716569321532129784145373)
              ·
                refine ⟨3643713495574548669054515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9716569321532129784145373 3643713495574548669054515)
                ·
                  refine ⟨5465570243361823003581773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3643713495574548669054515 5465570243361823003581773)
                  ·
                    refine ⟨2049588841260683626343165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5465570243361823003581773 2049588841260683626343165)
                    ·
                      refine ⟨768595815472756359878687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2049588841260683626343165 768595815472756359878687)
                      ·
                        rfl

theorem cell23_1496835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_1496835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496835 prefixEnd_1496835 := by exact prefixLift 1496835
  have htrace : WordTrace (prefixWord ++ tailWord_1496835) baseStart_1496835 baseEnd_1496835 := by
    simpa [prefixWord, tailWord_1496835, baseEnd_1496835] using wordTrace_append hprefix tailTrace_1496835
  have hstable : (prefixWord ++ tailWord_1496835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496835).length < 2 ^ (prefixWord ++ tailWord_1496835).sum := by decide
  have hdescent : baseEnd_1496835 < baseStart_1496835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496869 : List Nat := [1, 3, 1, 2, 3, 2, 3, 2, 2, 1, 3]
def baseStart_1496869 : Nat := 118140960795 + 1496869 * 2 ^ 59
def prefixEnd_1496869 : Nat := 4983230072969 + 3 ^ 40 * 1496869 * 2
def baseEnd_1496869 : Nat := 768613273815009226853531

theorem tailTrace_1496869 : CollatzResearch.WordTrace tailWord_1496869 prefixEnd_1496869 768613273815009226853531 := by
  unfold tailWord_1496869
  simp only [CollatzResearch.WordTrace]
  refine ⟨54595297614106732717381661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36396865076071155144921107 54595297614106732717381661)
  ·
    refine ⟨20473236605290024769018123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54595297614106732717381661 20473236605290024769018123)
    ·
      refine ⟨30709854907935037153527185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20473236605290024769018123 30709854907935037153527185)
      ·
        refine ⟨23032391180951277865145389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30709854907935037153527185 23032391180951277865145389)
        ·
          refine ⟨8637146692856729199429521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23032391180951277865145389 8637146692856729199429521)
          ·
            refine ⟨6477860019642546899572141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8637146692856729199429521 6477860019642546899572141)
            ·
              refine ⟨2429197507365955087339553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6477860019642546899572141 2429197507365955087339553)
              ·
                refine ⟨1821898130524466315504665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2429197507365955087339553 1821898130524466315504665)
                ·
                  refine ⟨1366423597893349736628499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1821898130524466315504665 1366423597893349736628499)
                  ·
                    refine ⟨2049635396840024604942749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1366423597893349736628499 2049635396840024604942749)
                    ·
                      refine ⟨768613273815009226853531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2049635396840024604942749 768613273815009226853531)
                      ·
                        rfl

theorem cell23_1496869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_1496869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496869 prefixEnd_1496869 := by exact prefixLift 1496869
  have htrace : WordTrace (prefixWord ++ tailWord_1496869) baseStart_1496869 baseEnd_1496869 := by
    simpa [prefixWord, tailWord_1496869, baseEnd_1496869] using wordTrace_append hprefix tailTrace_1496869
  have hstable : (prefixWord ++ tailWord_1496869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496869).length < 2 ^ (prefixWord ++ tailWord_1496869).sum := by decide
  have hdescent : baseEnd_1496869 < baseStart_1496869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496886 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1496886 : Nat := 118140960795 + 1496886 * 2 ^ 59
def prefixEnd_1496886 : Nat := 4983230072969 + 3 ^ 40 * 1496886 * 2
def baseEnd_1496886 : Nat := 768622002986135660340953

theorem tailTrace_1496886 : CollatzResearch.WordTrace tailWord_1496886 prefixEnd_1496886 768622002986135660340953 := by
  unfold tailWord_1496886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3412244853440321538796907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36397278436696763080500341 3412244853440321538796907)
  ·
    refine ⟨5118367280160482308195361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3412244853440321538796907 5118367280160482308195361)
    ·
      refine ⟨3838775460120361731146521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5118367280160482308195361 3838775460120361731146521)
      ·
        refine ⟨2879081595090271298359891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3838775460120361731146521 2879081595090271298359891)
        ·
          refine ⟨4318622392635406947539837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2879081595090271298359891 4318622392635406947539837)
          ·
            refine ⟨1619483397238277605327439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4318622392635406947539837 1619483397238277605327439)
            ·
              refine ⟨2429225095857416407991159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619483397238277605327439 2429225095857416407991159)
              ·
                refine ⟨3643837643786124611986739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429225095857416407991159 3643837643786124611986739)
                ·
                  refine ⟨5465756465679186917980109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3643837643786124611986739 5465756465679186917980109)
                  ·
                    refine ⟨2049658674629695094242541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5465756465679186917980109 2049658674629695094242541)
                    ·
                      refine ⟨768622002986135660340953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2049658674629695094242541 768622002986135660340953)
                      ·
                        rfl

theorem cell23_1496886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1496886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496886 prefixEnd_1496886 := by exact prefixLift 1496886
  have htrace : WordTrace (prefixWord ++ tailWord_1496886) baseStart_1496886 baseEnd_1496886 := by
    simpa [prefixWord, tailWord_1496886, baseEnd_1496886] using wordTrace_append hprefix tailTrace_1496886
  have hstable : (prefixWord ++ tailWord_1496886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496886).length < 2 ^ (prefixWord ++ tailWord_1496886).sum := by decide
  have hdescent : baseEnd_1496886 < baseStart_1496886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496945 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 4, 5]
def baseStart_1496945 : Nat := 118140960795 + 1496945 * 2 ^ 59
def prefixEnd_1496945 : Nat := 4983230072969 + 3 ^ 40 * 1496945 * 2
def baseEnd_1496945 : Nat := 256217432781583643167727

theorem tailTrace_1496945 : CollatzResearch.WordTrace tailWord_1496945 prefixEnd_1496945 256217432781583643167727 := by
  unfold tailWord_1496945
  simp only [CollatzResearch.WordTrace]
  refine ⟨54598069561831397697148289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36398713041220931798098859 54598069561831397697148289)
  ·
    refine ⟨40948552171373548272861217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54598069561831397697148289 40948552171373548272861217)
    ·
      refine ⟨30711414128530161204645913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40948552171373548272861217 30711414128530161204645913)
      ·
        refine ⟨23033560596397620903484435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30711414128530161204645913 23033560596397620903484435)
        ·
          refine ⟨34550340894596431355226653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23033560596397620903484435 34550340894596431355226653)
          ·
            refine ⟨12956377835473661758209995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34550340894596431355226653 12956377835473661758209995)
            ·
              refine ⟨19434566753210492637314993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12956377835473661758209995 19434566753210492637314993)
              ·
                refine ⟨14575925064907869477986245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19434566753210492637314993 14575925064907869477986245)
                ·
                  refine ⟨2732985949670225527122421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14575925064907869477986245 2732985949670225527122421)
                  ·
                    refine ⟨256217432781583643167727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2732985949670225527122421 256217432781583643167727)
                    ·
                      rfl

theorem cell23_1496945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_1496945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496945 prefixEnd_1496945 := by exact prefixLift 1496945
  have htrace : WordTrace (prefixWord ++ tailWord_1496945) baseStart_1496945 baseEnd_1496945 := by
    simpa [prefixWord, tailWord_1496945, baseEnd_1496945] using wordTrace_append hprefix tailTrace_1496945
  have hstable : (prefixWord ++ tailWord_1496945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496945).length < 2 ^ (prefixWord ++ tailWord_1496945).sum := by decide
  have hdescent : baseEnd_1496945 < baseStart_1496945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496992 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 3, 4]
def baseStart_1496992 : Nat := 118140960795 + 1496992 * 2 ^ 59
def prefixEnd_1496992 : Nat := 4983230072969 + 3 ^ 40 * 1496992 * 2
def baseEnd_1496992 : Nat := 256225477311837415205155

theorem tailTrace_1496992 : CollatzResearch.WordTrace tailWord_1496992 prefixEnd_1496992 256225477311837415205155 := by
  unfold tailWord_1496992
  simp only [CollatzResearch.WordTrace]
  refine ⟨27299891896330562362054615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36399855861774083149406153 27299891896330562362054615)
  ·
    refine ⟨40949837844495843543081923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27299891896330562362054615 40949837844495843543081923)
    ·
      refine ⟨61424756766743765314622885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40949837844495843543081923 61424756766743765314622885)
      ·
        refine ⟨11517141893764455996491791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61424756766743765314622885 11517141893764455996491791)
        ·
          refine ⟨17275712840646683994737687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11517141893764455996491791 17275712840646683994737687)
          ·
            refine ⟨25913569260970025992106531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17275712840646683994737687 25913569260970025992106531)
            ·
              refine ⟨38870353891455038988159797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25913569260970025992106531 38870353891455038988159797)
              ·
                refine ⟨3644095677323909905139981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38870353891455038988159797 3644095677323909905139981)
                ·
                  refine ⟨1366535878996466214427493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3644095677323909905139981 1366535878996466214427493)
                  ·
                    refine ⟨256225477311837415205155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1366535878996466214427493 256225477311837415205155)
                    ·
                      rfl

theorem cell23_1496992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 3, 4].length) (baseStart_1496992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496992 prefixEnd_1496992 := by exact prefixLift 1496992
  have htrace : WordTrace (prefixWord ++ tailWord_1496992) baseStart_1496992 baseEnd_1496992 := by
    simpa [prefixWord, tailWord_1496992, baseEnd_1496992] using wordTrace_append hprefix tailTrace_1496992
  have hstable : (prefixWord ++ tailWord_1496992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496992).length < 2 ^ (prefixWord ++ tailWord_1496992).sum := by decide
  have hdescent : baseEnd_1496992 < baseStart_1496992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496995 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 4]
def baseStart_1496995 : Nat := 118140960795 + 1496995 * 2 ^ 59
def prefixEnd_1496995 : Nat := 4983230072969 + 3 ^ 40 * 1496995 * 2
def baseEnd_1496995 : Nat := 768677972377475733877951

theorem tailTrace_1496995 : CollatzResearch.WordTrace tailWord_1496995 prefixEnd_1496995 768677972377475733877951 := by
  unfold tailWord_1496995
  simp only [CollatzResearch.WordTrace]
  refine ⟨54599893211650256236468439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36399928807766837490978959 54599893211650256236468439)
  ·
    refine ⟨81899839817475384354702659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54599893211650256236468439 81899839817475384354702659)
    ·
      refine ⟨122849759726213076532053989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81899839817475384354702659 122849759726213076532053989)
      ·
        refine ⟨23034329948664951849760123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122849759726213076532053989 23034329948664951849760123)
        ·
          refine ⟨34551494922997427774640185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23034329948664951849760123 34551494922997427774640185)
          ·
            refine ⟨25913621192248070830980139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34551494922997427774640185 25913621192248070830980139)
            ·
              refine ⟨38870431788372106246470209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25913621192248070830980139 38870431788372106246470209)
              ·
                refine ⟨29152823841279079684852657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38870431788372106246470209 29152823841279079684852657)
                ·
                  refine ⟨21864617880959309763639493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29152823841279079684852657 21864617880959309763639493)
                  ·
                    refine ⟨4099615852679870580682405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21864617880959309763639493 4099615852679870580682405)
                    ·
                      refine ⟨768677972377475733877951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4099615852679870580682405 768677972377475733877951)
                      ·
                        rfl

theorem cell23_1496995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_1496995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496995 prefixEnd_1496995 := by exact prefixLift 1496995
  have htrace : WordTrace (prefixWord ++ tailWord_1496995) baseStart_1496995 baseEnd_1496995 := by
    simpa [prefixWord, tailWord_1496995, baseEnd_1496995] using wordTrace_append hprefix tailTrace_1496995
  have hstable : (prefixWord ++ tailWord_1496995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496995).length < 2 ^ (prefixWord ++ tailWord_1496995).sum := by decide
  have hdescent : baseEnd_1496995 < baseStart_1496995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496999 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_1496999 : Nat := 118140960795 + 1496999 * 2 ^ 59
def prefixEnd_1496999 : Nat := 4983230072969 + 3 ^ 40 * 1496999 * 2
def baseEnd_1496999 : Nat := 768680026300093718227933

theorem tailTrace_1496999 : CollatzResearch.WordTrace tailWord_1496999 prefixEnd_1496999 768680026300093718227933 := by
  unfold tailWord_1496999
  simp only [CollatzResearch.WordTrace]
  refine ⟨54600039103635764919614051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36400026069090509946409367 54600039103635764919614051)
  ·
    refine ⟨81900058655453647379421077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54600039103635764919614051 81900058655453647379421077)
    ·
      refine ⟨3839065249474389720910363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81900058655453647379421077 3839065249474389720910363)
      ·
        refine ⟨5758597874211584581365545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3839065249474389720910363 5758597874211584581365545)
        ·
          refine ⟨4318948405658688436024159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5758597874211584581365545 4318948405658688436024159)
          ·
            refine ⟨6478422608488032654036239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4318948405658688436024159 6478422608488032654036239)
            ·
              refine ⟨9717633912732048981054359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6478422608488032654036239 9717633912732048981054359)
              ·
                refine ⟨14576450869098073471581539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9717633912732048981054359 14576450869098073471581539)
                ·
                  refine ⟨21864676303647110207372309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14576450869098073471581539 21864676303647110207372309)
                  ·
                    refine ⟨1024906701733458290970577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21864676303647110207372309 1024906701733458290970577)
                    ·
                      refine ⟨768680026300093718227933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1024906701733458290970577 768680026300093718227933)
                      ·
                        rfl

theorem cell23_1496999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_1496999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496999 prefixEnd_1496999 := by exact prefixLift 1496999
  have htrace : WordTrace (prefixWord ++ tailWord_1496999) baseStart_1496999 baseEnd_1496999 := by
    simpa [prefixWord, tailWord_1496999, baseEnd_1496999] using wordTrace_append hprefix tailTrace_1496999
  have hstable : (prefixWord ++ tailWord_1496999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496999).length < 2 ^ (prefixWord ++ tailWord_1496999).sum := by decide
  have hdescent : baseEnd_1496999 < baseStart_1496999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497009 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 3, 4]
def baseStart_1497009 : Nat := 118140960795 + 1497009 * 2 ^ 59
def prefixEnd_1497009 : Nat := 4983230072969 + 3 ^ 40 * 1497009 * 2
def baseEnd_1497009 : Nat := 256228387035546226367629

theorem tailTrace_1497009 : CollatzResearch.WordTrace tailWord_1497009 prefixEnd_1497009 256228387035546226367629 := by
  unfold tailWord_1497009
  simp only [CollatzResearch.WordTrace]
  refine ⟨54600403833599536627478081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36400269222399691084985387 54600403833599536627478081)
  ·
    refine ⟨40950302875199652470608561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54600403833599536627478081 40950302875199652470608561)
    ·
      refine ⟨30712727156399739352956421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40950302875199652470608561 30712727156399739352956421)
      ·
        refine ⟨5758636341824951128679329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30712727156399739352956421 5758636341824951128679329)
        ·
          refine ⟨4318977256368713346509497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5758636341824951128679329 4318977256368713346509497)
          ·
            refine ⟨3239232942276535009882123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4318977256368713346509497 3239232942276535009882123)
            ·
              refine ⟨4858849413414802514823185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3239232942276535009882123 4858849413414802514823185)
              ·
                refine ⟨3644137060061101886117389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4858849413414802514823185 3644137060061101886117389)
                ·
                  refine ⟨1366551397522913207294021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3644137060061101886117389 1366551397522913207294021)
                  ·
                    refine ⟨256228387035546226367629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1366551397522913207294021 256228387035546226367629)
                    ·
                      rfl

theorem cell23_1497009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_1497009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497009 prefixEnd_1497009 := by exact prefixLift 1497009
  have htrace : WordTrace (prefixWord ++ tailWord_1497009) baseStart_1497009 baseEnd_1497009 := by
    simpa [prefixWord, tailWord_1497009, baseEnd_1497009] using wordTrace_append hprefix tailTrace_1497009
  have hstable : (prefixWord ++ tailWord_1497009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497009).length < 2 ^ (prefixWord ++ tailWord_1497009).sum := by decide
  have hdescent : baseEnd_1497009 < baseStart_1497009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497059 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 1, 5, 2]
def baseStart_1497059 : Nat := 118140960795 + 1497059 * 2 ^ 59
def prefixEnd_1497059 : Nat := 4983230072969 + 3 ^ 40 * 1497059 * 2
def baseEnd_1497059 : Nat := 768710835139363483477657

theorem tailTrace_1497059 : CollatzResearch.WordTrace tailWord_1497059 prefixEnd_1497059 768710835139363483477657 := by
  unfold tailWord_1497059
  simp only [CollatzResearch.WordTrace]
  refine ⟨54602227483418395166798231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36401484988945596777865487 54602227483418395166798231)
  ·
    refine ⟨81903341225127592750197347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54602227483418395166798231 81903341225127592750197347)
    ·
      refine ⟨122855011837691389125296021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81903341225127592750197347 122855011837691389125296021)
      ·
        refine ⟨5758828679891783865248251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122855011837691389125296021 5758828679891783865248251)
        ·
          refine ⟨8638243019837675797872377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5758828679891783865248251 8638243019837675797872377)
          ·
            refine ⟨6478682264878256848404283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8638243019837675797872377 6478682264878256848404283)
            ·
              refine ⟨9718023397317385272606425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6478682264878256848404283 9718023397317385272606425)
              ·
                refine ⟨7288517547988038954454819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9718023397317385272606425 7288517547988038954454819)
                ·
                  refine ⟨10932776321982058431682229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7288517547988038954454819 10932776321982058431682229)
                  ·
                    refine ⟨1024947780185817977970209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10932776321982058431682229 1024947780185817977970209)
                    ·
                      refine ⟨768710835139363483477657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1024947780185817977970209 768710835139363483477657)
                      ·
                        rfl

theorem cell23_1497059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_1497059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497059 prefixEnd_1497059 := by exact prefixLift 1497059
  have htrace : WordTrace (prefixWord ++ tailWord_1497059) baseStart_1497059 baseEnd_1497059 := by
    simpa [prefixWord, tailWord_1497059, baseEnd_1497059] using wordTrace_append hprefix tailTrace_1497059
  have hstable : (prefixWord ++ tailWord_1497059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497059).length < 2 ^ (prefixWord ++ tailWord_1497059).sum := by decide
  have hdescent : baseEnd_1497059 < baseStart_1497059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497072 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 4]
def baseStart_1497072 : Nat := 118140960795 + 1497072 * 2 ^ 59
def prefixEnd_1497072 : Nat := 4983230072969 + 3 ^ 40 * 1497072 * 2
def baseEnd_1497072 : Nat := 768717510387871932615097

theorem tailTrace_1497072 : CollatzResearch.WordTrace tailWord_1497072 prefixEnd_1497072 768717510387871932615097 := by
  unfold tailWord_1497072
  simp only [CollatzResearch.WordTrace]
  refine ⟨27301350816185649193510735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36401801088247532258014313 27301350816185649193510735)
  ·
    refine ⟨40952026224278473790266103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27301350816185649193510735 40952026224278473790266103)
    ·
      refine ⟨61428039336417710685399155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40952026224278473790266103 61428039336417710685399155)
      ·
        refine ⟨92142059004626566028098733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61428039336417710685399155 92142059004626566028098733)
        ·
          refine ⟨34553272126734962260537025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92142059004626566028098733 34553272126734962260537025)
          ·
            refine ⟨25914954095051221695402769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34553272126734962260537025 25914954095051221695402769)
            ·
              refine ⟨19436215571288416271552077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25914954095051221695402769 19436215571288416271552077)
              ·
                refine ⟨7288580839233156101832029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19436215571288416271552077 7288580839233156101832029)
                ·
                  refine ⟨2733217814712433538187011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7288580839233156101832029 2733217814712433538187011)
                  ·
                    refine ⟨4099826722068650307280517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2733217814712433538187011 4099826722068650307280517)
                    ·
                      refine ⟨768717510387871932615097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4099826722068650307280517 768717510387871932615097)
                      ·
                        rfl

theorem cell23_1497072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 4].length) (baseStart_1497072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497072 prefixEnd_1497072 := by exact prefixLift 1497072
  have htrace : WordTrace (prefixWord ++ tailWord_1497072) baseStart_1497072 baseEnd_1497072 := by
    simpa [prefixWord, tailWord_1497072, baseEnd_1497072] using wordTrace_append hprefix tailTrace_1497072
  have hstable : (prefixWord ++ tailWord_1497072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497072).length < 2 ^ (prefixWord ++ tailWord_1497072).sum := by decide
  have hdescent : baseEnd_1497072 < baseStart_1497072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497086 : List Nat := [4, 2, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_1497086 : Nat := 118140960795 + 1497086 * 2 ^ 59
def prefixEnd_1497086 : Nat := 4983230072969 + 3 ^ 40 * 1497086 * 2
def baseEnd_1497086 : Nat := 256241566372344959280011

theorem tailTrace_1497086 : CollatzResearch.WordTrace tailWord_1497086 prefixEnd_1497086 256241566372344959280011 := by
  unfold tailWord_1497086
  simp only [CollatzResearch.WordTrace]
  refine ⟨6825401531790072347253889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36402141502880385852020741 6825401531790072347253889)
  ·
    refine ⟨5119051148842554260440417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6825401531790072347253889 5119051148842554260440417)
    ·
      refine ⟨3839288361631915695330313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5119051148842554260440417 3839288361631915695330313)
      ·
        refine ⟨2879466271223936771497735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3839288361631915695330313 2879466271223936771497735)
        ·
          refine ⟨4319199406835905157246603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2879466271223936771497735 4319199406835905157246603)
          ·
            refine ⟨6478799110253857735869905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319199406835905157246603 6478799110253857735869905)
            ·
              refine ⟨4859099332690393301902429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6478799110253857735869905 4859099332690393301902429)
              ·
                refine ⟨1822162249758897488213411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4859099332690393301902429 1822162249758897488213411)
                ·
                  refine ⟨2733243374638346232320117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822162249758897488213411 2733243374638346232320117)
                  ·
                    refine ⟨256241566372344959280011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2733243374638346232320117 256241566372344959280011)
                    ·
                      rfl

theorem cell23_1497086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_1497086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497086 prefixEnd_1497086 := by exact prefixLift 1497086
  have htrace : WordTrace (prefixWord ++ tailWord_1497086) baseStart_1497086 baseEnd_1497086 := by
    simpa [prefixWord, tailWord_1497086, baseEnd_1497086] using wordTrace_append hprefix tailTrace_1497086
  have hstable : (prefixWord ++ tailWord_1497086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497086).length < 2 ^ (prefixWord ++ tailWord_1497086).sum := by decide
  have hdescent : baseEnd_1497086 < baseStart_1497086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497089 : List Nat := [1, 2, 4, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_1497089 : Nat := 118140960795 + 1497089 * 2 ^ 59
def prefixEnd_1497089 : Nat := 4983230072969 + 3 ^ 40 * 1497089 * 2
def baseEnd_1497089 : Nat := 768726239558998366102519

theorem tailTrace_1497089 : CollatzResearch.WordTrace tailWord_1497089 prefixEnd_1497089 768726239558998366102519 := by
  unfold tailWord_1497089
  simp only [CollatzResearch.WordTrace]
  refine ⟨54603321673309710290390321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36402214448873140193593547 54603321673309710290390321)
  ·
    refine ⟨40952491254982282717792741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54603321673309710290390321 40952491254982282717792741)
    ·
      refine ⟨7678592110309178009586139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40952491254982282717792741 7678592110309178009586139)
      ·
        refine ⟨11517888165463767014379209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7678592110309178009586139 11517888165463767014379209)
        ·
          refine ⟨8638416124097825260784407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11517888165463767014379209 8638416124097825260784407)
          ·
            refine ⟨12957624186146737891176611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8638416124097825260784407 12957624186146737891176611)
            ·
              refine ⟨19436436279220106836764917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12957624186146737891176611 19436436279220106836764917)
              ·
                refine ⟨1822165901176885015946711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19436436279220106836764917 1822165901176885015946711)
                ·
                  refine ⟨2733248851765327523920067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822165901176885015946711 2733248851765327523920067)
                  ·
                    refine ⟨4099873277647991285880101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2733248851765327523920067 4099873277647991285880101)
                    ·
                      refine ⟨768726239558998366102519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4099873277647991285880101 768726239558998366102519)
                      ·
                        rfl

theorem cell23_1497089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_1497089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497089 prefixEnd_1497089 := by exact prefixLift 1497089
  have htrace : WordTrace (prefixWord ++ tailWord_1497089) baseStart_1497089 baseEnd_1497089 := by
    simpa [prefixWord, tailWord_1497089, baseEnd_1497089] using wordTrace_append hprefix tailTrace_1497089
  have hstable : (prefixWord ++ tailWord_1497089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497089).length < 2 ^ (prefixWord ++ tailWord_1497089).sum := by decide
  have hdescent : baseEnd_1497089 < baseStart_1497089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497094 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1497094 : Nat := 118140960795 + 1497094 * 2 ^ 59
def prefixEnd_1497094 : Nat := 4983230072969 + 3 ^ 40 * 1497094 * 2
def baseEnd_1497094 : Nat := 256242935654090282179999

theorem tailTrace_1497094 : CollatzResearch.WordTrace tailWord_1497094 prefixEnd_1497094 256242935654090282179999 := by
  unfold tailWord_1497094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1706359501196612379510073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36402336025527730762881557 1706359501196612379510073)
  ·
    refine ⟨1279769625897459284632555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1706359501196612379510073 1279769625897459284632555)
    ·
      refine ⟨1919654438846188926948833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1279769625897459284632555 1919654438846188926948833)
      ·
        refine ⟨1439740829134641695211625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1919654438846188926948833 1439740829134641695211625)
        ·
          refine ⟨1079805621850981271408719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1439740829134641695211625 1079805621850981271408719)
          ·
            refine ⟨1619708432776471907113079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079805621850981271408719 1619708432776471907113079)
            ·
              refine ⟨2429562649164707860669619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619708432776471907113079 2429562649164707860669619)
              ·
                refine ⟨3644343973747061791004429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429562649164707860669619 3644343973747061791004429)
                ·
                  refine ⟨1366628990155148171626661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3644343973747061791004429 1366628990155148171626661)
                  ·
                    refine ⟨256242935654090282179999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1366628990155148171626661 256242935654090282179999)
                    ·
                      rfl

theorem cell23_1497094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1497094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497094 prefixEnd_1497094 := by exact prefixLift 1497094
  have htrace : WordTrace (prefixWord ++ tailWord_1497094) baseStart_1497094 baseEnd_1497094 := by
    simpa [prefixWord, tailWord_1497094, baseEnd_1497094] using wordTrace_append hprefix tailTrace_1497094
  have hstable : (prefixWord ++ tailWord_1497094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497094).length < 2 ^ (prefixWord ++ tailWord_1497094).sum := by decide
  have hdescent : baseEnd_1497094 < baseStart_1497094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497099 : List Nat := [1, 1, 1, 1, 6, 1, 2, 4, 2, 4]
def baseStart_1497099 : Nat := 118140960795 + 1497099 * 2 ^ 59
def prefixEnd_1497099 : Nat := 4983230072969 + 3 ^ 40 * 1497099 * 2
def baseEnd_1497099 : Nat := 256243791455181108992491

theorem tailTrace_1497099 : CollatzResearch.WordTrace tailWord_1497099 prefixEnd_1497099 256243791455181108992491 := by
  unfold tailWord_1497099
  simp only [CollatzResearch.WordTrace]
  refine ⟨54603686403273481998254351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36402457602182321332169567 54603686403273481998254351)
  ·
    refine ⟨81905529604910222997381527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54603686403273481998254351 81905529604910222997381527)
    ·
      refine ⟨122858294407365334496072291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81905529604910222997381527 122858294407365334496072291)
      ·
        refine ⟨184287441611048001744108437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122858294407365334496072291 184287441611048001744108437)
        ·
          refine ⟨8638473825517875081755083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 184287441611048001744108437 8638473825517875081755083)
          ·
            refine ⟨12957710738276812622632625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8638473825517875081755083 12957710738276812622632625)
            ·
              refine ⟨9718283053707609466974469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12957710738276812622632625 9718283053707609466974469)
              ·
                refine ⟨1822178072570176775057713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9718283053707609466974469 1822178072570176775057713)
                ·
                  refine ⟨1366633554427632581293285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1822178072570176775057713 1366633554427632581293285)
                  ·
                    refine ⟨256243791455181108992491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1366633554427632581293285 256243791455181108992491)
                    ·
                      rfl

theorem cell23_1497099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 4].length) (baseStart_1497099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497099 prefixEnd_1497099 := by exact prefixLift 1497099
  have htrace : WordTrace (prefixWord ++ tailWord_1497099) baseStart_1497099 baseEnd_1497099 := by
    simpa [prefixWord, tailWord_1497099, baseEnd_1497099] using wordTrace_append hprefix tailTrace_1497099
  have hstable : (prefixWord ++ tailWord_1497099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497099).length < 2 ^ (prefixWord ++ tailWord_1497099).sum := by decide
  have hdescent : baseEnd_1497099 < baseStart_1497099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497102 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_1497102 : Nat := 118140960795 + 1497102 * 2 ^ 59
def prefixEnd_1497102 : Nat := 4983230072969 + 3 ^ 40 * 1497102 * 2
def baseEnd_1497102 : Nat := 768732914807506815239959

theorem tailTrace_1497102 : CollatzResearch.WordTrace tailWord_1497102 prefixEnd_1497102 768732914807506815239959 := by
  unfold tailWord_1497102
  simp only [CollatzResearch.WordTrace]
  refine ⟨6825474477782826688826695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36402530548175075673742373 6825474477782826688826695)
  ·
    refine ⟨10238211716674240033240043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6825474477782826688826695 10238211716674240033240043)
    ·
      refine ⟨15357317575011360049860065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10238211716674240033240043 15357317575011360049860065)
      ·
        refine ⟨11517988181258520037395049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15357317575011360049860065 11517988181258520037395049)
        ·
          refine ⟨8638491135943890028046287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11517988181258520037395049 8638491135943890028046287)
          ·
            refine ⟨12957736703915835042069431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8638491135943890028046287 12957736703915835042069431)
            ·
              refine ⟨19436605055873752563104147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12957736703915835042069431 19436605055873752563104147)
              ·
                refine ⟨29154907583810628844656221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19436605055873752563104147 29154907583810628844656221)
                ·
                  refine ⟨10933090343928985816746083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29154907583810628844656221 10933090343928985816746083)
                  ·
                    refine ⟨16399635515893478725119125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10933090343928985816746083 16399635515893478725119125)
                    ·
                      refine ⟨768732914807506815239959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16399635515893478725119125 768732914807506815239959)
                      ·
                        rfl

theorem cell23_1497102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_1497102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497102 prefixEnd_1497102 := by exact prefixLift 1497102
  have htrace : WordTrace (prefixWord ++ tailWord_1497102) baseStart_1497102 baseEnd_1497102 := by
    simpa [prefixWord, tailWord_1497102, baseEnd_1497102] using wordTrace_append hprefix tailTrace_1497102
  have hstable : (prefixWord ++ tailWord_1497102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497102).length < 2 ^ (prefixWord ++ tailWord_1497102).sum := by decide
  have hdescent : baseEnd_1497102 < baseStart_1497102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497112 : List Nat := [2, 1, 2, 3, 2, 1, 4, 8]
def baseStart_1497112 : Nat := 118140960795 + 1497112 * 2 ^ 59
def prefixEnd_1497112 : Nat := 4983230072969 + 3 ^ 40 * 1497112 * 2
def baseEnd_1497112 : Nat := 28471779615335250967219

theorem tailTrace_1497112 : CollatzResearch.WordTrace tailWord_1497112 prefixEnd_1497112 28471779615335250967219 := by
  unfold tailWord_1497112
  simp only [CollatzResearch.WordTrace]
  refine ⟨27302080276113192609238795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36402773701484256812318393 27302080276113192609238795)
  ·
    refine ⟨40953120414169788913858193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27302080276113192609238795 40953120414169788913858193)
    ·
      refine ⟨30714840310627341685393645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40953120414169788913858193 30714840310627341685393645)
      ·
        refine ⟨11518065116485253132022617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30714840310627341685393645 11518065116485253132022617)
        ·
          refine ⟨8638548837363939849016963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11518065116485253132022617 8638548837363939849016963)
          ·
            refine ⟨12957823256045909773525445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8638548837363939849016963 12957823256045909773525445)
            ·
              refine ⟨2429591860508608082536021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12957823256045909773525445 2429591860508608082536021)
              ·
                refine ⟨28471779615335250967219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2429591860508608082536021 28471779615335250967219)
                ·
                  rfl

theorem cell23_1497112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 8].length) (baseStart_1497112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497112 prefixEnd_1497112 := by exact prefixLift 1497112
  have htrace : WordTrace (prefixWord ++ tailWord_1497112) baseStart_1497112 baseEnd_1497112 := by
    simpa [prefixWord, tailWord_1497112, baseEnd_1497112] using wordTrace_append hprefix tailTrace_1497112
  have hstable : (prefixWord ++ tailWord_1497112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497112).length < 2 ^ (prefixWord ++ tailWord_1497112).sum := by decide
  have hdescent : baseEnd_1497112 < baseStart_1497112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497116 : List Nat := [2, 2, 3, 1, 3, 2, 1, 3, 2, 4]
def baseStart_1497116 : Nat := 118140960795 + 1497116 * 2 ^ 59
def prefixEnd_1497116 : Nat := 4983230072969 + 3 ^ 40 * 1497116 * 2
def baseEnd_1497116 : Nat := 256246701178889920154965

theorem tailTrace_1497116 : CollatzResearch.WordTrace tailWord_1497116 prefixEnd_1497116 256246701178889920154965 := by
  unfold tailWord_1497116
  simp only [CollatzResearch.WordTrace]
  refine ⟨27302153222105946950811601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36402870962807929267748801 27302153222105946950811601)
  ·
    refine ⟨20476614916579460213108701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27302153222105946950811601 20476614916579460213108701)
    ·
      refine ⟨7678730593717297579915763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20476614916579460213108701 7678730593717297579915763)
      ·
        refine ⟨11518095890575946369873645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7678730593717297579915763 11518095890575946369873645)
        ·
          refine ⟨4319285958965979888702617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11518095890575946369873645 4319285958965979888702617)
          ·
            refine ⟨3239464469224484916526963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4319285958965979888702617 3239464469224484916526963)
            ·
              refine ⟨4859196703836727374790445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3239464469224484916526963 4859196703836727374790445)
              ·
                refine ⟨1822198763938772765546417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4859196703836727374790445 1822198763938772765546417)
                ·
                  refine ⟨1366649072954079574159813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1822198763938772765546417 1366649072954079574159813)
                  ·
                    refine ⟨256246701178889920154965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1366649072954079574159813 256246701178889920154965)
                    ·
                      rfl

theorem cell23_1497116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_1497116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497116 prefixEnd_1497116 := by exact prefixLift 1497116
  have htrace : WordTrace (prefixWord ++ tailWord_1497116) baseStart_1497116 baseEnd_1497116 := by
    simpa [prefixWord, tailWord_1497116, baseEnd_1497116] using wordTrace_append hprefix tailTrace_1497116
  have hstable : (prefixWord ++ tailWord_1497116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497116).length < 2 ^ (prefixWord ++ tailWord_1497116).sum := by decide
  have hdescent : baseEnd_1497116 < baseStart_1497116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497139 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 6, 1, 3]
def baseStart_1497139 : Nat := 118140960795 + 1497139 * 2 ^ 59
def prefixEnd_1497139 : Nat := 4983230072969 + 3 ^ 40 * 1497139 * 2
def baseEnd_1497139 : Nat := 768751913591723170477289

theorem tailTrace_1497139 : CollatzResearch.WordTrace tailWord_1497139 prefixEnd_1497139 768751913591723170477289 := by
  unfold tailWord_1497139
  simp only [CollatzResearch.WordTrace]
  refine ⟨54605145323128568829710471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36403430215419045886473647 54605145323128568829710471)
  ·
    refine ⟨81907717984692853244565707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54605145323128568829710471 81907717984692853244565707)
    ·
      refine ⟨122861576977039279866848561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81907717984692853244565707 122861576977039279866848561)
      ·
        refine ⟨92146182732779459900136421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122861576977039279866848561 92146182732779459900136421)
        ·
          refine ⟨17277409262396148731275579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92146182732779459900136421 17277409262396148731275579)
          ·
            refine ⟨25916113893594223096913369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17277409262396148731275579 25916113893594223096913369)
            ·
              refine ⟨19437085420195667322685027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25916113893594223096913369 19437085420195667322685027)
              ·
                refine ⟨29155628130293500984027541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19437085420195667322685027 29155628130293500984027541)
                ·
                  refine ⟨1366670068607507858626291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29155628130293500984027541 1366670068607507858626291)
                  ·
                    refine ⟨2050005102911261787939437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1366670068607507858626291 2050005102911261787939437)
                    ·
                      refine ⟨768751913591723170477289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2050005102911261787939437 768751913591723170477289)
                      ·
                        rfl

theorem cell23_1497139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 1, 3].length) (baseStart_1497139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497139 prefixEnd_1497139 := by exact prefixLift 1497139
  have htrace : WordTrace (prefixWord ++ tailWord_1497139) baseStart_1497139 baseEnd_1497139 := by
    simpa [prefixWord, tailWord_1497139, baseEnd_1497139] using wordTrace_append hprefix tailTrace_1497139
  have hstable : (prefixWord ++ tailWord_1497139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497139).length < 2 ^ (prefixWord ++ tailWord_1497139).sum := by decide
  have hdescent : baseEnd_1497139 < baseStart_1497139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497140 : List Nat := [2, 5, 1, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_1497140 : Nat := 118140960795 + 1497140 * 2 ^ 59
def prefixEnd_1497140 : Nat := 4983230072969 + 3 ^ 40 * 1497140 * 2
def baseEnd_1497140 : Nat := 768752427072377666564785

theorem tailTrace_1497140 : CollatzResearch.WordTrace tailWord_1497140 prefixEnd_1497140 768752427072377666564785 := by
  unfold tailWord_1497140
  simp only [CollatzResearch.WordTrace]
  refine ⟨27302590898062473000248437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36403454530749964000331249 27302590898062473000248437)
  ·
    refine ⟨2559617896693356843773291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27302590898062473000248437 2559617896693356843773291)
    ·
      refine ⟨3839426845040035265659937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2559617896693356843773291 3839426845040035265659937)
      ·
        refine ⟨2879570133780026449244953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3839426845040035265659937 2879570133780026449244953)
        ·
          refine ⟨2159677600335019836933715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2879570133780026449244953 2159677600335019836933715)
          ·
            refine ⟨3239516400502529755400573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2159677600335019836933715 3239516400502529755400573)
            ·
              refine ⟨1214818650188448658275215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3239516400502529755400573 1214818650188448658275215)
              ·
                refine ⟨1822227975282672987412823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1214818650188448658275215 1822227975282672987412823)
                ·
                  refine ⟨2733341962924009481119235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822227975282672987412823 2733341962924009481119235)
                  ·
                    refine ⟨4100012944386014221678853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2733341962924009481119235 4100012944386014221678853)
                    ·
                      refine ⟨768752427072377666564785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4100012944386014221678853 768752427072377666564785)
                      ·
                        rfl

theorem cell23_1497140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_1497140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497140 prefixEnd_1497140 := by exact prefixLift 1497140
  have htrace : WordTrace (prefixWord ++ tailWord_1497140) baseStart_1497140 baseEnd_1497140 := by
    simpa [prefixWord, tailWord_1497140, baseEnd_1497140] using wordTrace_append hprefix tailTrace_1497140
  have hstable : (prefixWord ++ tailWord_1497140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497140).length < 2 ^ (prefixWord ++ tailWord_1497140).sum := by decide
  have hdescent : baseEnd_1497140 < baseStart_1497140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497166 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2]
def baseStart_1497166 : Nat := 118140960795 + 1497166 * 2 ^ 59
def prefixEnd_1497166 : Nat := 4983230072969 + 3 ^ 40 * 1497166 * 2
def baseEnd_1497166 : Nat := 768765777569394564839665

theorem tailTrace_1497166 : CollatzResearch.WordTrace tailWord_1497166 prefixEnd_1497166 768765777569394564839665 := by
  unfold tailWord_1497166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6825766261753844055117919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36404086729353834960628901 6825766261753844055117919)
  ·
    refine ⟨10238649392630766082676879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6825766261753844055117919 10238649392630766082676879)
    ·
      refine ⟨15357974088946149124015319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10238649392630766082676879 15357974088946149124015319)
      ·
        refine ⟨23036961133419223686022979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15357974088946149124015319 23036961133419223686022979)
        ·
          refine ⟨34555441700128835529034469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23036961133419223686022979 34555441700128835529034469)
          ·
            refine ⟨6479145318774156661693963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34555441700128835529034469 6479145318774156661693963)
            ·
              refine ⟨9718717978161234992540945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6479145318774156661693963 9718717978161234992540945)
              ·
                refine ⟨7289038483620926244405709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9718717978161234992540945 7289038483620926244405709)
                ·
                  refine ⟨2733389431357847341652141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7289038483620926244405709 2733389431357847341652141)
                  ·
                    refine ⟨1025021036759192753119553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2733389431357847341652141 1025021036759192753119553)
                    ·
                      refine ⟨768765777569394564839665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025021036759192753119553 768765777569394564839665)
                      ·
                        rfl

theorem cell23_1497166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_1497166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497166 prefixEnd_1497166 := by exact prefixLift 1497166
  have htrace : WordTrace (prefixWord ++ tailWord_1497166) baseStart_1497166 baseEnd_1497166 := by
    simpa [prefixWord, tailWord_1497166, baseEnd_1497166] using wordTrace_append hprefix tailTrace_1497166
  have hstable : (prefixWord ++ tailWord_1497166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497166).length < 2 ^ (prefixWord ++ tailWord_1497166).sum := by decide
  have hdescent : baseEnd_1497166 < baseStart_1497166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497196 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 1, 4, 2]
def baseStart_1497196 : Nat := 118140960795 + 1497196 * 2 ^ 59
def prefixEnd_1497196 : Nat := 4983230072969 + 3 ^ 40 * 1497196 * 2
def baseEnd_1497196 : Nat := 768781181989029447464527

theorem tailTrace_1497196 : CollatzResearch.WordTrace tailWord_1497196 prefixEnd_1497196 768781181989029447464527 := by
  unfold tailWord_1497196
  simp only [CollatzResearch.WordTrace]
  refine ⟨27303612141961033782267721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36404816189281378376356961 27303612141961033782267721)
  ·
    refine ⟨20477709106470775336700791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27303612141961033782267721 20477709106470775336700791)
    ·
      refine ⟨30716563659706163005051187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20477709106470775336700791 30716563659706163005051187)
      ·
        refine ⟨46074845489559244507576781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30716563659706163005051187 46074845489559244507576781)
        ·
          refine ⟨17278067058584716690341293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46074845489559244507576781 17278067058584716690341293)
          ·
            refine ⟨6479275146969268758877985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17278067058584716690341293 6479275146969268758877985)
            ·
              refine ⟨4859456360226951569158489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6479275146969268758877985 4859456360226951569158489)
              ·
                refine ⟨3644592270170213676868867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4859456360226951569158489 3644592270170213676868867)
                ·
                  refine ⟨5466888405255320515303301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3644592270170213676868867 5466888405255320515303301)
                  ·
                    refine ⟨1025041575985372596619369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5466888405255320515303301 1025041575985372596619369)
                    ·
                      refine ⟨768781181989029447464527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025041575985372596619369 768781181989029447464527)
                      ·
                        rfl

theorem cell23_1497196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 4, 2].length) (baseStart_1497196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497196 prefixEnd_1497196 := by exact prefixLift 1497196
  have htrace : WordTrace (prefixWord ++ tailWord_1497196) baseStart_1497196 baseEnd_1497196 := by
    simpa [prefixWord, tailWord_1497196, baseEnd_1497196] using wordTrace_append hprefix tailTrace_1497196
  have hstable : (prefixWord ++ tailWord_1497196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497196).length < 2 ^ (prefixWord ++ tailWord_1497196).sum := by decide
  have hdescent : baseEnd_1497196 < baseStart_1497196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497200 : List Nat := [2, 1, 1, 1, 5, 4, 2, 1, 1, 3, 2]
def baseStart_1497200 : Nat := 118140960795 + 1497200 * 2 ^ 59
def prefixEnd_1497200 : Nat := 4983230072969 + 3 ^ 40 * 1497200 * 2
def baseEnd_1497200 : Nat := 768783235911647431814509

theorem tailTrace_1497200 : CollatzResearch.WordTrace tailWord_1497200 prefixEnd_1497200 768783235911647431814509 := by
  unfold tailWord_1497200
  simp only [CollatzResearch.WordTrace]
  refine ⟨27303685087953788123840527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36404913450605050831787369 27303685087953788123840527)
  ·
    refine ⟨40955527631930682185760791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27303685087953788123840527 40955527631930682185760791)
    ·
      refine ⟨61433291447896023278641187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40955527631930682185760791 61433291447896023278641187)
      ·
        refine ⟨92149937171844034917961781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61433291447896023278641187 92149937171844034917961781)
        ·
          refine ⟨8639056609860378273558917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92149937171844034917961781 8639056609860378273558917)
          ·
            refine ⟨1619823114348820926292297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8639056609860378273558917 1619823114348820926292297)
            ·
              refine ⟨1214867335761615694719223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1619823114348820926292297 1214867335761615694719223)
              ·
                refine ⟨1822301003642423542078835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1214867335761615694719223 1822301003642423542078835)
                ·
                  refine ⟨2733451505463635313118253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822301003642423542078835 2733451505463635313118253)
                  ·
                    refine ⟨1025044314548863242419345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2733451505463635313118253 1025044314548863242419345)
                    ·
                      refine ⟨768783235911647431814509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025044314548863242419345 768783235911647431814509)
                      ·
                        rfl

theorem cell23_1497200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 1, 3, 2].length) (baseStart_1497200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497200 prefixEnd_1497200 := by exact prefixLift 1497200
  have htrace : WordTrace (prefixWord ++ tailWord_1497200) baseStart_1497200 baseEnd_1497200 := by
    simpa [prefixWord, tailWord_1497200, baseEnd_1497200] using wordTrace_append hprefix tailTrace_1497200
  have hstable : (prefixWord ++ tailWord_1497200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497200).length < 2 ^ (prefixWord ++ tailWord_1497200).sum := by decide
  have hdescent : baseEnd_1497200 < baseStart_1497200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497209 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 2, 2, 4]
def baseStart_1497209 : Nat := 118140960795 + 1497209 * 2 ^ 59
def prefixEnd_1497209 : Nat := 4983230072969 + 3 ^ 40 * 1497209 * 2
def baseEnd_1497209 : Nat := 768787857237537896601967

theorem tailTrace_1497209 : CollatzResearch.WordTrace tailWord_1497209 prefixEnd_1497209 768787857237537896601967 := by
  unfold tailWord_1497209
  simp only [CollatzResearch.WordTrace]
  refine ⟨54607698432874970784758681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36405132288583313856505787 54607698432874970784758681)
  ·
    refine ⟨40955773824656228088569011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54607698432874970784758681 40955773824656228088569011)
    ·
      refine ⟨61433660736984342132853517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40955773824656228088569011 61433660736984342132853517)
      ·
        refine ⟨23037622776369128299820069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61433660736984342132853517 23037622776369128299820069)
        ·
          refine ⟨4319554270569211556216263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23037622776369128299820069 4319554270569211556216263)
          ·
            refine ⟨6479331405853817334324395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319554270569211556216263 6479331405853817334324395)
            ·
              refine ⟨9718997108780726001486593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6479331405853817334324395 9718997108780726001486593)
              ·
                refine ⟨7289247831585544501114945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9718997108780726001486593 7289247831585544501114945)
                ·
                  refine ⟨5466935873689158375836209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7289247831585544501114945 5466935873689158375836209)
                  ·
                    refine ⟨4100201905266868781877157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5466935873689158375836209 4100201905266868781877157)
                    ·
                      refine ⟨768787857237537896601967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4100201905266868781877157 768787857237537896601967)
                      ·
                        rfl

theorem cell23_1497209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_1497209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497209 prefixEnd_1497209 := by exact prefixLift 1497209
  have htrace : WordTrace (prefixWord ++ tailWord_1497209) baseStart_1497209 baseEnd_1497209 := by
    simpa [prefixWord, tailWord_1497209, baseEnd_1497209] using wordTrace_append hprefix tailTrace_1497209
  have hstable : (prefixWord ++ tailWord_1497209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497209).length < 2 ^ (prefixWord ++ tailWord_1497209).sum := by decide
  have hdescent : baseEnd_1497209 < baseStart_1497209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497213 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 4, 2, 2]
def baseStart_1497213 : Nat := 118140960795 + 1497213 * 2 ^ 59
def prefixEnd_1497213 : Nat := 4983230072969 + 3 ^ 40 * 1497213 * 2
def baseEnd_1497213 : Nat := 768789911160155880951949

theorem tailTrace_1497213 : CollatzResearch.WordTrace tailWord_1497213 prefixEnd_1497213 768789911160155880951949 := by
  unfold tailWord_1497213
  simp only [CollatzResearch.WordTrace]
  refine ⟨54607844324860479467904293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36405229549906986311936195 54607844324860479467904293)
  ·
    refine ⟨10238970810911339900232055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54607844324860479467904293 10238970810911339900232055)
    ·
      refine ⟨15358456216367009850348083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10238970810911339900232055 15358456216367009850348083)
      ·
        refine ⟨23037684324550514775522125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15358456216367009850348083 23037684324550514775522125)
        ·
          refine ⟨8639131621706443040820797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23037684324550514775522125 8639131621706443040820797)
          ·
            refine ⟨3239674358139916140307799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8639131621706443040820797 3239674358139916140307799)
            ·
              refine ⟨4859511537209874210461699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3239674358139916140307799 4859511537209874210461699)
              ·
                refine ⟨7289267305814811315692549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4859511537209874210461699 7289267305814811315692549)
                ·
                  refine ⟨1366737619840277121692353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7289267305814811315692549 1366737619840277121692353)
                  ·
                    refine ⟨1025053214880207841269265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1366737619840277121692353 1025053214880207841269265)
                    ·
                      refine ⟨768789911160155880951949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025053214880207841269265 768789911160155880951949)
                      ·
                        rfl

theorem cell23_1497213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_1497213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497213 prefixEnd_1497213 := by exact prefixLift 1497213
  have htrace : WordTrace (prefixWord ++ tailWord_1497213) baseStart_1497213 baseEnd_1497213 := by
    simpa [prefixWord, tailWord_1497213, baseEnd_1497213] using wordTrace_append hprefix tailTrace_1497213
  have hstable : (prefixWord ++ tailWord_1497213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497213).length < 2 ^ (prefixWord ++ tailWord_1497213).sum := by decide
  have hdescent : baseEnd_1497213 < baseStart_1497213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497219 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 7]
def baseStart_1497219 : Nat := 118140960795 + 1497219 * 2 ^ 59
def prefixEnd_1497219 : Nat := 4983230072969 + 3 ^ 40 * 1497219 * 2
def baseEnd_1497219 : Nat := 85421443560453650830769

theorem tailTrace_1497219 : CollatzResearch.WordTrace tailWord_1497219 prefixEnd_1497219 85421443560453650830769 := by
  unfold tailWord_1497219
  simp only [CollatzResearch.WordTrace]
  refine ⟨54608063162838742492622711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36405375441892494995081807 54608063162838742492622711)
  ·
    refine ⟨81912094744258113738934067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54608063162838742492622711 81912094744258113738934067)
    ·
      refine ⟨122868142116387170608401101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81912094744258113738934067 122868142116387170608401101)
      ·
        refine ⟨46075553293645188978150413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122868142116387170608401101 46075553293645188978150413)
        ·
          refine ⟨17278332485116945866806405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46075553293645188978150413 17278332485116945866806405)
          ·
            refine ⟨3239687340959427350026201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17278332485116945866806405 3239687340959427350026201)
            ·
              refine ⟨2429765505719570512519651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3239687340959427350026201 2429765505719570512519651)
              ·
                refine ⟨3644648258579355768779477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429765505719570512519651 3644648258579355768779477)
                ·
                  refine ⟨85421443560453650830769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3644648258579355768779477 85421443560453650830769)
                  ·
                    rfl

theorem cell23_1497219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 7].length) (baseStart_1497219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497219 prefixEnd_1497219 := by exact prefixLift 1497219
  have htrace : WordTrace (prefixWord ++ tailWord_1497219) baseStart_1497219 baseEnd_1497219 := by
    simpa [prefixWord, tailWord_1497219, baseEnd_1497219] using wordTrace_append hprefix tailTrace_1497219
  have hstable : (prefixWord ++ tailWord_1497219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497219).length < 2 ^ (prefixWord ++ tailWord_1497219).sum := by decide
  have hdescent : baseEnd_1497219 < baseStart_1497219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497230 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2]
def baseStart_1497230 : Nat := 118140960795 + 1497230 * 2 ^ 59
def prefixEnd_1497230 : Nat := 4983230072969 + 3 ^ 40 * 1497230 * 2
def baseEnd_1497230 : Nat := 768798640331282314439371

theorem tailTrace_1497230 : CollatzResearch.WordTrace tailWord_1497230 prefixEnd_1497230 768798640331282314439371 := by
  unfold tailWord_1497230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6826058045724861421409143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36405642910532594247515429 6826058045724861421409143)
  ·
    refine ⟨10239087068587292132113715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6826058045724861421409143 10239087068587292132113715)
    ·
      refine ⟨15358630602880938198170573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10239087068587292132113715 15358630602880938198170573)
      ·
        refine ⟨5759486476080351824313965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15358630602880938198170573 5759486476080351824313965)
        ·
          refine ⟨2159807428530131934117737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5759486476080351824313965 2159807428530131934117737)
          ·
            refine ⟨1619855571397598950588303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2159807428530131934117737 1619855571397598950588303)
            ·
              refine ⟨2429783357096398425882455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619855571397598950588303 2429783357096398425882455)
              ·
                refine ⟨3644675035644597638823683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429783357096398425882455 3644675035644597638823683)
                ·
                  refine ⟨5467012553466896458235525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3644675035644597638823683 5467012553466896458235525)
                  ·
                    refine ⟨1025064853775043085919161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5467012553466896458235525 1025064853775043085919161)
                    ·
                      refine ⟨768798640331282314439371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025064853775043085919161 768798640331282314439371)
                      ·
                        rfl

theorem cell23_1497230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_1497230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497230 prefixEnd_1497230 := by exact prefixLift 1497230
  have htrace : WordTrace (prefixWord ++ tailWord_1497230) baseStart_1497230 baseEnd_1497230 := by
    simpa [prefixWord, tailWord_1497230, baseEnd_1497230] using wordTrace_append hprefix tailTrace_1497230
  have hstable : (prefixWord ++ tailWord_1497230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497230).length < 2 ^ (prefixWord ++ tailWord_1497230).sum := by decide
  have hdescent : baseEnd_1497230 < baseStart_1497230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497232 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 3, 7]
def baseStart_1497232 : Nat := 118140960795 + 1497232 * 2 ^ 59
def prefixEnd_1497232 : Nat := 4983230072969 + 3 ^ 40 * 1497232 * 2
def baseEnd_1497232 : Nat := 256266555764197102204787

theorem tailTrace_1497232 : CollatzResearch.WordTrace tailWord_1497232 prefixEnd_1497232 256266555764197102204787 := by
  unfold tailWord_1497232
  simp only [CollatzResearch.WordTrace]
  refine ⟨27304268655895822856422975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36405691541194430475230633 27304268655895822856422975)
  ·
    refine ⟨40956402983843734284634463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27304268655895822856422975 40956402983843734284634463)
    ·
      refine ⟨61434604475765601426951695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40956402983843734284634463 61434604475765601426951695)
      ·
        refine ⟨92151906713648402140427543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61434604475765601426951695 92151906713648402140427543)
        ·
          refine ⟨138227860070472603210641315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92151906713648402140427543 138227860070472603210641315)
          ·
            refine ⟨207341790105708904815961973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138227860070472603210641315 207341790105708904815961973)
            ·
              refine ⟨19438292822410209826496435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 207341790105708904815961973 19438292822410209826496435)
              ·
                refine ⟨29157439233615314739744653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19438292822410209826496435 29157439233615314739744653)
                ·
                  refine ⟨10934039712605743027404245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29157439233615314739744653 10934039712605743027404245)
                  ·
                    refine ⟨256266555764197102204787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10934039712605743027404245 256266555764197102204787)
                    ·
                      rfl

theorem cell23_1497232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3, 7].length) (baseStart_1497232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497232 prefixEnd_1497232 := by exact prefixLift 1497232
  have htrace : WordTrace (prefixWord ++ tailWord_1497232) baseStart_1497232 baseEnd_1497232 := by
    simpa [prefixWord, tailWord_1497232, baseEnd_1497232] using wordTrace_append hprefix tailTrace_1497232
  have hstable : (prefixWord ++ tailWord_1497232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497232).length < 2 ^ (prefixWord ++ tailWord_1497232).sum := by decide
  have hdescent : baseEnd_1497232 < baseStart_1497232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497249 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 1, 7]
def baseStart_1497249 : Nat := 118140960795 + 1497249 * 2 ^ 59
def prefixEnd_1497249 : Nat := 4983230072969 + 3 ^ 40 * 1497249 * 2
def baseEnd_1497249 : Nat := 256269465487905913367261

theorem tailTrace_1497249 : CollatzResearch.WordTrace tailWord_1497249 prefixEnd_1497249 256269465487905913367261 := by
  unfold tailWord_1497249
  simp only [CollatzResearch.WordTrace]
  refine ⟨54609157352730057616214801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36406104901820038410809867 54609157352730057616214801)
  ·
    refine ⟨40956868014547543212161101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54609157352730057616214801 40956868014547543212161101)
    ·
      refine ⟨15358825505455328704560413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40956868014547543212161101 15358825505455328704560413)
      ·
        refine ⟨5759559564545748264210155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15358825505455328704560413 5759559564545748264210155)
        ·
          refine ⟨8639339346818622396315233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5759559564545748264210155 8639339346818622396315233)
          ·
            refine ⟨6479504510113966797236425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8639339346818622396315233 6479504510113966797236425)
            ·
              refine ⟨4859628382585475097927319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6479504510113966797236425 4859628382585475097927319)
              ·
                refine ⟨7289442573878212646890979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4859628382585475097927319 7289442573878212646890979)
                ·
                  refine ⟨10934163860817318970336469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7289442573878212646890979 10934163860817318970336469)
                  ·
                    refine ⟨256269465487905913367261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10934163860817318970336469 256269465487905913367261)
                    ·
                      rfl

theorem cell23_1497249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_1497249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497249 prefixEnd_1497249 := by exact prefixLift 1497249
  have htrace : WordTrace (prefixWord ++ tailWord_1497249) baseStart_1497249 baseEnd_1497249 := by
    simpa [prefixWord, tailWord_1497249, baseEnd_1497249] using wordTrace_append hprefix tailTrace_1497249
  have hstable : (prefixWord ++ tailWord_1497249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497249).length < 2 ^ (prefixWord ++ tailWord_1497249).sum := by decide
  have hdescent : baseEnd_1497249 < baseStart_1497249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497276 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 1, 2, 5]
def baseStart_1497276 : Nat := 118140960795 + 1497276 * 2 ^ 59
def prefixEnd_1497276 : Nat := 4983230072969 + 3 ^ 40 * 1497276 * 2
def baseEnd_1497276 : Nat := 768822260441389134464159

theorem tailTrace_1497276 : CollatzResearch.WordTrace tailWord_1497276 prefixEnd_1497276 768822260441389134464159 := by
  unfold tailWord_1497276
  simp only [CollatzResearch.WordTrace]
  refine ⟨27305071061816120613723841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36406761415754827484965121 27305071061816120613723841)
  ·
    refine ⟨20478803296362090460292881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27305071061816120613723841 20478803296362090460292881)
    ·
      refine ⟨15359102472271567845219661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20478803296362090460292881 15359102472271567845219661)
      ·
        refine ⟨5759663427101837941957373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15359102472271567845219661 5759663427101837941957373)
        ·
          refine ⟨2159873785163189228234015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5759663427101837941957373 2159873785163189228234015)
          ·
            refine ⟨3239810677744783842351023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2159873785163189228234015 3239810677744783842351023)
            ·
              refine ⟨4859716016617175763526535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3239810677744783842351023 4859716016617175763526535)
              ·
                refine ⟨7289574024925763645289803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4859716016617175763526535 7289574024925763645289803)
                ·
                  refine ⟨10934361037388645467934705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7289574024925763645289803 10934361037388645467934705)
                  ·
                    refine ⟨8200770778041484100951029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10934361037388645467934705 8200770778041484100951029)
                    ·
                      refine ⟨768822260441389134464159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8200770778041484100951029 768822260441389134464159)
                      ·
                        rfl

theorem cell23_1497276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_1497276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497276 prefixEnd_1497276 := by exact prefixLift 1497276
  have htrace : WordTrace (prefixWord ++ tailWord_1497276) baseStart_1497276 baseEnd_1497276 := by
    simpa [prefixWord, tailWord_1497276, baseEnd_1497276] using wordTrace_append hprefix tailTrace_1497276
  have hstable : (prefixWord ++ tailWord_1497276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497276).length < 2 ^ (prefixWord ++ tailWord_1497276).sum := by decide
  have hdescent : baseEnd_1497276 < baseStart_1497276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497281 : List Nat := [1, 2, 6, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_1497281 : Nat := 118140960795 + 1497281 * 2 ^ 59
def prefixEnd_1497281 : Nat := 4983230072969 + 3 ^ 40 * 1497281 * 2
def baseEnd_1497281 : Nat := 768824827844661614901637

theorem tailTrace_1497281 : CollatzResearch.WordTrace tailWord_1497281 prefixEnd_1497281 768824827844661614901637 := by
  unfold tailWord_1497281
  simp only [CollatzResearch.WordTrace]
  refine ⟨54610324488614127081379697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36406882992409418054253131 54610324488614127081379697)
  ·
    refine ⟨40957743366460595311034773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54610324488614127081379697 40957743366460595311034773)
    ·
      refine ⟨1919894220302840405204755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40957743366460595311034773 1919894220302840405204755)
      ·
        refine ⟨2879841330454260607807133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1919894220302840405204755 2879841330454260607807133)
        ·
          refine ⟨1079940498920347727927675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2879841330454260607807133 1079940498920347727927675)
          ·
            refine ⟨1619910748380521591891513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079940498920347727927675 1619910748380521591891513)
            ·
              refine ⟨1214933061285391193918635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1619910748380521591891513 1214933061285391193918635)
              ·
                refine ⟨1822399591928086790877953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1214933061285391193918635 1822399591928086790877953)
                ·
                  refine ⟨1366799693946065093158465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1822399591928086790877953 1366799693946065093158465)
                  ·
                    refine ⟨1025099770459548819868849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1366799693946065093158465 1025099770459548819868849)
                    ·
                      refine ⟨768824827844661614901637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025099770459548819868849 768824827844661614901637)
                      ·
                        rfl

theorem cell23_1497281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_1497281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497281 prefixEnd_1497281 := by exact prefixLift 1497281
  have htrace : WordTrace (prefixWord ++ tailWord_1497281) baseStart_1497281 baseEnd_1497281 := by
    simpa [prefixWord, tailWord_1497281, baseEnd_1497281] using wordTrace_append hprefix tailTrace_1497281
  have hstable : (prefixWord ++ tailWord_1497281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497281).length < 2 ^ (prefixWord ++ tailWord_1497281).sum := by decide
  have hdescent : baseEnd_1497281 < baseStart_1497281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497289 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 1, 4, 3]
def baseStart_1497289 : Nat := 118140960795 + 1497289 * 2 ^ 59
def prefixEnd_1497289 : Nat := 4983230072969 + 3 ^ 40 * 1497289 * 2
def baseEnd_1497289 : Nat := 768828935689897583601599

theorem tailTrace_1497289 : CollatzResearch.WordTrace tailWord_1497289 prefixEnd_1497289 768828935689897583601599 := by
  unfold tailWord_1497289
  simp only [CollatzResearch.WordTrace]
  refine ⟨54610616272585144447670921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36407077515056762965113947 54610616272585144447670921)
  ·
    refine ⟨40957962204438858335753191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54610616272585144447670921 40957962204438858335753191)
    ·
      refine ⟨61436943306658287503629787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40957962204438858335753191 61436943306658287503629787)
      ·
        refine ⟨92155414959987431255444681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61436943306658287503629787 92155414959987431255444681)
        ·
          refine ⟨69116561219990573441583511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92155414959987431255444681 69116561219990573441583511)
          ·
            refine ⟨103674841829985860162375267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69116561219990573441583511 103674841829985860162375267)
            ·
              refine ⟨155512262744978790243562901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103674841829985860162375267 155512262744978790243562901)
              ·
                refine ⟨7289637316170880792667011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 155512262744978790243562901 7289637316170880792667011)
                ·
                  refine ⟨10934455974256321189000517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7289637316170880792667011 10934455974256321189000517)
                  ·
                    refine ⟨2050210495173060222937597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10934455974256321189000517 2050210495173060222937597)
                    ·
                      refine ⟨768828935689897583601599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2050210495173060222937597 768828935689897583601599)
                      ·
                        rfl

theorem cell23_1497289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 4, 3].length) (baseStart_1497289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497289 prefixEnd_1497289 := by exact prefixLift 1497289
  have htrace : WordTrace (prefixWord ++ tailWord_1497289) baseStart_1497289 baseEnd_1497289 := by
    simpa [prefixWord, tailWord_1497289, baseEnd_1497289] using wordTrace_append hprefix tailTrace_1497289
  have hstable : (prefixWord ++ tailWord_1497289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497289).length < 2 ^ (prefixWord ++ tailWord_1497289).sum := by decide
  have hdescent : baseEnd_1497289 < baseStart_1497289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497306 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3]
def baseStart_1497306 : Nat := 118140960795 + 1497306 * 2 ^ 59
def prefixEnd_1497306 : Nat := 4983230072969 + 3 ^ 40 * 1497306 * 2
def baseEnd_1497306 : Nat := 768837664861024017089021

theorem tailTrace_1497306 : CollatzResearch.WordTrace tailWord_1497306 prefixEnd_1497306 768837664861024017089021 := by
  unfold tailWord_1497306
  simp only [CollatzResearch.WordTrace]
  refine ⟨13652809078380889087759943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36407490875682370900693181 13652809078380889087759943)
  ·
    refine ⟨20479213617571333631639915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13652809078380889087759943 20479213617571333631639915)
    ·
      refine ⟨30718820426357000447459873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20479213617571333631639915 30718820426357000447459873)
      ·
        refine ⟨23039115319767750335594905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30718820426357000447459873 23039115319767750335594905)
        ·
          refine ⟨17279336489825812751696179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23039115319767750335594905 17279336489825812751696179)
          ·
            refine ⟨25919004734738719127544269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17279336489825812751696179 25919004734738719127544269)
            ·
              refine ⟨9719626775527019672829101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25919004734738719127544269 9719626775527019672829101)
              ·
                refine ⟨3644860040822632377310913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9719626775527019672829101 3644860040822632377310913)
                ·
                  refine ⟨2733645030616974282983185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3644860040822632377310913 2733645030616974282983185)
                  ·
                    refine ⟨2050233772962730712237389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2733645030616974282983185 2050233772962730712237389)
                    ·
                      refine ⟨768837664861024017089021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2050233772962730712237389 768837664861024017089021)
                      ·
                        rfl

theorem cell23_1497306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_1497306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497306 prefixEnd_1497306 := by exact prefixLift 1497306
  have htrace : WordTrace (prefixWord ++ tailWord_1497306) baseStart_1497306 baseEnd_1497306 := by
    simpa [prefixWord, tailWord_1497306, baseEnd_1497306] using wordTrace_append hprefix tailTrace_1497306
  have hstable : (prefixWord ++ tailWord_1497306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497306).length < 2 ^ (prefixWord ++ tailWord_1497306).sum := by decide
  have hdescent : baseEnd_1497306 < baseStart_1497306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497313 : List Nat := [1, 2, 3, 1, 3, 1, 2, 5, 1, 4]
def baseStart_1497313 : Nat := 118140960795 + 1497313 * 2 ^ 59
def prefixEnd_1497313 : Nat := 4983230072969 + 3 ^ 40 * 1497313 * 2
def baseEnd_1497313 : Nat := 256280419741868496567163

theorem tailTrace_1497313 : CollatzResearch.WordTrace tailWord_1497313 prefixEnd_1497313 256280419741868496567163 := by
  unfold tailWord_1497313
  simp only [CollatzResearch.WordTrace]
  refine ⟨54611491624498196546544593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36407661082998797697696395 54611491624498196546544593)
  ·
    refine ⟨40958618718373647409908445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54611491624498196546544593 40958618718373647409908445)
    ·
      refine ⟨15359482019390117778715667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40958618718373647409908445 15359482019390117778715667)
      ·
        refine ⟨23039223029085176668073501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15359482019390117778715667 23039223029085176668073501)
        ·
          refine ⟨8639708635906941250527563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23039223029085176668073501 8639708635906941250527563)
          ·
            refine ⟨12959562953860411875791345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8639708635906941250527563 12959562953860411875791345)
            ·
              refine ⟨9719672215395308906843509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12959562953860411875791345 9719672215395308906843509)
              ·
                refine ⟨911219270193310210016579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9719672215395308906843509 911219270193310210016579)
                ·
                  refine ⟨1366828905289965315024869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911219270193310210016579 1366828905289965315024869)
                  ·
                    refine ⟨256280419741868496567163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1366828905289965315024869 256280419741868496567163)
                    ·
                      rfl

theorem cell23_1497313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_1497313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497313 prefixEnd_1497313 := by exact prefixLift 1497313
  have htrace : WordTrace (prefixWord ++ tailWord_1497313) baseStart_1497313 baseEnd_1497313 := by
    simpa [prefixWord, tailWord_1497313, baseEnd_1497313] using wordTrace_append hprefix tailTrace_1497313
  have hstable : (prefixWord ++ tailWord_1497313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497313).length < 2 ^ (prefixWord ++ tailWord_1497313).sum := by decide
  have hdescent : baseEnd_1497313 < baseStart_1497313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497330 : List Nat := [3, 2, 1, 3, 2, 2, 1, 4, 1, 4]
def baseStart_1497330 : Nat := 118140960795 + 1497330 * 2 ^ 59
def prefixEnd_1497330 : Nat := 4983230072969 + 3 ^ 40 * 1497330 * 2
def baseEnd_1497330 : Nat := 256283329465577307729637

theorem tailTrace_1497330 : CollatzResearch.WordTrace tailWord_1497330 prefixEnd_1497330 256283329465577307729637 := by
  unfold tailWord_1497330
  simp only [CollatzResearch.WordTrace]
  refine ⟨13653027916359152112478361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36408074443624405633275629 13653027916359152112478361)
  ·
    refine ⟨10239770937269364084358771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13653027916359152112478361 10239770937269364084358771)
    ·
      refine ⟨15359656405904046126538157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10239770937269364084358771 15359656405904046126538157)
      ·
        refine ⟨5759871152214017297451809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15359656405904046126538157 5759871152214017297451809)
        ·
          refine ⟨4319903364160512973088857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5759871152214017297451809 4319903364160512973088857)
          ·
            refine ⟨3239927523120384729816643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4319903364160512973088857 3239927523120384729816643)
            ·
              refine ⟨4859891284680577094724965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3239927523120384729816643 4859891284680577094724965)
              ·
                refine ⟨911229615877608205260931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4859891284680577094724965 911229615877608205260931)
                ·
                  refine ⟨1366844423816412307891397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911229615877608205260931 1366844423816412307891397)
                  ·
                    refine ⟨256283329465577307729637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1366844423816412307891397 256283329465577307729637)
                    ·
                      rfl

theorem cell23_1497330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_1497330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497330 prefixEnd_1497330 := by exact prefixLift 1497330
  have htrace : WordTrace (prefixWord ++ tailWord_1497330) baseStart_1497330 baseEnd_1497330 := by
    simpa [prefixWord, tailWord_1497330, baseEnd_1497330] using wordTrace_append hprefix tailTrace_1497330
  have hstable : (prefixWord ++ tailWord_1497330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497330).length < 2 ^ (prefixWord ++ tailWord_1497330).sum := by decide
  have hdescent : baseEnd_1497330 < baseStart_1497330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497336 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 7, 1, 3]
def baseStart_1497336 : Nat := 118140960795 + 1497336 * 2 ^ 59
def prefixEnd_1497336 : Nat := 4983230072969 + 3 ^ 40 * 1497336 * 2
def baseEnd_1497336 : Nat := 768853069280658899713883

theorem tailTrace_1497336 : CollatzResearch.WordTrace tailWord_1497336 prefixEnd_1497336 768853069280658899713883 := by
  unfold tailWord_1497336
  simp only [CollatzResearch.WordTrace]
  refine ⟨27306165251707435737315931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36408220335609914316421241 27306165251707435737315931)
  ·
    refine ⟨40959247877561153605973897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27306165251707435737315931 40959247877561153605973897)
    ·
      refine ⟨30719435908170865204480423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40959247877561153605973897 30719435908170865204480423)
      ·
        refine ⟨46079153862256297806720635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30719435908170865204480423 46079153862256297806720635)
        ·
          refine ⟨69118730793384446710080953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46079153862256297806720635 69118730793384446710080953)
          ·
            refine ⟨51839048095038335032560715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69118730793384446710080953 51839048095038335032560715)
            ·
              refine ⟨77758572142557502548841073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51839048095038335032560715 77758572142557502548841073)
              ·
                refine ⟨58318929106918126911630805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77758572142557502548841073 58318929106918126911630805)
                ·
                  refine ⟨1366849900943393599491347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 58318929106918126911630805 1366849900943393599491347)
                  ·
                    refine ⟨2050274851415090399237021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1366849900943393599491347 2050274851415090399237021)
                    ·
                      refine ⟨768853069280658899713883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2050274851415090399237021 768853069280658899713883)
                      ·
                        rfl

theorem cell23_1497336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 7, 1, 3].length) (baseStart_1497336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497336 prefixEnd_1497336 := by exact prefixLift 1497336
  have htrace : WordTrace (prefixWord ++ tailWord_1497336) baseStart_1497336 baseEnd_1497336 := by
    simpa [prefixWord, tailWord_1497336, baseEnd_1497336] using wordTrace_append hprefix tailTrace_1497336
  have hstable : (prefixWord ++ tailWord_1497336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497336).length < 2 ^ (prefixWord ++ tailWord_1497336).sum := by decide
  have hdescent : baseEnd_1497336 < baseStart_1497336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497353 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 3, 1, 3]
def baseStart_1497353 : Nat := 118140960795 + 1497353 * 2 ^ 59
def prefixEnd_1497353 : Nat := 4983230072969 + 3 ^ 40 * 1497353 * 2
def baseEnd_1497353 : Nat := 768861798451785333201305

theorem tailTrace_1497353 : CollatzResearch.WordTrace tailWord_1497353 prefixEnd_1497353 768861798451785333201305 := by
  unfold tailWord_1497353
  simp only [CollatzResearch.WordTrace]
  refine ⟨54612950544353283378000713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36408633696235522252000475 54612950544353283378000713)
  ·
    refine ⟨40959712908264962533500535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54612950544353283378000713 40959712908264962533500535)
    ·
      refine ⟨61439569362397443800250803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40959712908264962533500535 61439569362397443800250803)
      ·
        refine ⟨92159354043596165700376205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61439569362397443800250803 92159354043596165700376205)
        ·
          refine ⟨34559757766348562137641077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92159354043596165700376205 34559757766348562137641077)
          ·
            refine ⟨3239977290595177700403851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34559757766348562137641077 3239977290595177700403851)
            ·
              refine ⟨4859965935892766550605777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3239977290595177700403851 4859965935892766550605777)
              ·
                refine ⟨3644974451919574912954333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4859965935892766550605777 3644974451919574912954333)
                ·
                  refine ⟨1366865419469840592357875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3644974451919574912954333 1366865419469840592357875)
                  ·
                    refine ⟨2050298129204760888536813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1366865419469840592357875 2050298129204760888536813)
                    ·
                      refine ⟨768861798451785333201305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2050298129204760888536813 768861798451785333201305)
                      ·
                        rfl

theorem cell23_1497353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 1, 3].length) (baseStart_1497353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497353 prefixEnd_1497353 := by exact prefixLift 1497353
  have htrace : WordTrace (prefixWord ++ tailWord_1497353) baseStart_1497353 baseEnd_1497353 := by
    simpa [prefixWord, tailWord_1497353, baseEnd_1497353] using wordTrace_append hprefix tailTrace_1497353
  have hstable : (prefixWord ++ tailWord_1497353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497353).length < 2 ^ (prefixWord ++ tailWord_1497353).sum := by decide
  have hdescent : baseEnd_1497353 < baseStart_1497353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497356 : List Nat := [2, 2, 1, 2, 2, 2, 2, 4, 1, 5]
def baseStart_1497356 : Nat := 118140960795 + 1497356 * 2 ^ 59
def prefixEnd_1497356 : Nat := 4983230072969 + 3 ^ 40 * 1497356 * 2
def baseEnd_1497356 : Nat := 256287779631249607154597

theorem tailTrace_1497356 : CollatzResearch.WordTrace tailWord_1497356 prefixEnd_1497356 256287779631249607154597 := by
  unfold tailWord_1497356
  simp only [CollatzResearch.WordTrace]
  refine ⟨27306529981671207445179961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36408706642228276593573281 27306529981671207445179961)
  ·
    refine ⟨20479897486253405583884971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27306529981671207445179961 20479897486253405583884971)
    ·
      refine ⟨30719846229380108375827457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20479897486253405583884971 30719846229380108375827457)
      ·
        refine ⟨23039884672035081281870593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30719846229380108375827457 23039884672035081281870593)
        ·
          refine ⟨17279913504026310961402945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23039884672035081281870593 17279913504026310961402945)
          ·
            refine ⟨12959935128019733221052209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17279913504026310961402945 12959935128019733221052209)
            ·
              refine ⟨9719951346014799915789157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12959935128019733221052209 9719951346014799915789157)
              ·
                refine ⟨1822490877377774984210467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9719951346014799915789157 1822490877377774984210467)
                ·
                  refine ⟨2733736316066662476315701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822490877377774984210467 2733736316066662476315701)
                  ·
                    refine ⟨256287779631249607154597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2733736316066662476315701 256287779631249607154597)
                    ·
                      rfl

theorem cell23_1497356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_1497356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497356 prefixEnd_1497356 := by exact prefixLift 1497356
  have htrace : WordTrace (prefixWord ++ tailWord_1497356) baseStart_1497356 baseEnd_1497356 := by
    simpa [prefixWord, tailWord_1497356, baseEnd_1497356] using wordTrace_append hprefix tailTrace_1497356
  have hstable : (prefixWord ++ tailWord_1497356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497356).length < 2 ^ (prefixWord ++ tailWord_1497356).sum := by decide
  have hdescent : baseEnd_1497356 < baseStart_1497356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497416 : List Nat := [2, 1, 3, 1, 1, 2, 6, 7]
def baseStart_1497416 : Nat := 118140960795 + 1497416 * 2 ^ 59
def prefixEnd_1497416 : Nat := 4983230072969 + 3 ^ 40 * 1497416 * 2
def baseEnd_1497416 : Nat := 28477561027148836544945

theorem tailTrace_1497416 : CollatzResearch.WordTrace tailWord_1497416 prefixEnd_1497416 28477561027148836544945 := by
  unfold tailWord_1497416
  simp only [CollatzResearch.WordTrace]
  refine ⟨27307624171562522568772051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36410165562083363425029401 27307624171562522568772051)
  ·
    refine ⟨40961436257343783853158077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27307624171562522568772051 40961436257343783853158077)
    ·
      refine ⟨15360538596503918944934279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40961436257343783853158077 15360538596503918944934279)
      ·
        refine ⟨23040807894755878417401419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15360538596503918944934279 23040807894755878417401419)
        ·
          refine ⟨34561211842133817626102129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23040807894755878417401419 34561211842133817626102129)
          ·
            refine ⟨25920908881600363219576597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34561211842133817626102129 25920908881600363219576597)
            ·
              refine ⟨1215042603825017025917653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25920908881600363219576597 1215042603825017025917653)
              ·
                refine ⟨28477561027148836544945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1215042603825017025917653 28477561027148836544945)
                ·
                  rfl

theorem cell23_1497416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 7].length) (baseStart_1497416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497416 prefixEnd_1497416 := by exact prefixLift 1497416
  have htrace : WordTrace (prefixWord ++ tailWord_1497416) baseStart_1497416 baseEnd_1497416 := by
    simpa [prefixWord, tailWord_1497416, baseEnd_1497416] using wordTrace_append hprefix tailTrace_1497416
  have hstable : (prefixWord ++ tailWord_1497416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497416).length < 2 ^ (prefixWord ++ tailWord_1497416).sum := by decide
  have hdescent : baseEnd_1497416 < baseStart_1497416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497438 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_1497438 : Nat := 118140960795 + 1497438 * 2 ^ 59
def prefixEnd_1497438 : Nat := 4983230072969 + 3 ^ 40 * 1497438 * 2
def baseEnd_1497438 : Nat := 768905444307417500638415

theorem tailTrace_1497438 : CollatzResearch.WordTrace tailWord_1497438 prefixEnd_1497438 768905444307417500638415 := by
  unfold tailWord_1497438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6827006343630667861855621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36410700499363561929896645 6827006343630667861855621)
  ·
    refine ⟨1280063689430750224097929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6827006343630667861855621 1280063689430750224097929)
    ·
      refine ⟨960047767073062668073447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1280063689430750224097929 960047767073062668073447)
      ·
        refine ⟨1440071650609594002110171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 960047767073062668073447 1440071650609594002110171)
        ·
          refine ⟨2160107475914391003165257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440071650609594002110171 2160107475914391003165257)
          ·
            refine ⟨1620080606935793252373943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2160107475914391003165257 1620080606935793252373943)
            ·
              refine ⟨2430120910403689878560915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620080606935793252373943 2430120910403689878560915)
              ·
                refine ⟨3645181365605534817841373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2430120910403689878560915 3645181365605534817841373)
                ·
                  refine ⟨1366943012102075556690515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3645181365605534817841373 1366943012102075556690515)
                  ·
                    refine ⟨2050414518153113335035773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1366943012102075556690515 2050414518153113335035773)
                    ·
                      refine ⟨768905444307417500638415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2050414518153113335035773 768905444307417500638415)
                      ·
                        rfl

theorem cell23_1497438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_1497438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497438 prefixEnd_1497438 := by exact prefixLift 1497438
  have htrace : WordTrace (prefixWord ++ tailWord_1497438) baseStart_1497438 baseEnd_1497438 := by
    simpa [prefixWord, tailWord_1497438, baseEnd_1497438] using wordTrace_append hprefix tailTrace_1497438
  have hstable : (prefixWord ++ tailWord_1497438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497438).length < 2 ^ (prefixWord ++ tailWord_1497438).sum := by decide
  have hdescent : baseEnd_1497438 < baseStart_1497438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497443 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 4, 1, 3]
def baseStart_1497443 : Nat := 118140960795 + 1497443 * 2 ^ 59
def prefixEnd_1497443 : Nat := 4983230072969 + 3 ^ 40 * 1497443 * 2
def baseEnd_1497443 : Nat := 768908011710689981075891

theorem tailTrace_1497443 : CollatzResearch.WordTrace tailWord_1497443 prefixEnd_1497443 768908011710689981075891 := by
  unfold tailWord_1497443
  simp only [CollatzResearch.WordTrace]
  refine ⟨54616233114027228748776983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36410822076018152499184655 54616233114027228748776983)
  ·
    refine ⟨81924349671040843123165475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54616233114027228748776983 81924349671040843123165475)
    ·
      refine ⟨122886524506561264684748213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81924349671040843123165475 122886524506561264684748213)
      ·
        refine ⟨11520611672490118564195145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122886524506561264684748213 11520611672490118564195145)
        ·
          refine ⟨8640458754367588923146359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11520611672490118564195145 8640458754367588923146359)
          ·
            refine ⟨12960688131551383384719539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8640458754367588923146359 12960688131551383384719539)
            ·
              refine ⟨19441032197327075077079309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12960688131551383384719539 19441032197327075077079309)
              ·
                refine ⟨7290387073997653153904741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19441032197327075077079309 7290387073997653153904741)
                ·
                  refine ⟨1366947576374559966357139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7290387073997653153904741 1366947576374559966357139)
                  ·
                    refine ⟨2050421364561839949535709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1366947576374559966357139 2050421364561839949535709)
                    ·
                      refine ⟨768908011710689981075891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2050421364561839949535709 768908011710689981075891)
                      ·
                        rfl

theorem cell23_1497443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_1497443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497443 prefixEnd_1497443 := by exact prefixLift 1497443
  have htrace : WordTrace (prefixWord ++ tailWord_1497443) baseStart_1497443 baseEnd_1497443 := by
    simpa [prefixWord, tailWord_1497443, baseEnd_1497443] using wordTrace_append hprefix tailTrace_1497443
  have hstable : (prefixWord ++ tailWord_1497443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497443).length < 2 ^ (prefixWord ++ tailWord_1497443).sum := by decide
  have hdescent : baseEnd_1497443 < baseStart_1497443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497444 : List Nat := [2, 3, 1, 1, 3, 1, 5, 2, 1, 2, 2]
def baseStart_1497444 : Nat := 118140960795 + 1497444 * 2 ^ 59
def prefixEnd_1497444 : Nat := 4983230072969 + 3 ^ 40 * 1497444 * 2
def baseEnd_1497444 : Nat := 768908525191344477163387

theorem tailTrace_1497444 : CollatzResearch.WordTrace tailWord_1497444 prefixEnd_1497444 768908525191344477163387 := by
  unfold tailWord_1497444
  simp only [CollatzResearch.WordTrace]
  refine ⟨27308134793511802959781693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36410846391349070613042257 27308134793511802959781693)
  ·
    refine ⟨10240550547566926109918135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27308134793511802959781693 10240550547566926109918135)
    ·
      refine ⟨15360825821350389164877203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10240550547566926109918135 15360825821350389164877203)
      ·
        refine ⟨23041238732025583747315805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15360825821350389164877203 23041238732025583747315805)
        ·
          refine ⟨8640464524509593905243427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23041238732025583747315805 8640464524509593905243427)
          ·
            refine ⟨12960696786764390857865141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8640464524509593905243427 12960696786764390857865141)
            ·
              refine ⟨1215065323759161642924857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12960696786764390857865141 1215065323759161642924857)
              ·
                refine ⟨911298992819371232193643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1215065323759161642924857 911298992819371232193643)
                ·
                  refine ⟨1366948489229056848290465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911298992819371232193643 1366948489229056848290465)
                  ·
                    refine ⟨1025211366921792636217849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1366948489229056848290465 1025211366921792636217849)
                    ·
                      refine ⟨768908525191344477163387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025211366921792636217849 768908525191344477163387)
                      ·
                        rfl

theorem cell23_1497444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_1497444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497444 prefixEnd_1497444 := by exact prefixLift 1497444
  have htrace : WordTrace (prefixWord ++ tailWord_1497444) baseStart_1497444 baseEnd_1497444 := by
    simpa [prefixWord, tailWord_1497444, baseEnd_1497444] using wordTrace_append hprefix tailTrace_1497444
  have hstable : (prefixWord ++ tailWord_1497444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497444).length < 2 ^ (prefixWord ++ tailWord_1497444).sum := by decide
  have hdescent : baseEnd_1497444 < baseStart_1497444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497483 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 3, 4, 2]
def baseStart_1497483 : Nat := 118140960795 + 1497483 * 2 ^ 59
def prefixEnd_1497483 : Nat := 4983230072969 + 3 ^ 40 * 1497483 * 2
def baseEnd_1497483 : Nat := 768928550936869824575707

theorem tailTrace_1497483 : CollatzResearch.WordTrace tailWord_1497483 prefixEnd_1497483 768928550936869824575707 := by
  unfold tailWord_1497483
  simp only [CollatzResearch.WordTrace]
  refine ⟨54617692033882315580233103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36411794689254877053488735 54617692033882315580233103)
  ·
    refine ⟨81926538050823473370349655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54617692033882315580233103 81926538050823473370349655)
    ·
      refine ⟨122889807076235210055524483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81926538050823473370349655 122889807076235210055524483)
      ·
        refine ⟨184334710614352815083286725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122889807076235210055524483 184334710614352815083286725)
        ·
          refine ⟨34562758240191152828116261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184334710614352815083286725 34562758240191152828116261)
          ·
            refine ⟨6480517170035841155271799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34562758240191152828116261 6480517170035841155271799)
            ·
              refine ⟨9720775755053761732907699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6480517170035841155271799 9720775755053761732907699)
              ·
                refine ⟨14581163632580642599361549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9720775755053761732907699 14581163632580642599361549)
                ·
                  refine ⟨5467936362217740974760581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14581163632580642599361549 5467936362217740974760581)
                  ·
                    refine ⟨1025238067915826432767609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5467936362217740974760581 1025238067915826432767609)
                    ·
                      refine ⟨768928550936869824575707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025238067915826432767609 768928550936869824575707)
                      ·
                        rfl

theorem cell23_1497483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 4, 2].length) (baseStart_1497483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497483 prefixEnd_1497483 := by exact prefixLift 1497483
  have htrace : WordTrace (prefixWord ++ tailWord_1497483) baseStart_1497483 baseEnd_1497483 := by
    simpa [prefixWord, tailWord_1497483, baseEnd_1497483] using wordTrace_append hprefix tailTrace_1497483
  have hstable : (prefixWord ++ tailWord_1497483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497483).length < 2 ^ (prefixWord ++ tailWord_1497483).sum := by decide
  have hdescent : baseEnd_1497483 < baseStart_1497483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497590 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1497590 : Nat := 118140960795 + 1497590 * 2 ^ 59
def prefixEnd_1497590 : Nat := 4983230072969 + 3 ^ 40 * 1497590 * 2
def baseEnd_1497590 : Nat := 768983493366900905937715

theorem tailTrace_1497590 : CollatzResearch.WordTrace tailWord_1497590 prefixEnd_1497590 768983493366900905937715 := by
  unfold tailWord_1497590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3413849665280917053398639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36414396429663115236252149 3413849665280917053398639)
  ·
    refine ⟨5120774497921375580097959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3413849665280917053398639 5120774497921375580097959)
    ·
      refine ⟨7681161746882063370146939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5120774497921375580097959 7681161746882063370146939)
      ·
        refine ⟨11521742620323095055220409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7681161746882063370146939 11521742620323095055220409)
        ·
          refine ⟨8641306965242321291415307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11521742620323095055220409 8641306965242321291415307)
          ·
            refine ⟨12961960447863481937122961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8641306965242321291415307 12961960447863481937122961)
            ·
              refine ⟨9721470335897611452842221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12961960447863481937122961 9721470335897611452842221)
              ·
                refine ⟨3645551375961604294815833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9721470335897611452842221 3645551375961604294815833)
                ·
                  refine ⟨2734163531971203221111875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3645551375961604294815833 2734163531971203221111875)
                  ·
                    refine ⟨4101245297956804831667813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2734163531971203221111875 4101245297956804831667813)
                    ·
                      refine ⟨768983493366900905937715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4101245297956804831667813 768983493366900905937715)
                      ·
                        rfl

theorem cell23_1497590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1497590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497590 prefixEnd_1497590 := by exact prefixLift 1497590
  have htrace : WordTrace (prefixWord ++ tailWord_1497590) baseStart_1497590 baseEnd_1497590 := by
    simpa [prefixWord, tailWord_1497590, baseEnd_1497590] using wordTrace_append hprefix tailTrace_1497590
  have hstable : (prefixWord ++ tailWord_1497590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497590).length < 2 ^ (prefixWord ++ tailWord_1497590).sum := by decide
  have hdescent : baseEnd_1497590 < baseStart_1497590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497593 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 1, 4, 3]
def baseStart_1497593 : Nat := 118140960795 + 1497593 * 2 ^ 59
def prefixEnd_1497593 : Nat := 4983230072969 + 3 ^ 40 * 1497593 * 2
def baseEnd_1497593 : Nat := 768985033808864394200201

theorem tailTrace_1497593 : CollatzResearch.WordTrace tailWord_1497593 prefixEnd_1497593 768985033808864394200201 := by
  unfold tailWord_1497593
  simp only [CollatzResearch.WordTrace]
  refine ⟨54621704063483804366737433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36414469375655869577824955 54621704063483804366737433)
  ·
    refine ⟨40966278047612853275053075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54621704063483804366737433 40966278047612853275053075)
    ·
      refine ⟨61449417071419279912579613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40966278047612853275053075 61449417071419279912579613)
      ·
        refine ⟨23043531401782229967217355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61449417071419279912579613 23043531401782229967217355)
        ·
          refine ⟨34565297102673344950826033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23043531401782229967217355 34565297102673344950826033)
          ·
            refine ⟨25923972827005008713119525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34565297102673344950826033 25923972827005008713119525)
            ·
              refine ⟨4860744905063439133709911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25923972827005008713119525 4860744905063439133709911)
              ·
                refine ⟨7291117357595158700564867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4860744905063439133709911 7291117357595158700564867)
                ·
                  refine ⟨10936676036392738050847301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7291117357595158700564867 10936676036392738050847301)
                  ·
                    refine ⟨2050626756823638384533869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10936676036392738050847301 2050626756823638384533869)
                    ·
                      refine ⟨768985033808864394200201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2050626756823638384533869 768985033808864394200201)
                      ·
                        rfl

theorem cell23_1497593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_1497593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497593 prefixEnd_1497593 := by exact prefixLift 1497593
  have htrace : WordTrace (prefixWord ++ tailWord_1497593) baseStart_1497593 baseEnd_1497593 := by
    simpa [prefixWord, tailWord_1497593, baseEnd_1497593] using wordTrace_append hprefix tailTrace_1497593
  have hstable : (prefixWord ++ tailWord_1497593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497593).length < 2 ^ (prefixWord ++ tailWord_1497593).sum := by decide
  have hdescent : baseEnd_1497593 < baseStart_1497593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497610 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 2, 2, 3]
def baseStart_1497610 : Nat := 118140960795 + 1497610 * 2 ^ 59
def prefixEnd_1497610 : Nat := 4983230072969 + 3 ^ 40 * 1497610 * 2
def baseEnd_1497610 : Nat := 768993762979990827687623

theorem tailTrace_1497610 : CollatzResearch.WordTrace tailWord_1497610 prefixEnd_1497610 768993762979990827687623 := by
  unfold tailWord_1497610
  simp only [CollatzResearch.WordTrace]
  refine ⟨13655581026105554067526571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36414882736281477513404189 13655581026105554067526571)
  ·
    refine ⟨20483371539158331101289857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13655581026105554067526571 20483371539158331101289857)
    ·
      refine ⟨15362528654368748325967393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20483371539158331101289857 15362528654368748325967393)
      ·
        refine ⟨11521896490776561244475545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15362528654368748325967393 11521896490776561244475545)
        ·
          refine ⟨8641422368082420933356659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11521896490776561244475545 8641422368082420933356659)
          ·
            refine ⟨12962133552123631400034989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8641422368082420933356659 12962133552123631400034989)
            ·
              refine ⟨4860800082046361775013121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12962133552123631400034989 4860800082046361775013121)
              ·
                refine ⟨3645600061534771331259841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4860800082046361775013121 3645600061534771331259841)
                ·
                  refine ⟨2734200046151078498444881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3645600061534771331259841 2734200046151078498444881)
                  ·
                    refine ⟨2050650034613308873833661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2734200046151078498444881 2050650034613308873833661)
                    ·
                      refine ⟨768993762979990827687623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2050650034613308873833661 768993762979990827687623)
                      ·
                        rfl

theorem cell23_1497610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_1497610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497610 prefixEnd_1497610 := by exact prefixLift 1497610
  have htrace : WordTrace (prefixWord ++ tailWord_1497610) baseStart_1497610 baseEnd_1497610 := by
    simpa [prefixWord, tailWord_1497610, baseEnd_1497610] using wordTrace_append hprefix tailTrace_1497610
  have hstable : (prefixWord ++ tailWord_1497610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497610).length < 2 ^ (prefixWord ++ tailWord_1497610).sum := by decide
  have hdescent : baseEnd_1497610 < baseStart_1497610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497616 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 6]
def baseStart_1497616 : Nat := 118140960795 + 1497616 * 2 ^ 59
def prefixEnd_1497616 : Nat := 4983230072969 + 3 ^ 40 * 1497616 * 2
def baseEnd_1497616 : Nat := 768996843863917804212595

theorem tailTrace_1497616 : CollatzResearch.WordTrace tailWord_1497616 prefixEnd_1497616 768996843863917804212595 := by
  unfold tailWord_1497616
  simp only [CollatzResearch.WordTrace]
  refine ⟨27311271471200239647412351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36415028628266986196549801 27311271471200239647412351)
  ·
    refine ⟨40966907206800359471118527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27311271471200239647412351 40966907206800359471118527)
    ·
      refine ⟨61450360810200539206677791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40966907206800359471118527 61450360810200539206677791)
      ·
        refine ⟨92175541215300808810016687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61450360810200539206677791 92175541215300808810016687)
        ·
          refine ⟨138263311822951213215025031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92175541215300808810016687 138263311822951213215025031)
          ·
            refine ⟨207394967734426819822537547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138263311822951213215025031 207394967734426819822537547)
            ·
              refine ⟨311092451601640229733806321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207394967734426819822537547 311092451601640229733806321)
              ·
                refine ⟨233319338701230172300354741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311092451601640229733806321 233319338701230172300354741)
                ·
                  refine ⟨21873688003240328653158257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 233319338701230172300354741 21873688003240328653158257)
                  ·
                    refine ⟨16405266002430246489868693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21873688003240328653158257 16405266002430246489868693)
                    ·
                      refine ⟨768996843863917804212595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16405266002430246489868693 768996843863917804212595)
                      ·
                        rfl

theorem cell23_1497616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_1497616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497616 prefixEnd_1497616 := by exact prefixLift 1497616
  have htrace : WordTrace (prefixWord ++ tailWord_1497616) baseStart_1497616 baseEnd_1497616 := by
    simpa [prefixWord, tailWord_1497616, baseEnd_1497616] using wordTrace_append hprefix tailTrace_1497616
  have hstable : (prefixWord ++ tailWord_1497616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497616).length < 2 ^ (prefixWord ++ tailWord_1497616).sum := by decide
  have hdescent : baseEnd_1497616 < baseStart_1497616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497650 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2]
def baseStart_1497650 : Nat := 118140960795 + 1497650 * 2 ^ 59
def prefixEnd_1497650 : Nat := 4983230072969 + 3 ^ 40 * 1497650 * 2
def baseEnd_1497650 : Nat := 769014302206170671187439

theorem tailTrace_1497650 : CollatzResearch.WordTrace tailWord_1497650 prefixEnd_1497650 769014302206170671187439 := by
  unfold tailWord_1497650
  simp only [CollatzResearch.WordTrace]
  refine ⟨13655945756069325775390601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36415855349518202067708269 13655945756069325775390601)
  ·
    refine ⟨10241959317051994331542951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13655945756069325775390601 10241959317051994331542951)
    ·
      refine ⟨15362938975577991497314427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10241959317051994331542951 15362938975577991497314427)
      ·
        refine ⟨23044408463366987245971641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15362938975577991497314427 23044408463366987245971641)
        ·
          refine ⟨17283306347525240434478731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23044408463366987245971641 17283306347525240434478731)
          ·
            refine ⟨25924959521287860651718097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17283306347525240434478731 25924959521287860651718097)
            ·
              refine ⟨19443719640965895488788573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25924959521287860651718097 19443719640965895488788573)
              ·
                refine ⟨7291394865362210808295715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19443719640965895488788573 7291394865362210808295715)
                ·
                  refine ⟨10937092298043316212443573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7291394865362210808295715 10937092298043316212443573)
                  ·
                    refine ⟨1025352402941560894916585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10937092298043316212443573 1025352402941560894916585)
                    ·
                      refine ⟨769014302206170671187439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025352402941560894916585 769014302206170671187439)
                      ·
                        rfl

theorem cell23_1497650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_1497650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497650 prefixEnd_1497650 := by exact prefixLift 1497650
  have htrace : WordTrace (prefixWord ++ tailWord_1497650) baseStart_1497650 baseEnd_1497650 := by
    simpa [prefixWord, tailWord_1497650, baseEnd_1497650] using wordTrace_append hprefix tailTrace_1497650
  have hstable : (prefixWord ++ tailWord_1497650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497650).length < 2 ^ (prefixWord ++ tailWord_1497650).sum := by decide
  have hdescent : baseEnd_1497650 < baseStart_1497650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497668 : List Nat := [2, 3, 5, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1497668 : Nat := 118140960795 + 1497668 * 2 ^ 59
def prefixEnd_1497668 : Nat := 4983230072969 + 3 ^ 40 * 1497668 * 2
def baseEnd_1497668 : Nat := 256341181619317200254119

theorem tailTrace_1497668 : CollatzResearch.WordTrace tailWord_1497668 prefixEnd_1497668 256341181619317200254119 := by
  unfold tailWord_1497668
  simp only [CollatzResearch.WordTrace]
  refine ⟨27312219769106046087858829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36416293025474728117145105 27312219769106046087858829)
  ·
    refine ⟨10242082413414767282947061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27312219769106046087858829 10242082413414767282947061)
    ·
      refine ⟨960195226257634432776287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10242082413414767282947061 960195226257634432776287)
      ·
        refine ⟨1440292839386451649164431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 960195226257634432776287 1440292839386451649164431)
        ·
          refine ⟨2160439259079677473746647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440292839386451649164431 2160439259079677473746647)
          ·
            refine ⟨3240658888619516210619971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2160439259079677473746647 3240658888619516210619971)
            ·
              refine ⟨4860988332929274315929957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3240658888619516210619971 4860988332929274315929957)
              ·
                refine ⟨911435312424238934236867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4860988332929274315929957 911435312424238934236867)
                ·
                  refine ⟨1367152968636358401355301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911435312424238934236867 1367152968636358401355301)
                  ·
                    refine ⟨256341181619317200254119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1367152968636358401355301 256341181619317200254119)
                    ·
                      rfl

theorem cell23_1497668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1497668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497668 prefixEnd_1497668 := by exact prefixLift 1497668
  have htrace : WordTrace (prefixWord ++ tailWord_1497668) baseStart_1497668 baseEnd_1497668 := by
    simpa [prefixWord, tailWord_1497668, baseEnd_1497668] using wordTrace_append hprefix tailTrace_1497668
  have hstable : (prefixWord ++ tailWord_1497668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497668).length < 2 ^ (prefixWord ++ tailWord_1497668).sum := by decide
  have hdescent : baseEnd_1497668 < baseStart_1497668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497674 : List Nat := [3, 1, 2, 1, 1, 5, 1, 4, 1, 1, 3]
def baseStart_1497674 : Nat := 118140960795 + 1497674 * 2 ^ 59
def prefixEnd_1497674 : Nat := 4983230072969 + 3 ^ 40 * 1497674 * 2
def baseEnd_1497674 : Nat := 769026625741878577287329

theorem tailTrace_1497674 : CollatzResearch.WordTrace tailWord_1497674 prefixEnd_1497674 769026625741878577287329 := by
  unfold tailWord_1497674
  simp only [CollatzResearch.WordTrace]
  refine ⟨13656164594047588800109019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36416438917460236800290717 13656164594047588800109019)
  ·
    refine ⟨20484246891071383200163529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13656164594047588800109019 20484246891071383200163529)
    ·
      refine ⟨15363185168303537400122647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20484246891071383200163529 15363185168303537400122647)
      ·
        refine ⟨23044777752455306100183971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15363185168303537400122647 23044777752455306100183971)
        ·
          refine ⟨34567166628682959150275957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23044777752455306100183971 34567166628682959150275957)
          ·
            refine ⟨3240671871439027420338371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34567166628682959150275957 3240671871439027420338371)
            ·
              refine ⟨4861007807158541130507557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3240671871439027420338371 4861007807158541130507557)
              ·
                refine ⟨911438963842226461970167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4861007807158541130507557 911438963842226461970167)
                ·
                  refine ⟨1367158445763339692955251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911438963842226461970167 1367158445763339692955251)
                  ·
                    refine ⟨2050737668645009539432877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1367158445763339692955251 2050737668645009539432877)
                    ·
                      refine ⟨769026625741878577287329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2050737668645009539432877 769026625741878577287329)
                      ·
                        rfl

theorem cell23_1497674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_1497674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497674 prefixEnd_1497674 := by exact prefixLift 1497674
  have htrace : WordTrace (prefixWord ++ tailWord_1497674) baseStart_1497674 baseEnd_1497674 := by
    simpa [prefixWord, tailWord_1497674, baseEnd_1497674] using wordTrace_append hprefix tailTrace_1497674
  have hstable : (prefixWord ++ tailWord_1497674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497674).length < 2 ^ (prefixWord ++ tailWord_1497674).sum := by decide
  have hdescent : baseEnd_1497674 < baseStart_1497674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497697 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 5, 2, 2]
def baseStart_1497697 : Nat := 118140960795 + 1497697 * 2 ^ 59
def prefixEnd_1497697 : Nat := 4983230072969 + 3 ^ 40 * 1497697 * 2
def baseEnd_1497697 : Nat := 769038435796931987299723

theorem tailTrace_1497697 : CollatzResearch.WordTrace tailWord_1497697 prefixEnd_1497697 769038435796931987299723 := by
  unfold tailWord_1497697
  simp only [CollatzResearch.WordTrace]
  refine ⟨54625497255107030128523345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36416998170071353419015563 54625497255107030128523345)
  ·
    refine ⟨40969122941330272596392509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54625497255107030128523345 40969122941330272596392509)
    ·
      refine ⟨15363421102998852223647191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40969122941330272596392509 15363421102998852223647191)
      ·
        refine ⟨23045131654498278335470787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15363421102998852223647191 23045131654498278335470787)
        ·
          refine ⟨34567697481747417503206181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23045131654498278335470787 34567697481747417503206181)
          ·
            refine ⟨6481443277827640781851159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34567697481747417503206181 6481443277827640781851159)
            ·
              refine ⟨9722164916741461172776739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6481443277827640781851159 9722164916741461172776739)
              ·
                refine ⟨14583247375112191759165109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9722164916741461172776739 14583247375112191759165109)
                ·
                  refine ⟨1367179441416767977421729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14583247375112191759165109 1367179441416767977421729)
                  ·
                    refine ⟨1025384581062575983066297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1367179441416767977421729 1025384581062575983066297)
                    ·
                      refine ⟨769038435796931987299723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025384581062575983066297 769038435796931987299723)
                      ·
                        rfl

theorem cell23_1497697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_1497697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497697 prefixEnd_1497697 := by exact prefixLift 1497697
  have htrace : WordTrace (prefixWord ++ tailWord_1497697) baseStart_1497697 baseEnd_1497697 := by
    simpa [prefixWord, tailWord_1497697, baseEnd_1497697] using wordTrace_append hprefix tailTrace_1497697
  have hstable : (prefixWord ++ tailWord_1497697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497697).length < 2 ^ (prefixWord ++ tailWord_1497697).sum := by decide
  have hdescent : baseEnd_1497697 < baseStart_1497697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497700 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 3, 2, 3]
def baseStart_1497700 : Nat := 118140960795 + 1497700 * 2 ^ 59
def prefixEnd_1497700 : Nat := 4983230072969 + 3 ^ 40 * 1497700 * 2
def baseEnd_1497700 : Nat := 769039976238895475562209

theorem tailTrace_1497700 : CollatzResearch.WordTrace tailWord_1497700 prefixEnd_1497700 769039976238895475562209 := by
  unfold tailWord_1497700
  simp only [CollatzResearch.WordTrace]
  refine ⟨27312803337048080820441277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36417071116064107760588369 27312803337048080820441277)
  ·
    refine ⟨10242301251393030307665479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27312803337048080820441277 10242301251393030307665479)
    ·
      refine ⟨15363451877089545461498219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10242301251393030307665479 15363451877089545461498219)
      ·
        refine ⟨23045177815634318192247329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15363451877089545461498219 23045177815634318192247329)
        ·
          refine ⟨17283883361725738644185497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23045177815634318192247329 17283883361725738644185497)
          ·
            refine ⟨12962912521294303983139123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17283883361725738644185497 12962912521294303983139123)
            ·
              refine ⟨19444368781941455974708685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12962912521294303983139123 19444368781941455974708685)
              ·
                refine ⟨7291638293228045990515757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19444368781941455974708685 7291638293228045990515757)
                ·
                  refine ⟨2734364359960517246443409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7291638293228045990515757 2734364359960517246443409)
                  ·
                    refine ⟨2050773269970387934832557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2734364359960517246443409 2050773269970387934832557)
                    ·
                      refine ⟨769039976238895475562209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2050773269970387934832557 769039976238895475562209)
                      ·
                        rfl

theorem cell23_1497700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_1497700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497700 prefixEnd_1497700 := by exact prefixLift 1497700
  have htrace : WordTrace (prefixWord ++ tailWord_1497700) baseStart_1497700 baseEnd_1497700 := by
    simpa [prefixWord, tailWord_1497700, baseEnd_1497700] using wordTrace_append hprefix tailTrace_1497700
  have hstable : (prefixWord ++ tailWord_1497700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497700).length < 2 ^ (prefixWord ++ tailWord_1497700).sum := by decide
  have hdescent : baseEnd_1497700 < baseStart_1497700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497701 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 2, 3, 2]
def baseStart_1497701 : Nat := 118140960795 + 1497701 * 2 ^ 59
def prefixEnd_1497701 : Nat := 4983230072969 + 3 ^ 40 * 1497701 * 2
def baseEnd_1497701 : Nat := 769040489719549971649705

theorem tailTrace_1497701 : CollatzResearch.WordTrace tailWord_1497701 prefixEnd_1497701 769040489719549971649705 := by
  unfold tailWord_1497701
  simp only [CollatzResearch.WordTrace]
  refine ⟨54625643147092538811668957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36417095431395025874445971 54625643147092538811668957)
  ·
    refine ⟨20484616180159702054375859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54625643147092538811668957 20484616180159702054375859)
    ·
      refine ⟨30726924270239553081563789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20484616180159702054375859 30726924270239553081563789)
      ·
        refine ⟨11522596601339832405586421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30726924270239553081563789 11522596601339832405586421)
        ·
          refine ⟨1080243431375609288023727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11522596601339832405586421 1080243431375609288023727)
          ·
            refine ⟨1620365147063413932035591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080243431375609288023727 1620365147063413932035591)
            ·
              refine ⟨2430547720595120898053387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620365147063413932035591 2430547720595120898053387)
              ·
                refine ⟨3645821580892681347080081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2430547720595120898053387 3645821580892681347080081)
                ·
                  refine ⟨2734366185669511010310061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3645821580892681347080081 2734366185669511010310061)
                  ·
                    refine ⟨1025387319626066628866273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2734366185669511010310061 1025387319626066628866273)
                    ·
                      refine ⟨769040489719549971649705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025387319626066628866273 769040489719549971649705)
                      ·
                        rfl

theorem cell23_1497701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_1497701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497701 prefixEnd_1497701 := by exact prefixLift 1497701
  have htrace : WordTrace (prefixWord ++ tailWord_1497701) baseStart_1497701 baseEnd_1497701 := by
    simpa [prefixWord, tailWord_1497701, baseEnd_1497701] using wordTrace_append hprefix tailTrace_1497701
  have hstable : (prefixWord ++ tailWord_1497701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497701).length < 2 ^ (prefixWord ++ tailWord_1497701).sum := by decide
  have hdescent : baseEnd_1497701 < baseStart_1497701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497740 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 2, 7, 2]
def baseStart_1497740 : Nat := 118140960795 + 1497740 * 2 ^ 59
def prefixEnd_1497740 : Nat := 4983230072969 + 3 ^ 40 * 1497740 * 2
def baseEnd_1497740 : Nat := 769060515465075319062025

theorem tailTrace_1497740 : CollatzResearch.WordTrace tailWord_1497740 prefixEnd_1497740 769060515465075319062025 := by
  unfold tailWord_1497740
  simp only [CollatzResearch.WordTrace]
  refine ⟨27313532796975624236169337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36418043729300832314892449 27313532796975624236169337)
  ·
    refine ⟨20485149597731718177127003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27313532796975624236169337 20485149597731718177127003)
    ·
      refine ⟨30727724396597577265690505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20485149597731718177127003 30727724396597577265690505)
      ·
        refine ⟨23045793297448182949267879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30727724396597577265690505 23045793297448182949267879)
        ·
          refine ⟨34568689946172274423901819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23045793297448182949267879 34568689946172274423901819)
          ·
            refine ⟨51853034919258411635852729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34568689946172274423901819 51853034919258411635852729)
            ·
              refine ⟨38889776189443808726889547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51853034919258411635852729 38889776189443808726889547)
              ·
                refine ⟨58334664284165713090334321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38889776189443808726889547 58334664284165713090334321)
                ·
                  refine ⟨43750998213124284817750741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58334664284165713090334321 43750998213124284817750741)
                  ·
                    refine ⟨1025414020620100425416033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43750998213124284817750741 1025414020620100425416033)
                    ·
                      refine ⟨769060515465075319062025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025414020620100425416033 769060515465075319062025)
                      ·
                        rfl

theorem cell23_1497740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_1497740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497740 prefixEnd_1497740 := by exact prefixLift 1497740
  have htrace : WordTrace (prefixWord ++ tailWord_1497740) baseStart_1497740 baseEnd_1497740 := by
    simpa [prefixWord, tailWord_1497740, baseEnd_1497740] using wordTrace_append hprefix tailTrace_1497740
  have hstable : (prefixWord ++ tailWord_1497740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497740).length < 2 ^ (prefixWord ++ tailWord_1497740).sum := by decide
  have hdescent : baseEnd_1497740 < baseStart_1497740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497754 : List Nat := [3, 1, 1, 6, 1, 2, 2, 7]
def baseStart_1497754 : Nat := 118140960795 + 1497754 * 2 ^ 59
def prefixEnd_1497754 : Nat := 4983230072969 + 3 ^ 40 * 1497754 * 2
def baseEnd_1497754 : Nat := 28483989044231046825443

theorem tailTrace_1497754 : CollatzResearch.WordTrace tailWord_1497754 prefixEnd_1497754 28483989044231046825443 := by
  unfold tailWord_1497754
  simp only [CollatzResearch.WordTrace]
  refine ⟨13656894053975132215837079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36418384143933685908898877 13656894053975132215837079)
  ·
    refine ⟨20485341080962698323755619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13656894053975132215837079 20485341080962698323755619)
    ·
      refine ⟨30728011621444047485633429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20485341080962698323755619 30728011621444047485633429)
      ·
        refine ⟨1440375544755189725889067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30728011621444047485633429 1440375544755189725889067)
        ·
          refine ⟨2160563317132784588833601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440375544755189725889067 2160563317132784588833601)
          ·
            refine ⟨1620422487849588441625201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2160563317132784588833601 1620422487849588441625201)
            ·
              refine ⟨1215316865887191331218901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1620422487849588441625201 1215316865887191331218901)
              ·
                refine ⟨28483989044231046825443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1215316865887191331218901 28483989044231046825443)
                ·
                  rfl

theorem cell23_1497754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 7].length) (baseStart_1497754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497754 prefixEnd_1497754 := by exact prefixLift 1497754
  have htrace : WordTrace (prefixWord ++ tailWord_1497754) baseStart_1497754 baseEnd_1497754 := by
    simpa [prefixWord, tailWord_1497754, baseEnd_1497754] using wordTrace_append hprefix tailTrace_1497754
  have hstable : (prefixWord ++ tailWord_1497754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497754).length < 2 ^ (prefixWord ++ tailWord_1497754).sum := by decide
  have hdescent : baseEnd_1497754 < baseStart_1497754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497757 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 3, 3, 2]
def baseStart_1497757 : Nat := 118140960795 + 1497757 * 2 ^ 59
def prefixEnd_1497757 : Nat := 4983230072969 + 3 ^ 40 * 1497757 * 2
def baseEnd_1497757 : Nat := 769069244636201752549447

theorem tailTrace_1497757 : CollatzResearch.WordTrace tailWord_1497757 prefixEnd_1497757 769069244636201752549447 := by
  unfold tailWord_1497757
  simp only [CollatzResearch.WordTrace]
  refine ⟨54627685634889660375707525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36418457089926440250471683 54627685634889660375707525)
  ·
    refine ⟨10242691056541811320445161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54627685634889660375707525 10242691056541811320445161)
    ·
      refine ⟨7682018292406358490333871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10242691056541811320445161 7682018292406358490333871)
      ·
        refine ⟨11523027438609537735500807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7682018292406358490333871 11523027438609537735500807)
        ·
          refine ⟨17284541157914306603251211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11523027438609537735500807 17284541157914306603251211)
          ·
            refine ⟨25926811736871459904876817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17284541157914306603251211 25926811736871459904876817)
            ·
              refine ⟨19445108802653594928657613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25926811736871459904876817 19445108802653594928657613)
              ·
                refine ⟨7291915800995098098246605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19445108802653594928657613 7291915800995098098246605)
                ·
                  refine ⟨2734468425373161786842477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7291915800995098098246605 2734468425373161786842477)
                  ·
                    refine ⟨1025425659514935670065929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2734468425373161786842477 1025425659514935670065929)
                    ·
                      refine ⟨769069244636201752549447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025425659514935670065929 769069244636201752549447)
                      ·
                        rfl

theorem cell23_1497757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_1497757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497757 prefixEnd_1497757 := by exact prefixLift 1497757
  have htrace : WordTrace (prefixWord ++ tailWord_1497757) baseStart_1497757 baseEnd_1497757 := by
    simpa [prefixWord, tailWord_1497757, baseEnd_1497757] using wordTrace_append hprefix tailTrace_1497757
  have hstable : (prefixWord ++ tailWord_1497757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497757).length < 2 ^ (prefixWord ++ tailWord_1497757).sum := by decide
  have hdescent : baseEnd_1497757 < baseStart_1497757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497763 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 4, 6]
def baseStart_1497763 : Nat := 118140960795 + 1497763 * 2 ^ 59
def prefixEnd_1497763 : Nat := 4983230072969 + 3 ^ 40 * 1497763 * 2
def baseEnd_1497763 : Nat := 256357441840042909691473

theorem tailTrace_1497763 : CollatzResearch.WordTrace tailWord_1497763 prefixEnd_1497763 256357441840042909691473 := by
  unfold tailWord_1497763
  simp only [CollatzResearch.WordTrace]
  refine ⟨54627904472867923400425943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36418602981911948933617295 54627904472867923400425943)
  ·
    refine ⟨81941856709301885100638915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54627904472867923400425943 81941856709301885100638915)
    ·
      refine ⟨122912785063952827650958373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81941856709301885100638915 122912785063952827650958373)
      ·
        refine ⟨23046147199491155184554695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122912785063952827650958373 23046147199491155184554695)
        ·
          refine ⟨34569220799236732776832043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23046147199491155184554695 34569220799236732776832043)
          ·
            refine ⟨51853831198855099165248065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34569220799236732776832043 51853831198855099165248065)
            ·
              refine ⟨38890373399141324373936049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51853831198855099165248065 38890373399141324373936049)
              ·
                refine ⟨29167780049355993280452037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38890373399141324373936049 29167780049355993280452037)
                ·
                  refine ⟨5468958759254248740084757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29167780049355993280452037 5468958759254248740084757)
                  ·
                    refine ⟨256357441840042909691473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5468958759254248740084757 256357441840042909691473)
                    ·
                      rfl

theorem cell23_1497763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 6].length) (baseStart_1497763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497763 prefixEnd_1497763 := by exact prefixLift 1497763
  have htrace : WordTrace (prefixWord ++ tailWord_1497763) baseStart_1497763 baseEnd_1497763 := by
    simpa [prefixWord, tailWord_1497763, baseEnd_1497763] using wordTrace_append hprefix tailTrace_1497763
  have hstable : (prefixWord ++ tailWord_1497763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497763).length < 2 ^ (prefixWord ++ tailWord_1497763).sum := by decide
  have hdescent : baseEnd_1497763 < baseStart_1497763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497782 : List Nat := [5, 1, 3, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_1497782 : Nat := 118140960795 + 1497782 * 2 ^ 59
def prefixEnd_1497782 : Nat := 4983230072969 + 3 ^ 40 * 1497782 * 2
def baseEnd_1497782 : Nat := 769082081652564154736833

theorem tailTrace_1497782 : CollatzResearch.WordTrace tailWord_1497782 prefixEnd_1497782 769082081652564154736833 := by
  unfold tailWord_1497782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3414287341237443102835475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36419064973199393096911733 3414287341237443102835475)
  ·
    refine ⟨5121431011856164654253213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3414287341237443102835475 5121431011856164654253213)
    ·
      refine ⟨1920536629446061745344955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5121431011856164654253213 1920536629446061745344955)
      ·
        refine ⟨2880804944169092618017433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1920536629446061745344955 2880804944169092618017433)
        ·
          refine ⟨2160603708126819463513075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2880804944169092618017433 2160603708126819463513075)
          ·
            refine ⟨3240905562190229195269613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2160603708126819463513075 3240905562190229195269613)
            ·
              refine ⟨1215339585821335948226105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3240905562190229195269613 1215339585821335948226105)
              ·
                refine ⟨911504689366001961169579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1215339585821335948226105 911504689366001961169579)
                ·
                  refine ⟨1367257034049002941754369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911504689366001961169579 1367257034049002941754369)
                  ·
                    refine ⟨1025442775536752206315777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1367257034049002941754369 1025442775536752206315777)
                    ·
                      refine ⟨769082081652564154736833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025442775536752206315777 769082081652564154736833)
                      ·
                        rfl

theorem cell23_1497782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_1497782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497782 prefixEnd_1497782 := by exact prefixLift 1497782
  have htrace : WordTrace (prefixWord ++ tailWord_1497782) baseStart_1497782 baseEnd_1497782 := by
    simpa [prefixWord, tailWord_1497782, baseEnd_1497782] using wordTrace_append hprefix tailTrace_1497782
  have hstable : (prefixWord ++ tailWord_1497782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497782).length < 2 ^ (prefixWord ++ tailWord_1497782).sum := by decide
  have hdescent : baseEnd_1497782 < baseStart_1497782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497790 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_1497790 : Nat := 118140960795 + 1497790 * 2 ^ 59
def prefixEnd_1497790 : Nat := 4983230072969 + 3 ^ 40 * 1497790 * 2
def baseEnd_1497790 : Nat := 769086189497800123436795

theorem tailTrace_1497790 : CollatzResearch.WordTrace tailWord_1497790 prefixEnd_1497790 769086189497800123436795 := by
  unfold tailWord_1497790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6828611155471263376457353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36419259495846738007772549 6828611155471263376457353)
  ·
    refine ⟨5121458366603447532343015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6828611155471263376457353 5121458366603447532343015)
    ·
      refine ⟨7682187549905171298514523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5121458366603447532343015 7682187549905171298514523)
      ·
        refine ⟨11523281324857756947771785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7682187549905171298514523 11523281324857756947771785)
        ·
          refine ⟨8642460993643317710828839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11523281324857756947771785 8642460993643317710828839)
          ·
            refine ⟨12963691490464976566243259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8642460993643317710828839 12963691490464976566243259)
            ·
              refine ⟨19445537235697464849364889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12963691490464976566243259 19445537235697464849364889)
              ·
                refine ⟨14584152926773098637023667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19445537235697464849364889 14584152926773098637023667)
                ·
                  refine ⟨21876229390159647955535501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14584152926773098637023667 21876229390159647955535501)
                  ·
                    refine ⟨8203586021309867983325813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21876229390159647955535501 8203586021309867983325813)
                    ·
                      refine ⟨769086189497800123436795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8203586021309867983325813 769086189497800123436795)
                      ·
                        rfl

theorem cell23_1497790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_1497790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497790 prefixEnd_1497790 := by exact prefixLift 1497790
  have htrace : WordTrace (prefixWord ++ tailWord_1497790) baseStart_1497790 baseEnd_1497790 := by
    simpa [prefixWord, tailWord_1497790, baseEnd_1497790] using wordTrace_append hprefix tailTrace_1497790
  have hstable : (prefixWord ++ tailWord_1497790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497790).length < 2 ^ (prefixWord ++ tailWord_1497790).sum := by decide
  have hdescent : baseEnd_1497790 < baseStart_1497790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497837 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_1497837 : Nat := 118140960795 + 1497837 * 2 ^ 59
def prefixEnd_1497837 : Nat := 4983230072969 + 3 ^ 40 * 1497837 * 2
def baseEnd_1497837 : Nat := 769110323088561439549079

theorem tailTrace_1497837 : CollatzResearch.WordTrace tailWord_1497837 prefixEnd_1497837 769110323088561439549079 := by
  unfold tailWord_1497837
  simp only [CollatzResearch.WordTrace]
  refine ⟨54630603474599834038619765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36420402316399889359079843 54630603474599834038619765)
  ·
    refine ⟨5121619075743734441120603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54630603474599834038619765 5121619075743734441120603)
    ·
      refine ⟨7682428613615601661680905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5121619075743734441120603 7682428613615601661680905)
      ·
        refine ⟨5761821460211701246260679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7682428613615601661680905 5761821460211701246260679)
        ·
          refine ⟨8642732190317551869391019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5761821460211701246260679 8642732190317551869391019)
          ·
            refine ⟨12964098285476327804086529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8642732190317551869391019 12964098285476327804086529)
            ·
              refine ⟨9723073714107245853064897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12964098285476327804086529 9723073714107245853064897)
              ·
                refine ⟨7292305285580434389798673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9723073714107245853064897 7292305285580434389798673)
                ·
                  refine ⟨5469228964185325792349005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7292305285580434389798673 5469228964185325792349005)
                  ·
                    refine ⟨2050960861569497172130877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5469228964185325792349005 2050960861569497172130877)
                    ·
                      refine ⟨769110323088561439549079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2050960861569497172130877 769110323088561439549079)
                      ·
                        rfl

theorem cell23_1497837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_1497837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497837 prefixEnd_1497837 := by exact prefixLift 1497837
  have htrace : WordTrace (prefixWord ++ tailWord_1497837) baseStart_1497837 baseEnd_1497837 := by
    simpa [prefixWord, tailWord_1497837, baseEnd_1497837] using wordTrace_append hprefix tailTrace_1497837
  have hstable : (prefixWord ++ tailWord_1497837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497837).length < 2 ^ (prefixWord ++ tailWord_1497837).sum := by decide
  have hdescent : baseEnd_1497837 < baseStart_1497837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497840 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 2, 5]
def baseStart_1497840 : Nat := 118140960795 + 1497840 * 2 ^ 59
def prefixEnd_1497840 : Nat := 4983230072969 + 3 ^ 40 * 1497840 * 2
def baseEnd_1497840 : Nat := 256370621176841642603855

theorem tailTrace_1497840 : CollatzResearch.WordTrace tailWord_1497840 prefixEnd_1497840 256370621176841642603855 := by
  unfold tailWord_1497840
  simp only [CollatzResearch.WordTrace]
  refine ⟨27315356446794482775489487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36420475262392643700652649 27315356446794482775489487)
  ·
    refine ⟨40973034670191724163234231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27315356446794482775489487 40973034670191724163234231)
    ·
      refine ⟨61459552005287586244851347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40973034670191724163234231 61459552005287586244851347)
      ·
        refine ⟨92189328007931379367277021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61459552005287586244851347 92189328007931379367277021)
        ·
          refine ⟨34570998002974267262728883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92189328007931379367277021 34570998002974267262728883)
          ·
            refine ⟨51856497004461400894093325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34570998002974267262728883 51856497004461400894093325)
            ·
              refine ⟨19446186376673025335284997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51856497004461400894093325 19446186376673025335284997)
              ·
                refine ⟨3646159945626192250365937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19446186376673025335284997 3646159945626192250365937)
                ·
                  refine ⟨2734619959219644187774453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3646159945626192250365937 2734619959219644187774453)
                  ·
                    refine ⟨256370621176841642603855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2734619959219644187774453 256370621176841642603855)
                    ·
                      rfl

theorem cell23_1497840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 2, 5].length) (baseStart_1497840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497840 prefixEnd_1497840 := by exact prefixLift 1497840
  have htrace : WordTrace (prefixWord ++ tailWord_1497840) baseStart_1497840 baseEnd_1497840 := by
    simpa [prefixWord, tailWord_1497840, baseEnd_1497840] using wordTrace_append hprefix tailTrace_1497840
  have hstable : (prefixWord ++ tailWord_1497840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497840).length < 2 ^ (prefixWord ++ tailWord_1497840).sum := by decide
  have hdescent : baseEnd_1497840 < baseStart_1497840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497850 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5]
def baseStart_1497850 : Nat := 118140960795 + 1497850 * 2 ^ 59
def prefixEnd_1497850 : Nat := 4983230072969 + 3 ^ 40 * 1497850 * 2
def baseEnd_1497850 : Nat := 769116998337069888686519

theorem tailTrace_1497850 : CollatzResearch.WordTrace tailWord_1497850 prefixEnd_1497850 769116998337069888686519 := by
  unfold tailWord_1497850
  simp only [CollatzResearch.WordTrace]
  refine ⟨13657769405888184314710751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36420718415701824839228669 13657769405888184314710751)
  ·
    refine ⟨20486654108832276472066127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13657769405888184314710751 20486654108832276472066127)
    ·
      refine ⟨30729981163248414708099191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20486654108832276472066127 30729981163248414708099191)
      ·
        refine ⟨46094971744872622062148787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30729981163248414708099191 46094971744872622062148787)
        ·
          refine ⟨69142457617308933093223181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46094971744872622062148787 69142457617308933093223181)
          ·
            refine ⟨25928421606490849909958693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69142457617308933093223181 25928421606490849909958693)
            ·
              refine ⟨4861579051217034358117255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25928421606490849909958693 4861579051217034358117255)
              ·
                refine ⟨7292368576825551537175883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4861579051217034358117255 7292368576825551537175883)
                ·
                  refine ⟨10938552865238327305763825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7292368576825551537175883 10938552865238327305763825)
                  ·
                    refine ⟨8203914648928745479322869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10938552865238327305763825 8203914648928745479322869)
                    ·
                      refine ⟨769116998337069888686519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8203914648928745479322869 769116998337069888686519)
                      ·
                        rfl

theorem cell23_1497850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_1497850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497850 prefixEnd_1497850 := by exact prefixLift 1497850
  have htrace : WordTrace (prefixWord ++ tailWord_1497850) baseStart_1497850 baseEnd_1497850 := by
    simpa [prefixWord, tailWord_1497850, baseEnd_1497850] using wordTrace_append hprefix tailTrace_1497850
  have hstable : (prefixWord ++ tailWord_1497850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497850).length < 2 ^ (prefixWord ++ tailWord_1497850).sum := by decide
  have hdescent : baseEnd_1497850 < baseStart_1497850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497854 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_1497854 : Nat := 118140960795 + 1497854 * 2 ^ 59
def prefixEnd_1497854 : Nat := 4983230072969 + 3 ^ 40 * 1497854 * 2
def baseEnd_1497854 : Nat := 769119052259687873036501

theorem tailTrace_1497854 : CollatzResearch.WordTrace tailWord_1497854 prefixEnd_1497854 769119052259687873036501 := by
  unfold tailWord_1497854
  simp only [CollatzResearch.WordTrace]
  refine ⟨6828902939442280742748577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36420815677025497294659077 6828902939442280742748577)
  ·
    refine ⟨5121677204581710557061433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6828902939442280742748577 5121677204581710557061433)
    ·
      refine ⟨3841257903436282917796075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5121677204581710557061433 3841257903436282917796075)
      ·
        refine ⟨5761886855154424376694113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3841257903436282917796075 5761886855154424376694113)
        ·
          refine ⟨4321415141365818282520585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5761886855154424376694113 4321415141365818282520585)
          ·
            refine ⟨3241061356024363711890439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4321415141365818282520585 3241061356024363711890439)
            ·
              refine ⟨4861592034036545567835659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3241061356024363711890439 4861592034036545567835659)
              ·
                refine ⟨7292388051054818351753489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4861592034036545567835659 7292388051054818351753489)
                ·
                  refine ⟨5469291038291113763815117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7292388051054818351753489 5469291038291113763815117)
                  ·
                    refine ⟨2050984139359167661430669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5469291038291113763815117 2050984139359167661430669)
                    ·
                      refine ⟨769119052259687873036501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2050984139359167661430669 769119052259687873036501)
                      ·
                        rfl

theorem cell23_1497854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_1497854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497854 prefixEnd_1497854 := by exact prefixLift 1497854
  have htrace : WordTrace (prefixWord ++ tailWord_1497854) baseStart_1497854 baseEnd_1497854 := by
    simpa [prefixWord, tailWord_1497854, baseEnd_1497854] using wordTrace_append hprefix tailTrace_1497854
  have hstable : (prefixWord ++ tailWord_1497854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497854).length < 2 ^ (prefixWord ++ tailWord_1497854).sum := by decide
  have hdescent : baseEnd_1497854 < baseStart_1497854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497874 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 1, 7]
def baseStart_1497874 : Nat := 118140960795 + 1497874 * 2 ^ 59
def prefixEnd_1497874 : Nat := 4983230072969 + 3 ^ 40 * 1497874 * 2
def baseEnd_1497874 : Nat := 256376440624259264928803

theorem tailTrace_1497874 : CollatzResearch.WordTrace tailWord_1497874 prefixEnd_1497874 256376440624259264928803 := by
  unfold tailWord_1497874
  simp only [CollatzResearch.WordTrace]
  refine ⟨13657988243866447339429169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36421301983643859571811117 13657988243866447339429169)
  ·
    refine ⟨10243491182899835504571877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13657988243866447339429169 10243491182899835504571877)
    ·
      refine ⟨1920654596793719157107227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10243491182899835504571877 1920654596793719157107227)
      ·
        refine ⟨2880981895190578735660841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1920654596793719157107227 2880981895190578735660841)
        ·
          refine ⟨2160736421392934051745631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2880981895190578735660841 2160736421392934051745631)
          ·
            refine ⟨3241104632089401077618447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2160736421392934051745631 3241104632089401077618447)
            ·
              refine ⟨4861656948134101616427671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3241104632089401077618447 4861656948134101616427671)
              ·
                refine ⟨7292485422201152424641507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4861656948134101616427671 7292485422201152424641507)
                ·
                  refine ⟨10938728133301728636962261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7292485422201152424641507 10938728133301728636962261)
                  ·
                    refine ⟨256376440624259264928803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10938728133301728636962261 256376440624259264928803)
                    ·
                      rfl

theorem cell23_1497874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_1497874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497874 prefixEnd_1497874 := by exact prefixLift 1497874
  have htrace : WordTrace (prefixWord ++ tailWord_1497874) baseStart_1497874 baseEnd_1497874 := by
    simpa [prefixWord, tailWord_1497874, baseEnd_1497874] using wordTrace_append hprefix tailTrace_1497874
  have hstable : (prefixWord ++ tailWord_1497874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497874).length < 2 ^ (prefixWord ++ tailWord_1497874).sum := by decide
  have hdescent : baseEnd_1497874 < baseStart_1497874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497877 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 1, 6, 2]
def baseStart_1497877 : Nat := 118140960795 + 1497877 * 2 ^ 59
def prefixEnd_1497877 : Nat := 4983230072969 + 3 ^ 40 * 1497877 * 2
def baseEnd_1497877 : Nat := 769130862314741283048895

theorem tailTrace_1497877 : CollatzResearch.WordTrace tailWord_1497877 prefixEnd_1497877 769130862314741283048895 := by
  unfold tailWord_1497877
  simp only [CollatzResearch.WordTrace]
  refine ⟨54632062394454920870075885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36421374929636613913383923 54632062394454920870075885)
  ·
    refine ⟨20487023397920595326278457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54632062394454920870075885 20487023397920595326278457)
    ·
      refine ⟨15365267548440446494708843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20487023397920595326278457 15365267548440446494708843)
      ·
        refine ⟨23047901322660669742063265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15365267548440446494708843 23047901322660669742063265)
        ·
          refine ⟨17285925991995502306547449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23047901322660669742063265 17285925991995502306547449)
          ·
            refine ⟨12964444493996626729910587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17285925991995502306547449 12964444493996626729910587)
            ·
              refine ⟨19446666740994940094865881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12964444493996626729910587 19446666740994940094865881)
              ·
                refine ⟨14585000055746205071149411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19446666740994940094865881 14585000055746205071149411)
                ·
                  refine ⟨21877500083619307606724117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14585000055746205071149411 21877500083619307606724117)
                  ·
                    refine ⟨1025507816419655044065193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21877500083619307606724117 1025507816419655044065193)
                    ·
                      refine ⟨769130862314741283048895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025507816419655044065193 769130862314741283048895)
                      ·
                        rfl

theorem cell23_1497877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_1497877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497877 prefixEnd_1497877 := by exact prefixLift 1497877
  have htrace : WordTrace (prefixWord ++ tailWord_1497877) baseStart_1497877 baseEnd_1497877 := by
    simpa [prefixWord, tailWord_1497877, baseEnd_1497877] using wordTrace_append hprefix tailTrace_1497877
  have hstable : (prefixWord ++ tailWord_1497877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497877).length < 2 ^ (prefixWord ++ tailWord_1497877).sum := by decide
  have hdescent : baseEnd_1497877 < baseStart_1497877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497900 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 8]
def baseStart_1497900 : Nat := 118140960795 + 1497900 * 2 ^ 59
def prefixEnd_1497900 : Nat := 4983230072969 + 3 ^ 40 * 1497900 * 2
def baseEnd_1497900 : Nat := 85460296929977188117921

theorem tailTrace_1497900 : CollatzResearch.WordTrace tailWord_1497900 prefixEnd_1497900 85460296929977188117921 := by
  unfold tailWord_1497900
  simp only [CollatzResearch.WordTrace]
  refine ⟨27316450636685797899081577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36421934182247730532108769 27316450636685797899081577)
  ·
    refine ⟨20487337977514348424311183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27316450636685797899081577 20487337977514348424311183)
    ·
      refine ⟨30731006966271522636466775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20487337977514348424311183 30731006966271522636466775)
      ·
        refine ⟨46096510449407283954700163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30731006966271522636466775 46096510449407283954700163)
        ·
          refine ⟨69144765674110925932050245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46096510449407283954700163 69144765674110925932050245)
          ·
            refine ⟨12964643563895798612259421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69144765674110925932050245 12964643563895798612259421)
            ·
              refine ⟨4861741336460924479597283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12964643563895798612259421 4861741336460924479597283)
              ·
                refine ⟨7292612004691386719395925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4861741336460924479597283 7292612004691386719395925)
                ·
                  refine ⟨85460296929977188117921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7292612004691386719395925 85460296929977188117921)
                  ·
                    rfl

theorem cell23_1497900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 8].length) (baseStart_1497900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497900 prefixEnd_1497900 := by exact prefixLift 1497900
  have htrace : WordTrace (prefixWord ++ tailWord_1497900) baseStart_1497900 baseEnd_1497900 := by
    simpa [prefixWord, tailWord_1497900, baseEnd_1497900] using wordTrace_append hprefix tailTrace_1497900
  have hstable : (prefixWord ++ tailWord_1497900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497900).length < 2 ^ (prefixWord ++ tailWord_1497900).sum := by decide
  have hdescent : baseEnd_1497900 < baseStart_1497900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1497994 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 1, 6]
def baseStart_1497994 : Nat := 118140960795 + 1497994 * 2 ^ 59
def prefixEnd_1497994 : Nat := 4983230072969 + 3 ^ 40 * 1497994 * 2
def baseEnd_1497994 : Nat := 256396979850439108428619

theorem tailTrace_1497994 : CollatzResearch.WordTrace tailWord_1497994 prefixEnd_1497994 256396979850439108428619 := by
  unfold tailWord_1497994
  simp only [CollatzResearch.WordTrace]
  refine ⟨13659082433757762463021259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36424219823354033234723357 13659082433757762463021259)
  ·
    refine ⟨20488623650636643694531889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13659082433757762463021259 20488623650636643694531889)
    ·
      refine ⟨15366467737977482770898917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20488623650636643694531889 15366467737977482770898917)
      ·
        refine ⟨2881212700870778019543547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15366467737977482770898917 2881212700870778019543547)
        ·
          refine ⟨4321819051306167029315321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2881212700870778019543547 4321819051306167029315321)
          ·
            refine ⟨3241364288479625271986491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4321819051306167029315321 3241364288479625271986491)
            ·
              refine ⟨4862046432719437907979737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3241364288479625271986491 4862046432719437907979737)
              ·
                refine ⟨3646534824539578430984803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4862046432719437907979737 3646534824539578430984803)
                ·
                  refine ⟨5469802236809367646477205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3646534824539578430984803 5469802236809367646477205)
                  ·
                    refine ⟨256396979850439108428619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5469802236809367646477205 256396979850439108428619)
                    ·
                      rfl

theorem cell23_1497994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_1497994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1497994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1497994 prefixEnd_1497994 := by exact prefixLift 1497994
  have htrace : WordTrace (prefixWord ++ tailWord_1497994) baseStart_1497994 baseEnd_1497994 := by
    simpa [prefixWord, tailWord_1497994, baseEnd_1497994] using wordTrace_append hprefix tailTrace_1497994
  have hstable : (prefixWord ++ tailWord_1497994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1497994).length < 2 ^ (prefixWord ++ tailWord_1497994).sum := by decide
  have hdescent : baseEnd_1497994 < baseStart_1497994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1497994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498000 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 7]
def baseStart_1498000 : Nat := 118140960795 + 1498000 * 2 ^ 59
def prefixEnd_1498000 : Nat := 4983230072969 + 3 ^ 40 * 1498000 * 2
def baseEnd_1498000 : Nat := 769194020435244301810829

theorem tailTrace_1498000 : CollatzResearch.WordTrace tailWord_1498000 prefixEnd_1498000 769194020435244301810829 := by
  unfold tailWord_1498000
  simp only [CollatzResearch.WordTrace]
  refine ⟨27318274286504656438401727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36424365715339541917868969 27318274286504656438401727)
  ·
    refine ⟨40977411429756984657602591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27318274286504656438401727 40977411429756984657602591)
    ·
      refine ⟨61466117144635476986403887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40977411429756984657602591 61466117144635476986403887)
      ·
        refine ⟨92199175716953215479605831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61466117144635476986403887 92199175716953215479605831)
        ·
          refine ⟨138298763575429823219408747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92199175716953215479605831 138298763575429823219408747)
          ·
            refine ⟨207448145363144734829113121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138298763575429823219408747 207448145363144734829113121)
            ·
              refine ⟨155586109022358551121834841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207448145363144734829113121 155586109022358551121834841)
              ·
                refine ⟨116689581766768913341376131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155586109022358551121834841 116689581766768913341376131)
                ·
                  refine ⟨175034372650153370012064197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116689581766768913341376131 175034372650153370012064197)
                  ·
                    refine ⟨32818944871903756877262037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 175034372650153370012064197 32818944871903756877262037)
                    ·
                      refine ⟨769194020435244301810829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32818944871903756877262037 769194020435244301810829)
                      ·
                        rfl

theorem cell23_1498000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_1498000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498000 prefixEnd_1498000 := by exact prefixLift 1498000
  have htrace : WordTrace (prefixWord ++ tailWord_1498000) baseStart_1498000 baseEnd_1498000 := by
    simpa [prefixWord, tailWord_1498000, baseEnd_1498000] using wordTrace_append hprefix tailTrace_1498000
  have hstable : (prefixWord ++ tailWord_1498000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498000).length < 2 ^ (prefixWord ++ tailWord_1498000).sum := by decide
  have hdescent : baseEnd_1498000 < baseStart_1498000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498012 : List Nat := [2, 2, 3, 3, 2, 2, 2, 2, 1, 1, 3]
def baseStart_1498012 : Nat := 118140960795 + 1498012 * 2 ^ 59
def prefixEnd_1498012 : Nat := 4983230072969 + 3 ^ 40 * 1498012 * 2
def baseEnd_1498012 : Nat := 769200182203098254860775

theorem tailTrace_1498012 : CollatzResearch.WordTrace tailWord_1498012 prefixEnd_1498012 769200182203098254860775 := by
  unfold tailWord_1498012
  simp only [CollatzResearch.WordTrace]
  refine ⟨27318493124482919463120145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36424657499310559284160193 27318493124482919463120145)
  ·
    refine ⟨20488869843362189597340109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27318493124482919463120145 20488869843362189597340109)
    ·
      refine ⟨7683326191260821099002541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20488869843362189597340109 7683326191260821099002541)
      ·
        refine ⟨2881247321722807912125953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7683326191260821099002541 2881247321722807912125953)
        ·
          refine ⟨2160935491292105934094465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2881247321722807912125953 2160935491292105934094465)
          ·
            refine ⟨1620701618469079450570849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2160935491292105934094465 1620701618469079450570849)
            ·
              refine ⟨1215526213851809587928137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1620701618469079450570849 1215526213851809587928137)
              ·
                refine ⟨911644660388857190946103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1215526213851809587928137 911644660388857190946103)
                ·
                  refine ⟨1367466990583285786419155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911644660388857190946103 1367466990583285786419155)
                  ·
                    refine ⟨2051200485874928679628733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1367466990583285786419155 2051200485874928679628733)
                    ·
                      refine ⟨769200182203098254860775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2051200485874928679628733 769200182203098254860775)
                      ·
                        rfl

theorem cell23_1498012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_1498012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498012 prefixEnd_1498012 := by exact prefixLift 1498012
  have htrace : WordTrace (prefixWord ++ tailWord_1498012) baseStart_1498012 baseEnd_1498012 := by
    simpa [prefixWord, tailWord_1498012, baseEnd_1498012] using wordTrace_append hprefix tailTrace_1498012
  have hstable : (prefixWord ++ tailWord_1498012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498012).length < 2 ^ (prefixWord ++ tailWord_1498012).sum := by decide
  have hdescent : baseEnd_1498012 < baseStart_1498012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498034 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3]
def baseStart_1498034 : Nat := 118140960795 + 1498034 * 2 ^ 59
def prefixEnd_1498034 : Nat := 4983230072969 + 3 ^ 40 * 1498034 * 2
def baseEnd_1498034 : Nat := 769211478777497168785673

theorem tailTrace_1498034 : CollatzResearch.WordTrace tailWord_1498034 prefixEnd_1498034 769211478777497168785673 := by
  unfold tailWord_1498034
  simp only [CollatzResearch.WordTrace]
  refine ⟨13659447163721534170885289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36425192436590757789027437 13659447163721534170885289)
  ·
    refine ⟨10244585372791150628163967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13659447163721534170885289 10244585372791150628163967)
    ·
      refine ⟨15366878059186725942245951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10244585372791150628163967 15366878059186725942245951)
      ·
        refine ⟨23050317088780088913368927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15366878059186725942245951 23050317088780088913368927)
        ·
          refine ⟨34575475633170133370053391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23050317088780088913368927 34575475633170133370053391)
          ·
            refine ⟨51863213449755200055080087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34575475633170133370053391 51863213449755200055080087)
            ·
              refine ⟨77794820174632800082620131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51863213449755200055080087 77794820174632800082620131)
              ·
                refine ⟨116692230261949200123930197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77794820174632800082620131 116692230261949200123930197)
                ·
                  refine ⟨1367487073382217188952307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 116692230261949200123930197 1367487073382217188952307)
                  ·
                    refine ⟨2051230610073325783428461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1367487073382217188952307 2051230610073325783428461)
                    ·
                      refine ⟨769211478777497168785673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2051230610073325783428461 769211478777497168785673)
                      ·
                        rfl

theorem cell23_1498034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_1498034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498034 prefixEnd_1498034 := by exact prefixLift 1498034
  have htrace : WordTrace (prefixWord ++ tailWord_1498034) baseStart_1498034 baseEnd_1498034 := by
    simpa [prefixWord, tailWord_1498034, baseEnd_1498034] using wordTrace_append hprefix tailTrace_1498034
  have hstable : (prefixWord ++ tailWord_1498034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498034).length < 2 ^ (prefixWord ++ tailWord_1498034).sum := by decide
  have hdescent : baseEnd_1498034 < baseStart_1498034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498037 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 2, 7]
def baseStart_1498037 : Nat := 118140960795 + 1498037 * 2 ^ 59
def prefixEnd_1498037 : Nat := 4983230072969 + 3 ^ 40 * 1498037 * 2
def baseEnd_1498037 : Nat := 256404339739820219016053

theorem tailTrace_1498037 : CollatzResearch.WordTrace tailWord_1498037 prefixEnd_1498037 256404339739820219016053 := by
  unfold tailWord_1498037
  simp only [CollatzResearch.WordTrace]
  refine ⟨54637898073875268195900365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36425265382583512130600243 54637898073875268195900365)
  ·
    refine ⟨20489211777703225573462637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54637898073875268195900365 20489211777703225573462637)
    ·
      refine ⟨7683454416638709590048489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20489211777703225573462637 7683454416638709590048489)
      ·
        refine ⟨5762590812479032192536367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7683454416638709590048489 5762590812479032192536367)
        ·
          refine ⟨8643886218718548288804551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5762590812479032192536367 8643886218718548288804551)
          ·
            refine ⟨12965829328077822433206827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8643886218718548288804551 12965829328077822433206827)
            ·
              refine ⟨19448743992116733649810241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12965829328077822433206827 19448743992116733649810241)
              ·
                refine ⟨14586557994087550237357681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19448743992116733649810241 14586557994087550237357681)
                ·
                  refine ⟨10939918495565662678018261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14586557994087550237357681 10939918495565662678018261)
                  ·
                    refine ⟨256404339739820219016053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10939918495565662678018261 256404339739820219016053)
                    ·
                      rfl

theorem cell23_1498037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_1498037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498037 prefixEnd_1498037 := by exact prefixLift 1498037
  have htrace : WordTrace (prefixWord ++ tailWord_1498037) baseStart_1498037 baseEnd_1498037 := by
    simpa [prefixWord, tailWord_1498037, baseEnd_1498037] using wordTrace_append hprefix tailTrace_1498037
  have hstable : (prefixWord ++ tailWord_1498037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498037).length < 2 ^ (prefixWord ++ tailWord_1498037).sum := by decide
  have hdescent : baseEnd_1498037 < baseStart_1498037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498052 : List Nat := [2, 3, 3, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_1498052 : Nat := 118140960795 + 1498052 * 2 ^ 59
def prefixEnd_1498052 : Nat := 4983230072969 + 3 ^ 40 * 1498052 * 2
def baseEnd_1498052 : Nat := 769220721429278098360591

theorem tailTrace_1498052 : CollatzResearch.WordTrace tailWord_1498052 prefixEnd_1498052 769220721429278098360591 := by
  unfold tailWord_1498052
  simp only [CollatzResearch.WordTrace]
  refine ⟨27319222584410462878848205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36425630112547283838464273 27319222584410462878848205)
  ·
    refine ⟨10244708469153923579568077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27319222584410462878848205 10244708469153923579568077)
    ·
      refine ⟨3841765675932721342338029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10244708469153923579568077 3841765675932721342338029)
      ·
        refine ⟨1440662128474770503376761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3841765675932721342338029 1440662128474770503376761)
        ·
          refine ⟨1080496596356077877532571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1440662128474770503376761 1080496596356077877532571)
          ·
            refine ⟨1620744894534116816298857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080496596356077877532571 1620744894534116816298857)
            ·
              refine ⟨1215558670900587612224143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1620744894534116816298857 1215558670900587612224143)
              ·
                refine ⟨1823338006350881418336215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215558670900587612224143 1823338006350881418336215)
                ·
                  refine ⟨2735007009526322127504323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823338006350881418336215 2735007009526322127504323)
                  ·
                    refine ⟨4102510514289483191256485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2735007009526322127504323 4102510514289483191256485)
                    ·
                      refine ⟨769220721429278098360591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4102510514289483191256485 769220721429278098360591)
                      ·
                        rfl

theorem cell23_1498052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_1498052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498052 prefixEnd_1498052 := by exact prefixLift 1498052
  have htrace : WordTrace (prefixWord ++ tailWord_1498052) baseStart_1498052 baseEnd_1498052 := by
    simpa [prefixWord, tailWord_1498052, baseEnd_1498052] using wordTrace_append hprefix tailTrace_1498052
  have hstable : (prefixWord ++ tailWord_1498052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498052).length < 2 ^ (prefixWord ++ tailWord_1498052).sum := by decide
  have hdescent : baseEnd_1498052 < baseStart_1498052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498068 : List Nat := [2, 4, 1, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_1498068 : Nat := 118140960795 + 1498068 * 2 ^ 59
def prefixEnd_1498068 : Nat := 4983230072969 + 3 ^ 40 * 1498068 * 2
def baseEnd_1498068 : Nat := 769228937119750035760517

theorem tailTrace_1498068 : CollatzResearch.WordTrace tailWord_1498068 prefixEnd_1498068 769228937119750035760517 := by
  unfold tailWord_1498068
  simp only [CollatzResearch.WordTrace]
  refine ⟨27319514368381480245139429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36426019157841973660185905 27319514368381480245139429)
  ·
    refine ⟨5122408944071527545963643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27319514368381480245139429 5122408944071527545963643)
    ·
      refine ⟨7683613416107291318945465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5122408944071527545963643 7683613416107291318945465)
      ·
        refine ⟨5762710062080468489209099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7683613416107291318945465 5762710062080468489209099)
        ·
          refine ⟨8644065093120702733813649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5762710062080468489209099 8644065093120702733813649)
          ·
            refine ⟨6483048819840527050360237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8644065093120702733813649 6483048819840527050360237)
            ·
              refine ⟨2431143307440197643885089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6483048819840527050360237 2431143307440197643885089)
              ·
                refine ⟨1823357480580148232913817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431143307440197643885089 1823357480580148232913817)
                ·
                  refine ⟨1367518110435111174685363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1823357480580148232913817 1367518110435111174685363)
                  ·
                    refine ⟨2051277165652666762028045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1367518110435111174685363 2051277165652666762028045)
                    ·
                      refine ⟨769228937119750035760517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2051277165652666762028045 769228937119750035760517)
                      ·
                        rfl

theorem cell23_1498068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_1498068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498068 prefixEnd_1498068 := by exact prefixLift 1498068
  have htrace : WordTrace (prefixWord ++ tailWord_1498068) baseStart_1498068 baseEnd_1498068 := by
    simpa [prefixWord, tailWord_1498068, baseEnd_1498068] using wordTrace_append hprefix tailTrace_1498068
  have hstable : (prefixWord ++ tailWord_1498068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498068).length < 2 ^ (prefixWord ++ tailWord_1498068).sum := by decide
  have hdescent : baseEnd_1498068 < baseStart_1498068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498085 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 1, 3, 3]
def baseStart_1498085 : Nat := 118140960795 + 1498085 * 2 ^ 59
def prefixEnd_1498085 : Nat := 4983230072969 + 3 ^ 40 * 1498085 * 2
def baseEnd_1498085 : Nat := 769237666290876469247939

theorem tailTrace_1498085 : CollatzResearch.WordTrace tailWord_1498085 prefixEnd_1498085 769237666290876469247939 := by
  unfold tailWord_1498085
  simp only [CollatzResearch.WordTrace]
  refine ⟨54639648777701372393647709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36426432518467581595765139 54639648777701372393647709)
  ·
    refine ⟨20489868291638014647617891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54639648777701372393647709 20489868291638014647617891)
    ·
      refine ⟨30734802437457021971426837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20489868291638014647617891 30734802437457021971426837)
      ·
        refine ⟨1440693864255797904910633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30734802437457021971426837 1440693864255797904910633)
        ·
          refine ⟨1080520398191848428682975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1440693864255797904910633 1080520398191848428682975)
          ·
            refine ⟨1620780597287772643024463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080520398191848428682975 1620780597287772643024463)
            ·
              refine ⟨2431170895931658964536695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620780597287772643024463 2431170895931658964536695)
              ·
                refine ⟨3646756343897488446805043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2431170895931658964536695 3646756343897488446805043)
                ·
                  refine ⟨5470134515846232670207565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3646756343897488446805043 5470134515846232670207565)
                  ·
                    refine ⟨2051300443442337251327837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5470134515846232670207565 2051300443442337251327837)
                    ·
                      refine ⟨769237666290876469247939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2051300443442337251327837 769237666290876469247939)
                      ·
                        rfl

theorem cell23_1498085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_1498085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498085 prefixEnd_1498085 := by exact prefixLift 1498085
  have htrace : WordTrace (prefixWord ++ tailWord_1498085) baseStart_1498085 baseEnd_1498085 := by
    simpa [prefixWord, tailWord_1498085, baseEnd_1498085] using wordTrace_append hprefix tailTrace_1498085
  have hstable : (prefixWord ++ tailWord_1498085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498085).length < 2 ^ (prefixWord ++ tailWord_1498085).sum := by decide
  have hdescent : baseEnd_1498085 < baseStart_1498085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498137 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 7]
def baseStart_1498137 : Nat := 118140960795 + 1498137 * 2 ^ 59
def prefixEnd_1498137 : Nat := 4983230072969 + 3 ^ 40 * 1498137 * 2
def baseEnd_1498137 : Nat := 769264367284910265797699

theorem tailTrace_1498137 : CollatzResearch.WordTrace tailWord_1498137 prefixEnd_1498137 769264367284910265797699 := by
  unfold tailWord_1498137
  simp only [CollatzResearch.WordTrace]
  refine ⟨54641545373512985274540665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36427696915675323516360443 54641545373512985274540665)
  ·
    refine ⟨40981159030134738955905499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54641545373512985274540665 40981159030134738955905499)
    ·
      refine ⟨61471738545202108433858249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40981159030134738955905499 61471738545202108433858249)
      ·
        refine ⟨46103803908901581325393687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61471738545202108433858249 46103803908901581325393687)
        ·
          refine ⟨69155705863352371988090531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46103803908901581325393687 69155705863352371988090531)
          ·
            refine ⟨103733558795028557982135797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69155705863352371988090531 103733558795028557982135797)
            ·
              refine ⟨9725021137033927310825231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103733558795028557982135797 9725021137033927310825231)
              ·
                refine ⟨14587531705550890966237847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9725021137033927310825231 14587531705550890966237847)
                ·
                  refine ⟨21881297558326336449356771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14587531705550890966237847 21881297558326336449356771)
                  ·
                    refine ⟨32821946337489504674035157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21881297558326336449356771 32821946337489504674035157)
                    ·
                      refine ⟨769264367284910265797699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32821946337489504674035157 769264367284910265797699)
                      ·
                        rfl

theorem cell23_1498137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_1498137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498137 prefixEnd_1498137 := by exact prefixLift 1498137
  have htrace : WordTrace (prefixWord ++ tailWord_1498137) baseStart_1498137 baseEnd_1498137 := by
    simpa [prefixWord, tailWord_1498137, baseEnd_1498137] using wordTrace_append hprefix tailTrace_1498137
  have hstable : (prefixWord ++ tailWord_1498137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498137).length < 2 ^ (prefixWord ++ tailWord_1498137).sum := by decide
  have hdescent : baseEnd_1498137 < baseStart_1498137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498182 : List Nat := [6, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_1498182 : Nat := 118140960795 + 1498182 * 2 ^ 59
def prefixEnd_1498182 : Nat := 4983230072969 + 3 ^ 40 * 1498182 * 2
def baseEnd_1498182 : Nat := 85476385990484732192777

theorem tailTrace_1498182 : CollatzResearch.WordTrace tailWord_1498182 prefixEnd_1498182 85476385990484732192777 := by
  unfold tailWord_1498182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1707599583073436186247775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36428791105566638639952533 1707599583073436186247775)
  ·
    refine ⟨2561399374610154279371663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1707599583073436186247775 2561399374610154279371663)
    ·
      refine ⟨3842099061915231419057495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2561399374610154279371663 3842099061915231419057495)
      ·
        refine ⟨5763148592872847128586243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3842099061915231419057495 5763148592872847128586243)
        ·
          refine ⟨8644722889309270692879365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5763148592872847128586243 8644722889309270692879365)
          ·
            refine ⟨1620885541745488254914881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8644722889309270692879365 1620885541745488254914881)
            ·
              refine ⟨1215664156309116191186161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1620885541745488254914881 1215664156309116191186161)
              ·
                refine ⟨911748117231837143389621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1215664156309116191186161 911748117231837143389621)
                ·
                  refine ⟨85476385990484732192777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 911748117231837143389621 85476385990484732192777)
                  ·
                    rfl

theorem cell23_1498182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_1498182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498182 prefixEnd_1498182 := by exact prefixLift 1498182
  have htrace : WordTrace (prefixWord ++ tailWord_1498182) baseStart_1498182 baseEnd_1498182 := by
    simpa [prefixWord, tailWord_1498182, baseEnd_1498182] using wordTrace_append hprefix tailTrace_1498182
  have hstable : (prefixWord ++ tailWord_1498182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498182).length < 2 ^ (prefixWord ++ tailWord_1498182).sum := by decide
  have hdescent : baseEnd_1498182 < baseStart_1498182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498218 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_1498218 : Nat := 118140960795 + 1498218 * 2 ^ 59
def prefixEnd_1498218 : Nat := 4983230072969 + 3 ^ 40 * 1498218 * 2
def baseEnd_1498218 : Nat := 769305959217924448884827

theorem tailTrace_1498218 : CollatzResearch.WordTrace tailWord_1498218 prefixEnd_1498218 769305959217924448884827 := by
  unfold tailWord_1498218
  simp only [CollatzResearch.WordTrace]
  refine ⟨13661124921554884027059827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36429666457479690738826205 13661124921554884027059827)
  ·
    refine ⟨20491687382332326040589741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13661124921554884027059827 20491687382332326040589741)
    ·
      refine ⟨7684382768374622265221153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20491687382332326040589741 7684382768374622265221153)
      ·
        refine ⟨5763287076280966698915865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7684382768374622265221153 5763287076280966698915865)
        ·
          refine ⟨4322465307210725024186899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5763287076280966698915865 4322465307210725024186899)
          ·
            refine ⟨6483697960816087536280349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4322465307210725024186899 6483697960816087536280349)
            ·
              refine ⟨2431386735306032826105131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6483697960816087536280349 2431386735306032826105131)
              ·
                refine ⟨3647080102959049239157697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2431386735306032826105131 3647080102959049239157697)
                ·
                  refine ⟨2735310077219286929368273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3647080102959049239157697 2735310077219286929368273)
                  ·
                    refine ⟨2051482557914465197026205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2735310077219286929368273 2051482557914465197026205)
                    ·
                      refine ⟨769305959217924448884827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2051482557914465197026205 769305959217924448884827)
                      ·
                        rfl

theorem cell23_1498218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_1498218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498218 prefixEnd_1498218 := by exact prefixLift 1498218
  have htrace : WordTrace (prefixWord ++ tailWord_1498218) baseStart_1498218 baseEnd_1498218 := by
    simpa [prefixWord, tailWord_1498218, baseEnd_1498218] using wordTrace_append hprefix tailTrace_1498218
  have hstable : (prefixWord ++ tailWord_1498218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498218).length < 2 ^ (prefixWord ++ tailWord_1498218).sum := by decide
  have hdescent : baseEnd_1498218 < baseStart_1498218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498231 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 5, 1, 3]
def baseStart_1498231 : Nat := 118140960795 + 1498231 * 2 ^ 59
def prefixEnd_1498231 : Nat := 4983230072969 + 3 ^ 40 * 1498231 * 2
def baseEnd_1498231 : Nat := 769312634466432898022267

theorem tailTrace_1498231 : CollatzResearch.WordTrace tailWord_1498231 prefixEnd_1498231 769312634466432898022267 := by
  unfold tailWord_1498231
  simp only [CollatzResearch.WordTrace]
  refine ⟨54644973835172439328462547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36429982556781626218975031 54644973835172439328462547)
  ·
    refine ⟨81967460752758658992693821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54644973835172439328462547 81967460752758658992693821)
    ·
      refine ⟨30737797782284497122260183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81967460752758658992693821 30737797782284497122260183)
      ·
        refine ⟨46106696673426745683390275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30737797782284497122260183 46106696673426745683390275)
        ·
          refine ⟨69160045010140118525085413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46106696673426745683390275 69160045010140118525085413)
          ·
            refine ⟨12967508439401272223453515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69160045010140118525085413 12967508439401272223453515)
            ·
              refine ⟨19451262659101908335180273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12967508439401272223453515 19451262659101908335180273)
              ·
                refine ⟨14588446994326431251385205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19451262659101908335180273 14588446994326431251385205)
                ·
                  refine ⟨1367666905718102929817363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14588446994326431251385205 1367666905718102929817363)
                  ·
                    refine ⟨2051500358577154394726045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1367666905718102929817363 2051500358577154394726045)
                    ·
                      refine ⟨769312634466432898022267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2051500358577154394726045 769312634466432898022267)
                      ·
                        rfl

theorem cell23_1498231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 1, 3].length) (baseStart_1498231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498231 prefixEnd_1498231 := by exact prefixLift 1498231
  have htrace : WordTrace (prefixWord ++ tailWord_1498231) baseStart_1498231 baseEnd_1498231 := by
    simpa [prefixWord, tailWord_1498231, baseEnd_1498231] using wordTrace_append hprefix tailTrace_1498231
  have hstable : (prefixWord ++ tailWord_1498231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498231).length < 2 ^ (prefixWord ++ tailWord_1498231).sum := by decide
  have hdescent : baseEnd_1498231 < baseStart_1498231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498258 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_1498258 : Nat := 118140960795 + 1498258 * 2 ^ 59
def prefixEnd_1498258 : Nat := 4983230072969 + 3 ^ 40 * 1498258 * 2
def baseEnd_1498258 : Nat := 769326498444104292384643

theorem tailTrace_1498258 : CollatzResearch.WordTrace tailWord_1498258 prefixEnd_1498258 769326498444104292384643 := by
  unfold tailWord_1498258
  simp only [CollatzResearch.WordTrace]
  refine ⟨13661489651518655734923857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36430639070716415293130285 13661489651518655734923857)
  ·
    refine ⟨10246117238638991801192893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13661489651518655734923857 10246117238638991801192893)
    ·
      refine ⟨3842293964489621925447335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10246117238638991801192893 3842293964489621925447335)
      ·
        refine ⟨5763440946734432888171003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3842293964489621925447335 5763440946734432888171003)
        ·
          refine ⟨8645161420101649332256505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5763440946734432888171003 8645161420101649332256505)
          ·
            refine ⟨6483871065076236999192379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8645161420101649332256505 6483871065076236999192379)
            ·
              refine ⟨9725806597614355498788569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6483871065076236999192379 9725806597614355498788569)
              ·
                refine ⟨7294354948210766624091427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9725806597614355498788569 7294354948210766624091427)
                ·
                  refine ⟨10941532422316149936137141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7294354948210766624091427 10941532422316149936137141)
                  ·
                    refine ⟨1025768664592139056512857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10941532422316149936137141 1025768664592139056512857)
                    ·
                      refine ⟨769326498444104292384643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025768664592139056512857 769326498444104292384643)
                      ·
                        rfl

theorem cell23_1498258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_1498258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498258 prefixEnd_1498258 := by exact prefixLift 1498258
  have htrace : WordTrace (prefixWord ++ tailWord_1498258) baseStart_1498258 baseEnd_1498258 := by
    simpa [prefixWord, tailWord_1498258, baseEnd_1498258] using wordTrace_append hprefix tailTrace_1498258
  have hstable : (prefixWord ++ tailWord_1498258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498258).length < 2 ^ (prefixWord ++ tailWord_1498258).sum := by decide
  have hdescent : baseEnd_1498258 < baseStart_1498258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498268 : List Nat := [2, 2, 3, 2, 1, 3, 2, 2, 1, 5]
def baseStart_1498268 : Nat := 118140960795 + 1498268 * 2 ^ 59
def prefixEnd_1498268 : Nat := 4983230072969 + 3 ^ 40 * 1498268 * 2
def baseEnd_1498268 : Nat := 256443877750216417753199

theorem tailTrace_1498268 : CollatzResearch.WordTrace tailWord_1498268 prefixEnd_1498268 256443877750216417753199 := by
  unfold tailWord_1498268
  simp only [CollatzResearch.WordTrace]
  refine ⟨27323161668019197323779729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36430882224025596431706305 27323161668019197323779729)
  ·
    refine ⟨20492371251014397992834797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27323161668019197323779729 20492371251014397992834797)
    ·
      refine ⟨7684639219130399247313049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20492371251014397992834797 7684639219130399247313049)
      ·
        refine ⟨5763479414347799435484787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7684639219130399247313049 5763479414347799435484787)
        ·
          refine ⟨8645219121521699153227181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5763479414347799435484787 8645219121521699153227181)
          ·
            refine ⟨3241957170570637182460193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8645219121521699153227181 3241957170570637182460193)
            ·
              refine ⟨2431467877927977886845145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3241957170570637182460193 2431467877927977886845145)
              ·
                refine ⟨1823600908445983415133859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431467877927977886845145 1823600908445983415133859)
                ·
                  refine ⟨2735401362668975122700789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823600908445983415133859 2735401362668975122700789)
                  ·
                    refine ⟨256443877750216417753199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2735401362668975122700789 256443877750216417753199)
                    ·
                      rfl

theorem cell23_1498268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_1498268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498268 prefixEnd_1498268 := by exact prefixLift 1498268
  have htrace : WordTrace (prefixWord ++ tailWord_1498268) baseStart_1498268 baseEnd_1498268 := by
    simpa [prefixWord, tailWord_1498268, baseEnd_1498268] using wordTrace_append hprefix tailTrace_1498268
  have hstable : (prefixWord ++ tailWord_1498268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498268).length < 2 ^ (prefixWord ++ tailWord_1498268).sum := by decide
  have hdescent : baseEnd_1498268 < baseStart_1498268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498321 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 1, 3, 3]
def baseStart_1498321 : Nat := 118140960795 + 1498321 * 2 ^ 59
def prefixEnd_1498321 : Nat := 4983230072969 + 3 ^ 40 * 1498321 * 2
def baseEnd_1498321 : Nat := 769358847725337545896853

theorem tailTrace_1498321 : CollatzResearch.WordTrace tailWord_1498321 prefixEnd_1498321 769358847725337545896853 := by
  unfold tailWord_1498321
  simp only [CollatzResearch.WordTrace]
  refine ⟨54648256404846384699238817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36432170936564256466159211 54648256404846384699238817)
  ·
    refine ⟨40986192303634788524429113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54648256404846384699238817 40986192303634788524429113)
    ·
      refine ⟨30739644227726091393321835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40986192303634788524429113 30739644227726091393321835)
      ·
        refine ⟨46109466341589137089982753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30739644227726091393321835 46109466341589137089982753)
        ·
          refine ⟨34582099756191852817487065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46109466341589137089982753 34582099756191852817487065)
          ·
            refine ⟨25936574817143889613115299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34582099756191852817487065 25936574817143889613115299)
            ·
              refine ⟨38904862225715834419672949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25936574817143889613115299 38904862225715834419672949)
              ·
                refine ⟨3647330833660859476844339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38904862225715834419672949 3647330833660859476844339)
                ·
                  refine ⟨5470996250491289215266509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647330833660859476844339 5470996250491289215266509)
                  ·
                    refine ⟨2051623593934233455724941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5470996250491289215266509 2051623593934233455724941)
                    ·
                      refine ⟨769358847725337545896853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2051623593934233455724941 769358847725337545896853)
                      ·
                        rfl

theorem cell23_1498321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_1498321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498321 prefixEnd_1498321 := by exact prefixLift 1498321
  have htrace : WordTrace (prefixWord ++ tailWord_1498321) baseStart_1498321 baseEnd_1498321 := by
    simpa [prefixWord, tailWord_1498321, baseEnd_1498321] using wordTrace_append hprefix tailTrace_1498321
  have hstable : (prefixWord ++ tailWord_1498321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498321).length < 2 ^ (prefixWord ++ tailWord_1498321).sum := by decide
  have hdescent : baseEnd_1498321 < baseStart_1498321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498325 : List Nat := [1, 3, 2, 4, 1, 1, 3, 2, 1, 2, 3]
def baseStart_1498325 : Nat := 118140960795 + 1498325 * 2 ^ 59
def prefixEnd_1498325 : Nat := 4983230072969 + 3 ^ 40 * 1498325 * 2
def baseEnd_1498325 : Nat := 769360901647955530246835

theorem tailTrace_1498325 : CollatzResearch.WordTrace tailWord_1498325 prefixEnd_1498325 769360901647955530246835 := by
  unfold tailWord_1498325
  simp only [CollatzResearch.WordTrace]
  refine ⟨54648402296831893382384429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36432268197887928921589619 54648402296831893382384429)
  ·
    refine ⟨20493150861311960018394161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54648402296831893382384429 20493150861311960018394161)
    ·
      refine ⟨15369863145983970013795621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20493150861311960018394161 15369863145983970013795621)
      ·
        refine ⟨2881849339871994377586679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15369863145983970013795621 2881849339871994377586679)
        ·
          refine ⟨4322774009807991566380019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2881849339871994377586679 4322774009807991566380019)
          ·
            refine ⟨6484161014711987349570029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4322774009807991566380019 6484161014711987349570029)
            ·
              refine ⟨2431560380516995256088761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6484161014711987349570029 2431560380516995256088761)
              ·
                refine ⟨1823670285387746442066571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431560380516995256088761 1823670285387746442066571)
                ·
                  refine ⟨2735505428081619663099857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823670285387746442066571 2735505428081619663099857)
                  ·
                    refine ⟨2051629071061214747324893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2735505428081619663099857 2051629071061214747324893)
                    ·
                      refine ⟨769360901647955530246835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2051629071061214747324893 769360901647955530246835)
                      ·
                        rfl

theorem cell23_1498325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_1498325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498325 prefixEnd_1498325 := by exact prefixLift 1498325
  have htrace : WordTrace (prefixWord ++ tailWord_1498325) baseStart_1498325 baseEnd_1498325 := by
    simpa [prefixWord, tailWord_1498325, baseEnd_1498325] using wordTrace_append hprefix tailTrace_1498325
  have hstable : (prefixWord ++ tailWord_1498325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498325).length < 2 ^ (prefixWord ++ tailWord_1498325).sum := by decide
  have hdescent : baseEnd_1498325 < baseStart_1498325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498355 : List Nat := [1, 1, 1, 2, 2, 6, 2, 2, 2, 1, 3]
def baseStart_1498355 : Nat := 118140960795 + 1498355 * 2 ^ 59
def prefixEnd_1498355 : Nat := 4983230072969 + 3 ^ 40 * 1498355 * 2
def baseEnd_1498355 : Nat := 769376306067590412871697

theorem tailTrace_1498355 : CollatzResearch.WordTrace tailWord_1498355 prefixEnd_1498355 769376306067590412871697 := by
  unfold tailWord_1498355
  simp only [CollatzResearch.WordTrace]
  refine ⟨54649496486723208505976519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36432997657815472337317679 54649496486723208505976519)
  ·
    refine ⟨81974244730084812758964779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54649496486723208505976519 81974244730084812758964779)
    ·
      refine ⟨122961367095127219138447169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81974244730084812758964779 122961367095127219138447169)
      ·
        refine ⟨92221025321345414353835377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122961367095127219138447169 92221025321345414353835377)
        ·
          refine ⟨69165768991009060765376533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92221025321345414353835377 69165768991009060765376533)
          ·
            refine ⟨3242145421453549723377025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69165768991009060765376533 3242145421453549723377025)
            ·
              refine ⟨2431609066090162292532769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3242145421453549723377025 2431609066090162292532769)
              ·
                refine ⟨1823706799567621719399577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431609066090162292532769 1823706799567621719399577)
                ·
                  refine ⟨1367780099675716289549683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1823706799567621719399577 1367780099675716289549683)
                  ·
                    refine ⟨2051670149513574434324525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1367780099675716289549683 2051670149513574434324525)
                    ·
                      refine ⟨769376306067590412871697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2051670149513574434324525 769376306067590412871697)
                      ·
                        rfl

theorem cell23_1498355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 1, 3].length) (baseStart_1498355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498355 prefixEnd_1498355 := by exact prefixLift 1498355
  have htrace : WordTrace (prefixWord ++ tailWord_1498355) baseStart_1498355 baseEnd_1498355 := by
    simpa [prefixWord, tailWord_1498355, baseEnd_1498355] using wordTrace_append hprefix tailTrace_1498355
  have hstable : (prefixWord ++ tailWord_1498355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498355).length < 2 ^ (prefixWord ++ tailWord_1498355).sum := by decide
  have hdescent : baseEnd_1498355 < baseStart_1498355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498371 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 2, 6]
def baseStart_1498371 : Nat := 118140960795 + 1498371 * 2 ^ 59
def prefixEnd_1498371 : Nat := 4983230072969 + 3 ^ 40 * 1498371 * 2
def baseEnd_1498371 : Nat := 256461507252687450090541

theorem tailTrace_1498371 : CollatzResearch.WordTrace tailWord_1498371 prefixEnd_1498371 256461507252687450090541 := by
  unfold tailWord_1498371
  simp only [CollatzResearch.WordTrace]
  refine ⟨54650080054665243238558967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36433386703110162159039311 54650080054665243238558967)
  ·
    refine ⟨81975120081997864857838451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54650080054665243238558967 81975120081997864857838451)
    ·
      refine ⟨122962680122996797286757677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81975120081997864857838451 122962680122996797286757677)
      ·
        refine ⟨46111005046123798982534129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122962680122996797286757677 46111005046123798982534129)
        ·
          refine ⟨34583253784592849236900597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46111005046123798982534129 34583253784592849236900597)
          ·
            refine ⟨3242180042305579615959431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34583253784592849236900597 3242180042305579615959431)
            ·
              refine ⟨4863270063458369423939147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3242180042305579615959431 4863270063458369423939147)
              ·
                refine ⟨7294905095187554135908721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4863270063458369423939147 7294905095187554135908721)
                ·
                  refine ⟨5471178821390665601931541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7294905095187554135908721 5471178821390665601931541)
                  ·
                    refine ⟨256461507252687450090541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5471178821390665601931541 256461507252687450090541)
                    ·
                      rfl

theorem cell23_1498371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 6].length) (baseStart_1498371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498371 prefixEnd_1498371 := by exact prefixLift 1498371
  have htrace : WordTrace (prefixWord ++ tailWord_1498371) baseStart_1498371 baseEnd_1498371 := by
    simpa [prefixWord, tailWord_1498371, baseEnd_1498371] using wordTrace_append hprefix tailTrace_1498371
  have hstable : (prefixWord ++ tailWord_1498371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498371).length < 2 ^ (prefixWord ++ tailWord_1498371).sum := by decide
  have hdescent : baseEnd_1498371 < baseStart_1498371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498391 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 4]
def baseStart_1498391 : Nat := 118140960795 + 1498391 * 2 ^ 59
def prefixEnd_1498391 : Nat := 4983230072969 + 3 ^ 40 * 1498391 * 2
def baseEnd_1498391 : Nat := 769394791371152272021531

theorem tailTrace_1498391 : CollatzResearch.WordTrace tailWord_1498391 prefixEnd_1498391 769394791371152272021531 := by
  unfold tailWord_1498391
  simp only [CollatzResearch.WordTrace]
  refine ⟨54650809514592786654287027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36433873009728524436191351 54650809514592786654287027)
  ·
    refine ⟨81976214271889179981430541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54650809514592786654287027 81976214271889179981430541)
    ·
      refine ⟨30741080351958442493036453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81976214271889179981430541 30741080351958442493036453)
      ·
        refine ⟨5763952565992207967444335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30741080351958442493036453 5763952565992207967444335)
        ·
          refine ⟨8645928848988311951166503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5763952565992207967444335 8645928848988311951166503)
          ·
            refine ⟨12968893273482467926749755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8645928848988311951166503 12968893273482467926749755)
            ·
              refine ⟨19453339910223701890124633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12968893273482467926749755 19453339910223701890124633)
              ·
                refine ⟨14590004932667776417593475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19453339910223701890124633 14590004932667776417593475)
                ·
                  refine ⟨21885007399001664626390213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14590004932667776417593475 21885007399001664626390213)
                  ·
                    refine ⟨4103438887312812117448165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21885007399001664626390213 4103438887312812117448165)
                    ·
                      refine ⟨769394791371152272021531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4103438887312812117448165 769394791371152272021531)
                      ·
                        rfl

theorem cell23_1498391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_1498391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498391 prefixEnd_1498391 := by exact prefixLift 1498391
  have htrace : WordTrace (prefixWord ++ tailWord_1498391) baseStart_1498391 baseEnd_1498391 := by
    simpa [prefixWord, tailWord_1498391, baseEnd_1498391] using wordTrace_append hprefix tailTrace_1498391
  have hstable : (prefixWord ++ tailWord_1498391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498391).length < 2 ^ (prefixWord ++ tailWord_1498391).sum := by decide
  have hdescent : baseEnd_1498391 < baseStart_1498391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498399 : List Nat := [1, 1, 2, 4, 4, 2, 2, 1, 1, 3, 2]
def baseStart_1498399 : Nat := 118140960795 + 1498399 * 2 ^ 59
def prefixEnd_1498399 : Nat := 4983230072969 + 3 ^ 40 * 1498399 * 2
def baseEnd_1498399 : Nat := 769398899216388240721495

theorem tailTrace_1498399 : CollatzResearch.WordTrace tailWord_1498399 prefixEnd_1498399 769398899216388240721495 := by
  unfold tailWord_1498399
  simp only [CollatzResearch.WordTrace]
  refine ⟨54651101298563804020578251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36434067532375869347052167 54651101298563804020578251)
  ·
    refine ⟨81976651947845706030867377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54651101298563804020578251 81976651947845706030867377)
    ·
      refine ⟨61482488960884279523150533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81976651947845706030867377 61482488960884279523150533)
      ·
        refine ⟨11527966680165802410590725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61482488960884279523150533 11527966680165802410590725)
        ·
          refine ⟨2161493752531087951985761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11527966680165802410590725 2161493752531087951985761)
          ·
            refine ⟨1621120314398315963989321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2161493752531087951985761 1621120314398315963989321)
            ·
              refine ⟨1215840235798736972991991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1621120314398315963989321 1215840235798736972991991)
              ·
                refine ⟨1823760353698105459487987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215840235798736972991991 1823760353698105459487987)
                ·
                  refine ⟨2735640530547158189231981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823760353698105459487987 2735640530547158189231981)
                  ·
                    refine ⟨1025865198955184320961993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2735640530547158189231981 1025865198955184320961993)
                    ·
                      refine ⟨769398899216388240721495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025865198955184320961993 769398899216388240721495)
                      ·
                        rfl

theorem cell23_1498399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_1498399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498399 prefixEnd_1498399 := by exact prefixLift 1498399
  have htrace : WordTrace (prefixWord ++ tailWord_1498399) baseStart_1498399 baseEnd_1498399 := by
    simpa [prefixWord, tailWord_1498399, baseEnd_1498399] using wordTrace_append hprefix tailTrace_1498399
  have hstable : (prefixWord ++ tailWord_1498399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498399).length < 2 ^ (prefixWord ++ tailWord_1498399).sum := by decide
  have hdescent : baseEnd_1498399 < baseStart_1498399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498408 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_1498408 : Nat := 118140960795 + 1498408 * 2 ^ 59
def prefixEnd_1498408 : Nat := 4983230072969 + 3 ^ 40 * 1498408 * 2
def baseEnd_1498408 : Nat := 769403520542278705508953

theorem tailTrace_1498408 : CollatzResearch.WordTrace tailWord_1498408 prefixEnd_1498408 769403520542278705508953 := by
  unfold tailWord_1498408
  simp only [CollatzResearch.WordTrace]
  refine ⟨27325714777765599278827939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36434286370354132371770585 27325714777765599278827939)
  ·
    refine ⟨40988572166648398918241909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27325714777765599278827939 40988572166648398918241909)
    ·
      refine ⟨3842678640623287398585179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40988572166648398918241909 3842678640623287398585179)
      ·
        refine ⟨5764017960934931097877769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3842678640623287398585179 5764017960934931097877769)
        ·
          refine ⟨4323013470701198323408327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5764017960934931097877769 4323013470701198323408327)
          ·
            refine ⟨6484520206051797485112491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4323013470701198323408327 6484520206051797485112491)
            ·
              refine ⟨9726780309077696227668737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6484520206051797485112491 9726780309077696227668737)
              ·
                refine ⟨7295085231808272170751553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9726780309077696227668737 7295085231808272170751553)
                ·
                  refine ⟨5471313923856204128063665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7295085231808272170751553 5471313923856204128063665)
                  ·
                    refine ⟨4103485442892153096047749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5471313923856204128063665 4103485442892153096047749)
                    ·
                      refine ⟨769403520542278705508953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4103485442892153096047749 769403520542278705508953)
                      ·
                        rfl

theorem cell23_1498408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_1498408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498408 prefixEnd_1498408 := by exact prefixLift 1498408
  have htrace : WordTrace (prefixWord ++ tailWord_1498408) baseStart_1498408 baseEnd_1498408 := by
    simpa [prefixWord, tailWord_1498408, baseEnd_1498408] using wordTrace_append hprefix tailTrace_1498408
  have hstable : (prefixWord ++ tailWord_1498408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498408).length < 2 ^ (prefixWord ++ tailWord_1498408).sum := by decide
  have hdescent : baseEnd_1498408 < baseStart_1498408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498418 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 7]
def baseStart_1498418 : Nat := 118140960795 + 1498418 * 2 ^ 59
def prefixEnd_1498418 : Nat := 4983230072969 + 3 ^ 40 * 1498418 * 2
def baseEnd_1498418 : Nat := 85489850594313740709323

theorem tailTrace_1498418 : CollatzResearch.WordTrace tailWord_1498418 prefixEnd_1498418 85489850594313740709323 := by
  unfold tailWord_1498418
  simp only [CollatzResearch.WordTrace]
  refine ⟨13662948571373742566379977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36434529523663313510346605 13662948571373742566379977)
  ·
    refine ⟨10247211428530306924784983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13662948571373742566379977 10247211428530306924784983)
    ·
      refine ⟨15370817142795460387177475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10247211428530306924784983 15370817142795460387177475)
      ·
        refine ⟨23056225714193190580766213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15370817142795460387177475 23056225714193190580766213)
        ·
          refine ⟨4323042321411223233893665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23056225714193190580766213 4323042321411223233893665)
          ·
            refine ⟨3242281741058417425420249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4323042321411223233893665 3242281741058417425420249)
            ·
              refine ⟨2431711305793813069065187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3242281741058417425420249 2431711305793813069065187)
              ·
                refine ⟨3647566958690719603597781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2431711305793813069065187 3647566958690719603597781)
                ·
                  refine ⟨85489850594313740709323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3647566958690719603597781 85489850594313740709323)
                  ·
                    rfl

theorem cell23_1498418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_1498418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498418 prefixEnd_1498418 := by exact prefixLift 1498418
  have htrace : WordTrace (prefixWord ++ tailWord_1498418) baseStart_1498418 baseEnd_1498418 := by
    simpa [prefixWord, tailWord_1498418, baseEnd_1498418] using wordTrace_append hprefix tailTrace_1498418
  have hstable : (prefixWord ++ tailWord_1498418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498418).length < 2 ^ (prefixWord ++ tailWord_1498418).sum := by decide
  have hdescent : baseEnd_1498418 < baseStart_1498418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498428 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 2, 3, 3]
def baseStart_1498428 : Nat := 118140960795 + 1498428 * 2 ^ 59
def prefixEnd_1498428 : Nat := 4983230072969 + 3 ^ 40 * 1498428 * 2
def baseEnd_1498428 : Nat := 769413790155368627258861

theorem tailTrace_1498428 : CollatzResearch.WordTrace tailWord_1498428 prefixEnd_1498428 769413790155368627258861 := by
  unfold tailWord_1498428
  simp only [CollatzResearch.WordTrace]
  refine ⟨27326079507729370986691969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36434772676972494648922625 27326079507729370986691969)
  ·
    refine ⟨20494559630797028240018977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27326079507729370986691969 20494559630797028240018977)
    ·
      refine ⟨15370919723097771180014233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20494559630797028240018977 15370919723097771180014233)
      ·
        refine ⟨11528189792323328385010675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15370919723097771180014233 11528189792323328385010675)
        ·
          refine ⟨17292284688484992577516013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11528189792323328385010675 17292284688484992577516013)
          ·
            refine ⟨6484606758181872216568505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17292284688484992577516013 6484606758181872216568505)
            ·
              refine ⟨4863455068636404162426379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6484606758181872216568505 4863455068636404162426379)
              ·
                refine ⟨7295182602954606243639569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4863455068636404162426379 7295182602954606243639569)
                ·
                  refine ⟨5471386952215954682729677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7295182602954606243639569 5471386952215954682729677)
                  ·
                    refine ⟨2051770107080983006023629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5471386952215954682729677 2051770107080983006023629)
                    ·
                      refine ⟨769413790155368627258861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2051770107080983006023629 769413790155368627258861)
                      ·
                        rfl

theorem cell23_1498428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_1498428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498428 prefixEnd_1498428 := by exact prefixLift 1498428
  have htrace : WordTrace (prefixWord ++ tailWord_1498428) baseStart_1498428 baseEnd_1498428 := by
    simpa [prefixWord, tailWord_1498428, baseEnd_1498428] using wordTrace_append hprefix tailTrace_1498428
  have hstable : (prefixWord ++ tailWord_1498428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498428).length < 2 ^ (prefixWord ++ tailWord_1498428).sum := by decide
  have hdescent : baseEnd_1498428 < baseStart_1498428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498429 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 1, 4, 2]
def baseStart_1498429 : Nat := 118140960795 + 1498429 * 2 ^ 59
def prefixEnd_1498429 : Nat := 4983230072969 + 3 ^ 40 * 1498429 * 2
def baseEnd_1498429 : Nat := 769414303636023123346357

theorem tailTrace_1498429 : CollatzResearch.WordTrace tailWord_1498429 prefixEnd_1498429 769414303636023123346357 := by
  unfold tailWord_1498429
  simp only [CollatzResearch.WordTrace]
  refine ⟨54652195488455119144170341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36434796992303412762780227 54652195488455119144170341)
  ·
    refine ⟨10247286654085334839531939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54652195488455119144170341 10247286654085334839531939)
    ·
      refine ⟨15370929981128002259297909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10247286654085334839531939 15370929981128002259297909)
      ·
        refine ⟨1441024685730750211809179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15370929981128002259297909 1441024685730750211809179)
        ·
          refine ⟨2161537028596125317713769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1441024685730750211809179 2161537028596125317713769)
          ·
            refine ⟨1621152771447093988285327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2161537028596125317713769 1621152771447093988285327)
            ·
              refine ⟨2431729157170640982427991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621152771447093988285327 2431729157170640982427991)
              ·
                refine ⟨3647593735755961473641987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2431729157170640982427991 3647593735755961473641987)
                ·
                  refine ⟨5471390603633942210462981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647593735755961473641987 5471390603633942210462981)
                  ·
                    refine ⟨1025885738181364164461809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5471390603633942210462981 1025885738181364164461809)
                    ·
                      refine ⟨769414303636023123346357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025885738181364164461809 769414303636023123346357)
                      ·
                        rfl

theorem cell23_1498429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_1498429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498429 prefixEnd_1498429 := by exact prefixLift 1498429
  have htrace : WordTrace (prefixWord ++ tailWord_1498429) baseStart_1498429 baseEnd_1498429 := by
    simpa [prefixWord, tailWord_1498429, baseEnd_1498429] using wordTrace_append hprefix tailTrace_1498429
  have hstable : (prefixWord ++ tailWord_1498429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498429).length < 2 ^ (prefixWord ++ tailWord_1498429).sum := by decide
  have hdescent : baseEnd_1498429 < baseStart_1498429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498431 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 1, 7]
def baseStart_1498431 : Nat := 118140960795 + 1498431 * 2 ^ 59
def prefixEnd_1498431 : Nat := 4983230072969 + 3 ^ 40 * 1498431 * 2
def baseEnd_1498431 : Nat := 256471776865777371840449

theorem tailTrace_1498431 : CollatzResearch.WordTrace tailWord_1498431 prefixEnd_1498431 256471776865777371840449 := by
  unfold tailWord_1498431
  simp only [CollatzResearch.WordTrace]
  refine ⟨54652268434447873485743147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36434845622965248990495431 54652268434447873485743147)
  ·
    refine ⟨81978402651671810228614721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54652268434447873485743147 81978402651671810228614721)
    ·
      refine ⟨61483801988753857671461041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81978402651671810228614721 61483801988753857671461041)
      ·
        refine ⟨46112851491565393253595781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61483801988753857671461041 46112851491565393253595781)
        ·
          refine ⟨8646159654668511235049209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46112851491565393253595781 8646159654668511235049209)
          ·
            refine ⟨6484619741001383426286907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8646159654668511235049209 6484619741001383426286907)
            ·
              refine ⟨9726929611502075139430361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6484619741001383426286907 9726929611502075139430361)
              ·
                refine ⟨7295197208626556354572771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9726929611502075139430361 7295197208626556354572771)
                ·
                  refine ⟨10942795812939834531859157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7295197208626556354572771 10942795812939834531859157)
                  ·
                    refine ⟨256471776865777371840449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10942795812939834531859157 256471776865777371840449)
                    ·
                      rfl

theorem cell23_1498431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 7].length) (baseStart_1498431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498431 prefixEnd_1498431 := by exact prefixLift 1498431
  have htrace : WordTrace (prefixWord ++ tailWord_1498431) baseStart_1498431 baseEnd_1498431 := by
    simpa [prefixWord, tailWord_1498431, baseEnd_1498431] using wordTrace_append hprefix tailTrace_1498431
  have hstable : (prefixWord ++ tailWord_1498431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498431).length < 2 ^ (prefixWord ++ tailWord_1498431).sum := by decide
  have hdescent : baseEnd_1498431 < baseStart_1498431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498451 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 4]
def baseStart_1498451 : Nat := 118140960795 + 1498451 * 2 ^ 59
def prefixEnd_1498451 : Nat := 4983230072969 + 3 ^ 40 * 1498451 * 2
def baseEnd_1498451 : Nat := 769425600210422037271255

theorem tailTrace_1498451 : CollatzResearch.WordTrace tailWord_1498451 prefixEnd_1498451 769425600210422037271255 := by
  unfold tailWord_1498451
  simp only [CollatzResearch.WordTrace]
  refine ⟨54652997894375416901471207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36435331929583611267647471 54652997894375416901471207)
  ·
    refine ⟨81979496841563125352206811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54652997894375416901471207 81979496841563125352206811)
    ·
      refine ⟨122969245262344688028310217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81979496841563125352206811 122969245262344688028310217)
      ·
        refine ⟨92226933946758516021232663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122969245262344688028310217 92226933946758516021232663)
        ·
          refine ⟨138340400920137774031848995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92226933946758516021232663 138340400920137774031848995)
          ·
            refine ⟨207510601380206661047773493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138340400920137774031848995 207510601380206661047773493)
            ·
              refine ⟨19454118879394374473228765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 207510601380206661047773493 19454118879394374473228765)
              ·
                refine ⟨7295294579772890427460787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19454118879394374473228765 7295294579772890427460787)
                ·
                  refine ⟨10942941869659335641191181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7295294579772890427460787 10942941869659335641191181)
                  ·
                    refine ⟨4103603201122250865446693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10942941869659335641191181 4103603201122250865446693)
                    ·
                      refine ⟨769425600210422037271255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4103603201122250865446693 769425600210422037271255)
                      ·
                        rfl

theorem cell23_1498451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_1498451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498451 prefixEnd_1498451 := by exact prefixLift 1498451
  have htrace : WordTrace (prefixWord ++ tailWord_1498451) baseStart_1498451 baseEnd_1498451 := by
    simpa [prefixWord, tailWord_1498451, baseEnd_1498451] using wordTrace_append hprefix tailTrace_1498451
  have hstable : (prefixWord ++ tailWord_1498451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498451).length < 2 ^ (prefixWord ++ tailWord_1498451).sum := by decide
  have hdescent : baseEnd_1498451 < baseStart_1498451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498468 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_1498468 : Nat := 118140960795 + 1498468 * 2 ^ 59
def prefixEnd_1498468 : Nat := 4983230072969 + 3 ^ 40 * 1498468 * 2
def baseEnd_1498468 : Nat := 769434329381548470758677

theorem tailTrace_1498468 : CollatzResearch.WordTrace tailWord_1498468 prefixEnd_1498468 769434329381548470758677 := by
  unfold tailWord_1498468
  simp only [CollatzResearch.WordTrace]
  refine ⟨27326808967656914402420029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36435745290209219203226705 27326808967656914402420029)
  ·
    refine ⟨10247553362871342900907511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27326808967656914402420029 10247553362871342900907511)
    ·
      refine ⟨15371330044307014351361267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10247553362871342900907511 15371330044307014351361267)
      ·
        refine ⟨23056995066460521527041901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15371330044307014351361267 23056995066460521527041901)
        ·
          refine ⟨8646373149922695572640713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23056995066460521527041901 8646373149922695572640713)
          ·
            refine ⟨6484779862442021679480535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8646373149922695572640713 6484779862442021679480535)
            ·
              refine ⟨9727169793663032519220803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6484779862442021679480535 9727169793663032519220803)
              ·
                refine ⟨14590754690494548778831205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9727169793663032519220803 14590754690494548778831205)
                ·
                  refine ⟨2735766504467727896030851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14590754690494548778831205 2735766504467727896030851)
                  ·
                    refine ⟨4103649756701591844046277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2735766504467727896030851 4103649756701591844046277)
                    ·
                      refine ⟨769434329381548470758677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4103649756701591844046277 769434329381548470758677)
                      ·
                        rfl

theorem cell23_1498468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_1498468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498468 prefixEnd_1498468 := by exact prefixLift 1498468
  have htrace : WordTrace (prefixWord ++ tailWord_1498468) baseStart_1498468 baseEnd_1498468 := by
    simpa [prefixWord, tailWord_1498468, baseEnd_1498468] using wordTrace_append hprefix tailTrace_1498468
  have hstable : (prefixWord ++ tailWord_1498468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498468).length < 2 ^ (prefixWord ++ tailWord_1498468).sum := by decide
  have hdescent : baseEnd_1498468 < baseStart_1498468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498481 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 6]
def baseStart_1498481 : Nat := 118140960795 + 1498481 * 2 ^ 59
def prefixEnd_1498481 : Nat := 4983230072969 + 3 ^ 40 * 1498481 * 2
def baseEnd_1498481 : Nat := 769441004630056919896117

theorem tailTrace_1498481 : CollatzResearch.WordTrace tailWord_1498481 prefixEnd_1498481 769441004630056919896117 := by
  unfold tailWord_1498481
  simp only [CollatzResearch.WordTrace]
  refine ⟨54654092084266732025063297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36436061389511154683375531 54654092084266732025063297)
  ·
    refine ⟨40990569063200049018797473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54654092084266732025063297 40990569063200049018797473)
    ·
      refine ⟨30742926797400036764098105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40990569063200049018797473 30742926797400036764098105)
      ·
        refine ⟨23057195098050027573073579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30742926797400036764098105 23057195098050027573073579)
        ·
          refine ⟨34585792647075041359610369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23057195098050027573073579 34585792647075041359610369)
          ·
            refine ⟨25939344485306281019707777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34585792647075041359610369 25939344485306281019707777)
            ·
              refine ⟨19454508363979710764780833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25939344485306281019707777 19454508363979710764780833)
              ·
                refine ⟨14590881272984783073585625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19454508363979710764780833 14590881272984783073585625)
                ·
                  refine ⟨10943160954738587305189219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14590881272984783073585625 10943160954738587305189219)
                  ·
                    refine ⟨16414741432107880957783829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10943160954738587305189219 16414741432107880957783829)
                    ·
                      refine ⟨769441004630056919896117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16414741432107880957783829 769441004630056919896117)
                      ·
                        rfl

theorem cell23_1498481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_1498481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498481 prefixEnd_1498481 := by exact prefixLift 1498481
  have htrace : WordTrace (prefixWord ++ tailWord_1498481) baseStart_1498481 baseEnd_1498481 := by
    simpa [prefixWord, tailWord_1498481, baseEnd_1498481] using wordTrace_append hprefix tailTrace_1498481
  have hstable : (prefixWord ++ tailWord_1498481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498481).length < 2 ^ (prefixWord ++ tailWord_1498481).sum := by decide
  have hdescent : baseEnd_1498481 < baseStart_1498481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498525 : List Nat := [1, 4, 2, 1, 3, 2, 2, 2, 6]
def baseStart_1498525 : Nat := 118140960795 + 1498525 * 2 ^ 59
def prefixEnd_1498525 : Nat := 4983230072969 + 3 ^ 40 * 1498525 * 2
def baseEnd_1498525 : Nat := 85495955308761638638435

theorem tailTrace_1498525 : CollatzResearch.WordTrace tailWord_1498525 prefixEnd_1498525 85495955308761638638435 := by
  unfold tailWord_1498525
  simp only [CollatzResearch.WordTrace]
  refine ⟨54655696896107327539665029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36437131264071551693110019 54655696896107327539665029)
  ·
    refine ⟨10247943168020123913687193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54655696896107327539665029 10247943168020123913687193)
    ·
      refine ⟨7685957376015092935265395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10247943168020123913687193 7685957376015092935265395)
      ·
        refine ⟨11528936064022639402898093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7685957376015092935265395 11528936064022639402898093)
        ·
          refine ⟨4323351024008489776086785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11528936064022639402898093 4323351024008489776086785)
          ·
            refine ⟨3242513268006367332065089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4323351024008489776086785 3242513268006367332065089)
            ·
              refine ⟨2431884951004775499048817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3242513268006367332065089 2431884951004775499048817)
              ·
                refine ⟨1823913713253581624286613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431884951004775499048817 1823913713253581624286613)
                ·
                  refine ⟨85495955308761638638435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1823913713253581624286613 85495955308761638638435)
                  ·
                    rfl

theorem cell23_1498525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_1498525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498525 prefixEnd_1498525 := by exact prefixLift 1498525
  have htrace : WordTrace (prefixWord ++ tailWord_1498525) baseStart_1498525 baseEnd_1498525 := by
    simpa [prefixWord, tailWord_1498525, baseEnd_1498525] using wordTrace_append hprefix tailTrace_1498525
  have hstable : (prefixWord ++ tailWord_1498525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498525).length < 2 ^ (prefixWord ++ tailWord_1498525).sum := by decide
  have hdescent : baseEnd_1498525 < baseStart_1498525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498545 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 1, 5, 2]
def baseStart_1498545 : Nat := 118140960795 + 1498545 * 2 ^ 59
def prefixEnd_1498545 : Nat := 4983230072969 + 3 ^ 40 * 1498545 * 2
def baseEnd_1498545 : Nat := 769473867391944669495823

theorem tailTrace_1498545 : CollatzResearch.WordTrace tailWord_1498545 prefixEnd_1498545 769473867391944669495823 := by
  unfold tailWord_1498545
  simp only [CollatzResearch.WordTrace]
  refine ⟨54656426356034870955393089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36437617570689913970262059 54656426356034870955393089)
  ·
    refine ⟨40992319767026153216544817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54656426356034870955393089 40992319767026153216544817)
    ·
      refine ⟨30744239825269614912408613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40992319767026153216544817 30744239825269614912408613)
      ·
        refine ⟨5764544967238052796076615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30744239825269614912408613 5764544967238052796076615)
        ·
          refine ⟨8646817450857079194114923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5764544967238052796076615 8646817450857079194114923)
          ·
            refine ⟨12970226176285618791172385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8646817450857079194114923 12970226176285618791172385)
            ·
              refine ⟨9727669632214214093379289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12970226176285618791172385 9727669632214214093379289)
              ·
                refine ⟨7295752224160660570034467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9727669632214214093379289 7295752224160660570034467)
                ·
                  refine ⟨10943628336240990855051701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7295752224160660570034467 10943628336240990855051701)
                  ·
                    refine ⟨1025965156522592892661097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10943628336240990855051701 1025965156522592892661097)
                    ·
                      refine ⟨769473867391944669495823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1025965156522592892661097 769473867391944669495823)
                      ·
                        rfl

theorem cell23_1498545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_1498545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498545 prefixEnd_1498545 := by exact prefixLift 1498545
  have htrace : WordTrace (prefixWord ++ tailWord_1498545) baseStart_1498545 baseEnd_1498545 := by
    simpa [prefixWord, tailWord_1498545, baseEnd_1498545] using wordTrace_append hprefix tailTrace_1498545
  have hstable : (prefixWord ++ tailWord_1498545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498545).length < 2 ^ (prefixWord ++ tailWord_1498545).sum := by decide
  have hdescent : baseEnd_1498545 < baseStart_1498545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498568 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 1, 6]
def baseStart_1498568 : Nat := 118140960795 + 1498568 * 2 ^ 59
def prefixEnd_1498568 : Nat := 4983230072969 + 3 ^ 40 * 1498568 * 2
def baseEnd_1498568 : Nat := 256495225815666026502739

theorem tailTrace_1498568 : CollatzResearch.WordTrace tailWord_1498568 prefixEnd_1498568 256495225815666026502739 := by
  unfold tailWord_1498568
  simp only [CollatzResearch.WordTrace]
  refine ⟨27328632617475772941740179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36438176823301030588986905 27328632617475772941740179)
  ·
    refine ⟨40992948926213659412610269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27328632617475772941740179 40992948926213659412610269)
    ·
      refine ⟨15372355847330122279728851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40992948926213659412610269 15372355847330122279728851)
      ·
        refine ⟨23058533770995183419593277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15372355847330122279728851 23058533770995183419593277)
        ·
          refine ⟨8646950164123193782347479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23058533770995183419593277 8646950164123193782347479)
          ·
            refine ⟨12970425246184790673521219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8646950164123193782347479 12970425246184790673521219)
            ·
              refine ⟨19455637869277186010281829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12970425246184790673521219 19455637869277186010281829)
              ·
                refine ⟨3647932100489472376927843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19455637869277186010281829 3647932100489472376927843)
                ·
                  refine ⟨5471898150734208565391765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647932100489472376927843 5471898150734208565391765)
                  ·
                    refine ⟨256495225815666026502739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5471898150734208565391765 256495225815666026502739)
                    ·
                      rfl

theorem cell23_1498568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_1498568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498568 prefixEnd_1498568 := by exact prefixLift 1498568
  have htrace : WordTrace (prefixWord ++ tailWord_1498568) baseStart_1498568 baseEnd_1498568 := by
    simpa [prefixWord, tailWord_1498568, baseEnd_1498568] using wordTrace_append hprefix tailTrace_1498568
  have hstable : (prefixWord ++ tailWord_1498568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498568).length < 2 ^ (prefixWord ++ tailWord_1498568).sum := by decide
  have hdescent : baseEnd_1498568 < baseStart_1498568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498572 : List Nat := [2, 2, 1, 4, 2, 1, 4, 1, 1, 5]
def baseStart_1498572 : Nat := 118140960795 + 1498572 * 2 ^ 59
def prefixEnd_1498572 : Nat := 4983230072969 + 3 ^ 40 * 1498572 * 2
def baseEnd_1498572 : Nat := 256495910456538687952733

theorem tailTrace_1498572 : CollatzResearch.WordTrace tailWord_1498572 prefixEnd_1498572 256495910456538687952733 := by
  unfold tailWord_1498572
  simp only [CollatzResearch.WordTrace]
  refine ⟨27328705563468527283312985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36438274084624703044417313 27328705563468527283312985)
  ·
    refine ⟨20496529172601395462484739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27328705563468527283312985 20496529172601395462484739)
    ·
      refine ⟨30744793758902093193727109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20496529172601395462484739 30744793758902093193727109)
      ·
        refine ⟨5764648829794142473823833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30744793758902093193727109 5764648829794142473823833)
        ·
          refine ⟨4323486622345606855367875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5764648829794142473823833 4323486622345606855367875)
          ·
            refine ⟨6485229933518410283051813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4323486622345606855367875 6485229933518410283051813)
            ·
              refine ⟨1215980612534701928072215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6485229933518410283051813 1215980612534701928072215)
              ·
                refine ⟨1823970918802052892108323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215980612534701928072215 1823970918802052892108323)
                ·
                  refine ⟨2735956378203079338162485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823970918802052892108323 2735956378203079338162485)
                  ·
                    refine ⟨256495910456538687952733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2735956378203079338162485 256495910456538687952733)
                    ·
                      rfl

theorem cell23_1498572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 1, 5].length) (baseStart_1498572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498572 prefixEnd_1498572 := by exact prefixLift 1498572
  have htrace : WordTrace (prefixWord ++ tailWord_1498572) baseStart_1498572 baseEnd_1498572 := by
    simpa [prefixWord, tailWord_1498572, baseEnd_1498572] using wordTrace_append hprefix tailTrace_1498572
  have hstable : (prefixWord ++ tailWord_1498572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498572).length < 2 ^ (prefixWord ++ tailWord_1498572).sum := by decide
  have hdescent : baseEnd_1498572 < baseStart_1498572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498585 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 4, 4]
def baseStart_1498585 : Nat := 118140960795 + 1498585 * 2 ^ 59
def prefixEnd_1498585 : Nat := 4983230072969 + 3 ^ 40 * 1498585 * 2
def baseEnd_1498585 : Nat := 256498135539374837665213

theorem tailTrace_1498585 : CollatzResearch.WordTrace tailWord_1498585 prefixEnd_1498585 256498135539374837665213 := by
  unfold tailWord_1498585
  simp only [CollatzResearch.WordTrace]
  refine ⟨54657885275889957786849209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36438590183926638524566139 54657885275889957786849209)
  ·
    refine ⟨40993413956917468340136907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54657885275889957786849209 40993413956917468340136907)
    ·
      refine ⟨61490120935376202510205361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40993413956917468340136907 61490120935376202510205361)
      ·
        refine ⟨46117590701532151882654021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61490120935376202510205361 46117590701532151882654021)
        ·
          refine ⟨8647048256537278477997629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46117590701532151882654021 8647048256537278477997629)
          ·
            refine ⟨3242643096201479429249111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8647048256537278477997629 3242643096201479429249111)
            ·
              refine ⟨4863964644302219143873667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3242643096201479429249111 4863964644302219143873667)
              ·
                refine ⟨7295946966453328715810501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4863964644302219143873667 7295946966453328715810501)
                ·
                  refine ⟨1367990056209999134214469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7295946966453328715810501 1367990056209999134214469)
                  ·
                    refine ⟨256498135539374837665213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1367990056209999134214469 256498135539374837665213)
                    ·
                      rfl

theorem cell23_1498585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 4].length) (baseStart_1498585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498585 prefixEnd_1498585 := by exact prefixLift 1498585
  have htrace : WordTrace (prefixWord ++ tailWord_1498585) baseStart_1498585 baseEnd_1498585 := by
    simpa [prefixWord, tailWord_1498585, baseEnd_1498585] using wordTrace_append hprefix tailTrace_1498585
  have hstable : (prefixWord ++ tailWord_1498585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498585).length < 2 ^ (prefixWord ++ tailWord_1498585).sum := by decide
  have hdescent : baseEnd_1498585 < baseStart_1498585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498595 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 5]
def baseStart_1498595 : Nat := 118140960795 + 1498595 * 2 ^ 59
def prefixEnd_1498595 : Nat := 4983230072969 + 3 ^ 40 * 1498595 * 2
def baseEnd_1498595 : Nat := 769499541424669473870593

theorem tailTrace_1498595 : CollatzResearch.WordTrace tailWord_1498595 prefixEnd_1498595 769499541424669473870593 := by
  unfold tailWord_1498595
  simp only [CollatzResearch.WordTrace]
  refine ⟨54658250005853729494713239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36438833337235819663142159 54658250005853729494713239)
  ·
    refine ⟨81987375008780594242069859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54658250005853729494713239 81987375008780594242069859)
    ·
      refine ⟨122981062513170891363104789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81987375008780594242069859 122981062513170891363104789)
      ·
        refine ⟨5764737305304885532645537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122981062513170891363104789 5764737305304885532645537)
        ·
          refine ⟨4323552978978664149484153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5764737305304885532645537 4323552978978664149484153)
          ·
            refine ⟨3242664734233998112113115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4323552978978664149484153 3242664734233998112113115)
            ·
              refine ⟨4863997101350997168169673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3242664734233998112113115 4863997101350997168169673)
              ·
                refine ⟨3647997826013247876127255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4863997101350997168169673 3647997826013247876127255)
                ·
                  refine ⟨5471996739019871814190883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647997826013247876127255 5471996739019871814190883)
                  ·
                    refine ⟨8207995108529807721286325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5471996739019871814190883 8207995108529807721286325)
                    ·
                      refine ⟨769499541424669473870593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8207995108529807721286325 769499541424669473870593)
                      ·
                        rfl

theorem cell23_1498595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_1498595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498595 prefixEnd_1498595 := by exact prefixLift 1498595
  have htrace : WordTrace (prefixWord ++ tailWord_1498595) baseStart_1498595 baseEnd_1498595 := by
    simpa [prefixWord, tailWord_1498595, baseEnd_1498595] using wordTrace_append hprefix tailTrace_1498595
  have hstable : (prefixWord ++ tailWord_1498595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498595).length < 2 ^ (prefixWord ++ tailWord_1498595).sum := by decide
  have hdescent : baseEnd_1498595 < baseStart_1498595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498602 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 1, 6]
def baseStart_1498602 : Nat := 118140960795 + 1498602 * 2 ^ 59
def prefixEnd_1498602 : Nat := 4983230072969 + 3 ^ 40 * 1498602 * 2
def baseEnd_1498602 : Nat := 256501045263083648827687

theorem tailTrace_1498602 : CollatzResearch.WordTrace tailWord_1498602 prefixEnd_1498602 256501045263083648827687 := by
  unfold tailWord_1498602
  simp only [CollatzResearch.WordTrace]
  refine ⟨13664626329207092422554515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36439003544552246460145373 13664626329207092422554515)
  ·
    refine ⟨20496939493810638633831773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13664626329207092422554515 20496939493810638633831773)
    ·
      refine ⟨7686352310178989487686915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20496939493810638633831773 7686352310178989487686915)
      ·
        refine ⟨11529528465268484231530373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7686352310178989487686915 11529528465268484231530373)
        ·
          refine ⟨2161786587237840793411945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11529528465268484231530373 2161786587237840793411945)
          ·
            refine ⟨1621339940428380595058959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2161786587237840793411945 1621339940428380595058959)
            ·
              refine ⟨2432009910642570892588439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621339940428380595058959 2432009910642570892588439)
              ·
                refine ⟨3648014865963856338882659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2432009910642570892588439 3648014865963856338882659)
                ·
                  refine ⟨5472022298945784508323989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3648014865963856338882659 5472022298945784508323989)
                  ·
                    refine ⟨256501045263083648827687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5472022298945784508323989 256501045263083648827687)
                    ·
                      rfl

theorem cell23_1498602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_1498602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498602 prefixEnd_1498602 := by exact prefixLift 1498602
  have htrace : WordTrace (prefixWord ++ tailWord_1498602) baseStart_1498602 baseEnd_1498602 := by
    simpa [prefixWord, tailWord_1498602, baseEnd_1498602] using wordTrace_append hprefix tailTrace_1498602
  have hstable : (prefixWord ++ tailWord_1498602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498602).length < 2 ^ (prefixWord ++ tailWord_1498602).sum := by decide
  have hdescent : baseEnd_1498602 < baseStart_1498602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498652 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 3, 3, 2]
def baseStart_1498652 : Nat := 118140960795 + 1498652 * 2 ^ 59
def prefixEnd_1498652 : Nat := 4983230072969 + 3 ^ 40 * 1498652 * 2
def baseEnd_1498652 : Nat := 769528809821975750857831

theorem tailTrace_1498652 : CollatzResearch.WordTrace tailWord_1498652 prefixEnd_1498652 769528809821975750857831 := by
  unfold tailWord_1498652
  simp only [CollatzResearch.WordTrace]
  refine ⟨27330164483323614114769105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36440219311098152153025473 27330164483323614114769105)
  ·
    refine ⟨20497623362492710586076829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27330164483323614114769105 20497623362492710586076829)
    ·
      refine ⟨7686608760934766469778811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20497623362492710586076829 7686608760934766469778811)
      ·
        refine ⟨11529913141402149704668217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7686608760934766469778811 11529913141402149704668217)
        ·
          refine ⟨8647434856051612278501163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11529913141402149704668217 8647434856051612278501163)
          ·
            refine ⟨12971152284077418417751745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8647434856051612278501163 12971152284077418417751745)
            ·
              refine ⟨9728364213058063813313809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12971152284077418417751745 9728364213058063813313809)
              ·
                refine ⟨7296273159793547859985357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9728364213058063813313809 7296273159793547859985357)
                ·
                  refine ⟨2736102434922580447494509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7296273159793547859985357 2736102434922580447494509)
                  ·
                    refine ⟨1026038413095967667810441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2736102434922580447494509 1026038413095967667810441)
                    ·
                      refine ⟨769528809821975750857831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1026038413095967667810441 769528809821975750857831)
                      ·
                        rfl

theorem cell23_1498652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_1498652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498652 prefixEnd_1498652 := by exact prefixLift 1498652
  have htrace : WordTrace (prefixWord ++ tailWord_1498652) baseStart_1498652 baseEnd_1498652 := by
    simpa [prefixWord, tailWord_1498652, baseEnd_1498652] using wordTrace_append hprefix tailTrace_1498652
  have hstable : (prefixWord ++ tailWord_1498652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498652).length < 2 ^ (prefixWord ++ tailWord_1498652).sum := by decide
  have hdescent : baseEnd_1498652 < baseStart_1498652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498659 : List Nat := [1, 1, 1, 4, 5, 1, 1, 3, 2, 1, 3]
def baseStart_1498659 : Nat := 118140960795 + 1498659 * 2 ^ 59
def prefixEnd_1498659 : Nat := 4983230072969 + 3 ^ 40 * 1498659 * 2
def baseEnd_1498659 : Nat := 769532404186557223470299

theorem tailTrace_1498659 : CollatzResearch.WordTrace tailWord_1498659 prefixEnd_1498659 769532404186557223470299 := by
  unfold tailWord_1498659
  simp only [CollatzResearch.WordTrace]
  refine ⟨54660584277621868425043031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36440389518414578950028687 54660584277621868425043031)
  ·
    refine ⟨81990876416432802637564547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54660584277621868425043031 81990876416432802637564547)
    ·
      refine ⟨122986314624649203956346821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81990876416432802637564547 122986314624649203956346821)
      ·
        refine ⟨23059933992121725741815029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122986314624649203956346821 23059933992121725741815029)
        ·
          refine ⟨2161868811761411788295159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23059933992121725741815029 2161868811761411788295159)
          ·
            refine ⟨3242803217642117682442739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2161868811761411788295159 3242803217642117682442739)
            ·
              refine ⟨4864204826463176523664109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3242803217642117682442739 4864204826463176523664109)
              ·
                refine ⟨1824076809923691196374041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4864204826463176523664109 1824076809923691196374041)
                ·
                  refine ⟨1368057607442768397280531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1824076809923691196374041 1368057607442768397280531)
                  ·
                    refine ⟨2052086411164152595920797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1368057607442768397280531 2052086411164152595920797)
                    ·
                      refine ⟨769532404186557223470299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2052086411164152595920797 769532404186557223470299)
                      ·
                        rfl

theorem cell23_1498659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_1498659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498659 prefixEnd_1498659 := by exact prefixLift 1498659
  have htrace : WordTrace (prefixWord ++ tailWord_1498659) baseStart_1498659 baseEnd_1498659 := by
    simpa [prefixWord, tailWord_1498659, baseEnd_1498659] using wordTrace_append hprefix tailTrace_1498659
  have hstable : (prefixWord ++ tailWord_1498659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498659).length < 2 ^ (prefixWord ++ tailWord_1498659).sum := by decide
  have hdescent : baseEnd_1498659 < baseStart_1498659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498682 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2]
def baseStart_1498682 : Nat := 118140960795 + 1498682 * 2 ^ 59
def prefixEnd_1498682 : Nat := 4983230072969 + 3 ^ 40 * 1498682 * 2
def baseEnd_1498682 : Nat := 769544214241610633482693

theorem tailTrace_1498682 : CollatzResearch.WordTrace tailWord_1498682 prefixEnd_1498682 769544214241610633482693 := by
  unfold tailWord_1498682
  simp only [CollatzResearch.WordTrace]
  refine ⟨13665355789134635838282575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36440948771025695568753533 13665355789134635838282575)
  ·
    refine ⟨20498033683701953757423863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13665355789134635838282575 20498033683701953757423863)
    ·
      refine ⟨30747050525552930636135795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20498033683701953757423863 30747050525552930636135795)
      ·
        refine ⟨46120575788329395954203693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30747050525552930636135795 46120575788329395954203693)
        ·
          refine ⟨17295215920623523482826385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46120575788329395954203693 17295215920623523482826385)
          ·
            refine ⟨12971411940467642612119789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17295215920623523482826385 12971411940467642612119789)
            ·
              refine ⟨4864279477675365979544921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12971411940467642612119789 4864279477675365979544921)
              ·
                refine ⟨3648209608256524484658691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4864279477675365979544921 3648209608256524484658691)
                ·
                  refine ⟨5472314412384786726988037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3648209608256524484658691 5472314412384786726988037)
                  ·
                    refine ⟨1026058952322147511310257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5472314412384786726988037 1026058952322147511310257)
                    ·
                      refine ⟨769544214241610633482693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1026058952322147511310257 769544214241610633482693)
                      ·
                        rfl

theorem cell23_1498682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2].length) (baseStart_1498682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498682 prefixEnd_1498682 := by exact prefixLift 1498682
  have htrace : WordTrace (prefixWord ++ tailWord_1498682) baseStart_1498682 baseEnd_1498682 := by
    simpa [prefixWord, tailWord_1498682, baseEnd_1498682] using wordTrace_append hprefix tailTrace_1498682
  have hstable : (prefixWord ++ tailWord_1498682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498682).length < 2 ^ (prefixWord ++ tailWord_1498682).sum := by decide
  have hdescent : baseEnd_1498682 < baseStart_1498682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498694 : List Nat := [6, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_1498694 : Nat := 118140960795 + 1498694 * 2 ^ 59
def prefixEnd_1498694 : Nat := 4983230072969 + 3 ^ 40 * 1498694 * 2
def baseEnd_1498694 : Nat := 769550376009464586532639

theorem tailTrace_1498694 : CollatzResearch.WordTrace tailWord_1498694 prefixEnd_1498694 769550376009464586532639 := by
  unfold tailWord_1498694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1708183151015470918830223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36441240554996712935044757 1708183151015470918830223)
  ·
    refine ⟨2562274726523206378245335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1708183151015470918830223 2562274726523206378245335)
    ·
      refine ⟨3843412089784809567368003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2562274726523206378245335 3843412089784809567368003)
      ·
        refine ⟨5765118134677214351052005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3843412089784809567368003 5765118134677214351052005)
        ·
          refine ⟨1080959650251977690822251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5765118134677214351052005 1080959650251977690822251)
          ·
            refine ⟨1621439475377966536233377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080959650251977690822251 1621439475377966536233377)
            ·
              refine ⟨1216079606533474902175033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1621439475377966536233377 1216079606533474902175033)
              ·
                refine ⟨912059704900106176631275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1216079606533474902175033 912059704900106176631275)
                ·
                  refine ⟨1368089557350159264946913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 912059704900106176631275 1368089557350159264946913)
                  ·
                    refine ⟨1026067168012619448710185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1368089557350159264946913 1026067168012619448710185)
                    ·
                      refine ⟨769550376009464586532639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1026067168012619448710185 769550376009464586532639)
                      ·
                        rfl

theorem cell23_1498694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_1498694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498694 prefixEnd_1498694 := by exact prefixLift 1498694
  have htrace : WordTrace (prefixWord ++ tailWord_1498694) baseStart_1498694 baseEnd_1498694 := by
    simpa [prefixWord, tailWord_1498694, baseEnd_1498694] using wordTrace_append hprefix tailTrace_1498694
  have hstable : (prefixWord ++ tailWord_1498694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498694).length < 2 ^ (prefixWord ++ tailWord_1498694).sum := by decide
  have hdescent : baseEnd_1498694 < baseStart_1498694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498716 : List Nat := [2, 2, 4, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_1498716 : Nat := 118140960795 + 1498716 * 2 ^ 59
def prefixEnd_1498716 : Nat := 4983230072969 + 3 ^ 40 * 1498716 * 2
def baseEnd_1498716 : Nat := 769561672583863500457537

theorem tailTrace_1498716 : CollatzResearch.WordTrace tailWord_1498716 prefixEnd_1498716 769561672583863500457537 := by
  unfold tailWord_1498716
  simp only [CollatzResearch.WordTrace]
  refine ⟨27331331619207683579934001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36441775492276911439912001 27331331619207683579934001)
  ·
    refine ⟨20498498714405762684950501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27331331619207683579934001 20498498714405762684950501)
    ·
      refine ⟨3843468508951080503428219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20498498714405762684950501 3843468508951080503428219)
      ·
        refine ⟨5765202763426620755142329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3843468508951080503428219 5765202763426620755142329)
        ·
          refine ⟨4323902072569965566356747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5765202763426620755142329 4323902072569965566356747)
          ·
            refine ⟨6485853108854948349535121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4323902072569965566356747 6485853108854948349535121)
            ·
              refine ⟨4864389831641211262151341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6485853108854948349535121 4864389831641211262151341)
              ·
                refine ⟨1824146186865454223306753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4864389831641211262151341 1824146186865454223306753)
                ·
                  refine ⟨1368109640149090667480065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1824146186865454223306753 1368109640149090667480065)
                  ·
                    refine ⟨1026082230111818000610049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1368109640149090667480065 1026082230111818000610049)
                    ·
                      refine ⟨769561672583863500457537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1026082230111818000610049 769561672583863500457537)
                      ·
                        rfl

theorem cell23_1498716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_1498716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498716 prefixEnd_1498716 := by exact prefixLift 1498716
  have htrace : WordTrace (prefixWord ++ tailWord_1498716) baseStart_1498716 baseEnd_1498716 := by
    simpa [prefixWord, tailWord_1498716, baseEnd_1498716] using wordTrace_append hprefix tailTrace_1498716
  have hstable : (prefixWord ++ tailWord_1498716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498716).length < 2 ^ (prefixWord ++ tailWord_1498716).sum := by decide
  have hdescent : baseEnd_1498716 < baseStart_1498716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498755 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 4]
def baseStart_1498755 : Nat := 118140960795 + 1498755 * 2 ^ 59
def prefixEnd_1498755 : Nat := 4983230072969 + 3 ^ 40 * 1498755 * 2
def baseEnd_1498755 : Nat := 769581698329388847869857

theorem tailTrace_1498755 : CollatzResearch.WordTrace tailWord_1498755 prefixEnd_1498755 769581698329388847869857 := by
  unfold tailWord_1498755
  simp only [CollatzResearch.WordTrace]
  refine ⟨54664085685274076820537719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36442723790182717880358479 54664085685274076820537719)
  ·
    refine ⟨81996128527911115230806579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54664085685274076820537719 81996128527911115230806579)
    ·
      refine ⟨122994192791866672846209869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81996128527911115230806579 122994192791866672846209869)
      ·
        refine ⟨46122822296950002317328701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122994192791866672846209869 46122822296950002317328701)
        ·
          refine ⟨17296058361356250868998263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46122822296950002317328701 17296058361356250868998263)
          ·
            refine ⟨25944087542034376303497395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17296058361356250868998263 25944087542034376303497395)
            ·
              refine ⟨38916131313051564455246093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25944087542034376303497395 38916131313051564455246093)
              ·
                refine ⟨14593549242394336670717285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38916131313051564455246093 14593549242394336670717285)
                ·
                  refine ⟨2736290482948938125759491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14593549242394336670717285 2736290482948938125759491)
                  ·
                    refine ⟨4104435724423407188639237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2736290482948938125759491 4104435724423407188639237)
                    ·
                      refine ⟨769581698329388847869857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4104435724423407188639237 769581698329388847869857)
                      ·
                        rfl

theorem cell23_1498755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_1498755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498755 prefixEnd_1498755 := by exact prefixLift 1498755
  have htrace : WordTrace (prefixWord ++ tailWord_1498755) baseStart_1498755 baseEnd_1498755 := by
    simpa [prefixWord, tailWord_1498755, baseEnd_1498755] using wordTrace_append hprefix tailTrace_1498755
  have hstable : (prefixWord ++ tailWord_1498755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498755).length < 2 ^ (prefixWord ++ tailWord_1498755).sum := by decide
  have hdescent : baseEnd_1498755 < baseStart_1498755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498806 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1498806 : Nat := 118140960795 + 1498806 * 2 ^ 59
def prefixEnd_1498806 : Nat := 4983230072969 + 3 ^ 40 * 1498806 * 2
def baseEnd_1498806 : Nat := 769607885842768148332123

theorem tailTrace_1498806 : CollatzResearch.WordTrace tailWord_1498806 prefixEnd_1498806 769607885842768148332123 := by
  unfold tailWord_1498806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3416621613005582033165267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36443963872059541687096181 3416621613005582033165267)
  ·
    refine ⟨5124932419508373049747901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3416621613005582033165267 5124932419508373049747901)
    ·
      refine ⟨1921849657315639893655463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5124932419508373049747901 1921849657315639893655463)
      ·
        refine ⟨2882774485973459840483195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1921849657315639893655463 2882774485973459840483195)
        ·
          refine ⟨4324161728960189760724793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2882774485973459840483195 4324161728960189760724793)
          ·
            refine ⟨3243121296720142320543595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4324161728960189760724793 3243121296720142320543595)
            ·
              refine ⟨4864681945080213480815393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3243121296720142320543595 4864681945080213480815393)
              ·
                refine ⟨3648511458810160110611545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4864681945080213480815393 3648511458810160110611545)
                ·
                  refine ⟨2736383594107620082958659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3648511458810160110611545 2736383594107620082958659)
                  ·
                    refine ⟨4104575391161430124437989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2736383594107620082958659 4104575391161430124437989)
                    ·
                      refine ⟨769607885842768148332123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4104575391161430124437989 769607885842768148332123)
                      ·
                        rfl

theorem cell23_1498806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1498806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498806 prefixEnd_1498806 := by exact prefixLift 1498806
  have htrace : WordTrace (prefixWord ++ tailWord_1498806) baseStart_1498806 baseEnd_1498806 := by
    simpa [prefixWord, tailWord_1498806, baseEnd_1498806] using wordTrace_append hprefix tailTrace_1498806
  have hstable : (prefixWord ++ tailWord_1498806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498806).length < 2 ^ (prefixWord ++ tailWord_1498806).sum := by decide
  have hdescent : baseEnd_1498806 < baseStart_1498806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498816 : List Nat := [2, 1, 1, 2, 4, 1, 5, 2, 1, 4]
def baseStart_1498816 : Nat := 118140960795 + 1498816 * 2 ^ 59
def prefixEnd_1498816 : Nat := 4983230072969 + 3 ^ 40 * 1498816 * 2
def baseEnd_1498816 : Nat := 256537673549771036402359

theorem tailTrace_1498816 : CollatzResearch.WordTrace tailWord_1498816 prefixEnd_1498816 256537673549771036402359 := by
  unfold tailWord_1498816
  simp only [CollatzResearch.WordTrace]
  refine ⟨27333155269026542119254151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36444207025368722825672201 27333155269026542119254151)
  ·
    refine ⟨40999732903539813178881227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27333155269026542119254151 40999732903539813178881227)
    ·
      refine ⟨61499599355309719768321841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40999732903539813178881227 61499599355309719768321841)
      ·
        refine ⟨46124699516482289826241381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61499599355309719768321841 46124699516482289826241381)
        ·
          refine ⟨8648381159340429342420259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46124699516482289826241381 8648381159340429342420259)
          ·
            refine ⟨12972571739010644013630389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8648381159340429342420259 12972571739010644013630389)
            ·
              refine ⟨1216178600532247876277849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12972571739010644013630389 1216178600532247876277849)
              ·
                refine ⟨912133950399185907208387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1216178600532247876277849 912133950399185907208387)
                ·
                  refine ⟨1368200925598778860812581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 912133950399185907208387 1368200925598778860812581)
                  ·
                    refine ⟨256537673549771036402359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1368200925598778860812581 256537673549771036402359)
                    ·
                      rfl

theorem cell23_1498816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 1, 4].length) (baseStart_1498816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498816 prefixEnd_1498816 := by exact prefixLift 1498816
  have htrace : WordTrace (prefixWord ++ tailWord_1498816) baseStart_1498816 baseEnd_1498816 := by
    simpa [prefixWord, tailWord_1498816, baseEnd_1498816] using wordTrace_append hprefix tailTrace_1498816
  have hstable : (prefixWord ++ tailWord_1498816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498816).length < 2 ^ (prefixWord ++ tailWord_1498816).sum := by decide
  have hdescent : baseEnd_1498816 < baseStart_1498816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498832 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 1, 5, 2]
def baseStart_1498832 : Nat := 118140960795 + 1498832 * 2 ^ 59
def prefixEnd_1498832 : Nat := 4983230072969 + 3 ^ 40 * 1498832 * 2
def baseEnd_1498832 : Nat := 769621236339785046607003

theorem tailTrace_1498832 : CollatzResearch.WordTrace tailWord_1498832 prefixEnd_1498832 769621236339785046607003 := by
  unfold tailWord_1498832
  simp only [CollatzResearch.WordTrace]
  refine ⟨27333447052997559485545375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36444596070663412647393833 27333447052997559485545375)
  ·
    refine ⟨41000170579496339228318063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27333447052997559485545375 41000170579496339228318063)
    ·
      refine ⟨61500255869244508842477095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41000170579496339228318063 61500255869244508842477095)
      ·
        refine ⟨92250383803866763263715643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61500255869244508842477095 92250383803866763263715643)
        ·
          refine ⟨138375575705800144895573465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92250383803866763263715643 138375575705800144895573465)
          ·
            refine ⟨103781681779350108671680099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138375575705800144895573465 103781681779350108671680099)
            ·
              refine ⟨155672522669025163007520149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103781681779350108671680099 155672522669025163007520149)
              ·
                refine ⟨7297149500110554515977507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 155672522669025163007520149 7297149500110554515977507)
                ·
                  refine ⟨10945724250165831773966261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7297149500110554515977507 10945724250165831773966261)
                  ·
                    refine ⟨1026161648453046728809337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10945724250165831773966261 1026161648453046728809337)
                    ·
                      refine ⟨769621236339785046607003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1026161648453046728809337 769621236339785046607003)
                      ·
                        rfl

theorem cell23_1498832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 1, 5, 2].length) (baseStart_1498832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498832 prefixEnd_1498832 := by exact prefixLift 1498832
  have htrace : WordTrace (prefixWord ++ tailWord_1498832) baseStart_1498832 baseEnd_1498832 := by
    simpa [prefixWord, tailWord_1498832, baseEnd_1498832] using wordTrace_append hprefix tailTrace_1498832
  have hstable : (prefixWord ++ tailWord_1498832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498832).length < 2 ^ (prefixWord ++ tailWord_1498832).sum := by decide
  have hdescent : baseEnd_1498832 < baseStart_1498832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498842 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 3, 5]
def baseStart_1498842 : Nat := 118140960795 + 1498842 * 2 ^ 59
def prefixEnd_1498842 : Nat := 4983230072969 + 3 ^ 40 * 1498842 * 2
def baseEnd_1498842 : Nat := 256542123715443335827319

theorem tailTrace_1498842 : CollatzResearch.WordTrace tailWord_1498842 prefixEnd_1498842 256542123715443335827319 := by
  unfold tailWord_1498842
  simp only [CollatzResearch.WordTrace]
  refine ⟨13666814708989722669738695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36444839223972593785969853 13666814708989722669738695)
  ·
    refine ⟨20500222063484584004608043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13666814708989722669738695 20500222063484584004608043)
    ·
      refine ⟨30750333095226876006912065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20500222063484584004608043 30750333095226876006912065)
      ·
        refine ⟨23062749821420157005184049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30750333095226876006912065 23062749821420157005184049)
        ·
          refine ⟨17297062366065117753888037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23062749821420157005184049 17297062366065117753888037)
          ·
            refine ⟨3243199193637209578854007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17297062366065117753888037 3243199193637209578854007)
            ·
              refine ⟨4864798790455814368281011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3243199193637209578854007 4864798790455814368281011)
              ·
                refine ⟨7297198185683721552421517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4864798790455814368281011 7297198185683721552421517)
                ·
                  refine ⟨2736449319631395582158069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7297198185683721552421517 2736449319631395582158069)
                  ·
                    refine ⟨256542123715443335827319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2736449319631395582158069 256542123715443335827319)
                    ·
                      rfl

theorem cell23_1498842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_1498842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498842 prefixEnd_1498842 := by exact prefixLift 1498842
  have htrace : WordTrace (prefixWord ++ tailWord_1498842) baseStart_1498842 baseEnd_1498842 := by
    simpa [prefixWord, tailWord_1498842, baseEnd_1498842] using wordTrace_append hprefix tailTrace_1498842
  have hstable : (prefixWord ++ tailWord_1498842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498842).length < 2 ^ (prefixWord ++ tailWord_1498842).sum := by decide
  have hdescent : baseEnd_1498842 < baseStart_1498842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498875 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 6]
def baseStart_1498875 : Nat := 118140960795 + 1498875 * 2 ^ 59
def prefixEnd_1498875 : Nat := 4983230072969 + 3 ^ 40 * 1498875 * 2
def baseEnd_1498875 : Nat := 769643316007928378369305

theorem tailTrace_1498875 : CollatzResearch.WordTrace tailWord_1498875 prefixEnd_1498875 769643316007928378369305 := by
  unfold tailWord_1498875
  simp only [CollatzResearch.WordTrace]
  refine ⟨54668462444839337314906079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36445641629892891543270719 54668462444839337314906079)
  ·
    refine ⟨82002693667259005972359119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54668462444839337314906079 82002693667259005972359119)
    ·
      refine ⟨123004040500888508958538679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82002693667259005972359119 123004040500888508958538679)
      ·
        refine ⟨184506060751332763437808019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123004040500888508958538679 184506060751332763437808019)
        ·
          refine ⟨276759091126999145156712029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184506060751332763437808019 276759091126999145156712029)
          ·
            refine ⟨103784659172624679433767011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276759091126999145156712029 103784659172624679433767011)
            ·
              refine ⟨155676988758937019150650517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103784659172624679433767011 155676988758937019150650517)
              ·
                refine ⟨7297358848075172772686743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 155676988758937019150650517 7297358848075172772686743)
                ·
                  refine ⟨10946038272112759159030115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7297358848075172772686743 10946038272112759159030115)
                  ·
                    refine ⟨16419057408169138738545173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10946038272112759159030115 16419057408169138738545173)
                    ·
                      refine ⟨769643316007928378369305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16419057408169138738545173 769643316007928378369305)
                      ·
                        rfl

theorem cell23_1498875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 6].length) (baseStart_1498875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498875 prefixEnd_1498875 := by exact prefixLift 1498875
  have htrace : WordTrace (prefixWord ++ tailWord_1498875) baseStart_1498875 baseEnd_1498875 := by
    simpa [prefixWord, tailWord_1498875, baseEnd_1498875] using wordTrace_append hprefix tailTrace_1498875
  have hstable : (prefixWord ++ tailWord_1498875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498875).length < 2 ^ (prefixWord ++ tailWord_1498875).sum := by decide
  have hdescent : baseEnd_1498875 < baseStart_1498875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498892 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 1, 2, 4]
def baseStart_1498892 : Nat := 118140960795 + 1498892 * 2 ^ 59
def prefixEnd_1498892 : Nat := 4983230072969 + 3 ^ 40 * 1498892 * 2
def baseEnd_1498892 : Nat := 769652045179054811856727

theorem tailTrace_1498892 : CollatzResearch.WordTrace tailWord_1498892 prefixEnd_1498892 769652045179054811856727 := by
  unfold tailWord_1498892
  simp only [CollatzResearch.WordTrace]
  refine ⟨27334541242888874609137465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36446054990518499478849953 27334541242888874609137465)
  ·
    refine ⟨20500905932166655956853099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27334541242888874609137465 20500905932166655956853099)
    ·
      refine ⟨30751358898249983935279649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20500905932166655956853099 30751358898249983935279649)
      ·
        refine ⟨23063519173687487951459737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30751358898249983935279649 23063519173687487951459737)
        ·
          refine ⟨17297639380265615963594803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23063519173687487951459737 17297639380265615963594803)
          ·
            refine ⟨25946459070398423945392205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17297639380265615963594803 25946459070398423945392205)
            ·
              refine ⟨9729922151399408979522077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25946459070398423945392205 9729922151399408979522077)
              ·
                refine ⟨3648720806774778367320779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9729922151399408979522077 3648720806774778367320779)
                ·
                  refine ⟨5473081210162167550981169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3648720806774778367320779 5473081210162167550981169)
                  ·
                    refine ⟨4104810907621625663235877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5473081210162167550981169 4104810907621625663235877)
                    ·
                      refine ⟨769652045179054811856727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4104810907621625663235877 769652045179054811856727)
                      ·
                        rfl

theorem cell23_1498892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_1498892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498892 prefixEnd_1498892 := by exact prefixLift 1498892
  have htrace : WordTrace (prefixWord ++ tailWord_1498892) baseStart_1498892 baseEnd_1498892 := by
    simpa [prefixWord, tailWord_1498892, baseEnd_1498892] using wordTrace_append hprefix tailTrace_1498892
  have hstable : (prefixWord ++ tailWord_1498892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498892).length < 2 ^ (prefixWord ++ tailWord_1498892).sum := by decide
  have hdescent : baseEnd_1498892 < baseStart_1498892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498900 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_1498900 : Nat := 118140960795 + 1498900 * 2 ^ 59
def prefixEnd_1498900 : Nat := 4983230072969 + 3 ^ 40 * 1498900 * 2
def baseEnd_1498900 : Nat := 769656153024290780556691

theorem tailTrace_1498900 : CollatzResearch.WordTrace tailWord_1498900 prefixEnd_1498900 769656153024290780556691 := by
  unfold tailWord_1498900
  simp only [CollatzResearch.WordTrace]
  refine ⟨27334687134874383292283077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36446249513165844389710769 27334687134874383292283077)
  ·
    refine ⟨5125253837788946867303077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27334687134874383292283077 5125253837788946867303077)
    ·
      refine ⟨960985094585427537619327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5125253837788946867303077 960985094585427537619327)
      ·
        refine ⟨1441477641878141306428991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 960985094585427537619327 1441477641878141306428991)
        ·
          refine ⟨2162216462817211959643487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1441477641878141306428991 2162216462817211959643487)
          ·
            refine ⟨3243324694225817939465231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2162216462817211959643487 3243324694225817939465231)
            ·
              refine ⟨4864987041338726909197847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3243324694225817939465231 4864987041338726909197847)
              ·
                refine ⟨7297480562008090363796771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4864987041338726909197847 7297480562008090363796771)
                ·
                  refine ⟨10946220843012135545695157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7297480562008090363796771 10946220843012135545695157)
                  ·
                    refine ⟨1026208204032387707408921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10946220843012135545695157 1026208204032387707408921)
                    ·
                      refine ⟨769656153024290780556691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1026208204032387707408921 769656153024290780556691)
                      ·
                        rfl

theorem cell23_1498900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_1498900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498900 prefixEnd_1498900 := by exact prefixLift 1498900
  have htrace : WordTrace (prefixWord ++ tailWord_1498900) baseStart_1498900 baseEnd_1498900 := by
    simpa [prefixWord, tailWord_1498900, baseEnd_1498900] using wordTrace_append hprefix tailTrace_1498900
  have hstable : (prefixWord ++ tailWord_1498900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498900).length < 2 ^ (prefixWord ++ tailWord_1498900).sum := by decide
  have hdescent : baseEnd_1498900 < baseStart_1498900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498905 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 6]
def baseStart_1498905 : Nat := 118140960795 + 1498905 * 2 ^ 59
def prefixEnd_1498905 : Nat := 4983230072969 + 3 ^ 40 * 1498905 * 2
def baseEnd_1498905 : Nat := 769658720427563260994167

theorem tailTrace_1498905 : CollatzResearch.WordTrace tailWord_1498905 prefixEnd_1498905 769658720427563260994167 := by
  unfold tailWord_1498905
  simp only [CollatzResearch.WordTrace]
  refine ⟨54669556634730652438498169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36446371089820434958998779 54669556634730652438498169)
  ·
    refine ⟨41002167476047989328873627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54669556634730652438498169 41002167476047989328873627)
    ·
      refine ⟨61503251214071983993310441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41002167476047989328873627 61503251214071983993310441)
      ·
        refine ⟨46127438410553987994982831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61503251214071983993310441 46127438410553987994982831)
        ·
          refine ⟨69191157615830981992474247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46127438410553987994982831 69191157615830981992474247)
          ·
            refine ⟨103786736423746472988711371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69191157615830981992474247 103786736423746472988711371)
            ·
              refine ⟨155680104635619709483067057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103786736423746472988711371 155680104635619709483067057)
              ·
                refine ⟨116760078476714782112300293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155680104635619709483067057 116760078476714782112300293)
                ·
                  refine ⟨21892514714384021646056305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116760078476714782112300293 21892514714384021646056305)
                  ·
                    refine ⟨16419386035788016234542229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21892514714384021646056305 16419386035788016234542229)
                    ·
                      refine ⟨769658720427563260994167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16419386035788016234542229 769658720427563260994167)
                      ·
                        rfl

theorem cell23_1498905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_1498905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498905 prefixEnd_1498905 := by exact prefixLift 1498905
  have htrace : WordTrace (prefixWord ++ tailWord_1498905) baseStart_1498905 baseEnd_1498905 := by
    simpa [prefixWord, tailWord_1498905, baseEnd_1498905] using wordTrace_append hprefix tailTrace_1498905
  have hstable : (prefixWord ++ tailWord_1498905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498905).length < 2 ^ (prefixWord ++ tailWord_1498905).sum := by decide
  have hdescent : baseEnd_1498905 < baseStart_1498905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498913 : List Nat := [1, 2, 3, 2, 1, 3, 1, 5, 1, 2, 2]
def baseStart_1498913 : Nat := 118140960795 + 1498913 * 2 ^ 59
def prefixEnd_1498913 : Nat := 4983230072969 + 3 ^ 40 * 1498913 * 2
def baseEnd_1498913 : Nat := 769662828272799229694131

theorem tailTrace_1498913 : CollatzResearch.WordTrace tailWord_1498913 prefixEnd_1498913 769662828272799229694131 := by
  unfold tailWord_1498913
  simp only [CollatzResearch.WordTrace]
  refine ⟨54669848418701669804789393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36446565612467779869859595 54669848418701669804789393)
  ·
    refine ⟨41002386314026252353592045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54669848418701669804789393 41002386314026252353592045)
    ·
      refine ⟨15375894867759844632597017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41002386314026252353592045 15375894867759844632597017)
      ·
        refine ⟨11531921150819883474447763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15375894867759844632597017 11531921150819883474447763)
        ·
          refine ⟨17297881726229825211671645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11531921150819883474447763 17297881726229825211671645)
          ·
            refine ⟨6486705647336184454376867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17297881726229825211671645 6486705647336184454376867)
            ·
              refine ⟨9730058471004276681565301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6486705647336184454376867 9730058471004276681565301)
              ·
                refine ⟨912192981656650938896747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9730058471004276681565301 912192981656650938896747)
                ·
                  refine ⟨1368289472484976408345121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 912192981656650938896747 1368289472484976408345121)
                  ·
                    refine ⟨1026217104363732306258841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1368289472484976408345121 1026217104363732306258841)
                    ·
                      refine ⟨769662828272799229694131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1026217104363732306258841 769662828272799229694131)
                      ·
                        rfl

theorem cell23_1498913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_1498913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498913 prefixEnd_1498913 := by exact prefixLift 1498913
  have htrace : WordTrace (prefixWord ++ tailWord_1498913) baseStart_1498913 baseEnd_1498913 := by
    simpa [prefixWord, tailWord_1498913, baseEnd_1498913] using wordTrace_append hprefix tailTrace_1498913
  have hstable : (prefixWord ++ tailWord_1498913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498913).length < 2 ^ (prefixWord ++ tailWord_1498913).sum := by decide
  have hdescent : baseEnd_1498913 < baseStart_1498913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498916 : List Nat := [2, 3, 1, 3, 2, 2, 1, 3, 1, 2, 3]
def baseStart_1498916 : Nat := 118140960795 + 1498916 * 2 ^ 59
def prefixEnd_1498916 : Nat := 4983230072969 + 3 ^ 40 * 1498916 * 2
def baseEnd_1498916 : Nat := 769664368714762717956617

theorem tailTrace_1498916 : CollatzResearch.WordTrace tailWord_1498916 prefixEnd_1498916 769664368714762717956617 := by
  unfold tailWord_1498916
  simp only [CollatzResearch.WordTrace]
  refine ⟨27334978918845400658574301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36446638558460534211432401 27334978918845400658574301)
  ·
    refine ⟨10250617094567025246965363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27334978918845400658574301 10250617094567025246965363)
    ·
      refine ⟨15375925641850537870448045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10250617094567025246965363 15375925641850537870448045)
      ·
        refine ⟨5765972115693951701418017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15375925641850537870448045 5765972115693951701418017)
        ·
          refine ⟨4324479086770463776063513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5765972115693951701418017 4324479086770463776063513)
          ·
            refine ⟨3243359315077847832047635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4324479086770463776063513 3243359315077847832047635)
            ·
              refine ⟨4865038972616771748071453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3243359315077847832047635 4865038972616771748071453)
              ·
                refine ⟨1824389614731289405526795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4865038972616771748071453 1824389614731289405526795)
                ·
                  refine ⟨2736584422096934108290193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1824389614731289405526795 2736584422096934108290193)
                  ·
                    refine ⟨2052438316572700581217645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2736584422096934108290193 2052438316572700581217645)
                    ·
                      refine ⟨769664368714762717956617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2052438316572700581217645 769664368714762717956617)
                      ·
                        rfl

theorem cell23_1498916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_1498916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498916 prefixEnd_1498916 := by exact prefixLift 1498916
  have htrace : WordTrace (prefixWord ++ tailWord_1498916) baseStart_1498916 baseEnd_1498916 := by
    simpa [prefixWord, tailWord_1498916, baseEnd_1498916] using wordTrace_append hprefix tailTrace_1498916
  have hstable : (prefixWord ++ tailWord_1498916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498916).length < 2 ^ (prefixWord ++ tailWord_1498916).sum := by decide
  have hdescent : baseEnd_1498916 < baseStart_1498916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498950 : List Nat := [6, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1498950 : Nat := 118140960795 + 1498950 * 2 ^ 59
def prefixEnd_1498950 : Nat := 4983230072969 + 3 ^ 40 * 1498950 * 2
def baseEnd_1498950 : Nat := 769681827057015584931461

theorem tailTrace_1498950 : CollatzResearch.WordTrace tailWord_1498950 prefixEnd_1498950 769681827057015584931461 := by
  unfold tailWord_1498950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1708474934986488285121447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36447465279711750082590869 1708474934986488285121447)
  ·
    refine ⟨2562712402479732427682171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1708474934986488285121447 2562712402479732427682171)
    ·
      refine ⟨3844068603719598641523257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2562712402479732427682171 3844068603719598641523257)
      ·
        refine ⟨2883051452789698981142443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3844068603719598641523257 2883051452789698981142443)
        ·
          refine ⟨4324577179184548471713665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2883051452789698981142443 4324577179184548471713665)
          ·
            refine ⟨3243432884388411353785249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4324577179184548471713665 3243432884388411353785249)
            ·
              refine ⟨2432574663291308515338937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3243432884388411353785249 2432574663291308515338937)
              ·
                refine ⟨1824430997468481386504203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2432574663291308515338937 1824430997468481386504203)
                ·
                  refine ⟨2736646496202722079756305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1824430997468481386504203 2736646496202722079756305)
                  ·
                    refine ⟨2052484872152041559817229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2736646496202722079756305 2052484872152041559817229)
                    ·
                      refine ⟨769681827057015584931461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2052484872152041559817229 769681827057015584931461)
                      ·
                        rfl

theorem cell23_1498950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1498950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498950 prefixEnd_1498950 := by exact prefixLift 1498950
  have htrace : WordTrace (prefixWord ++ tailWord_1498950) baseStart_1498950 baseEnd_1498950 := by
    simpa [prefixWord, tailWord_1498950, baseEnd_1498950] using wordTrace_append hprefix tailTrace_1498950
  have hstable : (prefixWord ++ tailWord_1498950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498950).length < 2 ^ (prefixWord ++ tailWord_1498950).sum := by decide
  have hdescent : baseEnd_1498950 < baseStart_1498950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1498969 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 3, 4, 2]
def baseStart_1498969 : Nat := 118140960795 + 1498969 * 2 ^ 59
def prefixEnd_1498969 : Nat := 4983230072969 + 3 ^ 40 * 1498969 * 2
def baseEnd_1498969 : Nat := 769691583189451010593873

theorem tailTrace_1498969 : CollatzResearch.WordTrace tailWord_1498969 prefixEnd_1498969 769691583189451010593873 := by
  unfold tailWord_1498969
  simp only [CollatzResearch.WordTrace]
  refine ⟨54671890906498791368827961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36447927270999194245885307 54671890906498791368827961)
  ·
    refine ⟨41003918179874093526620971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54671890906498791368827961 41003918179874093526620971)
    ·
      refine ⟨61505877269811140289931457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41003918179874093526620971 61505877269811140289931457)
      ·
        refine ⟨46129407952358355217448593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61505877269811140289931457 46129407952358355217448593)
        ·
          refine ⟨34597055964268766413086445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46129407952358355217448593 34597055964268766413086445)
          ·
            refine ⟨12973895986600787404907417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34597055964268766413086445 12973895986600787404907417)
            ·
              refine ⟨9730421989950590553680563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12973895986600787404907417 9730421989950590553680563)
              ·
                refine ⟨14595632984925885830520845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9730421989950590553680563 14595632984925885830520845)
                ·
                  refine ⟨5473362369347207186445317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14595632984925885830520845 5473362369347207186445317)
                  ·
                    refine ⟨1026255444252601347458497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5473362369347207186445317 1026255444252601347458497)
                    ·
                      refine ⟨769691583189451010593873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1026255444252601347458497 769691583189451010593873)
                      ·
                        rfl

theorem cell23_1498969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 4, 2].length) (baseStart_1498969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1498969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1498969 prefixEnd_1498969 := by exact prefixLift 1498969
  have htrace : WordTrace (prefixWord ++ tailWord_1498969) baseStart_1498969 baseEnd_1498969 := by
    simpa [prefixWord, tailWord_1498969, baseEnd_1498969] using wordTrace_append hprefix tailTrace_1498969
  have hstable : (prefixWord ++ tailWord_1498969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498969).length < 2 ^ (prefixWord ++ tailWord_1498969).sum := by decide
  have hdescent : baseEnd_1498969 < baseStart_1498969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499006 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1499006 : Nat := 118140960795 + 1499006 * 2 ^ 59
def prefixEnd_1499006 : Nat := 4983230072969 + 3 ^ 40 * 1499006 * 2
def baseEnd_1499006 : Nat := 769710581973667365831203

theorem tailTrace_1499006 : CollatzResearch.WordTrace tailWord_1499006 prefixEnd_1499006 769710581973667365831203 := by
  unfold tailWord_1499006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6834155050920593335990609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36448826938243164458616581 6834155050920593335990609)
  ·
    refine ⟨5125616288190445001992957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6834155050920593335990609 5125616288190445001992957)
    ·
      refine ⟨1922106108071416875747359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5125616288190445001992957 1922106108071416875747359)
      ·
        refine ⟨2883159162107125313621039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1922106108071416875747359 2883159162107125313621039)
        ·
          refine ⟨4324738743160687970431559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2883159162107125313621039 4324738743160687970431559)
          ·
            refine ⟨6487108114741031955647339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4324738743160687970431559 6487108114741031955647339)
            ·
              refine ⟨9730662172111547933471009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6487108114741031955647339 9730662172111547933471009)
              ·
                refine ⟨7297996629083660950103257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9730662172111547933471009 7297996629083660950103257)
                ·
                  refine ⟨5473497471812745712577443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7297996629083660950103257 5473497471812745712577443)
                  ·
                    refine ⟨8210246207719118568866165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5473497471812745712577443 8210246207719118568866165)
                    ·
                      refine ⟨769710581973667365831203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8210246207719118568866165 769710581973667365831203)
                      ·
                        rfl

theorem cell23_1499006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1499006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499006 prefixEnd_1499006 := by exact prefixLift 1499006
  have htrace : WordTrace (prefixWord ++ tailWord_1499006) baseStart_1499006 baseEnd_1499006 := by
    simpa [prefixWord, tailWord_1499006, baseEnd_1499006] using wordTrace_append hprefix tailTrace_1499006
  have hstable : (prefixWord ++ tailWord_1499006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499006).length < 2 ^ (prefixWord ++ tailWord_1499006).sum := by decide
  have hdescent : baseEnd_1499006 < baseStart_1499006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499103 : List Nat := [1, 1, 2, 3, 4, 1, 2, 4, 1, 4]
def baseStart_1499103 : Nat := 118140960795 + 1499103 * 2 ^ 59
def prefixEnd_1499103 : Nat := 4983230072969 + 3 ^ 40 * 1499103 * 2
def baseEnd_1499103 : Nat := 256586796532384495439419

theorem tailTrace_1499103 : CollatzResearch.WordTrace tailWord_1499103 prefixEnd_1499103 256586796532384495439419 := by
  unfold tailWord_1499103
  simp only [CollatzResearch.WordTrace]
  refine ⟨54676778288013332254205963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36451185525342221502803975 54676778288013332254205963)
  ·
    refine ⟨82015167432019998381308945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54676778288013332254205963 82015167432019998381308945)
    ·
      refine ⟨61511375574014998785981709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82015167432019998381308945 61511375574014998785981709)
      ·
        refine ⟨23066765840255624544743141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61511375574014998785981709 23066765840255624544743141)
        ·
          refine ⟨4325018595047929602139339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23066765840255624544743141 4325018595047929602139339)
          ·
            refine ⟨6487527892571894403209009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4325018595047929602139339 6487527892571894403209009)
            ·
              refine ⟨4865645919428920802406757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6487527892571894403209009 4865645919428920802406757)
              ·
                refine ⟨912308609892922650451267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4865645919428920802406757 912308609892922650451267)
                ·
                  refine ⟨1368462914839383975676901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 912308609892922650451267 1368462914839383975676901)
                  ·
                    refine ⟨256586796532384495439419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1368462914839383975676901 256586796532384495439419)
                    ·
                      rfl

theorem cell23_1499103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 1, 4].length) (baseStart_1499103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499103 prefixEnd_1499103 := by exact prefixLift 1499103
  have htrace : WordTrace (prefixWord ++ tailWord_1499103) baseStart_1499103 baseEnd_1499103 := by
    simpa [prefixWord, tailWord_1499103, baseEnd_1499103] using wordTrace_append hprefix tailTrace_1499103
  have hstable : (prefixWord ++ tailWord_1499103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499103).length < 2 ^ (prefixWord ++ tailWord_1499103).sum := by decide
  have hdescent : baseEnd_1499103 < baseStart_1499103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499189 : List Nat := [1, 3, 3, 1, 1, 1, 4, 9]
def baseStart_1499189 : Nat := 118140960795 + 1499189 * 2 ^ 59
def prefixEnd_1499189 : Nat := 4983230072969 + 3 ^ 40 * 1499189 * 2
def baseEnd_1499189 : Nat := 28511279590127412957143

theorem tailTrace_1499189 : CollatzResearch.WordTrace tailWord_1499189 prefixEnd_1499189 28511279590127412957143 := by
  unfold tailWord_1499189
  simp only [CollatzResearch.WordTrace]
  refine ⟨54679914965701768941836621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36453276643801179294557747 54679914965701768941836621)
  ·
    refine ⟨20504968112138163353188733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54679914965701768941836621 20504968112138163353188733)
    ·
      refine ⟨7689363042051811257445775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20504968112138163353188733 7689363042051811257445775)
      ·
        refine ⟨11534044563077716886168663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7689363042051811257445775 11534044563077716886168663)
        ·
          refine ⟨17301066844616575329252995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11534044563077716886168663 17301066844616575329252995)
          ·
            refine ⟨25951600266924862993879493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17301066844616575329252995 25951600266924862993879493)
            ·
              refine ⟨4865925050048411811352405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25951600266924862993879493 4865925050048411811352405)
              ·
                refine ⟨28511279590127412957143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4865925050048411811352405 28511279590127412957143)
                ·
                  rfl

theorem cell23_1499189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 9].length) (baseStart_1499189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499189 prefixEnd_1499189 := by exact prefixLift 1499189
  have htrace : WordTrace (prefixWord ++ tailWord_1499189) baseStart_1499189 baseEnd_1499189 := by
    simpa [prefixWord, tailWord_1499189, baseEnd_1499189] using wordTrace_append hprefix tailTrace_1499189
  have hstable : (prefixWord ++ tailWord_1499189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499189).length < 2 ^ (prefixWord ++ tailWord_1499189).sum := by decide
  have hdescent : baseEnd_1499189 < baseStart_1499189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499196 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_1499196 : Nat := 118140960795 + 1499196 * 2 ^ 59
def prefixEnd_1499196 : Nat := 4983230072969 + 3 ^ 40 * 1499196 * 2
def baseEnd_1499196 : Nat := 769808143298021622455329

theorem tailTrace_1499196 : CollatzResearch.WordTrace tailWord_1499196 prefixEnd_1499196 769808143298021622455329 := by
  unfold tailWord_1499196
  simp only [CollatzResearch.WordTrace]
  refine ⟨27340085138338204568670721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36453446851117606091560961 27340085138338204568670721)
  ·
    refine ⟨20505063853753653426503041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27340085138338204568670721 20505063853753653426503041)
    ·
      refine ⟨15378797890315240069877281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20505063853753653426503041 15378797890315240069877281)
      ·
        refine ⟨11534098417736430052407961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15378797890315240069877281 11534098417736430052407961)
        ·
          refine ⟨8650573813302322539305971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11534098417736430052407961 8650573813302322539305971)
          ·
            refine ⟨12975860719953483808958957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8650573813302322539305971 12975860719953483808958957)
            ·
              refine ⟨4865947769982556428359609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12975860719953483808958957 4865947769982556428359609)
              ·
                refine ⟨3649460827486917321269707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4865947769982556428359609 3649460827486917321269707)
                ·
                  refine ⟨5474191241230375981904561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3649460827486917321269707 5474191241230375981904561)
                  ·
                    refine ⟨4105643430922781986428421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5474191241230375981904561 4105643430922781986428421)
                    ·
                      refine ⟨769808143298021622455329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4105643430922781986428421 769808143298021622455329)
                      ·
                        rfl

theorem cell23_1499196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_1499196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499196 prefixEnd_1499196 := by exact prefixLift 1499196
  have htrace : WordTrace (prefixWord ++ tailWord_1499196) baseStart_1499196 baseEnd_1499196 := by
    simpa [prefixWord, tailWord_1499196, baseEnd_1499196] using wordTrace_append hprefix tailTrace_1499196
  have hstable : (prefixWord ++ tailWord_1499196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499196).length < 2 ^ (prefixWord ++ tailWord_1499196).sum := by decide
  have hdescent : baseEnd_1499196 < baseStart_1499196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499246 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_1499246 : Nat := 118140960795 + 1499246 * 2 ^ 59
def prefixEnd_1499246 : Nat := 4983230072969 + 3 ^ 40 * 1499246 * 2
def baseEnd_1499246 : Nat := 769833817330746426830099

theorem tailTrace_1499246 : CollatzResearch.WordTrace tailWord_1499246 prefixEnd_1499246 769833817330746426830099 := by
  unfold tailWord_1499246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6835249240811908459582699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36454662617663511784441061 6835249240811908459582699)
  ·
    refine ⟨10252873861217862689374049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6835249240811908459582699 10252873861217862689374049)
    ·
      refine ⟨7689655395913397017030537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10252873861217862689374049 7689655395913397017030537)
      ·
        refine ⟨5767241546935047762772903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7689655395913397017030537 5767241546935047762772903)
        ·
          refine ⟨8650862320402571644159355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5767241546935047762772903 8650862320402571644159355)
          ·
            refine ⟨12976293480603857466239033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8650862320402571644159355 12976293480603857466239033)
            ·
              refine ⟨9732220110452893099679275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12976293480603857466239033 9732220110452893099679275)
              ·
                refine ⟨14598330165679339649518913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9732220110452893099679275 14598330165679339649518913)
                ·
                  refine ⟨10948747624259504737139185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14598330165679339649518913 10948747624259504737139185)
                  ·
                    refine ⟨8211560718194628552854389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10948747624259504737139185 8211560718194628552854389)
                    ·
                      refine ⟨769833817330746426830099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8211560718194628552854389 769833817330746426830099)
                      ·
                        rfl

theorem cell23_1499246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_1499246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499246 prefixEnd_1499246 := by exact prefixLift 1499246
  have htrace : WordTrace (prefixWord ++ tailWord_1499246) baseStart_1499246 baseEnd_1499246 := by
    simpa [prefixWord, tailWord_1499246, baseEnd_1499246] using wordTrace_append hprefix tailTrace_1499246
  have hstable : (prefixWord ++ tailWord_1499246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499246).length < 2 ^ (prefixWord ++ tailWord_1499246).sum := by decide
  have hdescent : baseEnd_1499246 < baseStart_1499246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499249 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 1, 8]
def baseStart_1499249 : Nat := 118140960795 + 1499249 * 2 ^ 59
def prefixEnd_1499249 : Nat := 4983230072969 + 3 ^ 40 * 1499249 * 2
def baseEnd_1499249 : Nat := 256611785924236638364195

theorem tailTrace_1499249 : CollatzResearch.WordTrace tailWord_1499249 prefixEnd_1499249 256611785924236638364195 := by
  unfold tailWord_1499249
  simp only [CollatzResearch.WordTrace]
  refine ⟨54682103345484399189020801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36454735563656266126013867 54682103345484399189020801)
  ·
    refine ⟨41011577509113299391765601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54682103345484399189020801 41011577509113299391765601)
    ·
      refine ⟨30758683131834974543824201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41011577509113299391765601 30758683131834974543824201)
      ·
        refine ⟨23069012348876230907868151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30758683131834974543824201 23069012348876230907868151)
        ·
          refine ⟨34603518523314346361802227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23069012348876230907868151 34603518523314346361802227)
          ·
            refine ⟨51905277784971519542703341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34603518523314346361802227 51905277784971519542703341)
            ·
              refine ⟨19464479169364319828513753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51905277784971519542703341 19464479169364319828513753)
              ·
                refine ⟨14598359377023239871385315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19464479169364319828513753 14598359377023239871385315)
                ·
                  refine ⟨21897539065534859807077973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14598359377023239871385315 21897539065534859807077973)
                  ·
                    refine ⟨256611785924236638364195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21897539065534859807077973 256611785924236638364195)
                    ·
                      rfl

theorem cell23_1499249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_1499249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499249 prefixEnd_1499249 := by exact prefixLift 1499249
  have htrace : WordTrace (prefixWord ++ tailWord_1499249) baseStart_1499249 baseEnd_1499249 := by
    simpa [prefixWord, tailWord_1499249, baseEnd_1499249] using wordTrace_append hprefix tailTrace_1499249
  have hstable : (prefixWord ++ tailWord_1499249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499249).length < 2 ^ (prefixWord ++ tailWord_1499249).sum := by decide
  have hdescent : baseEnd_1499249 < baseStart_1499249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499260 : List Nat := [2, 2, 2, 1, 1, 5, 1, 3, 1, 3, 2]
def baseStart_1499260 : Nat := 118140960795 + 1499260 * 2 ^ 59
def prefixEnd_1499260 : Nat := 4983230072969 + 3 ^ 40 * 1499260 * 2
def baseEnd_1499260 : Nat := 769841006059909372055035

theorem tailTrace_1499260 : CollatzResearch.WordTrace tailWord_1499260 prefixEnd_1499260 769841006059909372055035 := by
  unfold tailWord_1499260
  simp only [CollatzResearch.WordTrace]
  refine ⟨27341252274222274033835617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36455003032296365378447489 27341252274222274033835617)
  ·
    refine ⟨20505939205666705525376713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27341252274222274033835617 20505939205666705525376713)
    ·
      refine ⟨15379454404250029144032535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20505939205666705525376713 15379454404250029144032535)
      ·
        refine ⟨23069181606375043716048803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15379454404250029144032535 23069181606375043716048803)
        ·
          refine ⟨34603772409562565574073205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23069181606375043716048803 34603772409562565574073205)
          ·
            refine ⟨3244103663396490522569363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34603772409562565574073205 3244103663396490522569363)
            ·
              refine ⟨4866155495094735783854045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3244103663396490522569363 4866155495094735783854045)
              ·
                refine ⟨1824808310660525918945267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4866155495094735783854045 1824808310660525918945267)
                ·
                  refine ⟨2737212465990788878417901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1824808310660525918945267 2737212465990788878417901)
                  ·
                    refine ⟨1026454674746545829406713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2737212465990788878417901 1026454674746545829406713)
                    ·
                      refine ⟨769841006059909372055035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1026454674746545829406713 769841006059909372055035)
                      ·
                        rfl

theorem cell23_1499260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_1499260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499260 prefixEnd_1499260 := by exact prefixLift 1499260
  have htrace : WordTrace (prefixWord ++ tailWord_1499260) baseStart_1499260 baseEnd_1499260 := by
    simpa [prefixWord, tailWord_1499260, baseEnd_1499260] using wordTrace_append hprefix tailTrace_1499260
  have hstable : (prefixWord ++ tailWord_1499260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499260).length < 2 ^ (prefixWord ++ tailWord_1499260).sum := by decide
  have hdescent : baseEnd_1499260 < baseStart_1499260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499284 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_1499284 : Nat := 118140960795 + 1499284 * 2 ^ 59
def prefixEnd_1499284 : Nat := 4983230072969 + 3 ^ 40 * 1499284 * 2
def baseEnd_1499284 : Nat := 769853329595617278154925

theorem tailTrace_1499284 : CollatzResearch.WordTrace tailWord_1499284 prefixEnd_1499284 769853329595617278154925 := by
  unfold tailWord_1499284
  simp only [CollatzResearch.WordTrace]
  refine ⟨27341689950178800083272453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36455586600238400111029937 27341689950178800083272453)
  ·
    refine ⟨5126566865658525015613585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27341689950178800083272453 5126566865658525015613585)
    ·
      refine ⟨3844925149243893761710189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5126566865658525015613585 3844925149243893761710189)
      ·
        refine ⟨1441846930966460160641321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3844925149243893761710189 1441846930966460160641321)
        ·
          refine ⟨1081385198224845120480991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1441846930966460160641321 1081385198224845120480991)
          ·
            refine ⟨1622077797337267680721487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081385198224845120480991 1622077797337267680721487)
            ·
              refine ⟨2433116696005901521082231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1622077797337267680721487 2433116696005901521082231)
              ·
                refine ⟨3649675044008852281623347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2433116696005901521082231 3649675044008852281623347)
                ·
                  refine ⟨5474512566013278422435021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3649675044008852281623347 5474512566013278422435021)
                  ·
                    refine ⟨2052942212254979408413133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5474512566013278422435021 2052942212254979408413133)
                    ·
                      refine ⟨769853329595617278154925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2052942212254979408413133 769853329595617278154925)
                      ·
                        rfl

theorem cell23_1499284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_1499284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499284 prefixEnd_1499284 := by exact prefixLift 1499284
  have htrace : WordTrace (prefixWord ++ tailWord_1499284) baseStart_1499284 baseEnd_1499284 := by
    simpa [prefixWord, tailWord_1499284, baseEnd_1499284] using wordTrace_append hprefix tailTrace_1499284
  have hstable : (prefixWord ++ tailWord_1499284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499284).length < 2 ^ (prefixWord ++ tailWord_1499284).sum := by decide
  have hdescent : baseEnd_1499284 < baseStart_1499284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499289 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 9]
def baseStart_1499289 : Nat := 118140960795 + 1499289 * 2 ^ 59
def prefixEnd_1499289 : Nat := 4983230072969 + 3 ^ 40 * 1499289 * 2
def baseEnd_1499289 : Nat := 769855896998889758592401

theorem tailTrace_1499289 : CollatzResearch.WordTrace tailWord_1499289 prefixEnd_1499289 769855896998889758592401 := by
  unfold tailWord_1499289
  simp only [CollatzResearch.WordTrace]
  refine ⟨54683562265339486020476921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36455708176892990680317947 54683562265339486020476921)
  ·
    refine ⟨41012671699004614515357691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54683562265339486020476921 41012671699004614515357691)
    ·
      refine ⟨61519007548506921773036537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41012671699004614515357691 61519007548506921773036537)
      ·
        refine ⟨46139255661380191329777403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61519007548506921773036537 46139255661380191329777403)
        ·
          refine ⟨69208883492070286994666105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46139255661380191329777403 69208883492070286994666105)
          ·
            refine ⟨51906662619052715245999579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69208883492070286994666105 51906662619052715245999579)
            ·
              refine ⟨77859993928579072868999369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51906662619052715245999579 77859993928579072868999369)
              ·
                refine ⟨58394995446434304651749527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77859993928579072868999369 58394995446434304651749527)
                ·
                  refine ⟨87592493169651456977624291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58394995446434304651749527 87592493169651456977624291)
                  ·
                    refine ⟨131388739754477185466436437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87592493169651456977624291 131388739754477185466436437)
                    ·
                      refine ⟨769855896998889758592401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 131388739754477185466436437 769855896998889758592401)
                      ·
                        rfl

theorem cell23_1499289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_1499289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499289 prefixEnd_1499289 := by exact prefixLift 1499289
  have htrace : WordTrace (prefixWord ++ tailWord_1499289) baseStart_1499289 baseEnd_1499289 := by
    simpa [prefixWord, tailWord_1499289, baseEnd_1499289] using wordTrace_append hprefix tailTrace_1499289
  have hstable : (prefixWord ++ tailWord_1499289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499289).length < 2 ^ (prefixWord ++ tailWord_1499289).sum := by decide
  have hdescent : baseEnd_1499289 < baseStart_1499289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499294 : List Nat := [4, 3, 1, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_1499294 : Nat := 118140960795 + 1499294 * 2 ^ 59
def prefixEnd_1499294 : Nat := 4983230072969 + 3 ^ 40 * 1499294 * 2
def baseEnd_1499294 : Nat := 769858464402162239029879

theorem tailTrace_1499294 : CollatzResearch.WordTrace tailWord_1499294 prefixEnd_1499294 769858464402162239029879 := by
  unfold tailWord_1499294
  simp only [CollatzResearch.WordTrace]
  refine ⟨6835468078790171484301117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36455829753547581249605957 6835468078790171484301117)
  ·
    refine ⟨2563300529546314306612919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6835468078790171484301117 2563300529546314306612919)
    ·
      refine ⟨3844950794319471459919379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2563300529546314306612919 3844950794319471459919379)
      ·
        refine ⟨5767426191479207189879069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3844950794319471459919379 5767426191479207189879069)
        ·
          refine ⟨2162784821804702696204651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5767426191479207189879069 2162784821804702696204651)
          ·
            refine ⟨3244177232707054044306977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2162784821804702696204651 3244177232707054044306977)
            ·
              refine ⟨2433132924530290533230233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3244177232707054044306977 2433132924530290533230233)
              ·
                refine ⟨1824849693397717899922675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2433132924530290533230233 1824849693397717899922675)
                ·
                  refine ⟨2737274540096576849884013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1824849693397717899922675 2737274540096576849884013)
                  ·
                    refine ⟨1026477952536216318706505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2737274540096576849884013 1026477952536216318706505)
                    ·
                      refine ⟨769858464402162239029879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1026477952536216318706505 769858464402162239029879)
                      ·
                        rfl

theorem cell23_1499294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_1499294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499294 prefixEnd_1499294 := by exact prefixLift 1499294
  have htrace : WordTrace (prefixWord ++ tailWord_1499294) baseStart_1499294 baseEnd_1499294 := by
    simpa [prefixWord, tailWord_1499294, baseEnd_1499294] using wordTrace_append hprefix tailTrace_1499294
  have hstable : (prefixWord ++ tailWord_1499294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499294).length < 2 ^ (prefixWord ++ tailWord_1499294).sum := by decide
  have hdescent : baseEnd_1499294 < baseStart_1499294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499296 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 7]
def baseStart_1499296 : Nat := 118140960795 + 1499296 * 2 ^ 59
def prefixEnd_1499296 : Nat := 4983230072969 + 3 ^ 40 * 1499296 * 2
def baseEnd_1499296 : Nat := 85539943484830136800541

theorem tailTrace_1499296 : CollatzResearch.WordTrace tailWord_1499296 prefixEnd_1499296 85539943484830136800541 := by
  unfold tailWord_1499296
  simp only [CollatzResearch.WordTrace]
  refine ⟨27341908788157063107990871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36455878384209417477321161 27341908788157063107990871)
  ·
    refine ⟨41012863182235594661986307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27341908788157063107990871 41012863182235594661986307)
    ·
      refine ⟨61519294773353391992979461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41012863182235594661986307 61519294773353391992979461)
      ·
        refine ⟨11534867770003760998683649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61519294773353391992979461 11534867770003760998683649)
        ·
          refine ⟨8651150827502820749012737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11534867770003760998683649 8651150827502820749012737)
          ·
            refine ⟨6488363120627115561759553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8651150827502820749012737 6488363120627115561759553)
            ·
              refine ⟨4866272340470336671319665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6488363120627115561759553 4866272340470336671319665)
              ·
                refine ⟨3649704255352752503489749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4866272340470336671319665 3649704255352752503489749)
                ·
                  refine ⟨85539943484830136800541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3649704255352752503489749 85539943484830136800541)
                  ·
                    rfl

theorem cell23_1499296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 7].length) (baseStart_1499296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499296 prefixEnd_1499296 := by exact prefixLift 1499296
  have htrace : WordTrace (prefixWord ++ tailWord_1499296) baseStart_1499296 baseEnd_1499296 := by
    simpa [prefixWord, tailWord_1499296, baseEnd_1499296] using wordTrace_append hprefix tailTrace_1499296
  have hstable : (prefixWord ++ tailWord_1499296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499296).length < 2 ^ (prefixWord ++ tailWord_1499296).sum := by decide
  have hdescent : baseEnd_1499296 < baseStart_1499296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499390 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_1499390 : Nat := 118140960795 + 1499390 * 2 ^ 59
def prefixEnd_1499390 : Nat := 4983230072969 + 3 ^ 40 * 1499390 * 2
def baseEnd_1499390 : Nat := 256635919514997954476479

theorem tailTrace_1499390 : CollatzResearch.WordTrace tailWord_1499390 prefixEnd_1499390 256635919514997954476479 := by
  unfold tailWord_1499390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6835905754746697533737953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36458164025315720179935749 6835905754746697533737953)
  ·
    refine ⟨5126929316060023150303465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6835905754746697533737953 5126929316060023150303465)
    ·
      refine ⟨3845196987045017362727599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5126929316060023150303465 3845196987045017362727599)
      ·
        refine ⟨5767795480567526044091399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3845196987045017362727599 5767795480567526044091399)
        ·
          refine ⟨8651693220851289066137099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5767795480567526044091399 8651693220851289066137099)
          ·
            refine ⟨12977539831276933599205649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8651693220851289066137099 12977539831276933599205649)
            ·
              refine ⟨9733154873457700199404237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12977539831276933599205649 9733154873457700199404237)
              ·
                refine ⟨3649933077546637574776589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9733154873457700199404237 3649933077546637574776589)
                ·
                  refine ⟨1368724904079989090541221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3649933077546637574776589 1368724904079989090541221)
                  ·
                    refine ⟨256635919514997954476479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1368724904079989090541221 256635919514997954476479)
                    ·
                      rfl

theorem cell23_1499390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_1499390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499390 prefixEnd_1499390 := by exact prefixLift 1499390
  have htrace : WordTrace (prefixWord ++ tailWord_1499390) baseStart_1499390 baseEnd_1499390 := by
    simpa [prefixWord, tailWord_1499390, baseEnd_1499390] using wordTrace_append hprefix tailTrace_1499390
  have hstable : (prefixWord ++ tailWord_1499390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499390).length < 2 ^ (prefixWord ++ tailWord_1499390).sum := by decide
  have hdescent : baseEnd_1499390 < baseStart_1499390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499490 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1499490 : Nat := 118140960795 + 1499490 * 2 ^ 59
def prefixEnd_1499490 : Nat := 4983230072969 + 3 ^ 40 * 1499490 * 2
def baseEnd_1499490 : Nat := 769959106610443472178977

theorem tailTrace_1499490 : CollatzResearch.WordTrace tailWord_1499490 prefixEnd_1499490 769959106610443472178977 := by
  unfold tailWord_1499490
  simp only [CollatzResearch.WordTrace]
  refine ⟨13672723334402824337135981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36460595558407531565695949 13672723334402824337135981)
  ·
    refine ⟨5127271250401059126425993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13672723334402824337135981 5127271250401059126425993)
    ·
      refine ⟨3845453437800794344819495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5127271250401059126425993 3845453437800794344819495)
      ·
        refine ⟨5768180156701191517229243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3845453437800794344819495 5768180156701191517229243)
        ·
          refine ⟨8652270235051787275843865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5768180156701191517229243 8652270235051787275843865)
          ·
            refine ⟨6489202676288840456882899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8652270235051787275843865 6489202676288840456882899)
            ·
              refine ⟨9733804014433260685324349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6489202676288840456882899 9733804014433260685324349)
              ·
                refine ⟨3650176505412472756996631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9733804014433260685324349 3650176505412472756996631)
                ·
                  refine ⟨5475264758118709135494947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3650176505412472756996631 5475264758118709135494947)
                  ·
                    refine ⟨8212897137178063703242421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5475264758118709135494947 8212897137178063703242421)
                    ·
                      refine ⟨769959106610443472178977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8212897137178063703242421 769959106610443472178977)
                      ·
                        rfl

theorem cell23_1499490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1499490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499490 prefixEnd_1499490 := by exact prefixLift 1499490
  have htrace : WordTrace (prefixWord ++ tailWord_1499490) baseStart_1499490 baseEnd_1499490 := by
    simpa [prefixWord, tailWord_1499490, baseEnd_1499490] using wordTrace_append hprefix tailTrace_1499490
  have hstable : (prefixWord ++ tailWord_1499490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499490).length < 2 ^ (prefixWord ++ tailWord_1499490).sum := by decide
  have hdescent : baseEnd_1499490 < baseStart_1499490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499493 : List Nat := [1, 3, 1, 3, 1, 5, 9]
def baseStart_1499493 : Nat := 118140960795 + 1499493 * 2 ^ 59
def prefixEnd_1499493 : Nat := 4983230072969 + 3 ^ 40 * 1499493 * 2
def baseEnd_1499493 : Nat := 9505687000646999511623

theorem tailTrace_1499493 : CollatzResearch.WordTrace tailWord_1499493 prefixEnd_1499493 9505687000646999511623 := by
  unfold tailWord_1499493
  simp only [CollatzResearch.WordTrace]
  refine ⟨54691002756600428860903133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36460668504400285907268755 54691002756600428860903133)
  ·
    refine ⟨20509126033725160822838675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54691002756600428860903133 20509126033725160822838675)
    ·
      refine ⟨30763689050587741234258013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20509126033725160822838675 30763689050587741234258013)
      ·
        refine ⟨11536383393970402962846755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30763689050587741234258013 11536383393970402962846755)
        ·
          refine ⟨17304575090955604444270133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11536383393970402962846755 17304575090955604444270133)
          ·
            refine ⟨1622303914777087916650325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17304575090955604444270133 1622303914777087916650325)
            ·
              refine ⟨9505687000646999511623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1622303914777087916650325 9505687000646999511623)
              ·
                rfl

theorem cell23_1499493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 9].length) (baseStart_1499493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499493 prefixEnd_1499493 := by exact prefixLift 1499493
  have htrace : WordTrace (prefixWord ++ tailWord_1499493) baseStart_1499493 baseEnd_1499493 := by
    simpa [prefixWord, tailWord_1499493, baseEnd_1499493] using wordTrace_append hprefix tailTrace_1499493
  have hstable : (prefixWord ++ tailWord_1499493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499493).length < 2 ^ (prefixWord ++ tailWord_1499493).sum := by decide
  have hdescent : baseEnd_1499493 < baseStart_1499493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499503 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 3]
def baseStart_1499503 : Nat := 118140960795 + 1499503 * 2 ^ 59
def prefixEnd_1499503 : Nat := 4983230072969 + 3 ^ 40 * 1499503 * 2
def baseEnd_1499503 : Nat := 769965781858951921316417

theorem tailTrace_1499503 : CollatzResearch.WordTrace tailWord_1499503 prefixEnd_1499503 769965781858951921316417 := by
  unfold tailWord_1499503
  simp only [CollatzResearch.WordTrace]
  refine ⟨54691367486564200568767163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36460911657709467045844775 54691367486564200568767163)
  ·
    refine ⟨82037051229846300853150745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54691367486564200568767163 82037051229846300853150745)
    ·
      refine ⟨61527788422384725639863059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82037051229846300853150745 61527788422384725639863059)
      ·
        refine ⟨92291682633577088459794589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61527788422384725639863059 92291682633577088459794589)
        ·
          refine ⟨34609380987591408172422971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92291682633577088459794589 34609380987591408172422971)
          ·
            refine ⟨51914071481387112258634457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34609380987591408172422971 51914071481387112258634457)
            ·
              refine ⟨38935553611040334193975843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51914071481387112258634457 38935553611040334193975843)
              ·
                refine ⟨58403330416560501290963765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38935553611040334193975843 58403330416560501290963765)
                ·
                  refine ⟨5475312226552546996027853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58403330416560501290963765 5475312226552546996027853)
                  ·
                    refine ⟨2053242084957205123510445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5475312226552546996027853 2053242084957205123510445)
                    ·
                      refine ⟨769965781858951921316417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2053242084957205123510445 769965781858951921316417)
                      ·
                        rfl

theorem cell23_1499503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 3].length) (baseStart_1499503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499503 prefixEnd_1499503 := by exact prefixLift 1499503
  have htrace : WordTrace (prefixWord ++ tailWord_1499503) baseStart_1499503 baseEnd_1499503 := by
    simpa [prefixWord, tailWord_1499503, baseEnd_1499503] using wordTrace_append hprefix tailTrace_1499503
  have hstable : (prefixWord ++ tailWord_1499503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499503).length < 2 ^ (prefixWord ++ tailWord_1499503).sum := by decide
  have hdescent : baseEnd_1499503 < baseStart_1499503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499504 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 3, 2, 2]
def baseStart_1499504 : Nat := 118140960795 + 1499504 * 2 ^ 59
def prefixEnd_1499504 : Nat := 4983230072969 + 3 ^ 40 * 1499504 * 2
def baseEnd_1499504 : Nat := 769966295339606417403913

theorem tailTrace_1499504 : CollatzResearch.WordTrace tailWord_1499504 prefixEnd_1499504 769966295339606417403913 := by
  unfold tailWord_1499504
  simp only [CollatzResearch.WordTrace]
  refine ⟨27345701979780288869776783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36460935973040385159702377 27345701979780288869776783)
  ·
    refine ⟨41018552969670433304665175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27345701979780288869776783 41018552969670433304665175)
    ·
      refine ⟨61527829454505649956997763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41018552969670433304665175 61527829454505649956997763)
      ·
        refine ⟨92291744181758474935496645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61527829454505649956997763 92291744181758474935496645)
        ·
          refine ⟨17304702034079714050405621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92291744181758474935496645 17304702034079714050405621)
          ·
            refine ⟨1622315815694973192225527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17304702034079714050405621 1622315815694973192225527)
            ·
              refine ⟨2433473723542459788338291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1622315815694973192225527 2433473723542459788338291)
              ·
                refine ⟨3650210585313689682507437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2433473723542459788338291 3650210585313689682507437)
                ·
                  refine ⟨1368828969492633630940289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3650210585313689682507437 1368828969492633630940289)
                  ·
                    refine ⟨1026621727119475223205217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1368828969492633630940289 1026621727119475223205217)
                    ·
                      refine ⟨769966295339606417403913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1026621727119475223205217 769966295339606417403913)
                      ·
                        rfl

theorem cell23_1499504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 3, 2, 2].length) (baseStart_1499504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499504 prefixEnd_1499504 := by exact prefixLift 1499504
  have htrace : WordTrace (prefixWord ++ tailWord_1499504) baseStart_1499504 baseEnd_1499504 := by
    simpa [prefixWord, tailWord_1499504, baseEnd_1499504] using wordTrace_append hprefix tailTrace_1499504
  have hstable : (prefixWord ++ tailWord_1499504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499504).length < 2 ^ (prefixWord ++ tailWord_1499504).sum := by decide
  have hdescent : baseEnd_1499504 < baseStart_1499504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499554 : List Nat := [3, 3, 1, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_1499554 : Nat := 118140960795 + 1499554 * 2 ^ 59
def prefixEnd_1499554 : Nat := 4983230072969 + 3 ^ 40 * 1499554 * 2
def baseEnd_1499554 : Nat := 769991969372331221778683

theorem tailTrace_1499554 : CollatzResearch.WordTrace tailWord_1499554 prefixEnd_1499554 769991969372331221778683 := by
  unfold tailWord_1499554
  simp only [CollatzResearch.WordTrace]
  refine ⟨13673306902344859069718429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36462151739586290852582477 13673306902344859069718429)
  ·
    refine ⟨5127490088379322151144411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13673306902344859069718429 5127490088379322151144411)
    ·
      refine ⟨7691235132568983226716617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5127490088379322151144411 7691235132568983226716617)
      ·
        refine ⟨5768426349426737420037463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7691235132568983226716617 5768426349426737420037463)
        ·
          refine ⟨8652639524140106130056195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5768426349426737420037463 8652639524140106130056195)
          ·
            refine ⟨12978959286210159195084293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8652639524140106130056195 12978959286210159195084293)
            ·
              refine ⟨2433554866164404849078305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12978959286210159195084293 2433554866164404849078305)
              ·
                refine ⟨1825166149623303636808729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2433554866164404849078305 1825166149623303636808729)
                ·
                  refine ⟨1368874612217477727606547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1825166149623303636808729 1368874612217477727606547)
                  ·
                    refine ⟨2053311918326216591409821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1368874612217477727606547 2053311918326216591409821)
                    ·
                      refine ⟨769991969372331221778683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2053311918326216591409821 769991969372331221778683)
                      ·
                        rfl

theorem cell23_1499554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_1499554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499554 prefixEnd_1499554 := by exact prefixLift 1499554
  have htrace : WordTrace (prefixWord ++ tailWord_1499554) baseStart_1499554 baseEnd_1499554 := by
    simpa [prefixWord, tailWord_1499554, baseEnd_1499554] using wordTrace_append hprefix tailTrace_1499554
  have hstable : (prefixWord ++ tailWord_1499554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499554).length < 2 ^ (prefixWord ++ tailWord_1499554).sum := by decide
  have hdescent : baseEnd_1499554 < baseStart_1499554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499577 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 1, 4, 2]
def baseStart_1499577 : Nat := 118140960795 + 1499577 * 2 ^ 59
def prefixEnd_1499577 : Nat := 4983230072969 + 3 ^ 40 * 1499577 * 2
def baseEnd_1499577 : Nat := 770003779427384631791077

theorem tailTrace_1499577 : CollatzResearch.WordTrace tailWord_1499577 prefixEnd_1499577 770003779427384631791077 := by
  unfold tailWord_1499577
  simp only [CollatzResearch.WordTrace]
  refine ⟨54694066488296111206960985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36462710992197407471307323 54694066488296111206960985)
  ·
    refine ⟨41020549866222083405220739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54694066488296111206960985 41020549866222083405220739)
    ·
      refine ⟨61530824799333125107831109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41020549866222083405220739 61530824799333125107831109)
      ·
        refine ⟨11537029649874960957718333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61530824799333125107831109 11537029649874960957718333)
        ·
          refine ⟨4326386118703110359144375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11537029649874960957718333 4326386118703110359144375)
          ·
            refine ⟨6489579178054665538716563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4326386118703110359144375 6489579178054665538716563)
            ·
              refine ⟨9734368767081998308074845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6489579178054665538716563 9734368767081998308074845)
              ·
                refine ⟨3650388287655749365528067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9734368767081998308074845 3650388287655749365528067)
                ·
                  refine ⟨5475582431483624048292101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3650388287655749365528067 5475582431483624048292101)
                  ·
                    refine ⟨1026671705903179509054769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5475582431483624048292101 1026671705903179509054769)
                    ·
                      refine ⟨770003779427384631791077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1026671705903179509054769 770003779427384631791077)
                      ·
                        rfl

theorem cell23_1499577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_1499577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499577 prefixEnd_1499577 := by exact prefixLift 1499577
  have htrace : WordTrace (prefixWord ++ tailWord_1499577) baseStart_1499577 baseEnd_1499577 := by
    simpa [prefixWord, tailWord_1499577, baseEnd_1499577] using wordTrace_append hprefix tailTrace_1499577
  have hstable : (prefixWord ++ tailWord_1499577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499577).length < 2 ^ (prefixWord ++ tailWord_1499577).sum := by decide
  have hdescent : baseEnd_1499577 < baseStart_1499577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499610 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3]
def baseStart_1499610 : Nat := 118140960795 + 1499610 * 2 ^ 59
def prefixEnd_1499610 : Nat := 4983230072969 + 3 ^ 40 * 1499610 * 2
def baseEnd_1499610 : Nat := 770020724288983002678425

theorem tailTrace_1499610 : CollatzResearch.WordTrace tailWord_1499610 prefixEnd_1499610 770020724288983002678425 := by
  unfold tailWord_1499610
  simp only [CollatzResearch.WordTrace]
  refine ⟨13673817524294139460728071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36463513398117705228608189 13673817524294139460728071)
  ·
    refine ⟨20510726286441209191092107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13673817524294139460728071 20510726286441209191092107)
    ·
      refine ⟨30766089429661813786638161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20510726286441209191092107 30766089429661813786638161)
      ·
        refine ⟨23074567072246360339978621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30766089429661813786638161 23074567072246360339978621)
        ·
          refine ⟨8652962652092385127491983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23074567072246360339978621 8652962652092385127491983)
          ·
            refine ⟨12979443978138577691237975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8652962652092385127491983 12979443978138577691237975)
            ·
              refine ⟨19469165967207866536856963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12979443978138577691237975 19469165967207866536856963)
              ·
                refine ⟨29203748950811799805285445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19469165967207866536856963 29203748950811799805285445)
                ·
                  refine ⟨5475702928277212463491021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29203748950811799805285445 5475702928277212463491021)
                  ·
                    refine ⟨2053388598103954673809133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5475702928277212463491021 2053388598103954673809133)
                    ·
                      refine ⟨770020724288983002678425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2053388598103954673809133 770020724288983002678425)
                      ·
                        rfl

theorem cell23_1499610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_1499610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499610 prefixEnd_1499610 := by exact prefixLift 1499610
  have htrace : WordTrace (prefixWord ++ tailWord_1499610) baseStart_1499610 baseEnd_1499610 := by
    simpa [prefixWord, tailWord_1499610, baseEnd_1499610] using wordTrace_append hprefix tailTrace_1499610
  have hstable : (prefixWord ++ tailWord_1499610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499610).length < 2 ^ (prefixWord ++ tailWord_1499610).sum := by decide
  have hdescent : baseEnd_1499610 < baseStart_1499610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499630 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 1, 7]
def baseStart_1499630 : Nat := 118140960795 + 1499630 * 2 ^ 59
def prefixEnd_1499630 : Nat := 4983230072969 + 3 ^ 40 * 1499630 * 2
def baseEnd_1499630 : Nat := 256676997967357641476111

theorem tailTrace_1499630 : CollatzResearch.WordTrace tailWord_1499630 prefixEnd_1499630 256676997967357641476111 := by
  unfold tailWord_1499630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6836999944638012657330043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36463999704736067505760229 6836999944638012657330043)
  ·
    refine ⟨10255499916957018985995065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6836999944638012657330043 10255499916957018985995065)
    ·
      refine ⟨7691624937717764239496299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10255499916957018985995065 7691624937717764239496299)
      ·
        refine ⟨11537437406576646359244449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7691624937717764239496299 11537437406576646359244449)
        ·
          refine ⟨8653078054932484769433337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11537437406576646359244449 8653078054932484769433337)
          ·
            refine ⟨6489808541199363577075003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8653078054932484769433337 6489808541199363577075003)
            ·
              refine ⟨9734712811799045365612505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6489808541199363577075003 9734712811799045365612505)
              ·
                refine ⟨7301034608849284024209379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9734712811799045365612505 7301034608849284024209379)
                ·
                  refine ⟨10951551913273926036314069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7301034608849284024209379 10951551913273926036314069)
                  ·
                    refine ⟨256676997967357641476111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10951551913273926036314069 256676997967357641476111)
                    ·
                      rfl

theorem cell23_1499630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_1499630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499630 prefixEnd_1499630 := by exact prefixLift 1499630
  have htrace : WordTrace (prefixWord ++ tailWord_1499630) baseStart_1499630 baseEnd_1499630 := by
    simpa [prefixWord, tailWord_1499630, baseEnd_1499630] using wordTrace_append hprefix tailTrace_1499630
  have hstable : (prefixWord ++ tailWord_1499630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499630).length < 2 ^ (prefixWord ++ tailWord_1499630).sum := by decide
  have hdescent : baseEnd_1499630 < baseStart_1499630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499770 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4]
def baseStart_1499770 : Nat := 118140960795 + 1499770 * 2 ^ 59
def prefixEnd_1499770 : Nat := 4983230072969 + 3 ^ 40 * 1499770 * 2
def baseEnd_1499770 : Nat := 770102881193702376677689

theorem tailTrace_1499770 : CollatzResearch.WordTrace tailWord_1499770 prefixEnd_1499770 770102881193702376677689 := by
  unfold tailWord_1499770
  simp only [CollatzResearch.WordTrace]
  refine ⟨13675276444149226292184191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36467403851064603445824509 13675276444149226292184191)
  ·
    refine ⟨20512914666223839438276287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13675276444149226292184191 20512914666223839438276287)
    ·
      refine ⟨30769371999335759157414431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20512914666223839438276287 30769371999335759157414431)
      ·
        refine ⟨46154057999003638736121647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30769371999335759157414431 46154057999003638736121647)
        ·
          refine ⟨69231086998505458104182471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46154057999003638736121647 69231086998505458104182471)
          ·
            refine ⟨103846630497758187156273707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69231086998505458104182471 103846630497758187156273707)
            ·
              refine ⟨155769945746637280734410561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103846630497758187156273707 155769945746637280734410561)
              ·
                refine ⟨116827459309977960550807921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155769945746637280734410561 116827459309977960550807921)
                ·
                  refine ⟨87620594482483470413105941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116827459309977960550807921 87620594482483470413105941)
                  ·
                    refine ⟨4107215366366412675614341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87620594482483470413105941 4107215366366412675614341)
                    ·
                      refine ⟨770102881193702376677689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4107215366366412675614341 770102881193702376677689)
                      ·
                        rfl

theorem cell23_1499770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_1499770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499770 prefixEnd_1499770 := by exact prefixLift 1499770
  have htrace : WordTrace (prefixWord ++ tailWord_1499770) baseStart_1499770 baseEnd_1499770 := by
    simpa [prefixWord, tailWord_1499770, baseEnd_1499770] using wordTrace_append hprefix tailTrace_1499770
  have hstable : (prefixWord ++ tailWord_1499770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499770).length < 2 ^ (prefixWord ++ tailWord_1499770).sum := by decide
  have hdescent : baseEnd_1499770 < baseStart_1499770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499777 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_1499777 : Nat := 118140960795 + 1499777 * 2 ^ 59
def prefixEnd_1499777 : Nat := 4983230072969 + 3 ^ 40 * 1499777 * 2
def baseEnd_1499777 : Nat := 770106475558283849290157

theorem tailTrace_1499777 : CollatzResearch.WordTrace tailWord_1499777 prefixEnd_1499777 770106475558283849290157 := by
  unfold tailWord_1499777
  simp only [CollatzResearch.WordTrace]
  refine ⟨54701361087571545364241585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36467574058381030242827723 54701361087571545364241585)
  ·
    refine ⟨41026020815678659023181189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54701361087571545364241585 41026020815678659023181189)
    ·
      refine ⟨7692378902939748566846473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41026020815678659023181189 7692378902939748566846473)
      ·
        refine ⟨5769284177204811425134855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7692378902939748566846473 5769284177204811425134855)
        ·
          refine ⟨8653926265807217137702283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5769284177204811425134855 8653926265807217137702283)
          ·
            refine ⟨12980889398710825706553425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8653926265807217137702283 12980889398710825706553425)
            ·
              refine ⟨9735667049033119279915069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12980889398710825706553425 9735667049033119279915069)
              ·
                refine ⟨3650875143387419729968151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9735667049033119279915069 3650875143387419729968151)
                ·
                  refine ⟨5476312715081129594952227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3650875143387419729968151 5476312715081129594952227)
                  ·
                    refine ⟨8214469072621694392428341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5476312715081129594952227 8214469072621694392428341)
                    ·
                      refine ⟨770106475558283849290157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8214469072621694392428341 770106475558283849290157)
                      ·
                        rfl

theorem cell23_1499777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_1499777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499777 prefixEnd_1499777 := by exact prefixLift 1499777
  have htrace : WordTrace (prefixWord ++ tailWord_1499777) baseStart_1499777 baseEnd_1499777 := by
    simpa [prefixWord, tailWord_1499777, baseEnd_1499777] using wordTrace_append hprefix tailTrace_1499777
  have hstable : (prefixWord ++ tailWord_1499777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499777).length < 2 ^ (prefixWord ++ tailWord_1499777).sum := by decide
  have hdescent : baseEnd_1499777 < baseStart_1499777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499794 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_1499794 : Nat := 118140960795 + 1499794 * 2 ^ 59
def prefixEnd_1499794 : Nat := 4983230072969 + 3 ^ 40 * 1499794 * 2
def baseEnd_1499794 : Nat := 770115204729410282777579

theorem tailTrace_1499794 : CollatzResearch.WordTrace tailWord_1499794 prefixEnd_1499794 770115204729410282777579 := by
  unfold tailWord_1499794
  simp only [CollatzResearch.WordTrace]
  refine ⟨13675495282127489316902609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36467987419006638178406957 13675495282127489316902609)
  ·
    refine ⟨10256621461595616987676957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13675495282127489316902609 10256621461595616987676957)
    ·
      refine ⟨3846233048098356370378859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10256621461595616987676957 3846233048098356370378859)
      ·
        refine ⟨5769349572147534555568289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3846233048098356370378859 5769349572147534555568289)
        ·
          refine ⟨4327012179110650916676217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5769349572147534555568289 4327012179110650916676217)
          ·
            refine ⟨3245259134332988187507163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4327012179110650916676217 3245259134332988187507163)
            ·
              refine ⟨4867888701499482281260745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3245259134332988187507163 4867888701499482281260745)
              ·
                refine ⟨3650916526124611710945559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4867888701499482281260745 3650916526124611710945559)
                ·
                  refine ⟨5476374789186917566418339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3650916526124611710945559 5476374789186917566418339)
                  ·
                    refine ⟨8214562183780376349627509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5476374789186917566418339 8214562183780376349627509)
                    ·
                      refine ⟨770115204729410282777579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8214562183780376349627509 770115204729410282777579)
                      ·
                        rfl

theorem cell23_1499794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_1499794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499794 prefixEnd_1499794 := by exact prefixLift 1499794
  have htrace : WordTrace (prefixWord ++ tailWord_1499794) baseStart_1499794 baseEnd_1499794 := by
    simpa [prefixWord, tailWord_1499794, baseEnd_1499794] using wordTrace_append hprefix tailTrace_1499794
  have hstable : (prefixWord ++ tailWord_1499794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499794).length < 2 ^ (prefixWord ++ tailWord_1499794).sum := by decide
  have hdescent : baseEnd_1499794 < baseStart_1499794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499804 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_1499804 : Nat := 118140960795 + 1499804 * 2 ^ 59
def prefixEnd_1499804 : Nat := 4983230072969 + 3 ^ 40 * 1499804 * 2
def baseEnd_1499804 : Nat := 770120339535955243652533

theorem tailTrace_1499804 : CollatzResearch.WordTrace tailWord_1499804 prefixEnd_1499804 770120339535955243652533 := by
  unfold tailWord_1499804
  simp only [CollatzResearch.WordTrace]
  refine ⟨27351172929236864487737233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36468230572315819316982977 27351172929236864487737233)
  ·
    refine ⟨20513379696927648365802925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27351172929236864487737233 20513379696927648365802925)
    ·
      refine ⟨7692517386347868137176097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20513379696927648365802925 7692517386347868137176097)
      ·
        refine ⟨5769388039760901102882073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7692517386347868137176097 5769388039760901102882073)
        ·
          refine ⟨4327041029820675827161555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5769388039760901102882073 4327041029820675827161555)
          ·
            refine ⟨6490561544731013740742333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4327041029820675827161555 6490561544731013740742333)
            ·
              refine ⟨2433960579274130152778375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6490561544731013740742333 2433960579274130152778375)
              ·
                refine ⟨3650940868911195229167563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2433960579274130152778375 3650940868911195229167563)
                ·
                  refine ⟨5476411303366792843751345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3650940868911195229167563 5476411303366792843751345)
                  ·
                    refine ⟨4107308477525094632813509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5476411303366792843751345 4107308477525094632813509)
                    ·
                      refine ⟨770120339535955243652533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4107308477525094632813509 770120339535955243652533)
                      ·
                        rfl

theorem cell23_1499804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_1499804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499804 prefixEnd_1499804 := by exact prefixLift 1499804
  have htrace : WordTrace (prefixWord ++ tailWord_1499804) baseStart_1499804 baseEnd_1499804 := by
    simpa [prefixWord, tailWord_1499804, baseEnd_1499804] using wordTrace_append hprefix tailTrace_1499804
  have hstable : (prefixWord ++ tailWord_1499804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499804).length < 2 ^ (prefixWord ++ tailWord_1499804).sum := by decide
  have hdescent : baseEnd_1499804 < baseStart_1499804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499858 : List Nat := [3, 2, 2, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_1499858 : Nat := 118140960795 + 1499858 * 2 ^ 59
def prefixEnd_1499858 : Nat := 4983230072969 + 3 ^ 40 * 1499858 * 2
def baseEnd_1499858 : Nat := 770148067491298032377285

theorem tailTrace_1499858 : CollatzResearch.WordTrace tailWord_1499858 prefixEnd_1499858 770148067491298032377285 := by
  unfold tailWord_1499858
  simp only [CollatzResearch.WordTrace]
  refine ⟨13676078850069524049485057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36469543600185397465293485 13676078850069524049485057)
  ·
    refine ⟨10257059137552143037113793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13676078850069524049485057 10257059137552143037113793)
    ·
      refine ⟨7692794353164107277835345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10257059137552143037113793 7692794353164107277835345)
      ·
        refine ⟨5769595764873080458376509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7692794353164107277835345 5769595764873080458376509)
        ·
          refine ⟨2163598411827405171891191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5769595764873080458376509 2163598411827405171891191)
          ·
            refine ⟨3245397617741107757836787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2163598411827405171891191 3245397617741107757836787)
            ·
              refine ⟨4868096426611661636755181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3245397617741107757836787 4868096426611661636755181)
              ·
                refine ⟨1825536159979373113783193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4868096426611661636755181 1825536159979373113783193)
                ·
                  refine ⟨1369152119984529835337395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1825536159979373113783193 1369152119984529835337395)
                  ·
                    refine ⟨2053728179976794753006093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1369152119984529835337395 2053728179976794753006093)
                    ·
                      refine ⟨770148067491298032377285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2053728179976794753006093 770148067491298032377285)
                      ·
                        rfl

theorem cell23_1499858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_1499858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499858 prefixEnd_1499858 := by exact prefixLift 1499858
  have htrace : WordTrace (prefixWord ++ tailWord_1499858) baseStart_1499858 baseEnd_1499858 := by
    simpa [prefixWord, tailWord_1499858, baseEnd_1499858] using wordTrace_append hprefix tailTrace_1499858
  have hstable : (prefixWord ++ tailWord_1499858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499858).length < 2 ^ (prefixWord ++ tailWord_1499858).sum := by decide
  have hdescent : baseEnd_1499858 < baseStart_1499858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499868 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_1499868 : Nat := 118140960795 + 1499868 * 2 ^ 59
def prefixEnd_1499868 : Nat := 4983230072969 + 3 ^ 40 * 1499868 * 2
def baseEnd_1499868 : Nat := 770153202297842993252239

theorem tailTrace_1499868 : CollatzResearch.WordTrace tailWord_1499868 prefixEnd_1499868 770153202297842993252239 := by
  unfold tailWord_1499868
  simp only [CollatzResearch.WordTrace]
  refine ⟨27352340065120933952902129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36469786753494578603869505 27352340065120933952902129)
  ·
    refine ⟨20514255048840700464676597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27352340065120933952902129 20514255048840700464676597)
    ·
      refine ⟨1923211410828815668563431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20514255048840700464676597 1923211410828815668563431)
      ·
        refine ⟨2884817116243223502845147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1923211410828815668563431 2884817116243223502845147)
        ·
          refine ⟨4327225674364835254267721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2884817116243223502845147 4327225674364835254267721)
          ·
            refine ⟨3245419255773626440700791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4327225674364835254267721 3245419255773626440700791)
            ·
              refine ⟨4868128883660439661051187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3245419255773626440700791 4868128883660439661051187)
              ·
                refine ⟨7302193325490659491576781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4868128883660439661051187 7302193325490659491576781)
                ·
                  refine ⟨2738322497058997309341293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7302193325490659491576781 2738322497058997309341293)
                  ·
                    refine ⟨1026870936397123991002985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2738322497058997309341293 1026870936397123991002985)
                    ·
                      refine ⟨770153202297842993252239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1026870936397123991002985 770153202297842993252239)
                      ·
                        rfl

theorem cell23_1499868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_1499868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499868 prefixEnd_1499868 := by exact prefixLift 1499868
  have htrace : WordTrace (prefixWord ++ tailWord_1499868) baseStart_1499868 baseEnd_1499868 := by
    simpa [prefixWord, tailWord_1499868, baseEnd_1499868] using wordTrace_append hprefix tailTrace_1499868
  have hstable : (prefixWord ++ tailWord_1499868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499868).length < 2 ^ (prefixWord ++ tailWord_1499868).sum := by decide
  have hdescent : baseEnd_1499868 < baseStart_1499868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499892 : List Nat := [2, 6, 1, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1499892 : Nat := 118140960795 + 1499892 * 2 ^ 59
def prefixEnd_1499892 : Nat := 4983230072969 + 3 ^ 40 * 1499892 * 2
def baseEnd_1499892 : Nat := 770165525833550899352129

theorem tailTrace_1499892 : CollatzResearch.WordTrace tailWord_1499892 prefixEnd_1499892 770165525833550899352129 := by
  unfold tailWord_1499892
  simp only [CollatzResearch.WordTrace]
  refine ⟨27352777741077460002338965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36470370321436613336451953 27352777741077460002338965)
  ·
    refine ⟨1282161456613005937609639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27352777741077460002338965 1282161456613005937609639)
    ·
      refine ⟨1923242184919508906414459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1282161456613005937609639 1923242184919508906414459)
      ·
        refine ⟨2884863277379263359621689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1923242184919508906414459 2884863277379263359621689)
        ·
          refine ⟨2163647458034447519716267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2884863277379263359621689 2163647458034447519716267)
          ·
            refine ⟨3245471187051671279574401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2163647458034447519716267 3245471187051671279574401)
            ·
              refine ⟨2434103390288753459680801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3245471187051671279574401 2434103390288753459680801)
              ·
                refine ⟨1825577542716565094760601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2434103390288753459680801 1825577542716565094760601)
                ·
                  refine ⟨1369183157037423821070451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1825577542716565094760601 1369183157037423821070451)
                  ·
                    refine ⟨2053774735556135731605677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1369183157037423821070451 2053774735556135731605677)
                    ·
                      refine ⟨770165525833550899352129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2053774735556135731605677 770165525833550899352129)
                      ·
                        rfl

theorem cell23_1499892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1499892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499892 prefixEnd_1499892 := by exact prefixLift 1499892
  have htrace : WordTrace (prefixWord ++ tailWord_1499892) baseStart_1499892 baseEnd_1499892 := by
    simpa [prefixWord, tailWord_1499892, baseEnd_1499892] using wordTrace_append hprefix tailTrace_1499892
  have hstable : (prefixWord ++ tailWord_1499892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499892).length < 2 ^ (prefixWord ++ tailWord_1499892).sum := by decide
  have hdescent : baseEnd_1499892 < baseStart_1499892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499893 : List Nat := [1, 3, 6, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_1499893 : Nat := 118140960795 + 1499893 * 2 ^ 59
def prefixEnd_1499893 : Nat := 4983230072969 + 3 ^ 40 * 1499893 * 2
def baseEnd_1499893 : Nat := 770166039314205395439625

theorem tailTrace_1499893 : CollatzResearch.WordTrace tailWord_1499893 prefixEnd_1499893 770166039314205395439625 := by
  unfold tailWord_1499893
  simp only [CollatzResearch.WordTrace]
  refine ⟨54705591955151297175464333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36470394636767531450309555 54705591955151297175464333)
  ·
    refine ⟨20514596983181736440799125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54705591955151297175464333 20514596983181736440799125)
    ·
      refine ⟨961621733586643895662459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20514596983181736440799125 961621733586643895662459)
      ·
        refine ⟨1442432600379965843493689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 961621733586643895662459 1442432600379965843493689)
        ·
          refine ⟨1081824450284974382620267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1442432600379965843493689 1081824450284974382620267)
          ·
            refine ⟨1622736675427461573930401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081824450284974382620267 1622736675427461573930401)
            ·
              refine ⟨1217052506570596180447801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1622736675427461573930401 1217052506570596180447801)
              ·
                refine ⟨912789379927947135335851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217052506570596180447801 912789379927947135335851)
                ·
                  refine ⟨1369184069891920703003777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 912789379927947135335851 1369184069891920703003777)
                  ·
                    refine ⟨1026888052418940527252833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1369184069891920703003777 1026888052418940527252833)
                    ·
                      refine ⟨770166039314205395439625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1026888052418940527252833 770166039314205395439625)
                      ·
                        rfl

theorem cell23_1499893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_1499893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499893 prefixEnd_1499893 := by exact prefixLift 1499893
  have htrace : WordTrace (prefixWord ++ tailWord_1499893) baseStart_1499893 baseEnd_1499893 := by
    simpa [prefixWord, tailWord_1499893, baseEnd_1499893] using wordTrace_append hprefix tailTrace_1499893
  have hstable : (prefixWord ++ tailWord_1499893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499893).length < 2 ^ (prefixWord ++ tailWord_1499893).sum := by decide
  have hdescent : baseEnd_1499893 < baseStart_1499893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499894 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1499894 : Nat := 118140960795 + 1499894 * 2 ^ 59
def prefixEnd_1499894 : Nat := 4983230072969 + 3 ^ 40 * 1499894 * 2
def baseEnd_1499894 : Nat := 770166552794859891527119

theorem tailTrace_1499894 : CollatzResearch.WordTrace tailWord_1499894 prefixEnd_1499894 770166552794859891527119 := by
  unfold tailWord_1499894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3419101776759229646640671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36470418952098449564167157 3419101776759229646640671)
  ·
    refine ⟨5128652665138844469961007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3419101776759229646640671 5128652665138844469961007)
    ·
      refine ⟨7692978997708266704941511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5128652665138844469961007 7692978997708266704941511)
      ·
        refine ⟨11539468496562400057412267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7692978997708266704941511 11539468496562400057412267)
        ·
          refine ⟨17309202744843600086118401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11539468496562400057412267 17309202744843600086118401)
          ·
            refine ⟨12981902058632700064588801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17309202744843600086118401 12981902058632700064588801)
            ·
              refine ⟨9736426543974525048441601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12981902058632700064588801 9736426543974525048441601)
              ·
                refine ⟨7302319907980893786331201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9736426543974525048441601 7302319907980893786331201)
                ·
                  refine ⟨5476739930985670339748401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7302319907980893786331201 5476739930985670339748401)
                  ·
                    refine ⟨4107554948239252754811301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5476739930985670339748401 4107554948239252754811301)
                    ·
                      refine ⟨770166552794859891527119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4107554948239252754811301 770166552794859891527119)
                      ·
                        rfl

theorem cell23_1499894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1499894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499894 prefixEnd_1499894 := by exact prefixLift 1499894
  have htrace : WordTrace (prefixWord ++ tailWord_1499894) baseStart_1499894 baseEnd_1499894 := by
    simpa [prefixWord, tailWord_1499894, baseEnd_1499894] using wordTrace_append hprefix tailTrace_1499894
  have hstable : (prefixWord ++ tailWord_1499894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499894).length < 2 ^ (prefixWord ++ tailWord_1499894).sum := by decide
  have hdescent : baseEnd_1499894 < baseStart_1499894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499897 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 3, 5, 3]
def baseStart_1499897 : Nat := 118140960795 + 1499897 * 2 ^ 59
def prefixEnd_1499897 : Nat := 4983230072969 + 3 ^ 40 * 1499897 * 2
def baseEnd_1499897 : Nat := 770168093236823379789605

theorem tailTrace_1499897 : CollatzResearch.WordTrace tailWord_1499897 prefixEnd_1499897 770168093236823379789605 := by
  unfold tailWord_1499897
  simp only [CollatzResearch.WordTrace]
  refine ⟨54705737847136805858609945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36470491898091203905739963 54705737847136805858609945)
  ·
    refine ⟨41029303385352604393957459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54705737847136805858609945 41029303385352604393957459)
    ·
      refine ⟨61543955078028906590936189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41029303385352604393957459 61543955078028906590936189)
      ·
        refine ⟨23078983154260839971601071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61543955078028906590936189 23078983154260839971601071)
        ·
          refine ⟨34618474731391259957401607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23078983154260839971601071 34618474731391259957401607)
          ·
            refine ⟨51927712097086889936102411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34618474731391259957401607 51927712097086889936102411)
            ·
              refine ⟨77891568145630334904153617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51927712097086889936102411 77891568145630334904153617)
              ·
                refine ⟨58418676109222751178115213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77891568145630334904153617 58418676109222751178115213)
                ·
                  refine ⟨21907003540958531691793205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58418676109222751178115213 21907003540958531691793205)
                  ·
                    refine ⟨2053781581964862346105613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21907003540958531691793205 2053781581964862346105613)
                    ·
                      refine ⟨770168093236823379789605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2053781581964862346105613 770168093236823379789605)
                      ·
                        rfl

theorem cell23_1499897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_1499897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499897 prefixEnd_1499897 := by exact prefixLift 1499897
  have htrace : WordTrace (prefixWord ++ tailWord_1499897) baseStart_1499897 baseEnd_1499897 := by
    simpa [prefixWord, tailWord_1499897, baseEnd_1499897] using wordTrace_append hprefix tailTrace_1499897
  have hstable : (prefixWord ++ tailWord_1499897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499897).length < 2 ^ (prefixWord ++ tailWord_1499897).sum := by decide
  have hdescent : baseEnd_1499897 < baseStart_1499897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499914 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 2, 3, 3]
def baseStart_1499914 : Nat := 118140960795 + 1499914 * 2 ^ 59
def prefixEnd_1499914 : Nat := 4983230072969 + 3 ^ 40 * 1499914 * 2
def baseEnd_1499914 : Nat := 770176822407949813277027

theorem tailTrace_1499914 : CollatzResearch.WordTrace tailWord_1499914 prefixEnd_1499914 770176822407949813277027 := by
  unfold tailWord_1499914
  simp only [CollatzResearch.WordTrace]
  refine ⟨13676589472018804440494699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36470905258716811841319197 13676589472018804440494699)
  ·
    refine ⟨20514884208028206660742049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13676589472018804440494699 20514884208028206660742049)
    ·
      refine ⟨15386163156021154995556537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20514884208028206660742049 15386163156021154995556537)
      ·
        refine ⟨11539622367015866246667403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15386163156021154995556537 11539622367015866246667403)
        ·
          refine ⟨17309433550523799370001105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11539622367015866246667403 17309433550523799370001105)
          ·
            refine ⟨12982075162892849527500829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17309433550523799370001105 12982075162892849527500829)
            ·
              refine ⟨4868278186084818572812811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12982075162892849527500829 4868278186084818572812811)
              ·
                refine ⟨7302417279127227859219217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4868278186084818572812811 7302417279127227859219217)
                ·
                  refine ⟨5476812959345420894414413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7302417279127227859219217 5476812959345420894414413)
                  ·
                    refine ⟨2053804859754532835405405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5476812959345420894414413 2053804859754532835405405)
                    ·
                      refine ⟨770176822407949813277027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2053804859754532835405405 770176822407949813277027)
                      ·
                        rfl

theorem cell23_1499914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_1499914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499914 prefixEnd_1499914 := by exact prefixLift 1499914
  have htrace : WordTrace (prefixWord ++ tailWord_1499914) baseStart_1499914 baseEnd_1499914 := by
    simpa [prefixWord, tailWord_1499914, baseEnd_1499914] using wordTrace_append hprefix tailTrace_1499914
  have hstable : (prefixWord ++ tailWord_1499914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499914).length < 2 ^ (prefixWord ++ tailWord_1499914).sum := by decide
  have hdescent : baseEnd_1499914 < baseStart_1499914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499949 : List Nat := [1, 5, 3, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_1499949 : Nat := 118140960795 + 1499949 * 2 ^ 59
def prefixEnd_1499949 : Nat := 4983230072969 + 3 ^ 40 * 1499949 * 2
def baseEnd_1499949 : Nat := 770194794230857176339367

theorem tailTrace_1499949 : CollatzResearch.WordTrace tailWord_1499949 prefixEnd_1499949 770194794230857176339367 := by
  unfold tailWord_1499949
  simp only [CollatzResearch.WordTrace]
  refine ⟨54707634442948418739502901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36471756295298945826335267 54707634442948418739502901)
  ·
    refine ⟨5128840729026414256828397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54707634442948418739502901 5128840729026414256828397)
    ·
      refine ⟨1923315273384905346310649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5128840729026414256828397 1923315273384905346310649)
      ·
        refine ⟨1442486455038679009732987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1923315273384905346310649 1442486455038679009732987)
        ·
          refine ⟨2163729682558018514599481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1442486455038679009732987 2163729682558018514599481)
          ·
            refine ⟨1622797261918513885949611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2163729682558018514599481 1622797261918513885949611)
            ·
              refine ⟨2434195892877770828924417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1622797261918513885949611 2434195892877770828924417)
              ·
                refine ⟨1825646919658328121693313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2434195892877770828924417 1825646919658328121693313)
                ·
                  refine ⟨1369235189743746091269985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1825646919658328121693313 1369235189743746091269985)
                  ·
                    refine ⟨1026926392307809568452489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1369235189743746091269985 1026926392307809568452489)
                    ·
                      refine ⟨770194794230857176339367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1026926392307809568452489 770194794230857176339367)
                      ·
                        rfl

theorem cell23_1499949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_1499949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499949 prefixEnd_1499949 := by exact prefixLift 1499949
  have htrace : WordTrace (prefixWord ++ tailWord_1499949) baseStart_1499949 baseEnd_1499949 := by
    simpa [prefixWord, tailWord_1499949, baseEnd_1499949] using wordTrace_append hprefix tailTrace_1499949
  have hstable : (prefixWord ++ tailWord_1499949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499949).length < 2 ^ (prefixWord ++ tailWord_1499949).sum := by decide
  have hdescent : baseEnd_1499949 < baseStart_1499949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499954 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_1499954 : Nat := 118140960795 + 1499954 * 2 ^ 59
def prefixEnd_1499954 : Nat := 4983230072969 + 3 ^ 40 * 1499954 * 2
def baseEnd_1499954 : Nat := 770197361634129656776843

theorem tailTrace_1499954 : CollatzResearch.WordTrace tailWord_1499954 prefixEnd_1499954 770197361634129656776843 := by
  unfold tailWord_1499954
  simp only [CollatzResearch.WordTrace]
  refine ⟨13676954201982576148358729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36471877871953536395623277 13676954201982576148358729)
  ·
    refine ⟨10257715651486932111269047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13676954201982576148358729 10257715651486932111269047)
    ·
      refine ⟨15386573477230398166903571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10257715651486932111269047 15386573477230398166903571)
      ·
        refine ⟨23079860215845597250355357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15386573477230398166903571 23079860215845597250355357)
        ·
          refine ⟨8654947580942098968883259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23079860215845597250355357 8654947580942098968883259)
          ·
            refine ⟨12982421371413148453324889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8654947580942098968883259 12982421371413148453324889)
            ·
              refine ⟨9736816028559861339993667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12982421371413148453324889 9736816028559861339993667)
              ·
                refine ⟨14605224042839792009990501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9736816028559861339993667 14605224042839792009990501)
                ·
                  refine ⟨2738479508032461001873219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14605224042839792009990501 2738479508032461001873219)
                  ·
                    refine ⟨4107719262048691502809829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2738479508032461001873219 4107719262048691502809829)
                    ·
                      refine ⟨770197361634129656776843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4107719262048691502809829 770197361634129656776843)
                      ·
                        rfl

theorem cell23_1499954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_1499954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1499954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1499954 prefixEnd_1499954 := by exact prefixLift 1499954
  have htrace : WordTrace (prefixWord ++ tailWord_1499954) baseStart_1499954 baseEnd_1499954 := by
    simpa [prefixWord, tailWord_1499954, baseEnd_1499954] using wordTrace_append hprefix tailTrace_1499954
  have hstable : (prefixWord ++ tailWord_1499954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499954).length < 2 ^ (prefixWord ++ tailWord_1499954).sum := by decide
  have hdescent : baseEnd_1499954 < baseStart_1499954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500041 : List Nat := [1, 2, 1, 1, 5, 2, 3, 2, 1, 5]
def baseStart_1500041 : Nat := 118140960795 + 1500041 * 2 ^ 59
def prefixEnd_1500041 : Nat := 4983230072969 + 3 ^ 40 * 1500041 * 2
def baseEnd_1500041 : Nat := 256747344817023605462981

theorem tailTrace_1500041 : CollatzResearch.WordTrace tailWord_1500041 prefixEnd_1500041 256747344817023605462981 := by
  unfold tailWord_1500041
  simp only [CollatzResearch.WordTrace]
  refine ⟨54710989958615118451851977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36473993305743412301234651 54710989958615118451851977)
  ·
    refine ⟨41033242468961338838888983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54710989958615118451851977 41033242468961338838888983)
    ·
      refine ⟨61549863703442008258333475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41033242468961338838888983 61549863703442008258333475)
      ·
        refine ⟨92324795555163012387500213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61549863703442008258333475 92324795555163012387500213)
        ·
          refine ⟨8655449583296532411328145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92324795555163012387500213 8655449583296532411328145)
          ·
            refine ⟨6491587187472399308496109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8655449583296532411328145 6491587187472399308496109)
            ·
              refine ⟨2434345195302149740686041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6491587187472399308496109 2434345195302149740686041)
              ·
                refine ⟨1825758896476612305514531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2434345195302149740686041 1825758896476612305514531)
                ·
                  refine ⟨2738638344714918458271797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1825758896476612305514531 2738638344714918458271797)
                  ·
                    refine ⟨256747344817023605462981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2738638344714918458271797 256747344817023605462981)
                    ·
                      rfl

theorem cell23_1500041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 5].length) (baseStart_1500041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500041 prefixEnd_1500041 := by exact prefixLift 1500041
  have htrace : WordTrace (prefixWord ++ tailWord_1500041) baseStart_1500041 baseEnd_1500041 := by
    simpa [prefixWord, tailWord_1500041, baseEnd_1500041] using wordTrace_append hprefix tailTrace_1500041
  have hstable : (prefixWord ++ tailWord_1500041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500041).length < 2 ^ (prefixWord ++ tailWord_1500041).sum := by decide
  have hdescent : baseEnd_1500041 < baseStart_1500041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500047 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 11]
def baseStart_1500047 : Nat := 118140960795 + 1500047 * 2 ^ 59
def prefixEnd_1500047 : Nat := 4983230072969 + 3 ^ 40 * 1500047 * 2
def baseEnd_1500047 : Nat := 770245115334997792913915

theorem tailTrace_1500047 : CollatzResearch.WordTrace tailWord_1500047 prefixEnd_1500047 770245115334997792913915 := by
  unfold tailWord_1500047
  simp only [CollatzResearch.WordTrace]
  refine ⟨54711208796593381476570395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36474139197728920984380263 54711208796593381476570395)
  ·
    refine ⟨82066813194890072214855593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54711208796593381476570395 82066813194890072214855593)
    ·
      refine ⟨61550109896167554161141695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82066813194890072214855593 61550109896167554161141695)
      ·
        refine ⟨92325164844251331241712543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61550109896167554161141695 92325164844251331241712543)
        ·
          refine ⟨138487747266376996862568815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92325164844251331241712543 138487747266376996862568815)
          ·
            refine ⟨207731620899565495293853223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138487747266376996862568815 207731620899565495293853223)
            ·
              refine ⟨311597431349348242940779835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207731620899565495293853223 311597431349348242940779835)
              ·
                refine ⟨467396147024022364411169753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311597431349348242940779835 467396147024022364411169753)
                ·
                  refine ⟨350547110268016773308377315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467396147024022364411169753 350547110268016773308377315)
                  ·
                    refine ⟨525820665402025159962565973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 350547110268016773308377315 525820665402025159962565973)
                    ·
                      refine ⟨770245115334997792913915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 525820665402025159962565973 770245115334997792913915)
                      ·
                        rfl

theorem cell23_1500047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_1500047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500047 prefixEnd_1500047 := by exact prefixLift 1500047
  have htrace : WordTrace (prefixWord ++ tailWord_1500047) baseStart_1500047 baseEnd_1500047 := by
    simpa [prefixWord, tailWord_1500047, baseEnd_1500047] using wordTrace_append hprefix tailTrace_1500047
  have hstable : (prefixWord ++ tailWord_1500047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500047).length < 2 ^ (prefixWord ++ tailWord_1500047).sum := by decide
  have hdescent : baseEnd_1500047 < baseStart_1500047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500111 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 3]
def baseStart_1500111 : Nat := 118140960795 + 1500111 * 2 ^ 59
def prefixEnd_1500111 : Nat := 4983230072969 + 3 ^ 40 * 1500111 * 2
def baseEnd_1500111 : Nat := 770277978096885542513621

theorem tailTrace_1500111 : CollatzResearch.WordTrace tailWord_1500111 prefixEnd_1500111 770277978096885542513621 := by
  unfold tailWord_1500111
  simp only [CollatzResearch.WordTrace]
  refine ⟨54713543068361520406900187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36475695378907680271266791 54713543068361520406900187)
  ·
    refine ⟨82070314602542280610350281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54713543068361520406900187 82070314602542280610350281)
    ·
      refine ⟨61552735951906710457762711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82070314602542280610350281 61552735951906710457762711)
      ·
        refine ⟨92329103927860065686644067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61552735951906710457762711 92329103927860065686644067)
        ·
          refine ⟨138493655891790098529966101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92329103927860065686644067 138493655891790098529966101)
          ·
            refine ⟨6491890119927660868592161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 138493655891790098529966101 6491890119927660868592161)
            ·
              refine ⟨4868917589945745651444121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6491890119927660868592161 4868917589945745651444121)
              ·
                refine ⟨3651688192459309238583091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4868917589945745651444121 3651688192459309238583091)
                ·
                  refine ⟨5477532288688963857874637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3651688192459309238583091 5477532288688963857874637)
                  ·
                    refine ⟨2054074608258361446702989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5477532288688963857874637 2054074608258361446702989)
                    ·
                      refine ⟨770277978096885542513621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2054074608258361446702989 770277978096885542513621)
                      ·
                        rfl

theorem cell23_1500111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 3].length) (baseStart_1500111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500111 prefixEnd_1500111 := by exact prefixLift 1500111
  have htrace : WordTrace (prefixWord ++ tailWord_1500111) baseStart_1500111 baseEnd_1500111 := by
    simpa [prefixWord, tailWord_1500111, baseEnd_1500111] using wordTrace_append hprefix tailTrace_1500111
  have hstable : (prefixWord ++ tailWord_1500111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500111).length < 2 ^ (prefixWord ++ tailWord_1500111).sum := by decide
  have hdescent : baseEnd_1500111 < baseStart_1500111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500154 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5]
def baseStart_1500154 : Nat := 118140960795 + 1500154 * 2 ^ 59
def prefixEnd_1500154 : Nat := 4983230072969 + 3 ^ 40 * 1500154 * 2
def baseEnd_1500154 : Nat := 770300057765028874275923

theorem tailTrace_1500154 : CollatzResearch.WordTrace tailWord_1500154 prefixEnd_1500154 770300057765028874275923 := by
  unfold tailWord_1500154
  simp only [CollatzResearch.WordTrace]
  refine ⟨13678777851801434687678879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36476740938137159167143677 13678777851801434687678879)
  ·
    refine ⟨20518166777702152031518319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13678777851801434687678879 20518166777702152031518319)
    ·
      refine ⟨30777250166553228047277479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20518166777702152031518319 30777250166553228047277479)
      ·
        refine ⟨46165875249829842070916219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30777250166553228047277479 46165875249829842070916219)
        ·
          refine ⟨69248812874744763106374329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46165875249829842070916219 69248812874744763106374329)
          ·
            refine ⟨51936609656058572329780747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69248812874744763106374329 51936609656058572329780747)
            ·
              refine ⟨77904914484087858494671121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51936609656058572329780747 77904914484087858494671121)
              ·
                refine ⟨58428685863065893871003341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77904914484087858494671121 58428685863065893871003341)
                ·
                  refine ⟨21910757198649710201626253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58428685863065893871003341 21910757198649710201626253)
                  ·
                    refine ⟨8216533949493641325609845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21910757198649710201626253 8216533949493641325609845)
                    ·
                      refine ⟨770300057765028874275923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8216533949493641325609845 770300057765028874275923)
                      ·
                        rfl

theorem cell23_1500154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_1500154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500154 prefixEnd_1500154 := by exact prefixLift 1500154
  have htrace : WordTrace (prefixWord ++ tailWord_1500154) baseStart_1500154 baseEnd_1500154 := by
    simpa [prefixWord, tailWord_1500154, baseEnd_1500154] using wordTrace_append hprefix tailTrace_1500154
  have hstable : (prefixWord ++ tailWord_1500154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500154).length < 2 ^ (prefixWord ++ tailWord_1500154).sum := by decide
  have hdescent : baseEnd_1500154 < baseStart_1500154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500171 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 5]
def baseStart_1500171 : Nat := 118140960795 + 1500171 * 2 ^ 59
def prefixEnd_1500171 : Nat := 4983230072969 + 3 ^ 40 * 1500171 * 2
def baseEnd_1500171 : Nat := 770308786936155307763345

theorem tailTrace_1500171 : CollatzResearch.WordTrace tailWord_1500171 prefixEnd_1500171 770308786936155307763345 := by
  unfold tailWord_1500171
  simp only [CollatzResearch.WordTrace]
  refine ⟨54715731448144150654084367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36477154298762767102722911 54715731448144150654084367)
  ·
    refine ⟨82073597172216225981126551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54715731448144150654084367 82073597172216225981126551)
    ·
      refine ⟨123110395758324338971689827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82073597172216225981126551 123110395758324338971689827)
      ·
        refine ⟨184665593637486508457534741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123110395758324338971689827 184665593637486508457534741)
        ·
          refine ⟨8656199701757180083946941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 184665593637486508457534741 8656199701757180083946941)
          ·
            refine ⟨3246074888158942531480103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8656199701757180083946941 3246074888158942531480103)
            ·
              refine ⟨4869112332238413797220155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3246074888158942531480103 4869112332238413797220155)
              ·
                refine ⟨7303668498357620695830233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4869112332238413797220155 7303668498357620695830233)
                ·
                  refine ⟨5477751373768215521872675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7303668498357620695830233 5477751373768215521872675)
                  ·
                    refine ⟨8216627060652323282809013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5477751373768215521872675 8216627060652323282809013)
                    ·
                      refine ⟨770308786936155307763345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8216627060652323282809013 770308786936155307763345)
                      ·
                        rfl

theorem cell23_1500171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 5].length) (baseStart_1500171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500171 prefixEnd_1500171 := by exact prefixLift 1500171
  have htrace : WordTrace (prefixWord ++ tailWord_1500171) baseStart_1500171 baseEnd_1500171 := by
    simpa [prefixWord, tailWord_1500171, baseEnd_1500171] using wordTrace_append hprefix tailTrace_1500171
  have hstable : (prefixWord ++ tailWord_1500171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500171).length < 2 ^ (prefixWord ++ tailWord_1500171).sum := by decide
  have hdescent : baseEnd_1500171 < baseStart_1500171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500191 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 7]
def baseStart_1500191 : Nat := 118140960795 + 1500191 * 2 ^ 59
def prefixEnd_1500191 : Nat := 4983230072969 + 3 ^ 40 * 1500191 * 2
def baseEnd_1500191 : Nat := 85591006283249469945917

theorem tailTrace_1500191 : CollatzResearch.WordTrace tailWord_1500191 prefixEnd_1500191 85591006283249469945917 := by
  unfold tailWord_1500191
  simp only [CollatzResearch.WordTrace]
  refine ⟨54716460908071694069812427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36477640605381129379874951 54716460908071694069812427)
  ·
    refine ⟨82074691362107541104718641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54716460908071694069812427 82074691362107541104718641)
    ·
      refine ⟨61556018521580655828538981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82074691362107541104718641 61556018521580655828538981)
      ·
        refine ⟨11541753472796372967851059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61556018521580655828538981 11541753472796372967851059)
        ·
          refine ⟨17312630209194559451776589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11541753472796372967851059 17312630209194559451776589)
          ·
            refine ⟨6492236328447959794416221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17312630209194559451776589 6492236328447959794416221)
            ·
              refine ⟨2434588623167984922906083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6492236328447959794416221 2434588623167984922906083)
              ·
                refine ⟨3651882934751977384359125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2434588623167984922906083 3651882934751977384359125)
                ·
                  refine ⟨85591006283249469945917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3651882934751977384359125 85591006283249469945917)
                  ·
                    rfl

theorem cell23_1500191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 7].length) (baseStart_1500191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500191 prefixEnd_1500191 := by exact prefixLift 1500191
  have htrace : WordTrace (prefixWord ++ tailWord_1500191) baseStart_1500191 baseEnd_1500191 := by
    simpa [prefixWord, tailWord_1500191, baseEnd_1500191] using wordTrace_append hprefix tailTrace_1500191
  have hstable : (prefixWord ++ tailWord_1500191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500191).length < 2 ^ (prefixWord ++ tailWord_1500191).sum := by decide
  have hdescent : baseEnd_1500191 < baseStart_1500191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500231 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_1500231 : Nat := 118140960795 + 1500231 * 2 ^ 59
def prefixEnd_1500231 : Nat := 4983230072969 + 3 ^ 40 * 1500231 * 2
def baseEnd_1500231 : Nat := 770339595775425073013069

theorem tailTrace_1500231 : CollatzResearch.WordTrace tailWord_1500231 prefixEnd_1500231 770339595775425073013069 := by
  unfold tailWord_1500231
  simp only [CollatzResearch.WordTrace]
  refine ⟨54717919827926780901268547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36478613218617853934179031 54717919827926780901268547)
  ·
    refine ⟨82076879741890171351902821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54717919827926780901268547 82076879741890171351902821)
    ·
      refine ⟨15389414951604407128481779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82076879741890171351902821 15389414951604407128481779)
      ·
        refine ⟨23084122427406610692722669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15389414951604407128481779 23084122427406610692722669)
        ·
          refine ⟨8656545910277479009771001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23084122427406610692722669 8656545910277479009771001)
          ·
            refine ⟨6492409432708109257328251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8656545910277479009771001 6492409432708109257328251)
            ·
              refine ⟨9738614149062163885992377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6492409432708109257328251 9738614149062163885992377)
              ·
                refine ⟨7303960611796622914494283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9738614149062163885992377 7303960611796622914494283)
                ·
                  refine ⟨10955940917694934371741425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7303960611796622914494283 10955940917694934371741425)
                  ·
                    refine ⟨8216955688271200778806069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10955940917694934371741425 8216955688271200778806069)
                    ·
                      refine ⟨770339595775425073013069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8216955688271200778806069 770339595775425073013069)
                      ·
                        rfl

theorem cell23_1500231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_1500231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500231 prefixEnd_1500231 := by exact prefixLift 1500231
  have htrace : WordTrace (prefixWord ++ tailWord_1500231) baseStart_1500231 baseEnd_1500231 := by
    simpa [prefixWord, tailWord_1500231, baseEnd_1500231] using wordTrace_append hprefix tailTrace_1500231
  have hstable : (prefixWord ++ tailWord_1500231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500231).length < 2 ^ (prefixWord ++ tailWord_1500231).sum := by decide
  have hdescent : baseEnd_1500231 < baseStart_1500231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500242 : List Nat := [3, 2, 2, 1, 3, 3, 2, 2, 5]
def baseStart_1500242 : Nat := 118140960795 + 1500242 * 2 ^ 59
def prefixEnd_1500242 : Nat := 4983230072969 + 3 ^ 40 * 1500242 * 2
def baseEnd_1500242 : Nat := 85593916006958281108391

theorem tailTrace_1500242 : CollatzResearch.WordTrace tailWord_1500242 prefixEnd_1500242 85593916006958281108391 := by
  unfold tailWord_1500242
  simp only [CollatzResearch.WordTrace]
  refine ⟨13679580257721732444979745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36478880687257953186612653 13679580257721732444979745)
  ·
    refine ⟨10259685193291299333734809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13679580257721732444979745 10259685193291299333734809)
    ·
      refine ⟨7694763894968474500301107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10259685193291299333734809 7694763894968474500301107)
      ·
        refine ⟨11542145842452711750451661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7694763894968474500301107 11542145842452711750451661)
        ·
          refine ⟨4328304690919766906419373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11542145842452711750451661 4328304690919766906419373)
          ·
            refine ⟨1623114259094912589907265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4328304690919766906419373 1623114259094912589907265)
            ·
              refine ⟨1217335694321184442430449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1623114259094912589907265 1217335694321184442430449)
              ·
                refine ⟨913001770740888331822837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217335694321184442430449 913001770740888331822837)
                ·
                  refine ⟨85593916006958281108391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 913001770740888331822837 85593916006958281108391)
                  ·
                    rfl

theorem cell23_1500242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_1500242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500242 prefixEnd_1500242 := by exact prefixLift 1500242
  have htrace : WordTrace (prefixWord ++ tailWord_1500242) baseStart_1500242 baseEnd_1500242 := by
    simpa [prefixWord, tailWord_1500242, baseEnd_1500242] using wordTrace_append hprefix tailTrace_1500242
  have hstable : (prefixWord ++ tailWord_1500242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500242).length < 2 ^ (prefixWord ++ tailWord_1500242).sum := by decide
  have hdescent : baseEnd_1500242 < baseStart_1500242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500268 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 3, 4]
def baseStart_1500268 : Nat := 118140960795 + 1500268 * 2 ^ 59
def prefixEnd_1500268 : Nat := 4983230072969 + 3 ^ 40 * 1500268 * 2
def baseEnd_1500268 : Nat := 256786198186547142750133

theorem tailTrace_1500268 : CollatzResearch.WordTrace tailWord_1500268 prefixEnd_1500268 256786198186547142750133 := by
  unfold tailWord_1500268
  simp only [CollatzResearch.WordTrace]
  refine ⟨27359634664396368110182729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36479512885861824146910305 27359634664396368110182729)
  ·
    refine ⟨20519725998297276082637047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27359634664396368110182729 20519725998297276082637047)
    ·
      refine ⟨30779588997445914123955571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20519725998297276082637047 30779588997445914123955571)
      ·
        refine ⟨46169383496168871185933357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30779588997445914123955571 46169383496168871185933357)
        ·
          refine ⟨17313518811063326694725009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46169383496168871185933357 17313518811063326694725009)
          ·
            refine ⟨12985139108297495021043757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17313518811063326694725009 12985139108297495021043757)
            ·
              refine ⟨4869427165611560632891409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12985139108297495021043757 4869427165611560632891409)
              ·
                refine ⟨3652070374208670474668557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4869427165611560632891409 3652070374208670474668557)
                ·
                  refine ⟨1369526390328251428000709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3652070374208670474668557 1369526390328251428000709)
                  ·
                    refine ⟨256786198186547142750133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1369526390328251428000709 256786198186547142750133)
                    ·
                      rfl

theorem cell23_1500268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_1500268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500268 prefixEnd_1500268 := by exact prefixLift 1500268
  have htrace : WordTrace (prefixWord ++ tailWord_1500268) baseStart_1500268 baseEnd_1500268 := by
    simpa [prefixWord, tailWord_1500268, baseEnd_1500268] using wordTrace_append hprefix tailTrace_1500268
  have hstable : (prefixWord ++ tailWord_1500268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500268).length < 2 ^ (prefixWord ++ tailWord_1500268).sum := by decide
  have hdescent : baseEnd_1500268 < baseStart_1500268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500302 : List Nat := [4, 1, 1, 3, 2, 1, 2, 4, 1, 4]
def baseStart_1500302 : Nat := 118140960795 + 1500302 * 2 ^ 59
def prefixEnd_1500302 : Nat := 4983230072969 + 3 ^ 40 * 1500302 * 2
def baseEnd_1500302 : Nat := 256792017633964765075081

theorem tailTrace_1500302 : CollatzResearch.WordTrace tailWord_1500302 prefixEnd_1500302 256792017633964765075081 := by
  unfold tailWord_1500302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6840063676333695003387895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36480339607113040018068773 6840063676333695003387895)
  ·
    refine ⟨10260095514500542505081843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6840063676333695003387895 10260095514500542505081843)
    ·
      refine ⟨15390143271750813757622765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10260095514500542505081843 15390143271750813757622765)
      ·
        refine ⟨5771303726906555159108537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15390143271750813757622765 5771303726906555159108537)
        ·
          refine ⟨4328477795179916369331403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5771303726906555159108537 4328477795179916369331403)
          ·
            refine ⟨6492716692769874553997105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4328477795179916369331403 6492716692769874553997105)
            ·
              refine ⟨4869537519577405915497829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6492716692769874553997105 4869537519577405915497829)
              ·
                refine ⟨913038284920763609155843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4869537519577405915497829 913038284920763609155843)
                ·
                  refine ⟨1369557427381145413733765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 913038284920763609155843 1369557427381145413733765)
                  ·
                    refine ⟨256792017633964765075081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1369557427381145413733765 256792017633964765075081)
                    ·
                      rfl

theorem cell23_1500302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_1500302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500302 prefixEnd_1500302 := by exact prefixLift 1500302
  have htrace : WordTrace (prefixWord ++ tailWord_1500302) baseStart_1500302 baseEnd_1500302 := by
    simpa [prefixWord, tailWord_1500302, baseEnd_1500302] using wordTrace_append hprefix tailTrace_1500302
  have hstable : (prefixWord ++ tailWord_1500302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500302).length < 2 ^ (prefixWord ++ tailWord_1500302).sum := by decide
  have hdescent : baseEnd_1500302 < baseStart_1500302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500325 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 3, 1, 3]
def baseStart_1500325 : Nat := 118140960795 + 1500325 * 2 ^ 59
def prefixEnd_1500325 : Nat := 4983230072969 + 3 ^ 40 * 1500325 * 2
def baseEnd_1500325 : Nat := 770387862956947705237637

theorem tailTrace_1500325 : CollatzResearch.WordTrace tailWord_1500325 prefixEnd_1500325 770387862956947705237637 := by
  unfold tailWord_1500325
  simp only [CollatzResearch.WordTrace]
  refine ⟨54721348289586234955190429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36480898859724156636793619 54721348289586234955190429)
  ·
    refine ⟨20520505608594838108196411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54721348289586234955190429 20520505608594838108196411)
    ·
      refine ⟨30780758412892257162294617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20520505608594838108196411 30780758412892257162294617)
      ·
        refine ⟨23085568809669192871720963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30780758412892257162294617 23085568809669192871720963)
        ·
          refine ⟨34628353214503789307581445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23085568809669192871720963 34628353214503789307581445)
          ·
            refine ⟨6492816227719460495171521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34628353214503789307581445 6492816227719460495171521)
            ·
              refine ⟨4869612170789595371378641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6492816227719460495171521 4869612170789595371378641)
              ·
                refine ⟨3652209128092196528533981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4869612170789595371378641 3652209128092196528533981)
                ·
                  refine ⟨1369578423034573698200243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3652209128092196528533981 1369578423034573698200243)
                  ·
                    refine ⟨2054367634551860547300365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1369578423034573698200243 2054367634551860547300365)
                    ·
                      refine ⟨770387862956947705237637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2054367634551860547300365 770387862956947705237637)
                      ·
                        rfl

theorem cell23_1500325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_1500325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500325 prefixEnd_1500325 := by exact prefixLift 1500325
  have htrace : WordTrace (prefixWord ++ tailWord_1500325) baseStart_1500325 baseEnd_1500325 := by
    simpa [prefixWord, tailWord_1500325, baseEnd_1500325] using wordTrace_append hprefix tailTrace_1500325
  have hstable : (prefixWord ++ tailWord_1500325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500325).length < 2 ^ (prefixWord ++ tailWord_1500325).sum := by decide
  have hdescent : baseEnd_1500325 < baseStart_1500325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500352 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 2, 3, 2]
def baseStart_1500352 : Nat := 118140960795 + 1500352 * 2 ^ 59
def prefixEnd_1500352 : Nat := 4983230072969 + 3 ^ 40 * 1500352 * 2
def baseEnd_1500352 : Nat := 770401726934619099600013

theorem tailTrace_1500352 : CollatzResearch.WordTrace tailWord_1500352 prefixEnd_1500352 770401726934619099600013 := by
  unfold tailWord_1500352
  simp only [CollatzResearch.WordTrace]
  refine ⟨27361166530244209283211655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36481555373658945710948873 27361166530244209283211655)
  ·
    refine ⟨41041749795366313924817483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27361166530244209283211655 41041749795366313924817483)
    ·
      refine ⟨61562624693049470887226225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41041749795366313924817483 61562624693049470887226225)
      ·
        refine ⟨46171968519787103165419669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61562624693049470887226225 46171968519787103165419669)
        ·
          refine ⟨2164311024365020460879047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46171968519787103165419669 2164311024365020460879047)
          ·
            refine ⟨3246466536547530691318571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164311024365020460879047 3246466536547530691318571)
            ·
              refine ⟨4869699804821296036977857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3246466536547530691318571 4869699804821296036977857)
              ·
                refine ⟨3652274853615972027733393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4869699804821296036977857 3652274853615972027733393)
                ·
                  refine ⟨2739206140211979020800045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3652274853615972027733393 2739206140211979020800045)
                  ·
                    refine ⟨1027202302579492132800017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2739206140211979020800045 1027202302579492132800017)
                    ·
                      refine ⟨770401726934619099600013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1027202302579492132800017 770401726934619099600013)
                      ·
                        rfl

theorem cell23_1500352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 2, 3, 2].length) (baseStart_1500352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500352 prefixEnd_1500352 := by exact prefixLift 1500352
  have htrace : WordTrace (prefixWord ++ tailWord_1500352) baseStart_1500352 baseEnd_1500352 := by
    simpa [prefixWord, tailWord_1500352, baseEnd_1500352] using wordTrace_append hprefix tailTrace_1500352
  have hstable : (prefixWord ++ tailWord_1500352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500352).length < 2 ^ (prefixWord ++ tailWord_1500352).sum := by decide
  have hdescent : baseEnd_1500352 < baseStart_1500352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500378 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4]
def baseStart_1500378 : Nat := 118140960795 + 1500378 * 2 ^ 59
def prefixEnd_1500378 : Nat := 4983230072969 + 3 ^ 40 * 1500378 * 2
def baseEnd_1500378 : Nat := 770415077431635997874893

theorem tailTrace_1500378 : CollatzResearch.WordTrace tailWord_1500378 prefixEnd_1500378 770415077431635997874893 := by
  unfold tailWord_1500378
  simp only [CollatzResearch.WordTrace]
  refine ⟨13680820339598556251717447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36482187572262816671246525 13680820339598556251717447)
  ·
    refine ⟨20521230509397834377576171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13680820339598556251717447 20521230509397834377576171)
    ·
      refine ⟨30781845764096751566364257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20521230509397834377576171 30781845764096751566364257)
      ·
        refine ⟨23086384323072563674773193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30781845764096751566364257 23086384323072563674773193)
        ·
          refine ⟨17314788242304422756079895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23086384323072563674773193 17314788242304422756079895)
          ·
            refine ⟨25972182363456634134119843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17314788242304422756079895 25972182363456634134119843)
            ·
              refine ⟨38958273545184951201179765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25972182363456634134119843 38958273545184951201179765)
              ·
                refine ⟨3652338144861089175110603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38958273545184951201179765 3652338144861089175110603)
                ·
                  refine ⟨5478507217291633762665905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3652338144861089175110603 5478507217291633762665905)
                  ·
                    refine ⟨4108880412968725321999429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5478507217291633762665905 4108880412968725321999429)
                    ·
                      refine ⟨770415077431635997874893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4108880412968725321999429 770415077431635997874893)
                      ·
                        rfl

theorem cell23_1500378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_1500378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500378 prefixEnd_1500378 := by exact prefixLift 1500378
  have htrace : WordTrace (prefixWord ++ tailWord_1500378) baseStart_1500378 baseEnd_1500378 := by
    simpa [prefixWord, tailWord_1500378, baseEnd_1500378] using wordTrace_append hprefix tailTrace_1500378
  have hstable : (prefixWord ++ tailWord_1500378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500378).length < 2 ^ (prefixWord ++ tailWord_1500378).sum := by decide
  have hdescent : baseEnd_1500378 < baseStart_1500378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500385 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 3, 2, 3]
def baseStart_1500385 : Nat := 118140960795 + 1500385 * 2 ^ 59
def prefixEnd_1500385 : Nat := 4983230072969 + 3 ^ 40 * 1500385 * 2
def baseEnd_1500385 : Nat := 770418671796217470487361

theorem tailTrace_1500385 : CollatzResearch.WordTrace tailWord_1500385 prefixEnd_1500385 770418671796217470487361 := by
  unfold tailWord_1500385
  simp only [CollatzResearch.WordTrace]
  refine ⟨54723536669368865202374609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36482357779579243468249739 54723536669368865202374609)
  ·
    refine ⟨41042652502026648901780957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54723536669368865202374609 41042652502026648901780957)
    ·
      refine ⟨15390994688259993338167859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41042652502026648901780957 15390994688259993338167859)
      ·
        refine ⟨23086492032389990007251789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15390994688259993338167859 23086492032389990007251789)
        ·
          refine ⟨8657434512146246252719421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23086492032389990007251789 8657434512146246252719421)
          ·
            refine ⟨3246537942054842344769783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8657434512146246252719421 3246537942054842344769783)
            ·
              refine ⟨4869806913082263517154675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3246537942054842344769783 4869806913082263517154675)
              ·
                refine ⟨7304710369623395275732013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4869806913082263517154675 7304710369623395275732013)
                ·
                  refine ⟨2739266388608773228399505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7304710369623395275732013 2739266388608773228399505)
                  ·
                    refine ⟨2054449791456579921299629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2739266388608773228399505 2054449791456579921299629)
                    ·
                      refine ⟨770418671796217470487361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2054449791456579921299629 770418671796217470487361)
                      ·
                        rfl

theorem cell23_1500385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_1500385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500385 prefixEnd_1500385 := by exact prefixLift 1500385
  have htrace : WordTrace (prefixWord ++ tailWord_1500385) baseStart_1500385 baseEnd_1500385 := by
    simpa [prefixWord, tailWord_1500385, baseEnd_1500385] using wordTrace_append hprefix tailTrace_1500385
  have hstable : (prefixWord ++ tailWord_1500385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500385).length < 2 ^ (prefixWord ++ tailWord_1500385).sum := by decide
  have hdescent : baseEnd_1500385 < baseStart_1500385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500402 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 1, 1, 5]
def baseStart_1500402 : Nat := 118140960795 + 1500402 * 2 ^ 59
def prefixEnd_1500402 : Nat := 4983230072969 + 3 ^ 40 * 1500402 * 2
def baseEnd_1500402 : Nat := 770427400967343903974783

theorem tailTrace_1500402 : CollatzResearch.WordTrace tailWord_1500402 prefixEnd_1500402 770427400967343903974783 := by
  unfold tailWord_1500402
  simp only [CollatzResearch.WordTrace]
  refine ⟨13681039177576819276435865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36482771140204851403828973 13681039177576819276435865)
  ·
    refine ⟨10260779383182614457326899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13681039177576819276435865 10260779383182614457326899)
    ·
      refine ⟨15391169074773921685990349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10260779383182614457326899 15391169074773921685990349)
      ·
        refine ⟨5771688403040220632246381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15391169074773921685990349 5771688403040220632246381)
        ·
          refine ⟨2164383151140082737092393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5771688403040220632246381 2164383151140082737092393)
          ·
            refine ⟨1623287363355062052819295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2164383151140082737092393 1623287363355062052819295)
            ·
              refine ⟨2434931045032593079228943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623287363355062052819295 2434931045032593079228943)
              ·
                refine ⟨3652396567548889618843415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2434931045032593079228943 3652396567548889618843415)
                ·
                  refine ⟨5478594851323334428265123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3652396567548889618843415 5478594851323334428265123)
                  ·
                    refine ⟨8217892276985001642397685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5478594851323334428265123 8217892276985001642397685)
                    ·
                      refine ⟨770427400967343903974783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8217892276985001642397685 770427400967343903974783)
                      ·
                        rfl

theorem cell23_1500402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_1500402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500402 prefixEnd_1500402 := by exact prefixLift 1500402
  have htrace : WordTrace (prefixWord ++ tailWord_1500402) baseStart_1500402 baseEnd_1500402 := by
    simpa [prefixWord, tailWord_1500402, baseEnd_1500402] using wordTrace_append hprefix tailTrace_1500402
  have hstable : (prefixWord ++ tailWord_1500402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500402).length < 2 ^ (prefixWord ++ tailWord_1500402).sum := by decide
  have hdescent : baseEnd_1500402 < baseStart_1500402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500411 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 7]
def baseStart_1500411 : Nat := 118140960795 + 1500411 * 2 ^ 59
def prefixEnd_1500411 : Nat := 4983230072969 + 3 ^ 40 * 1500411 * 2
def baseEnd_1500411 : Nat := 770432022293234368762241

theorem tailTrace_1500411 : CollatzResearch.WordTrace tailWord_1500411 prefixEnd_1500411 770432022293234368762241 := by
  unfold tailWord_1500411
  simp only [CollatzResearch.WordTrace]
  refine ⟨54724484967274671642821087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36482989978183114428547391 54724484967274671642821087)
  ·
    refine ⟨82086727450912007464231631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54724484967274671642821087 82086727450912007464231631)
    ·
      refine ⟨123130091176368011196347447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82086727450912007464231631 123130091176368011196347447)
      ·
        refine ⟨184695136764552016794521171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123130091176368011196347447 184695136764552016794521171)
        ·
          refine ⟨277042705146828025191781757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184695136764552016794521171 277042705146828025191781757)
          ·
            refine ⟨103891014430060509446918159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277042705146828025191781757 103891014430060509446918159)
            ·
              refine ⟨155836521645090764170377239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103891014430060509446918159 155836521645090764170377239)
              ·
                refine ⟨233754782467636146255565859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155836521645090764170377239 233754782467636146255565859)
                ·
                  refine ⟨350632173701454219383348789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233754782467636146255565859 350632173701454219383348789)
                  ·
                    refine ⟨32871766284511333067188949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 350632173701454219383348789 32871766284511333067188949)
                    ·
                      refine ⟨770432022293234368762241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32871766284511333067188949 770432022293234368762241)
                      ·
                        rfl

theorem cell23_1500411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 7].length) (baseStart_1500411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500411 prefixEnd_1500411 := by exact prefixLift 1500411
  have htrace : WordTrace (prefixWord ++ tailWord_1500411) baseStart_1500411 baseEnd_1500411 := by
    simpa [prefixWord, tailWord_1500411, baseEnd_1500411] using wordTrace_append hprefix tailTrace_1500411
  have hstable : (prefixWord ++ tailWord_1500411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500411).length < 2 ^ (prefixWord ++ tailWord_1500411).sum := by decide
  have hdescent : baseEnd_1500411 < baseStart_1500411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500425 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 5, 3, 2]
def baseStart_1500425 : Nat := 118140960795 + 1500425 * 2 ^ 59
def prefixEnd_1500425 : Nat := 4983230072969 + 3 ^ 40 * 1500425 * 2
def baseEnd_1500425 : Nat := 770439211022397313987177

theorem tailTrace_1500425 : CollatzResearch.WordTrace tailWord_1500425 prefixEnd_1500425 770439211022397313987177 := by
  unfold tailWord_1500425
  simp only [CollatzResearch.WordTrace]
  refine ⟨54724995589223952033830729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36483330392815968022553819 54724995589223952033830729)
  ·
    refine ⟨41043746691917964025373047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54724995589223952033830729 41043746691917964025373047)
    ·
      refine ⟨61565620037876946038059571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41043746691917964025373047 61565620037876946038059571)
      ·
        refine ⟨92348430056815419057089357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61565620037876946038059571 92348430056815419057089357)
        ·
          refine ⟨34630661271305782146408509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92348430056815419057089357 34630661271305782146408509)
          ·
            refine ⟨12986497976739668304903191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34630661271305782146408509 12986497976739668304903191)
            ·
              refine ⟨19479746965109502457354787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12986497976739668304903191 19479746965109502457354787)
              ·
                refine ⟨29219620447664253686032181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19479746965109502457354787 29219620447664253686032181)
                ·
                  refine ⟨2739339416968523783065517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29219620447664253686032181 2739339416968523783065517)
                  ·
                    refine ⟨1027252281363196418649569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2739339416968523783065517 1027252281363196418649569)
                    ·
                      refine ⟨770439211022397313987177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1027252281363196418649569 770439211022397313987177)
                      ·
                        rfl

theorem cell23_1500425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 3, 2].length) (baseStart_1500425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500425 prefixEnd_1500425 := by exact prefixLift 1500425
  have htrace : WordTrace (prefixWord ++ tailWord_1500425) baseStart_1500425 baseEnd_1500425 := by
    simpa [prefixWord, tailWord_1500425, baseEnd_1500425] using wordTrace_append hprefix tailTrace_1500425
  have hstable : (prefixWord ++ tailWord_1500425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500425).length < 2 ^ (prefixWord ++ tailWord_1500425).sum := by decide
  have hdescent : baseEnd_1500425 < baseStart_1500425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500442 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2]
def baseStart_1500442 : Nat := 118140960795 + 1500442 * 2 ^ 59
def prefixEnd_1500442 : Nat := 4983230072969 + 3 ^ 40 * 1500442 * 2
def baseEnd_1500442 : Nat := 770447940193523747474599

theorem tailTrace_1500442 : CollatzResearch.WordTrace tailWord_1500442 prefixEnd_1500442 770447940193523747474599 := by
  unfold tailWord_1500442
  simp only [CollatzResearch.WordTrace]
  refine ⟨13681403907540590984299895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36483743753441575958133053 13681403907540590984299895)
  ·
    refine ⟨20522105861310886476449843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13681403907540590984299895 20522105861310886476449843)
    ·
      refine ⟨30783158791966329714674765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20522105861310886476449843 30783158791966329714674765)
      ·
        refine ⟨11543684546987373643003037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30783158791966329714674765 11543684546987373643003037)
        ·
          refine ⟨4328881705120265116126139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11543684546987373643003037 4328881705120265116126139)
          ·
            refine ⟨6493322557680397674189209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4328881705120265116126139 6493322557680397674189209)
            ·
              refine ⟨4869991918260298255641907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6493322557680397674189209 4869991918260298255641907)
              ·
                refine ⟨7304987877390447383462861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4869991918260298255641907 7304987877390447383462861)
                ·
                  refine ⟨2739370454021417768798573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7304987877390447383462861 2739370454021417768798573)
                  ·
                    refine ⟨1027263920258031663299465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2739370454021417768798573 1027263920258031663299465)
                    ·
                      refine ⟨770447940193523747474599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1027263920258031663299465 770447940193523747474599)
                      ·
                        rfl

theorem cell23_1500442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_1500442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500442 prefixEnd_1500442 := by exact prefixLift 1500442
  have htrace : WordTrace (prefixWord ++ tailWord_1500442) baseStart_1500442 baseEnd_1500442 := by
    simpa [prefixWord, tailWord_1500442, baseEnd_1500442] using wordTrace_append hprefix tailTrace_1500442
  have hstable : (prefixWord ++ tailWord_1500442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500442).length < 2 ^ (prefixWord ++ tailWord_1500442).sum := by decide
  have hdescent : baseEnd_1500442 < baseStart_1500442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500493 : List Nat := [1, 6, 1, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_1500493 : Nat := 118140960795 + 1500493 * 2 ^ 59
def prefixEnd_1500493 : Nat := 4983230072969 + 3 ^ 40 * 1500493 * 2
def baseEnd_1500493 : Nat := 770474127706903047936865

theorem tailTrace_1500493 : CollatzResearch.WordTrace tailWord_1500493 prefixEnd_1500493 770474127706903047936865 := by
  unfold tailWord_1500493
  simp only [CollatzResearch.WordTrace]
  refine ⟨54727475752977599647306133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36484983835318399764870755 54727475752977599647306133)
  ·
    refine ⟨2565350425920824983467475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54727475752977599647306133 2565350425920824983467475)
    ·
      refine ⟨3848025638881237475201213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2565350425920824983467475 3848025638881237475201213)
      ·
        refine ⟨1443009614580464053200455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3848025638881237475201213 1443009614580464053200455)
        ·
          refine ⟨2164514421870696079800683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443009614580464053200455 2164514421870696079800683)
          ·
            refine ⟨3246771632806044119701025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164514421870696079800683 3246771632806044119701025)
            ·
              refine ⟨2435078724604533089775769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3246771632806044119701025 2435078724604533089775769)
              ·
                refine ⟨1826309043453399817331827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2435078724604533089775769 1826309043453399817331827)
                ·
                  refine ⟨2739463565180099725997741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1826309043453399817331827 2739463565180099725997741)
                  ·
                    refine ⟨1027298836942537397249153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2739463565180099725997741 1027298836942537397249153)
                    ·
                      refine ⟨770474127706903047936865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1027298836942537397249153 770474127706903047936865)
                      ·
                        rfl

theorem cell23_1500493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_1500493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500493 prefixEnd_1500493 := by exact prefixLift 1500493
  have htrace : WordTrace (prefixWord ++ tailWord_1500493) baseStart_1500493 baseEnd_1500493 := by
    simpa [prefixWord, tailWord_1500493, baseEnd_1500493] using wordTrace_append hprefix tailTrace_1500493
  have hstable : (prefixWord ++ tailWord_1500493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500493).length < 2 ^ (prefixWord ++ tailWord_1500493).sum := by decide
  have hdescent : baseEnd_1500493 < baseStart_1500493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500512 : List Nat := [2, 1, 1, 3, 4, 1, 3, 3, 5]
def baseStart_1500512 : Nat := 118140960795 + 1500512 * 2 ^ 59
def prefixEnd_1500512 : Nat := 4983230072969 + 3 ^ 40 * 1500512 * 2
def baseEnd_1500512 : Nat := 85609320426593163733253

theorem tailTrace_1500512 : CollatzResearch.WordTrace tailWord_1500512 prefixEnd_1500512 85609320426593163733253 := by
  unfold tailWord_1500512
  simp only [CollatzResearch.WordTrace]
  refine ⟨27364084369954382946123895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36485445826605843928165193 27364084369954382946123895)
  ·
    refine ⟨41046126554931574419185843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27364084369954382946123895 41046126554931574419185843)
    ·
      refine ⟨61569189832397361628778765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41046126554931574419185843 61569189832397361628778765)
      ·
        refine ⟨23088446187149010610792037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61569189832397361628778765 23088446187149010610792037)
        ·
          refine ⟨4329083660090439489523507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23088446187149010610792037 4329083660090439489523507)
          ·
            refine ⟨6493625490135659234285261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329083660090439489523507 6493625490135659234285261)
            ·
              refine ⟨2435109558800872212856973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6493625490135659234285261 2435109558800872212856973)
              ·
                refine ⟨913166084550327079821365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2435109558800872212856973 913166084550327079821365)
                ·
                  refine ⟨85609320426593163733253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 913166084550327079821365 85609320426593163733253)
                  ·
                    rfl

theorem cell23_1500512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 5].length) (baseStart_1500512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500512 prefixEnd_1500512 := by exact prefixLift 1500512
  have htrace : WordTrace (prefixWord ++ tailWord_1500512) baseStart_1500512 baseEnd_1500512 := by
    simpa [prefixWord, tailWord_1500512, baseEnd_1500512] using wordTrace_append hprefix tailTrace_1500512
  have hstable : (prefixWord ++ tailWord_1500512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500512).length < 2 ^ (prefixWord ++ tailWord_1500512).sum := by decide
  have hdescent : baseEnd_1500512 < baseStart_1500512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500525 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_1500525 : Nat := 118140960795 + 1500525 * 2 ^ 59
def prefixEnd_1500525 : Nat := 4983230072969 + 3 ^ 40 * 1500525 * 2
def baseEnd_1500525 : Nat := 256830186362615640912239

theorem tailTrace_1500525 : CollatzResearch.WordTrace tailWord_1500525 prefixEnd_1500525 256830186362615640912239 := by
  unfold tailWord_1500525
  simp only [CollatzResearch.WordTrace]
  refine ⟨54728642888861669112471029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36485761925907779408314019 54728642888861669112471029)
  ·
    refine ⟨5130810270830781479294159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54728642888861669112471029 5130810270830781479294159)
    ·
      refine ⟨7696215406246172218941239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5130810270830781479294159 7696215406246172218941239)
      ·
        refine ⟨11544323109369258328411859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7696215406246172218941239 11544323109369258328411859)
        ·
          refine ⟨17316484664053887492617789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11544323109369258328411859 17316484664053887492617789)
          ·
            refine ⟨6493681749020207809731671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17316484664053887492617789 6493681749020207809731671)
            ·
              refine ⟨9740522623530311714597507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6493681749020207809731671 9740522623530311714597507)
              ·
                refine ⟨14610783935295467571896261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9740522623530311714597507 14610783935295467571896261)
                ·
                  refine ⟨2739521987867900169730549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14610783935295467571896261 2739521987867900169730549)
                  ·
                    refine ⟨256830186362615640912239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2739521987867900169730549 256830186362615640912239)
                    ·
                      rfl

theorem cell23_1500525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_1500525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500525 prefixEnd_1500525 := by exact prefixLift 1500525
  have htrace : WordTrace (prefixWord ++ tailWord_1500525) baseStart_1500525 baseEnd_1500525 := by
    simpa [prefixWord, tailWord_1500525, baseEnd_1500525] using wordTrace_append hprefix tailTrace_1500525
  have hstable : (prefixWord ++ tailWord_1500525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500525).length < 2 ^ (prefixWord ++ tailWord_1500525).sum := by decide
  have hdescent : baseEnd_1500525 < baseStart_1500525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500555 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 5, 4]
def baseStart_1500555 : Nat := 118140960795 + 1500555 * 2 ^ 59
def prefixEnd_1500555 : Nat := 4983230072969 + 3 ^ 40 * 1500555 * 2
def baseEnd_1500555 : Nat := 256835321169160601787193

theorem tailTrace_1500555 : CollatzResearch.WordTrace tailWord_1500555 prefixEnd_1500555 256835321169160601787193 := by
  unfold tailWord_1500555
  simp only [CollatzResearch.WordTrace]
  refine ⟨54729737078752984236063119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36486491385835322824042079 54729737078752984236063119)
  ·
    refine ⟨82094605618129476354094679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54729737078752984236063119 82094605618129476354094679)
    ·
      refine ⟨123141908427194214531142019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82094605618129476354094679 123141908427194214531142019)
      ·
        refine ⟨184712862640791321796713029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123141908427194214531142019 184712862640791321796713029)
        ·
          refine ⟨34633661745148372836883693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184712862640791321796713029 34633661745148372836883693)
          ·
            refine ⟨12987623154430639813831385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34633661745148372836883693 12987623154430639813831385)
            ·
              refine ⟨9740717365822979860373539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12987623154430639813831385 9740717365822979860373539)
              ·
                refine ⟨14611076048734469790560309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9740717365822979860373539 14611076048734469790560309)
                ·
                  refine ⟨1369788379568856542865029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14611076048734469790560309 1369788379568856542865029)
                  ·
                    refine ⟨256835321169160601787193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1369788379568856542865029 256835321169160601787193)
                    ·
                      rfl

theorem cell23_1500555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 4].length) (baseStart_1500555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500555 prefixEnd_1500555 := by exact prefixLift 1500555
  have htrace : WordTrace (prefixWord ++ tailWord_1500555) baseStart_1500555 baseEnd_1500555 := by
    simpa [prefixWord, tailWord_1500555, baseEnd_1500555] using wordTrace_append hprefix tailTrace_1500555
  have hstable : (prefixWord ++ tailWord_1500555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500555).length < 2 ^ (prefixWord ++ tailWord_1500555).sum := by decide
  have hdescent : baseEnd_1500555 < baseStart_1500555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500565 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 1, 4, 3]
def baseStart_1500565 : Nat := 118140960795 + 1500565 * 2 ^ 59
def prefixEnd_1500565 : Nat := 4983230072969 + 3 ^ 40 * 1500565 * 2
def baseEnd_1500565 : Nat := 770511098314026766236533

theorem tailTrace_1500565 : CollatzResearch.WordTrace tailWord_1500565 prefixEnd_1500565 770511098314026766236533 := by
  unfold tailWord_1500565
  simp only [CollatzResearch.WordTrace]
  refine ⟨54730101808716755943927149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36486734539144503962618099 54730101808716755943927149)
  ·
    refine ⟨20523788178268783478972681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54730101808716755943927149 20523788178268783478972681)
    ·
      refine ⟨15392841133701587609229511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20523788178268783478972681 15392841133701587609229511)
      ·
        refine ⟨23089261700552381413844267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15392841133701587609229511 23089261700552381413844267)
        ·
          refine ⟨34633892550828572120766401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23089261700552381413844267 34633892550828572120766401)
          ·
            refine ⟨25975419413121429090574801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34633892550828572120766401 25975419413121429090574801)
            ·
              refine ⟨19481564559841071817931101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25975419413121429090574801 19481564559841071817931101)
              ·
                refine ⟨7305586709940401931724163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19481564559841071817931101 7305586709940401931724163)
                ·
                  refine ⟨10958380064910602897586245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7305586709940401931724163 10958380064910602897586245)
                  ·
                    refine ⟨2054696262170738043297421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10958380064910602897586245 2054696262170738043297421)
                    ·
                      refine ⟨770511098314026766236533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2054696262170738043297421 770511098314026766236533)
                      ·
                        rfl

theorem cell23_1500565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_1500565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500565 prefixEnd_1500565 := by exact prefixLift 1500565
  have htrace : WordTrace (prefixWord ++ tailWord_1500565) baseStart_1500565 baseEnd_1500565 := by
    simpa [prefixWord, tailWord_1500565, baseEnd_1500565] using wordTrace_append hprefix tailTrace_1500565
  have hstable : (prefixWord ++ tailWord_1500565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500565).length < 2 ^ (prefixWord ++ tailWord_1500565).sum := by decide
  have hdescent : baseEnd_1500565 < baseStart_1500565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500610 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1500610 : Nat := 118140960795 + 1500610 * 2 ^ 59
def prefixEnd_1500610 : Nat := 4983230072969 + 3 ^ 40 * 1500610 * 2
def baseEnd_1500610 : Nat := 256844734981159696724609

theorem tailTrace_1500610 : CollatzResearch.WordTrace tailWord_1500610 prefixEnd_1500610 256844734981159696724609 := by
  unfold tailWord_1500610
  simp only [CollatzResearch.WordTrace]
  refine ⟨13682935773388432157328821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36487828729035819086210189 13682935773388432157328821)
  ·
    refine ⟨1282775228755165514749577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13682935773388432157328821 1282775228755165514749577)
    ·
      refine ⟨962081421566374136062183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1282775228755165514749577 962081421566374136062183)
      ·
        refine ⟨1443122132349561204093275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 962081421566374136062183 1443122132349561204093275)
        ·
          refine ⟨2164683198524341806139913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443122132349561204093275 2164683198524341806139913)
          ·
            refine ⟨1623512398893256354604935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2164683198524341806139913 1623512398893256354604935)
            ·
              refine ⟨2435268598339884531907403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623512398893256354604935 2435268598339884531907403)
              ·
                refine ⟨3652902897509826797861105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2435268598339884531907403 3652902897509826797861105)
                ·
                  refine ⟨2739677173132370098395829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3652902897509826797861105 2739677173132370098395829)
                  ·
                    refine ⟨256844734981159696724609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2739677173132370098395829 256844734981159696724609)
                    ·
                      rfl

theorem cell23_1500610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1500610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500610 prefixEnd_1500610 := by exact prefixLift 1500610
  have htrace : WordTrace (prefixWord ++ tailWord_1500610) baseStart_1500610 baseEnd_1500610 := by
    simpa [prefixWord, tailWord_1500610, baseEnd_1500610] using wordTrace_append hprefix tailTrace_1500610
  have hstable : (prefixWord ++ tailWord_1500610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500610).length < 2 ^ (prefixWord ++ tailWord_1500610).sum := by decide
  have hdescent : baseEnd_1500610 < baseStart_1500610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500615 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 3, 5]
def baseStart_1500615 : Nat := 118140960795 + 1500615 * 2 ^ 59
def prefixEnd_1500615 : Nat := 4983230072969 + 3 ^ 40 * 1500615 * 2
def baseEnd_1500615 : Nat := 256845590782250523537101

theorem tailTrace_1500615 : CollatzResearch.WordTrace tailWord_1500615 prefixEnd_1500615 256845590782250523537101 := by
  unfold tailWord_1500615
  simp only [CollatzResearch.WordTrace]
  refine ⟨54731925458535614483247299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36487950305690409655498199 54731925458535614483247299)
  ·
    refine ⟨82097888187803421724870949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54731925458535614483247299 82097888187803421724870949)
    ·
      refine ⟨15393354035213141573413303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82097888187803421724870949 15393354035213141573413303)
      ·
        refine ⟨23090031052819712360119955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15393354035213141573413303 23090031052819712360119955)
        ·
          refine ⟨34635046579229568540179933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23090031052819712360119955 34635046579229568540179933)
          ·
            refine ⟨12988142467211088202567475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34635046579229568540179933 12988142467211088202567475)
            ·
              refine ⟨19482213700816632303851213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12988142467211088202567475 19482213700816632303851213)
              ·
                refine ⟨7305830137806237113944205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19482213700816632303851213 7305830137806237113944205)
                ·
                  refine ⟨2739686301677338917729077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7305830137806237113944205 2739686301677338917729077)
                  ·
                    refine ⟨256845590782250523537101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2739686301677338917729077 256845590782250523537101)
                    ·
                      rfl

theorem cell23_1500615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_1500615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500615 prefixEnd_1500615 := by exact prefixLift 1500615
  have htrace : WordTrace (prefixWord ++ tailWord_1500615) baseStart_1500615 baseEnd_1500615 := by
    simpa [prefixWord, tailWord_1500615, baseEnd_1500615] using wordTrace_append hprefix tailTrace_1500615
  have hstable : (prefixWord ++ tailWord_1500615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500615).length < 2 ^ (prefixWord ++ tailWord_1500615).sum := by decide
  have hdescent : baseEnd_1500615 < baseStart_1500615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500655 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 5]
def baseStart_1500655 : Nat := 118140960795 + 1500655 * 2 ^ 59
def prefixEnd_1500655 : Nat := 4983230072969 + 3 ^ 40 * 1500655 * 2
def baseEnd_1500655 : Nat := 770557311572931414111119

theorem tailTrace_1500655 : CollatzResearch.WordTrace tailWord_1500655 prefixEnd_1500655 770557311572931414111119 := by
  unfold tailWord_1500655
  simp only [CollatzResearch.WordTrace]
  refine ⟨54733384378390701314703419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36488922918927134209802279 54733384378390701314703419)
  ·
    refine ⟨82100076567586051972055129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54733384378390701314703419 82100076567586051972055129)
    ·
      refine ⟨61575057425689538979041347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82100076567586051972055129 61575057425689538979041347)
      ·
        refine ⟨92362586138534308468562021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61575057425689538979041347 92362586138534308468562021)
        ·
          refine ⟨17317984900975182837855379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92362586138534308468562021 17317984900975182837855379)
          ·
            refine ⟨25976977351462774256783069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17317984900975182837855379 25976977351462774256783069)
            ·
              refine ⟨9741366506798540346293651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25976977351462774256783069 9741366506798540346293651)
              ·
                refine ⟨14612049760197810519440477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9741366506798540346293651 14612049760197810519440477)
                ·
                  refine ⟨5479518660074178944790179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14612049760197810519440477 5479518660074178944790179)
                  ·
                    refine ⟨8219277990111268417185269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5479518660074178944790179 8219277990111268417185269)
                    ·
                      refine ⟨770557311572931414111119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8219277990111268417185269 770557311572931414111119)
                      ·
                        rfl

theorem cell23_1500655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_1500655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500655 prefixEnd_1500655 := by exact prefixLift 1500655
  have htrace : WordTrace (prefixWord ++ tailWord_1500655) baseStart_1500655 baseEnd_1500655 := by
    simpa [prefixWord, tailWord_1500655, baseEnd_1500655] using wordTrace_append hprefix tailTrace_1500655
  have hstable : (prefixWord ++ tailWord_1500655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500655).length < 2 ^ (prefixWord ++ tailWord_1500655).sum := by decide
  have hdescent : baseEnd_1500655 < baseStart_1500655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500669 : List Nat := [1, 4, 1, 1, 1, 5, 2, 2, 1, 1, 4]
def baseStart_1500669 : Nat := 118140960795 + 1500669 * 2 ^ 59
def prefixEnd_1500669 : Nat := 4983230072969 + 3 ^ 40 * 1500669 * 2
def baseEnd_1500669 : Nat := 770564500302094359336055

theorem tailTrace_1500669 : CollatzResearch.WordTrace tailWord_1500669 prefixEnd_1500669 770564500302094359336055 := by
  unfold tailWord_1500669
  simp only [CollatzResearch.WordTrace]
  refine ⟨54733895000339981705713061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36489263333559987803808707 54733895000339981705713061)
  ·
    refine ⟨10262605312563746569821199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54733895000339981705713061 10262605312563746569821199)
    ·
      refine ⟨15393907968845619854731799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10262605312563746569821199 15393907968845619854731799)
      ·
        refine ⟨23090861953268429782097699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15393907968845619854731799 23090861953268429782097699)
        ·
          refine ⟨34636292929902644673146549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23090861953268429782097699 34636292929902644673146549)
          ·
            refine ⟨3247152462178372938107489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34636292929902644673146549 3247152462178372938107489)
            ·
              refine ⟨2435364346633779703580617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3247152462178372938107489 2435364346633779703580617)
              ·
                refine ⟨1826523259975334777685463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2435364346633779703580617 1826523259975334777685463)
                ·
                  refine ⟨2739784889963002166528195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1826523259975334777685463 2739784889963002166528195)
                  ·
                    refine ⟨4109677334944503249792293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2739784889963002166528195 4109677334944503249792293)
                    ·
                      refine ⟨770564500302094359336055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4109677334944503249792293 770564500302094359336055)
                      ·
                        rfl

theorem cell23_1500669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_1500669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500669 prefixEnd_1500669 := by exact prefixLift 1500669
  have htrace : WordTrace (prefixWord ++ tailWord_1500669) baseStart_1500669 baseEnd_1500669 := by
    simpa [prefixWord, tailWord_1500669, baseEnd_1500669] using wordTrace_append hprefix tailTrace_1500669
  have hstable : (prefixWord ++ tailWord_1500669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500669).length < 2 ^ (prefixWord ++ tailWord_1500669).sum := by decide
  have hdescent : baseEnd_1500669 < baseStart_1500669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500772 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_1500772 : Nat := 118140960795 + 1500772 * 2 ^ 59
def prefixEnd_1500772 : Nat := 4983230072969 + 3 ^ 40 * 1500772 * 2
def baseEnd_1500772 : Nat := 770617388809507456348081

theorem tailTrace_1500772 : CollatzResearch.WordTrace tailWord_1500772 prefixEnd_1500772 770617388809507456348081 := by
  unfold tailWord_1500772
  simp only [CollatzResearch.WordTrace]
  refine ⟨27368825859483415148356285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36491767812644553531141713 27368825859483415148356285)
  ·
    refine ⟨10263309697306280680633607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27368825859483415148356285 10263309697306280680633607)
    ·
      refine ⟨15394964545959421020950411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10263309697306280680633607 15394964545959421020950411)
      ·
        refine ⟨23092446818939131531425617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15394964545959421020950411 23092446818939131531425617)
        ·
          refine ⟨17319335114204348648569213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23092446818939131531425617 17319335114204348648569213)
          ·
            refine ⟨6494750667826630743213455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17319335114204348648569213 6494750667826630743213455)
            ·
              refine ⟨9742126001739946114820183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494750667826630743213455 9742126001739946114820183)
              ·
                refine ⟨14613189002609919172230275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9742126001739946114820183 14613189002609919172230275)
                ·
                  refine ⟨21919783503914878758345413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14613189002609919172230275 21919783503914878758345413)
                  ·
                    refine ⟨4109959406984039767189765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21919783503914878758345413 4109959406984039767189765)
                    ·
                      refine ⟨770617388809507456348081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4109959406984039767189765 770617388809507456348081)
                      ·
                        rfl

theorem cell23_1500772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_1500772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500772 prefixEnd_1500772 := by exact prefixLift 1500772
  have htrace : WordTrace (prefixWord ++ tailWord_1500772) baseStart_1500772 baseEnd_1500772 := by
    simpa [prefixWord, tailWord_1500772, baseEnd_1500772] using wordTrace_append hprefix tailTrace_1500772
  have hstable : (prefixWord ++ tailWord_1500772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500772).length < 2 ^ (prefixWord ++ tailWord_1500772).sum := by decide
  have hdescent : baseEnd_1500772 < baseStart_1500772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500776 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 1, 4, 2]
def baseStart_1500776 : Nat := 118140960795 + 1500776 * 2 ^ 59
def prefixEnd_1500776 : Nat := 4983230072969 + 3 ^ 40 * 1500776 * 2
def baseEnd_1500776 : Nat := 770619442732125440698063

theorem tailTrace_1500776 : CollatzResearch.WordTrace tailWord_1500776 prefixEnd_1500776 770619442732125440698063 := by
  unfold tailWord_1500776
  simp only [CollatzResearch.WordTrace]
  refine ⟨27368898805476169489929091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36491865073968225986572121 27368898805476169489929091)
  ·
    refine ⟨41053348208214254234893637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27368898805476169489929091 41053348208214254234893637)
    ·
      refine ⟨7697502789040172669042557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41053348208214254234893637 7697502789040172669042557)
      ·
        refine ⟨2886563545890064750890959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7697502789040172669042557 2886563545890064750890959)
        ·
          refine ⟨4329845318835097126336439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2886563545890064750890959 4329845318835097126336439)
          ·
            refine ⟨6494767978252645689504659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329845318835097126336439 6494767978252645689504659)
            ·
              refine ⟨9742151967378968534256989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494767978252645689504659 9742151967378968534256989)
              ·
                refine ⟨3653306987767113200346371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9742151967378968534256989 3653306987767113200346371)
                ·
                  refine ⟨5479960481650669800519557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3653306987767113200346371 5479960481650669800519557)
                  ·
                    refine ⟨1027492590309500587597417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5479960481650669800519557 1027492590309500587597417)
                    ·
                      refine ⟨770619442732125440698063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1027492590309500587597417 770619442732125440698063)
                      ·
                        rfl

theorem cell23_1500776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_1500776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500776 prefixEnd_1500776 := by exact prefixLift 1500776
  have htrace : WordTrace (prefixWord ++ tailWord_1500776) baseStart_1500776 baseEnd_1500776 := by
    simpa [prefixWord, tailWord_1500776, baseEnd_1500776] using wordTrace_append hprefix tailTrace_1500776
  have hstable : (prefixWord ++ tailWord_1500776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500776).length < 2 ^ (prefixWord ++ tailWord_1500776).sum := by decide
  have hdescent : baseEnd_1500776 < baseStart_1500776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500792 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 6, 3, 3]
def baseStart_1500792 : Nat := 118140960795 + 1500792 * 2 ^ 59
def prefixEnd_1500792 : Nat := 4983230072969 + 3 ^ 40 * 1500792 * 2
def baseEnd_1500792 : Nat := 770627658422597378097989

theorem tailTrace_1500792 : CollatzResearch.WordTrace tailWord_1500792 prefixEnd_1500792 770627658422597378097989 := by
  unfold tailWord_1500792
  simp only [CollatzResearch.WordTrace]
  refine ⟨27369190589447186856220315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36492254119262915808293753 27369190589447186856220315)
  ·
    refine ⟨41053785884170780284330473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27369190589447186856220315 41053785884170780284330473)
    ·
      refine ⟨30790339413128085213247855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41053785884170780284330473 30790339413128085213247855)
      ·
        refine ⟨46185509119692127819871783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30790339413128085213247855 46185509119692127819871783)
        ·
          refine ⟨69278263679538191729807675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46185509119692127819871783 69278263679538191729807675)
          ·
            refine ⟨103917395519307287594711513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69278263679538191729807675 103917395519307287594711513)
            ·
              refine ⟨77938046639480465696033635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103917395519307287594711513 77938046639480465696033635)
              ·
                refine ⟨116907069959220698544050453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77938046639480465696033635 116907069959220698544050453)
                ·
                  refine ⟨5480018904338470244252365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116907069959220698544050453 5480018904338470244252365)
                  ·
                    refine ⟨2055007089126926341594637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5480018904338470244252365 2055007089126926341594637)
                    ·
                      refine ⟨770627658422597378097989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2055007089126926341594637 770627658422597378097989)
                      ·
                        rfl

theorem cell23_1500792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_1500792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500792 prefixEnd_1500792 := by exact prefixLift 1500792
  have htrace : WordTrace (prefixWord ++ tailWord_1500792) baseStart_1500792 baseEnd_1500792 := by
    simpa [prefixWord, tailWord_1500792, baseEnd_1500792] using wordTrace_append hprefix tailTrace_1500792
  have hstable : (prefixWord ++ tailWord_1500792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500792).length < 2 ^ (prefixWord ++ tailWord_1500792).sum := by decide
  have hdescent : baseEnd_1500792 < baseStart_1500792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500810 : List Nat := [3, 1, 2, 3, 2, 3, 1, 2, 2, 2, 2]
def baseStart_1500810 : Nat := 118140960795 + 1500810 * 2 ^ 59
def prefixEnd_1500810 : Nat := 4983230072969 + 3 ^ 40 * 1500810 * 2
def baseEnd_1500810 : Nat := 770636901074378307672907

theorem tailTrace_1500810 : CollatzResearch.WordTrace tailWord_1500810 prefixEnd_1500810 770636901074378307672907 := by
  unfold tailWord_1500810
  simp only [CollatzResearch.WordTrace]
  refine ⟨13684759423207290696648971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36492691795219441857730589 13684759423207290696648971)
  ·
    refine ⟨20527139134810936044973457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13684759423207290696648971 20527139134810936044973457)
    ·
      refine ⟨15395354351108202033730093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20527139134810936044973457 15395354351108202033730093)
      ·
        refine ⟨5773257881665575762648785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15395354351108202033730093 5773257881665575762648785)
        ·
          refine ⟨4329943411249181821986589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5773257881665575762648785 4329943411249181821986589)
          ·
            refine ⟨1623728779218443183244971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4329943411249181821986589 1623728779218443183244971)
            ·
              refine ⟨2435593168827664774867457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623728779218443183244971 2435593168827664774867457)
              ·
                refine ⟨1826694876620748581150593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2435593168827664774867457 1826694876620748581150593)
                ·
                  refine ⟨1370021157465561435862945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1826694876620748581150593 1370021157465561435862945)
                  ·
                    refine ⟨1027515868099171076897209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1370021157465561435862945 1027515868099171076897209)
                    ·
                      refine ⟨770636901074378307672907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1027515868099171076897209 770636901074378307672907)
                      ·
                        rfl

theorem cell23_1500810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_1500810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500810 prefixEnd_1500810 := by exact prefixLift 1500810
  have htrace : WordTrace (prefixWord ++ tailWord_1500810) baseStart_1500810 baseEnd_1500810 := by
    simpa [prefixWord, tailWord_1500810, baseEnd_1500810] using wordTrace_append hprefix tailTrace_1500810
  have hstable : (prefixWord ++ tailWord_1500810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500810).length < 2 ^ (prefixWord ++ tailWord_1500810).sum := by decide
  have hdescent : baseEnd_1500810 < baseStart_1500810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500812 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 4, 5]
def baseStart_1500812 : Nat := 118140960795 + 1500812 * 2 ^ 59
def prefixEnd_1500812 : Nat := 4983230072969 + 3 ^ 40 * 1500812 * 2
def baseEnd_1500812 : Nat := 256879309345229099949299

theorem tailTrace_1500812 : CollatzResearch.WordTrace tailWord_1500812 prefixEnd_1500812 256879309345229099949299 := by
  unfold tailWord_1500812
  simp only [CollatzResearch.WordTrace]
  refine ⟨27369555319410958564084345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36492740425881278085445793 27369555319410958564084345)
  ·
    refine ⟨20527166489558218923063259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27369555319410958564084345 20527166489558218923063259)
    ·
      refine ⟨30790749734337328384594889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20527166489558218923063259 30790749734337328384594889)
      ·
        refine ⟨23093062300752996288446167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30790749734337328384594889 23093062300752996288446167)
        ·
          refine ⟨34639593451129494432669251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23093062300752996288446167 34639593451129494432669251)
          ·
            refine ⟨51959390176694241649003877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34639593451129494432669251 51959390176694241649003877)
            ·
              refine ⟨9742385658130170309188227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51959390176694241649003877 9742385658130170309188227)
              ·
                refine ⟨14613578487195255463782341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9742385658130170309188227 14613578487195255463782341)
                ·
                  refine ⟨2740045966349110399459189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14613578487195255463782341 2740045966349110399459189)
                  ·
                    refine ⟨256879309345229099949299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2740045966349110399459189 256879309345229099949299)
                    ·
                      rfl

theorem cell23_1500812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_1500812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500812 prefixEnd_1500812 := by exact prefixLift 1500812
  have htrace : WordTrace (prefixWord ++ tailWord_1500812) baseStart_1500812 baseEnd_1500812 := by
    simpa [prefixWord, tailWord_1500812, baseEnd_1500812] using wordTrace_append hprefix tailTrace_1500812
  have hstable : (prefixWord ++ tailWord_1500812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500812).length < 2 ^ (prefixWord ++ tailWord_1500812).sum := by decide
  have hdescent : baseEnd_1500812 < baseStart_1500812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500869 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 2, 2, 3]
def baseStart_1500869 : Nat := 118140960795 + 1500869 * 2 ^ 59
def prefixEnd_1500869 : Nat := 4983230072969 + 3 ^ 40 * 1500869 * 2
def baseEnd_1500869 : Nat := 770667196432993576835135

theorem tailTrace_1500869 : CollatzResearch.WordTrace tailWord_1500869 prefixEnd_1500869 770667196432993576835135 := by
  unfold tailWord_1500869
  simp only [CollatzResearch.WordTrace]
  refine ⟨54741189599615415862993661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36494126399743610575329107 54741189599615415862993661)
  ·
    refine ⟨20527946099855780948622623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54741189599615415862993661 20527946099855780948622623)
    ·
      refine ⟨30791919149783671422933935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20527946099855780948622623 30791919149783671422933935)
      ·
        refine ⟨46187878724675507134400903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30791919149783671422933935 46187878724675507134400903)
        ·
          refine ⟨69281818087013260701601355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46187878724675507134400903 69281818087013260701601355)
          ·
            refine ⟨103922727130519891052402033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69281818087013260701601355 103922727130519891052402033)
            ·
              refine ⟨77942045347889918289301525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103922727130519891052402033 77942045347889918289301525)
              ·
                refine ⟨3653533375682339919811009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77942045347889918289301525 3653533375682339919811009)
                ·
                  refine ⟨2740150031761754939858257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3653533375682339919811009 2740150031761754939858257)
                  ·
                    refine ⟨2055112523821316204893693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2740150031761754939858257 2055112523821316204893693)
                    ·
                      refine ⟨770667196432993576835135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2055112523821316204893693 770667196432993576835135)
                      ·
                        rfl

theorem cell23_1500869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_1500869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500869 prefixEnd_1500869 := by exact prefixLift 1500869
  have htrace : WordTrace (prefixWord ++ tailWord_1500869) baseStart_1500869 baseEnd_1500869 := by
    simpa [prefixWord, tailWord_1500869, baseEnd_1500869] using wordTrace_append hprefix tailTrace_1500869
  have hstable : (prefixWord ++ tailWord_1500869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500869).length < 2 ^ (prefixWord ++ tailWord_1500869).sum := by decide
  have hdescent : baseEnd_1500869 < baseStart_1500869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500872 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 8]
def baseStart_1500872 : Nat := 118140960795 + 1500872 * 2 ^ 59
def prefixEnd_1500872 : Nat := 4983230072969 + 3 ^ 40 * 1500872 * 2
def baseEnd_1500872 : Nat := 85629859652773007233069

theorem tailTrace_1500872 : CollatzResearch.WordTrace tailWord_1500872 prefixEnd_1500872 85629859652773007233069 := by
  unfold tailWord_1500872
  simp only [CollatzResearch.WordTrace]
  refine ⟨27370649509302273687676435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36494199345736364916901913 27370649509302273687676435)
  ·
    refine ⟨41055974263953410531514653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27370649509302273687676435 41055974263953410531514653)
    ·
      refine ⟨15395990348982528949317995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41055974263953410531514653 15395990348982528949317995)
      ·
        refine ⟨23093985523473793423976993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15395990348982528949317995 23093985523473793423976993)
        ·
          refine ⟨17320489142605345067982745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23093985523473793423976993 17320489142605345067982745)
          ·
            refine ⟨12990366856954008800987059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17320489142605345067982745 12990366856954008800987059)
            ·
              refine ⟨19485550285431013201480589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12990366856954008800987059 19485550285431013201480589)
              ·
                refine ⟨7307081357036629950555221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19485550285431013201480589 7307081357036629950555221)
                ·
                  refine ⟨85629859652773007233069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7307081357036629950555221 85629859652773007233069)
                  ·
                    rfl

theorem cell23_1500872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 8].length) (baseStart_1500872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500872 prefixEnd_1500872 := by exact prefixLift 1500872
  have htrace : WordTrace (prefixWord ++ tailWord_1500872) baseStart_1500872 baseEnd_1500872 := by
    simpa [prefixWord, tailWord_1500872, baseEnd_1500872] using wordTrace_append hprefix tailTrace_1500872
  have hstable : (prefixWord ++ tailWord_1500872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500872).length < 2 ^ (prefixWord ++ tailWord_1500872).sum := by decide
  have hdescent : baseEnd_1500872 < baseStart_1500872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500889 : List Nat := [1, 2, 1, 2, 3, 4, 1, 3, 6]
def baseStart_1500889 : Nat := 118140960795 + 1500889 * 2 ^ 59
def prefixEnd_1500889 : Nat := 4983230072969 + 3 ^ 40 * 1500889 * 2
def baseEnd_1500889 : Nat := 85630829560675944287227

theorem tailTrace_1500889 : CollatzResearch.WordTrace tailWord_1500889 prefixEnd_1500889 85630829560675944287227 := by
  unfold tailWord_1500889
  simp only [CollatzResearch.WordTrace]
  refine ⟨54741919059542959278721721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36494612706361972852481147 54741919059542959278721721)
  ·
    refine ⟨41056439294657219459041291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54741919059542959278721721 41056439294657219459041291)
    ·
      refine ⟨61584658941985829188561937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41056439294657219459041291 61584658941985829188561937)
      ·
        refine ⟨46188494206489371891421453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61584658941985829188561937 46188494206489371891421453)
        ·
          refine ⟨17320685327433514459283045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46188494206489371891421453 17320685327433514459283045)
          ·
            refine ⟨3247628498893783961115571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17320685327433514459283045 3247628498893783961115571)
            ·
              refine ⟨4871442748340675941673357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3247628498893783961115571 4871442748340675941673357)
              ·
                refine ⟨1826791030627753478127509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4871442748340675941673357 1826791030627753478127509)
                ·
                  refine ⟨85630829560675944287227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1826791030627753478127509 85630829560675944287227)
                  ·
                    rfl

theorem cell23_1500889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 6].length) (baseStart_1500889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500889 prefixEnd_1500889 := by exact prefixLift 1500889
  have htrace : WordTrace (prefixWord ++ tailWord_1500889) baseStart_1500889 baseEnd_1500889 := by
    simpa [prefixWord, tailWord_1500889, baseEnd_1500889] using wordTrace_append hprefix tailTrace_1500889
  have hstable : (prefixWord ++ tailWord_1500889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500889).length < 2 ^ (prefixWord ++ tailWord_1500889).sum := by decide
  have hdescent : baseEnd_1500889 < baseStart_1500889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500912 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 5]
def baseStart_1500912 : Nat := 118140960795 + 1500912 * 2 ^ 59
def prefixEnd_1500912 : Nat := 4983230072969 + 3 ^ 40 * 1500912 * 2
def baseEnd_1500912 : Nat := 770689276101136908597437

theorem tailTrace_1500912 : CollatzResearch.WordTrace tailWord_1500912 prefixEnd_1500912 770689276101136908597437 := by
  unfold tailWord_1500912
  simp only [CollatzResearch.WordTrace]
  refine ⟨27371378969229817103404495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36495171958973089471205993 27371378969229817103404495)
  ·
    refine ⟨41057068453844725655106743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27371378969229817103404495 41057068453844725655106743)
    ·
      refine ⟨61585602680767088482660115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41057068453844725655106743 61585602680767088482660115)
      ·
        refine ⟨92378404021150632723990173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61585602680767088482660115 92378404021150632723990173)
        ·
          refine ⟨34641901507931487271496315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92378404021150632723990173 34641901507931487271496315)
          ·
            refine ⟨51962852261897230907244473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34641901507931487271496315 51962852261897230907244473)
            ·
              refine ⟨38972139196422923180433355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51962852261897230907244473 38972139196422923180433355)
              ·
                refine ⟨58458208794634384770650033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38972139196422923180433355 58458208794634384770650033)
                ·
                  refine ⟨43843656595975788577987525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58458208794634384770650033 43843656595975788577987525)
                  ·
                    refine ⟨8220685611745460358372661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43843656595975788577987525 8220685611745460358372661)
                    ·
                      refine ⟨770689276101136908597437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8220685611745460358372661 770689276101136908597437)
                      ·
                        rfl

theorem cell23_1500912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_1500912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500912 prefixEnd_1500912 := by exact prefixLift 1500912
  have htrace : WordTrace (prefixWord ++ tailWord_1500912) baseStart_1500912 baseEnd_1500912 := by
    simpa [prefixWord, tailWord_1500912, baseEnd_1500912] using wordTrace_append hprefix tailTrace_1500912
  have hstable : (prefixWord ++ tailWord_1500912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500912).length < 2 ^ (prefixWord ++ tailWord_1500912).sum := by decide
  have hdescent : baseEnd_1500912 < baseStart_1500912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500919 : List Nat := [1, 1, 3, 1, 1, 1, 4, 5, 1, 5]
def baseStart_1500919 : Nat := 118140960795 + 1500919 * 2 ^ 59
def prefixEnd_1500919 : Nat := 4983230072969 + 3 ^ 40 * 1500919 * 2
def baseEnd_1500919 : Nat := 256897623488572793736635

theorem tailTrace_1500919 : CollatzResearch.WordTrace tailWord_1500919 prefixEnd_1500919 256897623488572793736635 := by
  unfold tailWord_1500919
  simp only [CollatzResearch.WordTrace]
  refine ⟨54743013249434274402313811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36495342166289516268209207 54743013249434274402313811)
  ·
    refine ⟨82114519874151411603470717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54743013249434274402313811 82114519874151411603470717)
    ·
      refine ⟨30792944952806779351301519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82114519874151411603470717 30792944952806779351301519)
      ·
        refine ⟨46189417429210169026952279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30792944952806779351301519 46189417429210169026952279)
        ·
          refine ⟨69284126143815253540428419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46189417429210169026952279 69284126143815253540428419)
          ·
            refine ⟨103926189215722880310642629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69284126143815253540428419 103926189215722880310642629)
            ·
              refine ⟨19486160477948040058245493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103926189215722880310642629 19486160477948040058245493)
              ·
                refine ⟨1826827544807628755460515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19486160477948040058245493 1826827544807628755460515)
                ·
                  refine ⟨2740241317211443133190773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1826827544807628755460515 2740241317211443133190773)
                  ·
                    refine ⟨256897623488572793736635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2740241317211443133190773 256897623488572793736635)
                    ·
                      rfl

theorem cell23_1500919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_1500919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500919 prefixEnd_1500919 := by exact prefixLift 1500919
  have htrace : WordTrace (prefixWord ++ tailWord_1500919) baseStart_1500919 baseEnd_1500919 := by
    simpa [prefixWord, tailWord_1500919, baseEnd_1500919] using wordTrace_append hprefix tailTrace_1500919
  have hstable : (prefixWord ++ tailWord_1500919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500919).length < 2 ^ (prefixWord ++ tailWord_1500919).sum := by decide
  have hdescent : baseEnd_1500919 < baseStart_1500919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500939 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 4]
def baseStart_1500939 : Nat := 118140960795 + 1500939 * 2 ^ 59
def prefixEnd_1500939 : Nat := 4983230072969 + 3 ^ 40 * 1500939 * 2
def baseEnd_1500939 : Nat := 770703140078808302959813

theorem tailTrace_1500939 : CollatzResearch.WordTrace tailWord_1500939 prefixEnd_1500939 770703140078808302959813 := by
  unfold tailWord_1500939
  simp only [CollatzResearch.WordTrace]
  refine ⟨54743742709361817818041871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36495828472907878545361247 54743742709361817818041871)
  ·
    refine ⟨82115614064042726727062807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54743742709361817818041871 82115614064042726727062807)
    ·
      refine ⟨123173421096064090090594211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82115614064042726727062807 123173421096064090090594211)
      ·
        refine ⟨184760131644096135135891317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123173421096064090090594211 184760131644096135135891317)
        ·
          refine ⟨17321262341634012668989811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184760131644096135135891317 17321262341634012668989811)
          ·
            refine ⟨25981893512451019003484717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17321262341634012668989811 25981893512451019003484717)
            ·
              refine ⟨9743210067169132126306769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25981893512451019003484717 9743210067169132126306769)
              ·
                refine ⟨7307407550376849094730077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9743210067169132126306769 7307407550376849094730077)
                ·
                  refine ⟨2740277831391318410523779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7307407550376849094730077 2740277831391318410523779)
                  ·
                    refine ⟨4110416747086977615785669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2740277831391318410523779 4110416747086977615785669)
                    ·
                      refine ⟨770703140078808302959813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4110416747086977615785669 770703140078808302959813)
                      ·
                        rfl

theorem cell23_1500939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 4].length) (baseStart_1500939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500939 prefixEnd_1500939 := by exact prefixLift 1500939
  have htrace : WordTrace (prefixWord ++ tailWord_1500939) baseStart_1500939 baseEnd_1500939 := by
    simpa [prefixWord, tailWord_1500939, baseEnd_1500939] using wordTrace_append hprefix tailTrace_1500939
  have hstable : (prefixWord ++ tailWord_1500939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500939).length < 2 ^ (prefixWord ++ tailWord_1500939).sum := by decide
  have hdescent : baseEnd_1500939 < baseStart_1500939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500949 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 1, 6]
def baseStart_1500949 : Nat := 118140960795 + 1500949 * 2 ^ 59
def prefixEnd_1500949 : Nat := 4983230072969 + 3 ^ 40 * 1500949 * 2
def baseEnd_1500949 : Nat := 256902758295117754611589

theorem tailTrace_1500949 : CollatzResearch.WordTrace tailWord_1500949 prefixEnd_1500949 256902758295117754611589 := by
  unfold tailWord_1500949
  simp only [CollatzResearch.WordTrace]
  refine ⟨54744107439325589525905901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36496071626217059683937267 54744107439325589525905901)
  ·
    refine ⟨20529040289747096072214713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54744107439325589525905901 20529040289747096072214713)
    ·
      refine ⟨15396780217310322054161035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20529040289747096072214713 15396780217310322054161035)
      ·
        refine ⟨23095170325965483081241553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15396780217310322054161035 23095170325965483081241553)
        ·
          refine ⟨17321377744474112310931165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23095170325965483081241553 17321377744474112310931165)
          ·
            refine ⟨6495516654177792116599187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17321377744474112310931165 6495516654177792116599187)
            ·
              refine ⟨9743274981266688174898781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6495516654177792116599187 9743274981266688174898781)
              ·
                refine ⟨3653728117975008065587043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9743274981266688174898781 3653728117975008065587043)
                ·
                  refine ⟨5480592176962512098380565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3653728117975008065587043 5480592176962512098380565)
                  ·
                    refine ⟨256902758295117754611589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5480592176962512098380565 256902758295117754611589)
                    ·
                      rfl

theorem cell23_1500949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_1500949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500949 prefixEnd_1500949 := by exact prefixLift 1500949
  have htrace : WordTrace (prefixWord ++ tailWord_1500949) baseStart_1500949 baseEnd_1500949 := by
    simpa [prefixWord, tailWord_1500949, baseEnd_1500949] using wordTrace_append hprefix tailTrace_1500949
  have hstable : (prefixWord ++ tailWord_1500949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500949).length < 2 ^ (prefixWord ++ tailWord_1500949).sum := by decide
  have hdescent : baseEnd_1500949 < baseStart_1500949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500956 : List Nat := [2, 2, 3, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_1500956 : Nat := 118140960795 + 1500956 * 2 ^ 59
def prefixEnd_1500956 : Nat := 4983230072969 + 3 ^ 40 * 1500956 * 2
def baseEnd_1500956 : Nat := 770711869249934736447235

theorem tailTrace_1500956 : CollatzResearch.WordTrace tailWord_1500956 prefixEnd_1500956 770711869249934736447235 := by
  unfold tailWord_1500956
  simp only [CollatzResearch.WordTrace]
  refine ⟨27372181375150114860705361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36496241833533486480940481 27372181375150114860705361)
  ·
    refine ⟨20529136031362586145529021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27372181375150114860705361 20529136031362586145529021)
    ·
      refine ⟨7698426011760969804573383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20529136031362586145529021 7698426011760969804573383)
      ·
        refine ⟨11547639017641454706860075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7698426011760969804573383 11547639017641454706860075)
        ·
          refine ⟨17321458526462182060290113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11547639017641454706860075 17321458526462182060290113)
          ·
            refine ⟨12991093894846636545217585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17321458526462182060290113 12991093894846636545217585)
            ·
              refine ⟨9743320421134977408913189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12991093894846636545217585 9743320421134977408913189)
              ·
                refine ⟨1826872578962808264171223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9743320421134977408913189 1826872578962808264171223)
                ·
                  refine ⟨2740308868444212396256835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1826872578962808264171223 2740308868444212396256835)
                  ·
                    refine ⟨4110463302666318594385253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2740308868444212396256835 4110463302666318594385253)
                    ·
                      refine ⟨770711869249934736447235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4110463302666318594385253 770711869249934736447235)
                      ·
                        rfl

theorem cell23_1500956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_1500956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500956 prefixEnd_1500956 := by exact prefixLift 1500956
  have htrace : WordTrace (prefixWord ++ tailWord_1500956) baseStart_1500956 baseEnd_1500956 := by
    simpa [prefixWord, tailWord_1500956, baseEnd_1500956] using wordTrace_append hprefix tailTrace_1500956
  have hstable : (prefixWord ++ tailWord_1500956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500956).length < 2 ^ (prefixWord ++ tailWord_1500956).sum := by decide
  have hdescent : baseEnd_1500956 < baseStart_1500956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500979 : List Nat := [1, 1, 1, 2, 7, 1, 10]
def baseStart_1500979 : Nat := 118140960795 + 1500979 * 2 ^ 59
def prefixEnd_1500979 : Nat := 4983230072969 + 3 ^ 40 * 1500979 * 2
def baseEnd_1500979 : Nat := 9515107151913433906909

theorem tailTrace_1500979 : CollatzResearch.WordTrace tailWord_1500979 prefixEnd_1500979 9515107151913433906909 := by
  unfold tailWord_1500979
  simp only [CollatzResearch.WordTrace]
  refine ⟨54745201629216904649497991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36496801086144603099665327 54745201629216904649497991)
  ·
    refine ⟨82117802443825356974246987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54745201629216904649497991 82117802443825356974246987)
    ·
      refine ⟨123176703665738035461370481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82117802443825356974246987 123176703665738035461370481)
      ·
        refine ⟨92382527749303526596027861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123176703665738035461370481 92382527749303526596027861)
        ·
          refine ⟨2165215494124301404594403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 92382527749303526596027861 2165215494124301404594403)
          ·
            refine ⟨3247823241186452106891605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2165215494124301404594403 3247823241186452106891605)
            ·
              refine ⟨9515107151913433906909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3247823241186452106891605 9515107151913433906909)
              ·
                rfl

theorem cell23_1500979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 10].length) (baseStart_1500979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500979 prefixEnd_1500979 := by exact prefixLift 1500979
  have htrace : WordTrace (prefixWord ++ tailWord_1500979) baseStart_1500979 baseEnd_1500979 := by
    simpa [prefixWord, tailWord_1500979, baseEnd_1500979] using wordTrace_append hprefix tailTrace_1500979
  have hstable : (prefixWord ++ tailWord_1500979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500979).length < 2 ^ (prefixWord ++ tailWord_1500979).sum := by decide
  have hdescent : baseEnd_1500979 < baseStart_1500979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500990 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 3, 2, 2]
def baseStart_1500990 : Nat := 118140960795 + 1500990 * 2 ^ 59
def prefixEnd_1500990 : Nat := 4983230072969 + 3 ^ 40 * 1500990 * 2
def baseEnd_1500990 : Nat := 770729327592187603422079

theorem tailTrace_1500990 : CollatzResearch.WordTrace tailWord_1500990 prefixEnd_1500990 770729327592187603422079 := by
  unfold tailWord_1500990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6843200354022131691018553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36497068554784702352098949 6843200354022131691018553)
  ·
    refine ⟨5132400265516598768263915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6843200354022131691018553 5132400265516598768263915)
    ·
      refine ⟨7698600398274898152395873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5132400265516598768263915 7698600398274898152395873)
      ·
        refine ⟨5773950298706173614296905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7698600398274898152395873 5773950298706173614296905)
        ·
          refine ⟨4330462724029630210722679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5773950298706173614296905 4330462724029630210722679)
          ·
            refine ⟨6495694086044445316084019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4330462724029630210722679 6495694086044445316084019)
            ·
              refine ⟨9743541129066667974126029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6495694086044445316084019 9743541129066667974126029)
              ·
                refine ⟨3653827923400000490297261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9743541129066667974126029 3653827923400000490297261)
                ·
                  refine ⟨1370185471275000183861473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3653827923400000490297261 1370185471275000183861473)
                  ·
                    refine ⟨1027639103456250137896105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1370185471275000183861473 1027639103456250137896105)
                    ·
                      refine ⟨770729327592187603422079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1027639103456250137896105 770729327592187603422079)
                      ·
                        rfl

theorem cell23_1500990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_1500990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1500990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1500990 prefixEnd_1500990 := by exact prefixLift 1500990
  have htrace : WordTrace (prefixWord ++ tailWord_1500990) baseStart_1500990 baseEnd_1500990 := by
    simpa [prefixWord, tailWord_1500990, baseEnd_1500990] using wordTrace_append hprefix tailTrace_1500990
  have hstable : (prefixWord ++ tailWord_1500990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500990).length < 2 ^ (prefixWord ++ tailWord_1500990).sum := by decide
  have hdescent : baseEnd_1500990 < baseStart_1500990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501029 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 1, 5, 4]
def baseStart_1501029 : Nat := 118140960795 + 1501029 * 2 ^ 59
def prefixEnd_1501029 : Nat := 4983230072969 + 3 ^ 40 * 1501029 * 2
def baseEnd_1501029 : Nat := 770749353337712950834399

theorem tailTrace_1501029 : CollatzResearch.WordTrace tailWord_1501029 prefixEnd_1501029 770749353337712950834399 := by
  unfold tailWord_1501029
  simp only [CollatzResearch.WordTrace]
  refine ⟨54747025279035763188818141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36498016852690508792545427 54747025279035763188818141)
  ·
    refine ⟨20530134479638411195806803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54747025279035763188818141 20530134479638411195806803)
    ·
      refine ⟨30795201719457616793710205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20530134479638411195806803 30795201719457616793710205)
      ·
        refine ⟨11548200644796606297641327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30795201719457616793710205 11548200644796606297641327)
        ·
          refine ⟨17322300967194909446461991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11548200644796606297641327 17322300967194909446461991)
          ·
            refine ⟨25983451450792364169692987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17322300967194909446461991 25983451450792364169692987)
            ·
              refine ⟨38975177176188546254539481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25983451450792364169692987 38975177176188546254539481)
              ·
                refine ⟨29231382882141409690904611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38975177176188546254539481 29231382882141409690904611)
                ·
                  refine ⟨43847074323212114536356917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29231382882141409690904611 43847074323212114536356917)
                  ·
                    refine ⟨4110663217801135737783461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43847074323212114536356917 4110663217801135737783461)
                    ·
                      refine ⟨770749353337712950834399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4110663217801135737783461 770749353337712950834399)
                      ·
                        rfl

theorem cell23_1501029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_1501029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501029 prefixEnd_1501029 := by exact prefixLift 1501029
  have htrace : WordTrace (prefixWord ++ tailWord_1501029) baseStart_1501029 baseEnd_1501029 := by
    simpa [prefixWord, tailWord_1501029, baseEnd_1501029] using wordTrace_append hprefix tailTrace_1501029
  have hstable : (prefixWord ++ tailWord_1501029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501029).length < 2 ^ (prefixWord ++ tailWord_1501029).sum := by decide
  have hdescent : baseEnd_1501029 < baseStart_1501029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501049 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 1, 3, 5]
def baseStart_1501049 : Nat := 118140960795 + 1501049 * 2 ^ 59
def prefixEnd_1501049 : Nat := 4983230072969 + 3 ^ 40 * 1501049 * 2
def baseEnd_1501049 : Nat := 770759622950802872584307

theorem tailTrace_1501049 : CollatzResearch.WordTrace tailWord_1501049 prefixEnd_1501049 770759622950802872584307 := by
  unfold tailWord_1501049
  simp only [CollatzResearch.WordTrace]
  refine ⟨54747754738963306604546201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36498503159308871069697467 54747754738963306604546201)
  ·
    refine ⟨41060816054222479953409651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54747754738963306604546201 41060816054222479953409651)
    ·
      refine ⟨61591224081333719930114477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41060816054222479953409651 61591224081333719930114477)
      ·
        refine ⟨23096709030500144973792929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61591224081333719930114477 23096709030500144973792929)
        ·
          refine ⟨17322531772875108730344697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23096709030500144973792929 17322531772875108730344697)
          ·
            refine ⟨12991898829656331547758523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17322531772875108730344697 12991898829656331547758523)
            ·
              refine ⟨19487848244484497321637785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12991898829656331547758523 19487848244484497321637785)
              ·
                refine ⟨14615886183363372991228339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19487848244484497321637785 14615886183363372991228339)
                ·
                  refine ⟨21923829275045059486842509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14615886183363372991228339 21923829275045059486842509)
                  ·
                    refine ⟨8221435978141897307565941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21923829275045059486842509 8221435978141897307565941)
                    ·
                      refine ⟨770759622950802872584307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8221435978141897307565941 770759622950802872584307)
                      ·
                        rfl

theorem cell23_1501049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_1501049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501049 prefixEnd_1501049 := by exact prefixLift 1501049
  have htrace : WordTrace (prefixWord ++ tailWord_1501049) baseStart_1501049 baseEnd_1501049 := by
    simpa [prefixWord, tailWord_1501049, baseEnd_1501049] using wordTrace_append hprefix tailTrace_1501049
  have hstable : (prefixWord ++ tailWord_1501049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501049).length < 2 ^ (prefixWord ++ tailWord_1501049).sum := by decide
  have hdescent : baseEnd_1501049 < baseStart_1501049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501057 : List Nat := [1, 2, 4, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_1501057 : Nat := 118140960795 + 1501057 * 2 ^ 59
def prefixEnd_1501057 : Nat := 4983230072969 + 3 ^ 40 * 1501057 * 2
def baseEnd_1501057 : Nat := 770763730796038841284271

theorem tailTrace_1501057 : CollatzResearch.WordTrace tailWord_1501057 prefixEnd_1501057 770763730796038841284271 := by
  unfold tailWord_1501057
  simp only [CollatzResearch.WordTrace]
  refine ⟨54748046522934323970837425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36498697681956215980558283 54748046522934323970837425)
  ·
    refine ⟨41061034892200742978128069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54748046522934323970837425 41061034892200742978128069)
    ·
      refine ⟨7698944042287639308399013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41061034892200742978128069 7698944042287639308399013)
      ·
        refine ⟨1443552007928932370324815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7698944042287639308399013 1443552007928932370324815)
        ·
          refine ⟨2165328011893398555487223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443552007928932370324815 2165328011893398555487223)
          ·
            refine ⟨3247992017840097833230835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2165328011893398555487223 3247992017840097833230835)
            ·
              refine ⟨4871988026760146749846253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3247992017840097833230835 4871988026760146749846253)
              ·
                refine ⟨1826995510035055031192345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4871988026760146749846253 1826995510035055031192345)
                ·
                  refine ⟨1370246632526291273394259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1826995510035055031192345 1370246632526291273394259)
                  ·
                    refine ⟨2055369948789436910091389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1370246632526291273394259 2055369948789436910091389)
                    ·
                      refine ⟨770763730796038841284271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2055369948789436910091389 770763730796038841284271)
                      ·
                        rfl

theorem cell23_1501057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_1501057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501057 prefixEnd_1501057 := by exact prefixLift 1501057
  have htrace : WordTrace (prefixWord ++ tailWord_1501057) baseStart_1501057 baseEnd_1501057 := by
    simpa [prefixWord, tailWord_1501057, baseEnd_1501057] using wordTrace_append hprefix tailTrace_1501057
  have hstable : (prefixWord ++ tailWord_1501057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501057).length < 2 ^ (prefixWord ++ tailWord_1501057).sum := by decide
  have hdescent : baseEnd_1501057 < baseStart_1501057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501129 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 2, 8]
def baseStart_1501129 : Nat := 118140960795 + 1501129 * 2 ^ 59
def prefixEnd_1501129 : Nat := 4983230072969 + 3 ^ 40 * 1501129 * 2
def baseEnd_1501129 : Nat := 256933567134387519861313

theorem tailTrace_1501129 : CollatzResearch.WordTrace tailWord_1501129 prefixEnd_1501129 256933567134387519861313 := by
  unfold tailWord_1501129
  simp only [CollatzResearch.WordTrace]
  refine ⟨54750672578673480267458441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36500448385782320178305627 54750672578673480267458441)
  ·
    refine ⟨41063004434005110200593831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54750672578673480267458441 41063004434005110200593831)
    ·
      refine ⟨61594506651007665300890747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41063004434005110200593831 61594506651007665300890747)
      ·
        refine ⟨92391759976511497951336121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61594506651007665300890747 92391759976511497951336121)
        ·
          refine ⟨69293819982383623463502091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92391759976511497951336121 69293819982383623463502091)
          ·
            refine ⟨103940729973575435195253137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69293819982383623463502091 103940729973575435195253137)
            ·
              refine ⟨77955547480181576396439853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103940729973575435195253137 77955547480181576396439853)
              ·
                refine ⟨29233330305068091148664945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77955547480181576396439853 29233330305068091148664945)
                ·
                  refine ⟨21924997728801068361498709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29233330305068091148664945 21924997728801068361498709)
                  ·
                    refine ⟨256933567134387519861313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21924997728801068361498709 256933567134387519861313)
                    ·
                      rfl

theorem cell23_1501129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 8].length) (baseStart_1501129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501129 prefixEnd_1501129 := by exact prefixLift 1501129
  have htrace : WordTrace (prefixWord ++ tailWord_1501129) baseStart_1501129 baseEnd_1501129 := by
    simpa [prefixWord, tailWord_1501129, baseEnd_1501129] using wordTrace_append hprefix tailTrace_1501129
  have hstable : (prefixWord ++ tailWord_1501129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501129).length < 2 ^ (prefixWord ++ tailWord_1501129).sum := by decide
  have hdescent : baseEnd_1501129 < baseStart_1501129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501148 : List Nat := [2, 2, 6, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_1501148 : Nat := 118140960795 + 1501148 * 2 ^ 59
def prefixEnd_1501148 : Nat := 4983230072969 + 3 ^ 40 * 1501148 * 2
def baseEnd_1501148 : Nat := 770810457535597985246353

theorem tailTrace_1501148 : CollatzResearch.WordTrace tailWord_1501148 prefixEnd_1501148 770810457535597985246353 := by
  unfold tailWord_1501148
  simp only [CollatzResearch.WordTrace]
  refine ⟨27375682782802323256200049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36500910377069764341600065 27375682782802323256200049)
  ·
    refine ⟨20531762087101742442150037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27375682782802323256200049 20531762087101742442150037)
    ·
      refine ⟨962426347832894176975783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20531762087101742442150037 962426347832894176975783)
      ·
        refine ⟨1443639521749341265463675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 962426347832894176975783 1443639521749341265463675)
        ·
          refine ⟨2165459282624011898195513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443639521749341265463675 2165459282624011898195513)
          ·
            refine ⟨1624094461968008923646635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2165459282624011898195513 1624094461968008923646635)
            ·
              refine ⟨2436141692952013385469953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1624094461968008923646635 2436141692952013385469953)
              ·
                refine ⟨1827106269714010039102465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2436141692952013385469953 1827106269714010039102465)
                ·
                  refine ⟨1370329702285507529326849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1827106269714010039102465 1370329702285507529326849)
                  ·
                    refine ⟨1027747276714130646995137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1370329702285507529326849 1027747276714130646995137)
                    ·
                      refine ⟨770810457535597985246353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1027747276714130646995137 770810457535597985246353)
                      ·
                        rfl

theorem cell23_1501148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_1501148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501148 prefixEnd_1501148 := by exact prefixLift 1501148
  have htrace : WordTrace (prefixWord ++ tailWord_1501148) baseStart_1501148 baseEnd_1501148 := by
    simpa [prefixWord, tailWord_1501148, baseEnd_1501148] using wordTrace_append hprefix tailTrace_1501148
  have hstable : (prefixWord ++ tailWord_1501148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501148).length < 2 ^ (prefixWord ++ tailWord_1501148).sum := by decide
  have hdescent : baseEnd_1501148 < baseStart_1501148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501153 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 2, 4, 2]
def baseStart_1501153 : Nat := 118140960795 + 1501153 * 2 ^ 59
def prefixEnd_1501153 : Nat := 4983230072969 + 3 ^ 40 * 1501153 * 2
def baseEnd_1501153 : Nat := 770813024938870465683829

theorem tailTrace_1501153 : CollatzResearch.WordTrace tailWord_1501153 prefixEnd_1501153 770813024938870465683829 := by
  unfold tailWord_1501153
  simp only [CollatzResearch.WordTrace]
  refine ⟨54751547930586532366332113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36501031953724354910888075 54751547930586532366332113)
  ·
    refine ⟨41063660947939899274749085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54751547930586532366332113 41063660947939899274749085)
    ·
      refine ⟨15398872855477462228030907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41063660947939899274749085 15398872855477462228030907)
      ·
        refine ⟨23098309283216193342046361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15398872855477462228030907 23098309283216193342046361)
        ·
          refine ⟨17323731962412145006534771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23098309283216193342046361 17323731962412145006534771)
          ·
            refine ⟨25985597943618217509802157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17323731962412145006534771 25985597943618217509802157)
            ·
              refine ⟨9744599228856831566175809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25985597943618217509802157 9744599228856831566175809)
              ·
                refine ⟨7308449421642623674631857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9744599228856831566175809 7308449421642623674631857)
                ·
                  refine ⟨5481337066231967755973893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7308449421642623674631857 5481337066231967755973893)
                  ·
                    refine ⟨1027750699918493954245105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5481337066231967755973893 1027750699918493954245105)
                    ·
                      refine ⟨770813024938870465683829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1027750699918493954245105 770813024938870465683829)
                      ·
                        rfl

theorem cell23_1501153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_1501153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501153 prefixEnd_1501153 := by exact prefixLift 1501153
  have htrace : WordTrace (prefixWord ++ tailWord_1501153) baseStart_1501153 baseEnd_1501153 := by
    simpa [prefixWord, tailWord_1501153, baseEnd_1501153] using wordTrace_append hprefix tailTrace_1501153
  have hstable : (prefixWord ++ tailWord_1501153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501153).length < 2 ^ (prefixWord ++ tailWord_1501153).sum := by decide
  have hdescent : baseEnd_1501153 < baseStart_1501153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501176 : List Nat := [2, 1, 2, 1, 1, 3, 2, 5, 6]
def baseStart_1501176 : Nat := 118140960795 + 1501176 * 2 ^ 59
def prefixEnd_1501176 : Nat := 4983230072969 + 3 ^ 40 * 1501176 * 2
def baseEnd_1501176 : Nat := 85647203888213763966247

theorem tailTrace_1501176 : CollatzResearch.WordTrace tailWord_1501176 prefixEnd_1501176 85647203888213763966247 := by
  unfold tailWord_1501176
  simp only [CollatzResearch.WordTrace]
  refine ⟨27376193404751603647209691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36501591206335471529612921 27376193404751603647209691)
  ·
    refine ⟨41064290107127405470814537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27376193404751603647209691 41064290107127405470814537)
    ·
      refine ⟨30798217580345554103110903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41064290107127405470814537 30798217580345554103110903)
      ·
        refine ⟨46197326370518331154666355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30798217580345554103110903 46197326370518331154666355)
        ·
          refine ⟨69295989555777496731999533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46197326370518331154666355 69295989555777496731999533)
          ·
            refine ⟨25985996083416561274499825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69295989555777496731999533 25985996083416561274499825)
            ·
              refine ⟨19489497062562420955874869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25985996083416561274499825 19489497062562420955874869)
              ·
                refine ⟨1827140349615226964613269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19489497062562420955874869 1827140349615226964613269)
                ·
                  refine ⟨85647203888213763966247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1827140349615226964613269 85647203888213763966247)
                  ·
                    rfl

theorem cell23_1501176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 6].length) (baseStart_1501176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501176 prefixEnd_1501176 := by exact prefixLift 1501176
  have htrace : WordTrace (prefixWord ++ tailWord_1501176) baseStart_1501176 baseEnd_1501176 := by
    simpa [prefixWord, tailWord_1501176, baseEnd_1501176] using wordTrace_append hprefix tailTrace_1501176
  have hstable : (prefixWord ++ tailWord_1501176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501176).length < 2 ^ (prefixWord ++ tailWord_1501176).sum := by decide
  have hdescent : baseEnd_1501176 < baseStart_1501176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501203 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 5, 1, 3]
def baseStart_1501203 : Nat := 118140960795 + 1501203 * 2 ^ 59
def prefixEnd_1501203 : Nat := 4983230072969 + 3 ^ 40 * 1501203 * 2
def baseEnd_1501203 : Nat := 770838698971595270058599

theorem tailTrace_1501203 : CollatzResearch.WordTrace tailWord_1501203 prefixEnd_1501203 770838698971595270058599 := by
  unfold tailWord_1501203
  simp only [CollatzResearch.WordTrace]
  refine ⟨54753371580405390905652263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36502247720270260603768175 54753371580405390905652263)
  ·
    refine ⟨82130057370608086358478395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54753371580405390905652263 82130057370608086358478395)
    ·
      refine ⟨123195086055912129537717593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82130057370608086358478395 123195086055912129537717593)
      ·
        refine ⟨92396314541934097153288195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123195086055912129537717593 92396314541934097153288195)
        ·
          refine ⟨138594471812901145729932293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92396314541934097153288195 138594471812901145729932293)
          ·
            refine ⟨25986463464918964824362305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138594471812901145729932293 25986463464918964824362305)
            ·
              refine ⟨19489847598689223618271729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25986463464918964824362305 19489847598689223618271729)
              ·
                refine ⟨14617385699016917713703797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19489847598689223618271729 14617385699016917713703797)
                ·
                  refine ⟨1370379909282836035659731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14617385699016917713703797 1370379909282836035659731)
                  ·
                    refine ⟨2055569863924254053489597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1370379909282836035659731 2055569863924254053489597)
                    ·
                      refine ⟨770838698971595270058599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2055569863924254053489597 770838698971595270058599)
                      ·
                        rfl

theorem cell23_1501203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 1, 3].length) (baseStart_1501203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501203 prefixEnd_1501203 := by exact prefixLift 1501203
  have htrace : WordTrace (prefixWord ++ tailWord_1501203) baseStart_1501203 baseEnd_1501203 := by
    simpa [prefixWord, tailWord_1501203, baseEnd_1501203] using wordTrace_append hprefix tailTrace_1501203
  have hstable : (prefixWord ++ tailWord_1501203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501203).length < 2 ^ (prefixWord ++ tailWord_1501203).sum := by decide
  have hdescent : baseEnd_1501203 < baseStart_1501203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501256 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_1501256 : Nat := 118140960795 + 1501256 * 2 ^ 59
def prefixEnd_1501256 : Nat := 4983230072969 + 3 ^ 40 * 1501256 * 2
def baseEnd_1501256 : Nat := 770865913446283562695855

theorem tailTrace_1501256 : CollatzResearch.WordTrace tailWord_1501256 prefixEnd_1501256 770865913446283562695855 := by
  unfold tailWord_1501256
  simp only [CollatzResearch.WordTrace]
  refine ⟨27377652324606690478665811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36503536432808920638221081 27377652324606690478665811)
  ·
    refine ⟨41066478486910035717998717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27377652324606690478665811 41066478486910035717998717)
    ·
      refine ⟨15399929432591263394249519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41066478486910035717998717 15399929432591263394249519)
      ·
        refine ⟨23099894148886895091374279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15399929432591263394249519 23099894148886895091374279)
        ·
          refine ⟨34649841223330342637061419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23099894148886895091374279 34649841223330342637061419)
          ·
            refine ⟨51974761834995513955592129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34649841223330342637061419 51974761834995513955592129)
            ·
              refine ⟨38981071376246635466694097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51974761834995513955592129 38981071376246635466694097)
              ·
                refine ⟨29235803532184976600020573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38981071376246635466694097 29235803532184976600020573)
                ·
                  refine ⟨10963426324569366225007715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29235803532184976600020573 10963426324569366225007715)
                  ·
                    refine ⟨16445139486854049337511573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10963426324569366225007715 16445139486854049337511573)
                    ·
                      refine ⟨770865913446283562695855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16445139486854049337511573 770865913446283562695855)
                      ·
                        rfl

theorem cell23_1501256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_1501256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501256 prefixEnd_1501256 := by exact prefixLift 1501256
  have htrace : WordTrace (prefixWord ++ tailWord_1501256) baseStart_1501256 baseEnd_1501256 := by
    simpa [prefixWord, tailWord_1501256, baseEnd_1501256] using wordTrace_append hprefix tailTrace_1501256
  have hstable : (prefixWord ++ tailWord_1501256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501256).length < 2 ^ (prefixWord ++ tailWord_1501256).sum := by decide
  have hdescent : baseEnd_1501256 < baseStart_1501256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501266 : List Nat := [3, 2, 2, 1, 15]
def baseStart_1501266 : Nat := 118140960795 + 1501266 * 2 ^ 59
def prefixEnd_1501266 : Nat := 4983230072969 + 3 ^ 40 * 1501266 * 2
def baseEnd_1501266 : Nat := 1057436280182206479521

theorem tailTrace_1501266 : CollatzResearch.WordTrace tailWord_1501266 prefixEnd_1501266 1057436280182206479521 := by
  unfold tailWord_1501266
  simp only [CollatzResearch.WordTrace]
  refine ⟨13688917344794288166298913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36503779586118101776797101 13688917344794288166298913)
  ·
    refine ⟨10266688008595716124724185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13688917344794288166298913 10266688008595716124724185)
    ·
      refine ⟨7700016006446787093543139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10266688008595716124724185 7700016006446787093543139)
      ·
        refine ⟨11550024009670180640314709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7700016006446787093543139 11550024009670180640314709)
        ·
          refine ⟨1057436280182206479521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 11550024009670180640314709 1057436280182206479521)
          ·
            rfl

theorem cell23_1501266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 15].length) (baseStart_1501266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501266 prefixEnd_1501266 := by exact prefixLift 1501266
  have htrace : WordTrace (prefixWord ++ tailWord_1501266) baseStart_1501266 baseEnd_1501266 := by
    simpa [prefixWord, tailWord_1501266, baseEnd_1501266] using wordTrace_append hprefix tailTrace_1501266
  have hstable : (prefixWord ++ tailWord_1501266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501266).length < 2 ^ (prefixWord ++ tailWord_1501266).sum := by decide
  have hdescent : baseEnd_1501266 < baseStart_1501266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501344 : List Nat := [2, 1, 1, 4, 2, 3, 3, 1, 2, 1, 3]
def baseStart_1501344 : Nat := 118140960795 + 1501344 * 2 ^ 59
def prefixEnd_1501344 : Nat := 4983230072969 + 3 ^ 40 * 1501344 * 2
def baseEnd_1501344 : Nat := 770911099743879218395451

theorem tailTrace_1501344 : CollatzResearch.WordTrace tailWord_1501344 prefixEnd_1501344 770911099743879218395451 := by
  unfold tailWord_1501344
  simp only [CollatzResearch.WordTrace]
  refine ⟨27379257136447285993267543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36505676181929714657690057 27379257136447285993267543)
  ·
    refine ⟨41068885704670928989901315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27379257136447285993267543 41068885704670928989901315)
    ·
      refine ⟨61603328557006393484851973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41068885704670928989901315 61603328557006393484851973)
      ·
        refine ⟨11550624104438698778409745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61603328557006393484851973 11550624104438698778409745)
        ·
          refine ⟨8662968078329024083807309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11550624104438698778409745 8662968078329024083807309)
          ·
            refine ⟨3248613029373384031427741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8662968078329024083807309 3248613029373384031427741)
            ·
              refine ⟨1218229886015019011785403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3248613029373384031427741 1218229886015019011785403)
              ·
                refine ⟨1827344829022528517678105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1218229886015019011785403 1827344829022528517678105)
                ·
                  refine ⟨1370508621766896388258579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1827344829022528517678105 1370508621766896388258579)
                  ·
                    refine ⟨2055762932650344582387869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1370508621766896388258579 2055762932650344582387869)
                    ·
                      refine ⟨770911099743879218395451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2055762932650344582387869 770911099743879218395451)
                      ·
                        rfl

theorem cell23_1501344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_1501344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501344 prefixEnd_1501344 := by exact prefixLift 1501344
  have htrace : WordTrace (prefixWord ++ tailWord_1501344) baseStart_1501344 baseEnd_1501344 := by
    simpa [prefixWord, tailWord_1501344, baseEnd_1501344] using wordTrace_append hprefix tailTrace_1501344
  have hstable : (prefixWord ++ tailWord_1501344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501344).length < 2 ^ (prefixWord ++ tailWord_1501344).sum := by decide
  have hdescent : baseEnd_1501344 < baseStart_1501344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501367 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 4, 2, 2]
def baseStart_1501367 : Nat := 118140960795 + 1501367 * 2 ^ 59
def prefixEnd_1501367 : Nat := 4983230072969 + 3 ^ 40 * 1501367 * 2
def baseEnd_1501367 : Nat := 770922909798932628407845

theorem tailTrace_1501367 : CollatzResearch.WordTrace tailWord_1501367 prefixEnd_1501367 770922909798932628407845 := by
  unfold tailWord_1501367
  simp only [CollatzResearch.WordTrace]
  refine ⟨54759353151811246914622355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36506235434540831276414903 54759353151811246914622355)
  ·
    refine ⟨82139029727716870371933533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54759353151811246914622355 82139029727716870371933533)
    ·
      refine ⟨30802136147893826389475075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82139029727716870371933533 30802136147893826389475075)
      ·
        refine ⟨46203204221840739584212613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30802136147893826389475075 46203204221840739584212613)
        ·
          refine ⟨8663100791595138672039865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46203204221840739584212613 8663100791595138672039865)
          ·
            refine ⟨6497325593696354004029899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8663100791595138672039865 6497325593696354004029899)
            ·
              refine ⟨9745988390544531006044849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6497325593696354004029899 9745988390544531006044849)
              ·
                refine ⟨7309491292908398254533637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9745988390544531006044849 7309491292908398254533637)
                ·
                  refine ⟨1370529617420324672725057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7309491292908398254533637 1370529617420324672725057)
                  ·
                    refine ⟨1027897213065243504543793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1370529617420324672725057 1027897213065243504543793)
                    ·
                      refine ⟨770922909798932628407845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1027897213065243504543793 770922909798932628407845)
                      ·
                        rfl

theorem cell23_1501367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 2, 2].length) (baseStart_1501367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501367 prefixEnd_1501367 := by exact prefixLift 1501367
  have htrace : WordTrace (prefixWord ++ tailWord_1501367) baseStart_1501367 baseEnd_1501367 := by
    simpa [prefixWord, tailWord_1501367, baseEnd_1501367] using wordTrace_append hprefix tailTrace_1501367
  have hstable : (prefixWord ++ tailWord_1501367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501367).length < 2 ^ (prefixWord ++ tailWord_1501367).sum := by decide
  have hdescent : baseEnd_1501367 < baseStart_1501367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501390 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 7]
def baseStart_1501390 : Nat := 118140960795 + 1501390 * 2 ^ 59
def prefixEnd_1501390 : Nat := 4983230072969 + 3 ^ 40 * 1501390 * 2
def baseEnd_1501390 : Nat := 85659413317109559824471

theorem tailTrace_1501390 : CollatzResearch.WordTrace tailWord_1501390 prefixEnd_1501390 85659413317109559824471 := by
  unfold tailWord_1501390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6845024003840990230338703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36506794687151947895139749 6845024003840990230338703)
  ·
    refine ⟨10267536005761485345508055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6845024003840990230338703 10267536005761485345508055)
    ·
      refine ⟨15401304008642228018262083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10267536005761485345508055 15401304008642228018262083)
      ·
        refine ⟨23101956012963342027393125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15401304008642228018262083 23101956012963342027393125)
        ·
          refine ⟨4331616752430626630136211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23101956012963342027393125 4331616752430626630136211)
          ·
            refine ⟨6497425128645939945204317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4331616752430626630136211 6497425128645939945204317)
            ·
              refine ⟨2436534423242227479451619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6497425128645939945204317 2436534423242227479451619)
              ·
                refine ⟨3654801634863341219177429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2436534423242227479451619 3654801634863341219177429)
                ·
                  refine ⟨85659413317109559824471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3654801634863341219177429 85659413317109559824471)
                  ·
                    rfl

theorem cell23_1501390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_1501390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501390 prefixEnd_1501390 := by exact prefixLift 1501390
  have htrace : WordTrace (prefixWord ++ tailWord_1501390) baseStart_1501390 baseEnd_1501390 := by
    simpa [prefixWord, tailWord_1501390, baseEnd_1501390] using wordTrace_append hprefix tailTrace_1501390
  have hstable : (prefixWord ++ tailWord_1501390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501390).length < 2 ^ (prefixWord ++ tailWord_1501390).sum := by decide
  have hdescent : baseEnd_1501390 < baseStart_1501390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501420 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 2, 5]
def baseStart_1501420 : Nat := 118140960795 + 1501420 * 2 ^ 59
def prefixEnd_1501420 : Nat := 4983230072969 + 3 ^ 40 * 1501420 * 2
def baseEnd_1501420 : Nat := 256983374757873640348367

theorem tailTrace_1501420 : CollatzResearch.WordTrace tailWord_1501420 prefixEnd_1501420 256983374757873640348367 := by
  unfold tailWord_1501420
  simp only [CollatzResearch.WordTrace]
  refine ⟨27380643110309618483150857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36507524147079491310867809 27380643110309618483150857)
  ·
    refine ⟨20535482332732213862363143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27380643110309618483150857 20535482332732213862363143)
    ·
      refine ⟨30803223499098320793544715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20535482332732213862363143 30803223499098320793544715)
      ·
        refine ⟨46204835248647481190317073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30803223499098320793544715 46204835248647481190317073)
        ·
          refine ⟨34653626436485610892737805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46204835248647481190317073 34653626436485610892737805)
          ·
            refine ⟨12995109913682104084776677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34653626436485610892737805 12995109913682104084776677)
            ·
              refine ⟨2436583108815394515895627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12995109913682104084776677 2436583108815394515895627)
              ·
                refine ⟨3654874663223091773843441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2436583108815394515895627 3654874663223091773843441)
                ·
                  refine ⟨2741155997417318830382581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3654874663223091773843441 2741155997417318830382581)
                  ·
                    refine ⟨256983374757873640348367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2741155997417318830382581 256983374757873640348367)
                    ·
                      rfl

theorem cell23_1501420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_1501420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501420 prefixEnd_1501420 := by exact prefixLift 1501420
  have htrace : WordTrace (prefixWord ++ tailWord_1501420) baseStart_1501420 baseEnd_1501420 := by
    simpa [prefixWord, tailWord_1501420, baseEnd_1501420] using wordTrace_append hprefix tailTrace_1501420
  have hstable : (prefixWord ++ tailWord_1501420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501420).length < 2 ^ (prefixWord ++ tailWord_1501420).sum := by decide
  have hdescent : baseEnd_1501420 < baseStart_1501420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501430 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1501430 : Nat := 118140960795 + 1501430 * 2 ^ 59
def prefixEnd_1501430 : Nat := 4983230072969 + 3 ^ 40 * 1501430 * 2
def baseEnd_1501430 : Nat := 770955259080165881920055

theorem tailTrace_1501430 : CollatzResearch.WordTrace tailWord_1501430 prefixEnd_1501430 770955259080165881920055 := by
  unfold tailWord_1501430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3422603184411438042135359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36507767300388672449443829 3422603184411438042135359)
  ·
    refine ⟨5133904776617157063203039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3422603184411438042135359 5133904776617157063203039)
    ·
      refine ⟨7700857164925735594804559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5133904776617157063203039 7700857164925735594804559)
      ·
        refine ⟨11551285747388603392206839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7700857164925735594804559 11551285747388603392206839)
        ·
          refine ⟨17326928621082905088310259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11551285747388603392206839 17326928621082905088310259)
          ·
            refine ⟨25990392931624357632465389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17326928621082905088310259 25990392931624357632465389)
            ·
              refine ⟨9746397349359134112174521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25990392931624357632465389 9746397349359134112174521)
              ·
                refine ⟨7309798012019350584130891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9746397349359134112174521 7309798012019350584130891)
                ·
                  refine ⟨10964697018029025876196337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7309798012019350584130891 10964697018029025876196337)
                  ·
                    refine ⟨8223522763521769407147253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10964697018029025876196337 8223522763521769407147253)
                    ·
                      refine ⟨770955259080165881920055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8223522763521769407147253 770955259080165881920055)
                      ·
                        rfl

theorem cell23_1501430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1501430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501430 prefixEnd_1501430 := by exact prefixLift 1501430
  have htrace : WordTrace (prefixWord ++ tailWord_1501430) baseStart_1501430 baseEnd_1501430 := by
    simpa [prefixWord, tailWord_1501430, baseEnd_1501430] using wordTrace_append hprefix tailTrace_1501430
  have hstable : (prefixWord ++ tailWord_1501430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501430).length < 2 ^ (prefixWord ++ tailWord_1501430).sum := by decide
  have hdescent : baseEnd_1501430 < baseStart_1501430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501440 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 4]
def baseStart_1501440 : Nat := 118140960795 + 1501440 * 2 ^ 59
def prefixEnd_1501440 : Nat := 4983230072969 + 3 ^ 40 * 1501440 * 2
def baseEnd_1501440 : Nat := 770960393886710842795009

theorem tailTrace_1501440 : CollatzResearch.WordTrace tailWord_1501440 prefixEnd_1501440 770960393886710842795009 := by
  unfold tailWord_1501440
  simp only [CollatzResearch.WordTrace]
  refine ⟨27381007840273390191014887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36508010453697853588019849 27381007840273390191014887)
  ·
    refine ⟨41071511760410085286522331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27381007840273390191014887 41071511760410085286522331)
    ·
      refine ⟨61607267640615127929783497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41071511760410085286522331 61607267640615127929783497)
      ·
        refine ⟨46205450730461345947337623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61607267640615127929783497 46205450730461345947337623)
        ·
          refine ⟨69308176095692018921006435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46205450730461345947337623 69308176095692018921006435)
          ·
            refine ⟨103962264143538028381509653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69308176095692018921006435 103962264143538028381509653)
            ·
              refine ⟨4873231131728345080383265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103962264143538028381509653 4873231131728345080383265)
              ·
                refine ⟨3654923348796258810287449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4873231131728345080383265 3654923348796258810287449)
                ·
                  refine ⟨2741192511597194107715587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3654923348796258810287449 2741192511597194107715587)
                  ·
                    refine ⟨4111788767395791161573381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2741192511597194107715587 4111788767395791161573381)
                    ·
                      refine ⟨770960393886710842795009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4111788767395791161573381 770960393886710842795009)
                      ·
                        rfl

theorem cell23_1501440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_1501440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501440 prefixEnd_1501440 := by exact prefixLift 1501440
  have htrace : WordTrace (prefixWord ++ tailWord_1501440) baseStart_1501440 baseEnd_1501440 := by
    simpa [prefixWord, tailWord_1501440, baseEnd_1501440] using wordTrace_append hprefix tailTrace_1501440
  have hstable : (prefixWord ++ tailWord_1501440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501440).length < 2 ^ (prefixWord ++ tailWord_1501440).sum := by decide
  have hdescent : baseEnd_1501440 < baseStart_1501440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501443 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 5]
def baseStart_1501443 : Nat := 118140960795 + 1501443 * 2 ^ 59
def prefixEnd_1501443 : Nat := 4983230072969 + 3 ^ 40 * 1501443 * 2
def baseEnd_1501443 : Nat := 770961934328674331057495

theorem tailTrace_1501443 : CollatzResearch.WordTrace tailWord_1501443 prefixEnd_1501443 770961934328674331057495 := by
  unfold tailWord_1501443
  simp only [CollatzResearch.WordTrace]
  refine ⟨54762125099535911894388983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36508083399690607929592655 54762125099535911894388983)
  ·
    refine ⟨82143187649303867841583475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54762125099535911894388983 82143187649303867841583475)
    ·
      refine ⟨123214781473955801762375213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82143187649303867841583475 123214781473955801762375213)
      ·
        refine ⟨46205543052733425660890705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123214781473955801762375213 46205543052733425660890705)
        ·
          refine ⟨34654157289550069245668029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46205543052733425660890705 34654157289550069245668029)
          ·
            refine ⟨12995308983581275967125511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34654157289550069245668029 12995308983581275967125511)
            ·
              refine ⟨19492963475371913950688267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12995308983581275967125511 19492963475371913950688267)
              ·
                refine ⟨29239445213057870926032401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19492963475371913950688267 29239445213057870926032401)
                ·
                  refine ⟨21929583909793403194524301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29239445213057870926032401 21929583909793403194524301)
                  ·
                    refine ⟨8223593966172526197946613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21929583909793403194524301 8223593966172526197946613)
                    ·
                      refine ⟨770961934328674331057495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8223593966172526197946613 770961934328674331057495)
                      ·
                        rfl

theorem cell23_1501443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_1501443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501443 prefixEnd_1501443 := by exact prefixLift 1501443
  have htrace : WordTrace (prefixWord ++ tailWord_1501443) baseStart_1501443 baseEnd_1501443 := by
    simpa [prefixWord, tailWord_1501443, baseEnd_1501443] using wordTrace_append hprefix tailTrace_1501443
  have hstable : (prefixWord ++ tailWord_1501443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501443).length < 2 ^ (prefixWord ++ tailWord_1501443).sum := by decide
  have hdescent : baseEnd_1501443 < baseStart_1501443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501457 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 2, 4, 2]
def baseStart_1501457 : Nat := 118140960795 + 1501457 * 2 ^ 59
def prefixEnd_1501457 : Nat := 4983230072969 + 3 ^ 40 * 1501457 * 2
def baseEnd_1501457 : Nat := 770969123057837276282431

theorem tailTrace_1501457 : CollatzResearch.WordTrace tailWord_1501457 prefixEnd_1501457 770969123057837276282431 := by
  unfold tailWord_1501457
  simp only [CollatzResearch.WordTrace]
  refine ⟨54762635721485192285398625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36508423814323461523599083 54762635721485192285398625)
  ·
    refine ⟨41071976791113894214048969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54762635721485192285398625 41071976791113894214048969)
    ·
      refine ⟨30803982593335420660536727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41071976791113894214048969 30803982593335420660536727)
      ·
        refine ⟨46205973890003130990805091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30803982593335420660536727 46205973890003130990805091)
        ·
          refine ⟨69308960835004696486207637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46205973890003130990805091 69308960835004696486207637)
          ·
            refine ⟨3248857539140845147790983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69308960835004696486207637 3248857539140845147790983)
            ·
              refine ⟨4873286308711267721686475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3248857539140845147790983 4873286308711267721686475)
              ·
                refine ⟨7309929463066901582529713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4873286308711267721686475 7309929463066901582529713)
                ·
                  refine ⟨5482447097300176186897285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7309929463066901582529713 5482447097300176186897285)
                  ·
                    refine ⟨1027958830743783035043241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5482447097300176186897285 1027958830743783035043241)
                    ·
                      refine ⟨770969123057837276282431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1027958830743783035043241 770969123057837276282431)
                      ·
                        rfl

theorem cell23_1501457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 4, 2].length) (baseStart_1501457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501457 prefixEnd_1501457 := by exact prefixLift 1501457
  have htrace : WordTrace (prefixWord ++ tailWord_1501457) baseStart_1501457 baseEnd_1501457 := by
    simpa [prefixWord, tailWord_1501457, baseEnd_1501457] using wordTrace_append hprefix tailTrace_1501457
  have hstable : (prefixWord ++ tailWord_1501457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501457).length < 2 ^ (prefixWord ++ tailWord_1501457).sum := by decide
  have hdescent : baseEnd_1501457 < baseStart_1501457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501474 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_1501474 : Nat := 118140960795 + 1501474 * 2 ^ 59
def prefixEnd_1501474 : Nat := 4983230072969 + 3 ^ 40 * 1501474 * 2
def baseEnd_1501474 : Nat := 770977852228963709769853

theorem tailTrace_1501474 : CollatzResearch.WordTrace tailWord_1501474 prefixEnd_1501474 770977852228963709769853 := by
  unfold tailWord_1501474
  simp only [CollatzResearch.WordTrace]
  refine ⟨13690813940605901047191869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36508837174949069459178317 13690813940605901047191869)
  ·
    refine ⟨5134055227727212892696951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13690813940605901047191869 5134055227727212892696951)
    ·
      refine ⟨7701082841590819339045427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5134055227727212892696951 7701082841590819339045427)
      ·
        refine ⟨11551624262386229008568141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7701082841590819339045427 11551624262386229008568141)
        ·
          refine ⟨4331859098394835878213053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11551624262386229008568141 4331859098394835878213053)
          ·
            refine ⟨1624447161898063454329895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4331859098394835878213053 1624447161898063454329895)
            ·
              refine ⟨2436670742847095181494843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1624447161898063454329895 2436670742847095181494843)
              ·
                refine ⟨3655006114270642772242265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2436670742847095181494843 3655006114270642772242265)
                ·
                  refine ⟨2741254585702982079181699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3655006114270642772242265 2741254585702982079181699)
                  ·
                    refine ⟨4111881878554473118772549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2741254585702982079181699 4111881878554473118772549)
                    ·
                      refine ⟨770977852228963709769853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4111881878554473118772549 770977852228963709769853)
                      ·
                        rfl

theorem cell23_1501474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_1501474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501474 prefixEnd_1501474 := by exact prefixLift 1501474
  have htrace : WordTrace (prefixWord ++ tailWord_1501474) baseStart_1501474 baseEnd_1501474 := by
    simpa [prefixWord, tailWord_1501474, baseEnd_1501474] using wordTrace_append hprefix tailTrace_1501474
  have hstable : (prefixWord ++ tailWord_1501474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501474).length < 2 ^ (prefixWord ++ tailWord_1501474).sum := by decide
  have hdescent : baseEnd_1501474 < baseStart_1501474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501477 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 1, 4, 3]
def baseStart_1501477 : Nat := 118140960795 + 1501477 * 2 ^ 59
def prefixEnd_1501477 : Nat := 4983230072969 + 3 ^ 40 * 1501477 * 2
def baseEnd_1501477 : Nat := 770979392670927198032339

theorem tailTrace_1501477 : CollatzResearch.WordTrace tailWord_1501477 prefixEnd_1501477 770979392670927198032339 := by
  unfold tailWord_1501477
  simp only [CollatzResearch.WordTrace]
  refine ⟨54763365181412735701126685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36508910120941823800751123 54763365181412735701126685)
  ·
    refine ⟨20536261943029775887922507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54763365181412735701126685 20536261943029775887922507)
    ·
      refine ⟨30804392914544663831883761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20536261943029775887922507 30804392914544663831883761)
      ·
        refine ⟨23103294685908497873912821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30804392914544663831883761 23103294685908497873912821)
        ·
          refine ⟨2165933876803921675679327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23103294685908497873912821 2165933876803921675679327)
          ·
            refine ⟨3248900815205882513518991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2165933876803921675679327 3248900815205882513518991)
            ·
              refine ⟨4873351222808823770278487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3248900815205882513518991 4873351222808823770278487)
              ·
                refine ⟨7310026834213235655417731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4873351222808823770278487 7310026834213235655417731)
                ·
                  refine ⟨10965040251319853483126597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7310026834213235655417731 10965040251319853483126597)
                  ·
                    refine ⟨2055945047122472528086237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10965040251319853483126597 2055945047122472528086237)
                    ·
                      refine ⟨770979392670927198032339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2055945047122472528086237 770979392670927198032339)
                      ·
                        rfl

theorem cell23_1501477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_1501477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501477 prefixEnd_1501477 := by exact prefixLift 1501477
  have htrace : WordTrace (prefixWord ++ tailWord_1501477) baseStart_1501477 baseEnd_1501477 := by
    simpa [prefixWord, tailWord_1501477, baseEnd_1501477] using wordTrace_append hprefix tailTrace_1501477
  have hstable : (prefixWord ++ tailWord_1501477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501477).length < 2 ^ (prefixWord ++ tailWord_1501477).sum := by decide
  have hdescent : baseEnd_1501477 < baseStart_1501477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501497 : List Nat := [1, 2, 1, 6, 1, 1, 3, 2, 6]
def baseStart_1501497 : Nat := 118140960795 + 1501497 * 2 ^ 59
def prefixEnd_1501497 : Nat := 4983230072969 + 3 ^ 40 * 1501497 * 2
def baseEnd_1501497 : Nat := 85665518031557457753583

theorem tailTrace_1501497 : CollatzResearch.WordTrace tailWord_1501497 prefixEnd_1501497 85665518031557457753583 := by
  unfold tailWord_1501497
  simp only [CollatzResearch.WordTrace]
  refine ⟨54764094641340279116854745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36509396427560186077903163 54764094641340279116854745)
  ·
    refine ⟨41073070981005209337641059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54764094641340279116854745 41073070981005209337641059)
    ·
      refine ⟨61609606471507814006461589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41073070981005209337641059 61609606471507814006461589)
      ·
        refine ⟨2887950303351928781552887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61609606471507814006461589 2887950303351928781552887)
        ·
          refine ⟨4331925455027893172329331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2887950303351928781552887 4331925455027893172329331)
          ·
            refine ⟨6497888182541839758493997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4331925455027893172329331 6497888182541839758493997)
            ·
              refine ⟨2436708068453189909435249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6497888182541839758493997 2436708068453189909435249)
              ·
                refine ⟨1827531051339892432076437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2436708068453189909435249 1827531051339892432076437)
                ·
                  refine ⟨85665518031557457753583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1827531051339892432076437 85665518031557457753583)
                  ·
                    rfl

theorem cell23_1501497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 6].length) (baseStart_1501497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501497 prefixEnd_1501497 := by exact prefixLift 1501497
  have htrace : WordTrace (prefixWord ++ tailWord_1501497) baseStart_1501497 baseEnd_1501497 := by
    simpa [prefixWord, tailWord_1501497, baseEnd_1501497] using wordTrace_append hprefix tailTrace_1501497
  have hstable : (prefixWord ++ tailWord_1501497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501497).length < 2 ^ (prefixWord ++ tailWord_1501497).sum := by decide
  have hdescent : baseEnd_1501497 < baseStart_1501497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501507 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 3, 1, 3]
def baseStart_1501507 : Nat := 118140960795 + 1501507 * 2 ^ 59
def prefixEnd_1501507 : Nat := 4983230072969 + 3 ^ 40 * 1501507 * 2
def baseEnd_1501507 : Nat := 770994797090562080657201

theorem tailTrace_1501507 : CollatzResearch.WordTrace tailWord_1501507 prefixEnd_1501507 770994797090562080657201 := by
  unfold tailWord_1501507
  simp only [CollatzResearch.WordTrace]
  refine ⟨54764459371304050824718775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36509639580869367216479183 54764459371304050824718775)
  ·
    refine ⟨82146689056956076237078163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54764459371304050824718775 82146689056956076237078163)
    ·
      refine ⟨123220033585434114355617245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82146689056956076237078163 123220033585434114355617245)
      ·
        refine ⟨46207512594537792883356467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123220033585434114355617245 46207512594537792883356467)
        ·
          refine ⟨69311268891806689325034701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46207512594537792883356467 69311268891806689325034701)
          ·
            refine ⟨25991725834427508496888013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69311268891806689325034701 25991725834427508496888013)
            ·
              refine ⟨9746897187910315686333005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25991725834427508496888013 9746897187910315686333005)
              ·
                refine ⟨3655086445466368382374877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9746897187910315686333005 3655086445466368382374877)
                ·
                  refine ⟨1370657417049888143390579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3655086445466368382374877 1370657417049888143390579)
                  ·
                    refine ⟨2055986125574832215085869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1370657417049888143390579 2055986125574832215085869)
                    ·
                      refine ⟨770994797090562080657201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2055986125574832215085869 770994797090562080657201)
                      ·
                        rfl

theorem cell23_1501507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 1, 3].length) (baseStart_1501507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501507 prefixEnd_1501507 := by exact prefixLift 1501507
  have htrace : WordTrace (prefixWord ++ tailWord_1501507) baseStart_1501507 baseEnd_1501507 := by
    simpa [prefixWord, tailWord_1501507, baseEnd_1501507] using wordTrace_append hprefix tailTrace_1501507
  have hstable : (prefixWord ++ tailWord_1501507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501507).length < 2 ^ (prefixWord ++ tailWord_1501507).sum := by decide
  have hdescent : baseEnd_1501507 < baseStart_1501507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501524 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_1501524 : Nat := 118140960795 + 1501524 * 2 ^ 59
def prefixEnd_1501524 : Nat := 4983230072969 + 3 ^ 40 * 1501524 * 2
def baseEnd_1501524 : Nat := 771003526261688514144623

theorem tailTrace_1501524 : CollatzResearch.WordTrace tailWord_1501524 prefixEnd_1501524 771003526261688514144623 := by
  unfold tailWord_1501524
  simp only [CollatzResearch.WordTrace]
  refine ⟨27382539706121231364043813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36510052941494975152058417 27382539706121231364043813)
  ·
    refine ⟨5134226194897730880758215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27382539706121231364043813 5134226194897730880758215)
    ·
      refine ⟨7701339292346596321137323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5134226194897730880758215 7701339292346596321137323)
      ·
        refine ⟨11552008938519894481705985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7701339292346596321137323 11552008938519894481705985)
        ·
          refine ⟨8664006703889920861279489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11552008938519894481705985 8664006703889920861279489)
          ·
            refine ⟨6498005027917440645959617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8664006703889920861279489 6498005027917440645959617)
            ·
              refine ⟨4873503770938080484469713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6498005027917440645959617 4873503770938080484469713)
              ·
                refine ⟨3655127828203560363352285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4873503770938080484469713 3655127828203560363352285)
                ·
                  refine ⟨1370672935576335136257107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3655127828203560363352285 1370672935576335136257107)
                  ·
                    refine ⟨2056009403364502704385661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1370672935576335136257107 2056009403364502704385661)
                    ·
                      refine ⟨771003526261688514144623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2056009403364502704385661 771003526261688514144623)
                      ·
                        rfl

theorem cell23_1501524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_1501524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501524 prefixEnd_1501524 := by exact prefixLift 1501524
  have htrace : WordTrace (prefixWord ++ tailWord_1501524) baseStart_1501524 baseEnd_1501524 := by
    simpa [prefixWord, tailWord_1501524, baseEnd_1501524] using wordTrace_append hprefix tailTrace_1501524
  have hstable : (prefixWord ++ tailWord_1501524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501524).length < 2 ^ (prefixWord ++ tailWord_1501524).sum := by decide
  have hdescent : baseEnd_1501524 < baseStart_1501524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501527 : List Nat := [1, 1, 3, 2, 3, 1, 4, 2, 1, 5]
def baseStart_1501527 : Nat := 118140960795 + 1501527 * 2 ^ 59
def prefixEnd_1501527 : Nat := 4983230072969 + 3 ^ 40 * 1501527 * 2
def baseEnd_1501527 : Nat := 257001688901217334135703

theorem tailTrace_1501527 : CollatzResearch.WordTrace tailWord_1501527 prefixEnd_1501527 257001688901217334135703 := by
  unfold tailWord_1501527
  simp only [CollatzResearch.WordTrace]
  refine ⟨54765188831231594240446835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36510125887487729493631223 54765188831231594240446835)
  ·
    refine ⟨82147783246847391360670253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54765188831231594240446835 82147783246847391360670253)
    ·
      refine ⟨30805418717567771760251345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82147783246847391360670253 30805418717567771760251345)
      ·
        refine ⟨23104064038175828820188509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30805418717567771760251345 23104064038175828820188509)
        ·
          refine ⟨8664024014315935807570691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23104064038175828820188509 8664024014315935807570691)
          ·
            refine ⟨12996036021473903711356037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8664024014315935807570691 12996036021473903711356037)
            ·
              refine ⟨2436756754026356945879257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12996036021473903711356037 2436756754026356945879257)
              ·
                refine ⟨1827567565519767709409443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2436756754026356945879257 1827567565519767709409443)
                ·
                  refine ⟨2741351348279651564114165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1827567565519767709409443 2741351348279651564114165)
                  ·
                    refine ⟨257001688901217334135703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2741351348279651564114165 257001688901217334135703)
                    ·
                      rfl

theorem cell23_1501527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_1501527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501527 prefixEnd_1501527 := by exact prefixLift 1501527
  have htrace : WordTrace (prefixWord ++ tailWord_1501527) baseStart_1501527 baseEnd_1501527 := by
    simpa [prefixWord, tailWord_1501527, baseEnd_1501527] using wordTrace_append hprefix tailTrace_1501527
  have hstable : (prefixWord ++ tailWord_1501527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501527).length < 2 ^ (prefixWord ++ tailWord_1501527).sum := by decide
  have hdescent : baseEnd_1501527 < baseStart_1501527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501540 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 3, 6]
def baseStart_1501540 : Nat := 118140960795 + 1501540 * 2 ^ 59
def prefixEnd_1501540 : Nat := 4983230072969 + 3 ^ 40 * 1501540 * 2
def baseEnd_1501540 : Nat := 257003913984053483848183

theorem tailTrace_1501540 : CollatzResearch.WordTrace tailWord_1501540 prefixEnd_1501540 257003913984053483848183 := by
  unfold tailWord_1501540
  simp only [CollatzResearch.WordTrace]
  refine ⟨27382831490092248730335037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36510441986789664973780049 27382831490092248730335037)
  ·
    refine ⟨10268561808784593273875639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27382831490092248730335037 10268561808784593273875639)
    ·
      refine ⟨15402842713176889910813459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10268561808784593273875639 15402842713176889910813459)
      ·
        refine ⟨23104264069765334866220189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15402842713176889910813459 23104264069765334866220189)
        ·
          refine ⟨8664099026162000574832571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23104264069765334866220189 8664099026162000574832571)
          ·
            refine ⟨12996148539243000862248857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8664099026162000574832571 12996148539243000862248857)
            ·
              refine ⟨9747111404432250646686643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12996148539243000862248857 9747111404432250646686643)
              ·
                refine ⟨14620667106648375970029965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9747111404432250646686643 14620667106648375970029965)
                ·
                  refine ⟨5482750164993140988761237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14620667106648375970029965 5482750164993140988761237)
                  ·
                    refine ⟨257003913984053483848183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5482750164993140988761237 257003913984053483848183)
                    ·
                      rfl

theorem cell23_1501540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_1501540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501540 prefixEnd_1501540 := by exact prefixLift 1501540
  have htrace : WordTrace (prefixWord ++ tailWord_1501540) baseStart_1501540 baseEnd_1501540 := by
    simpa [prefixWord, tailWord_1501540, baseEnd_1501540] using wordTrace_append hprefix tailTrace_1501540
  have hstable : (prefixWord ++ tailWord_1501540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501540).length < 2 ^ (prefixWord ++ tailWord_1501540).sum := by decide
  have hdescent : baseEnd_1501540 < baseStart_1501540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501541 : List Nat := [1, 3, 1, 3, 1, 3, 3, 3, 1, 1, 3]
def baseStart_1501541 : Nat := 118140960795 + 1501541 * 2 ^ 59
def prefixEnd_1501541 : Nat := 4983230072969 + 3 ^ 40 * 1501541 * 2
def baseEnd_1501541 : Nat := 771012255432814947632045

theorem tailTrace_1501541 : CollatzResearch.WordTrace tailWord_1501541 prefixEnd_1501541 771012255432814947632045 := by
  unfold tailWord_1501541
  simp only [CollatzResearch.WordTrace]
  refine ⟨54765699453180874631456477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36510466302120583087637651 54765699453180874631456477)
  ·
    refine ⟨20537137294942827986796179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54765699453180874631456477 20537137294942827986796179)
    ·
      refine ⟨30805705942414241980194269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20537137294942827986796179 30805705942414241980194269)
      ·
        refine ⟨11552139728405340742572851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30805705942414241980194269 11552139728405340742572851)
        ·
          refine ⟨17328209592608011113859277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11552139728405340742572851 17328209592608011113859277)
          ·
            refine ⟨6498078597228004167697229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17328209592608011113859277 6498078597228004167697229)
            ·
              refine ⟨2436779473960501562886461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6498078597228004167697229 2436779473960501562886461)
              ·
                refine ⟨913792302735188086082423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2436779473960501562886461 913792302735188086082423)
                ·
                  refine ⟨1370688454102782129123635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 913792302735188086082423 1370688454102782129123635)
                  ·
                    refine ⟨2056032681154173193685453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1370688454102782129123635 2056032681154173193685453)
                    ·
                      refine ⟨771012255432814947632045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2056032681154173193685453 771012255432814947632045)
                      ·
                        rfl

theorem cell23_1501541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_1501541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501541 prefixEnd_1501541 := by exact prefixLift 1501541
  have htrace : WordTrace (prefixWord ++ tailWord_1501541) baseStart_1501541 baseEnd_1501541 := by
    simpa [prefixWord, tailWord_1501541, baseEnd_1501541] using wordTrace_append hprefix tailTrace_1501541
  have hstable : (prefixWord ++ tailWord_1501541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501541).length < 2 ^ (prefixWord ++ tailWord_1501541).sum := by decide
  have hdescent : baseEnd_1501541 < baseStart_1501541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501564 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 3, 2, 2]
def baseStart_1501564 : Nat := 118140960795 + 1501564 * 2 ^ 59
def prefixEnd_1501564 : Nat := 4983230072969 + 3 ^ 40 * 1501564 * 2
def baseEnd_1501564 : Nat := 771024065487868357644439

theorem tailTrace_1501564 : CollatzResearch.WordTrace tailWord_1501564 prefixEnd_1501564 771024065487868357644439 := by
  unfold tailWord_1501564
  simp only [CollatzResearch.WordTrace]
  refine ⟨27383269166048774779771873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36511025554731699706362497 27383269166048774779771873)
  ·
    refine ⟨20537451874536581084828905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27383269166048774779771873 20537451874536581084828905)
    ·
      refine ⟨15403088905902435813621679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20537451874536581084828905 15403088905902435813621679)
      ·
        refine ⟨23104633358853653720432519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15403088905902435813621679 23104633358853653720432519)
        ·
          refine ⟨34656950038280480580648779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23104633358853653720432519 34656950038280480580648779)
          ·
            refine ⟨51985425057420720870973169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34656950038280480580648779 51985425057420720870973169)
            ·
              refine ⟨38989068793065540653229877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51985425057420720870973169 38989068793065540653229877)
              ·
                refine ⟨3655225199349894436240301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38989068793065540653229877 3655225199349894436240301)
                ·
                  refine ⟨1370709449756210413590113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3655225199349894436240301 1370709449756210413590113)
                  ·
                    refine ⟨1028032087317157810192585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1370709449756210413590113 1028032087317157810192585)
                    ·
                      refine ⟨771024065487868357644439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1028032087317157810192585 771024065487868357644439)
                      ·
                        rfl

theorem cell23_1501564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_1501564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501564 prefixEnd_1501564 := by exact prefixLift 1501564
  have htrace : WordTrace (prefixWord ++ tailWord_1501564) baseStart_1501564 baseEnd_1501564 := by
    simpa [prefixWord, tailWord_1501564, baseEnd_1501564] using wordTrace_append hprefix tailTrace_1501564
  have hstable : (prefixWord ++ tailWord_1501564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501564).length < 2 ^ (prefixWord ++ tailWord_1501564).sum := by decide
  have hdescent : baseEnd_1501564 < baseStart_1501564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501578 : List Nat := [3, 1, 2, 5, 2, 1, 1, 2, 1, 5]
def baseStart_1501578 : Nat := 118140960795 + 1501578 * 2 ^ 59
def prefixEnd_1501578 : Nat := 4983230072969 + 3 ^ 40 * 1501578 * 2
def baseEnd_1501578 : Nat := 257010418072343767623125

theorem tailTrace_1501578 : CollatzResearch.WordTrace tailWord_1501578 prefixEnd_1501578 257010418072343767623125 := by
  unfold tailWord_1501578
  simp only [CollatzResearch.WordTrace]
  refine ⟨13691762238511707487638347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36511365969364553300368925 13691762238511707487638347)
  ·
    refine ⟨20537643357767561231457521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13691762238511707487638347 20537643357767561231457521)
    ·
      refine ⟨15403232518325670923593141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20537643357767561231457521 15403232518325670923593141)
      ·
        refine ⟨1444053048593031649086857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15403232518325670923593141 1444053048593031649086857)
        ·
          refine ⟨1083039786444773736815143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1444053048593031649086857 1083039786444773736815143)
          ·
            refine ⟨1624559679667160605222715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083039786444773736815143 1624559679667160605222715)
            ·
              refine ⟨2436839519500740907834073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1624559679667160605222715 2436839519500740907834073)
              ·
                refine ⟨1827629639625555680875555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2436839519500740907834073 1827629639625555680875555)
                ·
                  refine ⟨2741444459438333521313333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1827629639625555680875555 2741444459438333521313333)
                  ·
                    refine ⟨257010418072343767623125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2741444459438333521313333 257010418072343767623125)
                    ·
                      rfl

theorem cell23_1501578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_1501578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501578 prefixEnd_1501578 := by exact prefixLift 1501578
  have htrace : WordTrace (prefixWord ++ tailWord_1501578) baseStart_1501578 baseEnd_1501578 := by
    simpa [prefixWord, tailWord_1501578, baseEnd_1501578] using wordTrace_append hprefix tailTrace_1501578
  have hstable : (prefixWord ++ tailWord_1501578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501578).length < 2 ^ (prefixWord ++ tailWord_1501578).sum := by decide
  have hdescent : baseEnd_1501578 < baseStart_1501578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501598 : List Nat := [4, 3, 1, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_1501598 : Nat := 118140960795 + 1501598 * 2 ^ 59
def prefixEnd_1501598 : Nat := 4983230072969 + 3 ^ 40 * 1501598 * 2
def baseEnd_1501598 : Nat := 771041523830121224619283

theorem tailTrace_1501598 : CollatzResearch.WordTrace tailWord_1501598 prefixEnd_1501598 771041523830121224619283 := by
  unfold tailWord_1501598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6845972301746796670785181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36511852275982915577520965 6845972301746796670785181)
  ·
    refine ⟨2567239613155048751544443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6845972301746796670785181 2567239613155048751544443)
    ·
      refine ⟨3850859419732573127316665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2567239613155048751544443 3850859419732573127316665)
      ·
        refine ⟨2888144564799429845487499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3850859419732573127316665 2888144564799429845487499)
        ·
          refine ⟨4332216847199144768231249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2888144564799429845487499 4332216847199144768231249)
          ·
            refine ⟨3249162635399358576173437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4332216847199144768231249 3249162635399358576173437)
            ·
              refine ⟨1218435988274759466065039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3249162635399358576173437 1218435988274759466065039)
              ·
                refine ⟨1827653982412139199097559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1218435988274759466065039 1827653982412139199097559)
                ·
                  refine ⟨2741480973618208798646339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1827653982412139199097559 2741480973618208798646339)
                  ·
                    refine ⟨4112221460427313197969509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2741480973618208798646339 4112221460427313197969509)
                    ·
                      refine ⟨771041523830121224619283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4112221460427313197969509 771041523830121224619283)
                      ·
                        rfl

theorem cell23_1501598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_1501598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501598 prefixEnd_1501598 := by exact prefixLift 1501598
  have htrace : WordTrace (prefixWord ++ tailWord_1501598) baseStart_1501598 baseEnd_1501598 := by
    simpa [prefixWord, tailWord_1501598, baseEnd_1501598] using wordTrace_append hprefix tailTrace_1501598
  have hstable : (prefixWord ++ tailWord_1501598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501598).length < 2 ^ (prefixWord ++ tailWord_1501598).sum := by decide
  have hdescent : baseEnd_1501598 < baseStart_1501598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501601 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1501601 : Nat := 118140960795 + 1501601 * 2 ^ 59
def prefixEnd_1501601 : Nat := 4983230072969 + 3 ^ 40 * 1501601 * 2
def baseEnd_1501601 : Nat := 771043064272084712881769

theorem tailTrace_1501601 : CollatzResearch.WordTrace tailWord_1501601 prefixEnd_1501601 771043064272084712881769 := by
  unfold tailWord_1501601
  simp only [CollatzResearch.WordTrace]
  refine ⟨54767887832963504878640657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36511925221975669919093771 54767887832963504878640657)
  ·
    refine ⟨41075915874722628658980493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54767887832963504878640657 41075915874722628658980493)
    ·
      refine ⟨15403468453020985747117685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41075915874722628658980493 15403468453020985747117685)
      ·
        refine ⟨1444075167470717413792283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15403468453020985747117685 1444075167470717413792283)
        ·
          refine ⟨2166112751206076120688425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1444075167470717413792283 2166112751206076120688425)
          ·
            refine ⟨1624584563404557090516319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2166112751206076120688425 1624584563404557090516319)
            ·
              refine ⟨2436876845106835635774479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1624584563404557090516319 2436876845106835635774479)
              ·
                refine ⟨3655315267660253453661719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2436876845106835635774479 3655315267660253453661719)
                ·
                  refine ⟨5482972901490380180492579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3655315267660253453661719 5482972901490380180492579)
                  ·
                    refine ⟨8224459352235570270738869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5482972901490380180492579 8224459352235570270738869)
                    ·
                      refine ⟨771043064272084712881769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8224459352235570270738869 771043064272084712881769)
                      ·
                        rfl

theorem cell23_1501601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1501601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501601 prefixEnd_1501601 := by exact prefixLift 1501601
  have htrace : WordTrace (prefixWord ++ tailWord_1501601) baseStart_1501601 baseEnd_1501601 := by
    simpa [prefixWord, tailWord_1501601, baseEnd_1501601] using wordTrace_append hprefix tailTrace_1501601
  have hstable : (prefixWord ++ tailWord_1501601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501601).length < 2 ^ (prefixWord ++ tailWord_1501601).sum := by decide
  have hdescent : baseEnd_1501601 < baseStart_1501601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501671 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 4, 2, 2]
def baseStart_1501671 : Nat := 118140960795 + 1501671 * 2 ^ 59
def prefixEnd_1501671 : Nat := 4983230072969 + 3 ^ 40 * 1501671 * 2
def baseEnd_1501671 : Nat := 771079007917899439006447

theorem tailTrace_1501671 : CollatzResearch.WordTrace tailWord_1501671 prefixEnd_1501671 771079007917899439006447 := by
  unfold tailWord_1501671
  simp only [CollatzResearch.WordTrace]
  refine ⟨54770440942709906833688867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36513627295139937889125911 54770440942709906833688867)
  ·
    refine ⟨82155661414064860250533301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54770440942709906833688867 82155661414064860250533301)
    ·
      refine ⟨7702093257568580648487497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82155661414064860250533301 7702093257568580648487497)
      ·
        refine ⟨5776569943176435486365623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7702093257568580648487497 5776569943176435486365623)
        ·
          refine ⟨8664854914764653229548435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5776569943176435486365623 8664854914764653229548435)
          ·
            refine ⟨12997282372146979844322653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8664854914764653229548435 12997282372146979844322653)
            ·
              refine ⟨4873980889555117441620995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12997282372146979844322653 4873980889555117441620995)
              ·
                refine ⟨7310971334332676162431493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4873980889555117441620995 7310971334332676162431493)
                ·
                  refine ⟨1370807125187376780455905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7310971334332676162431493 1370807125187376780455905)
                  ·
                    refine ⟨1028105343890532585341929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1370807125187376780455905 1028105343890532585341929)
                    ·
                      refine ⟨771079007917899439006447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1028105343890532585341929 771079007917899439006447)
                      ·
                        rfl

theorem cell23_1501671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_1501671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501671 prefixEnd_1501671 := by exact prefixLift 1501671
  have htrace : WordTrace (prefixWord ++ tailWord_1501671) baseStart_1501671 baseEnd_1501671 := by
    simpa [prefixWord, tailWord_1501671, baseEnd_1501671] using wordTrace_append hprefix tailTrace_1501671
  have hstable : (prefixWord ++ tailWord_1501671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501671).length < 2 ^ (prefixWord ++ tailWord_1501671).sum := by decide
  have hdescent : baseEnd_1501671 < baseStart_1501671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501688 : List Nat := [2, 1, 2, 1, 1, 4, 5, 1, 2, 2, 2]
def baseStart_1501688 : Nat := 118140960795 + 1501688 * 2 ^ 59
def prefixEnd_1501688 : Nat := 4983230072969 + 3 ^ 40 * 1501688 * 2
def baseEnd_1501688 : Nat := 771087737089025872493869

theorem tailTrace_1501688 : CollatzResearch.WordTrace tailWord_1501688 prefixEnd_1501688 771087737089025872493869 := by
  unfold tailWord_1501688
  simp only [CollatzResearch.WordTrace]
  refine ⟨27385530491824159368528859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36514040655765545824705145 27385530491824159368528859)
  ·
    refine ⟨41078295737736239052793289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27385530491824159368528859 41078295737736239052793289)
    ·
      refine ⟨30808721803302179289594967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41078295737736239052793289 30808721803302179289594967)
      ·
        refine ⟨46213082704953268934392451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30808721803302179289594967 46213082704953268934392451)
        ·
          refine ⟨69319624057429903401588677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46213082704953268934392451 69319624057429903401588677)
          ·
            refine ⟨12997429510768106887797877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69319624057429903401588677 12997429510768106887797877)
            ·
              refine ⟨1218509016634510020731051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12997429510768106887797877 1218509016634510020731051)
              ·
                refine ⟨1827763524951765031096577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1218509016634510020731051 1827763524951765031096577)
                ·
                  refine ⟨1370822643713823773322433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1827763524951765031096577 1370822643713823773322433)
                  ·
                    refine ⟨1028116982785367829991825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1370822643713823773322433 1028116982785367829991825)
                    ·
                      refine ⟨771087737089025872493869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1028116982785367829991825 771087737089025872493869)
                      ·
                        rfl

theorem cell23_1501688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 2, 2, 2].length) (baseStart_1501688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501688 prefixEnd_1501688 := by exact prefixLift 1501688
  have htrace : WordTrace (prefixWord ++ tailWord_1501688) baseStart_1501688 baseEnd_1501688 := by
    simpa [prefixWord, tailWord_1501688, baseEnd_1501688] using wordTrace_append hprefix tailTrace_1501688
  have hstable : (prefixWord ++ tailWord_1501688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501688).length < 2 ^ (prefixWord ++ tailWord_1501688).sum := by decide
  have hdescent : baseEnd_1501688 < baseStart_1501688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501707 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 1, 7]
def baseStart_1501707 : Nat := 118140960795 + 1501707 * 2 ^ 59
def prefixEnd_1501707 : Nat := 4983230072969 + 3 ^ 40 * 1501707 * 2
def baseEnd_1501707 : Nat := 257032497740487099385427

theorem tailTrace_1501707 : CollatzResearch.WordTrace tailWord_1501707 prefixEnd_1501707 257032497740487099385427 := by
  unfold tailWord_1501707
  simp only [CollatzResearch.WordTrace]
  refine ⟨54771753970579484981999375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36514502647052989987999583 54771753970579484981999375)
  ·
    refine ⟨82157630955869227472999063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54771753970579484981999375 82157630955869227472999063)
    ·
      refine ⟨123236446433803841209498595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82157630955869227472999063 123236446433803841209498595)
      ·
        refine ⟨184854669650705761814247893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123236446433803841209498595 184854669650705761814247893)
        ·
          refine ⟨4332531319938416292521435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 184854669650705761814247893 4332531319938416292521435)
          ·
            refine ⟨6498796979907624438782153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4332531319938416292521435 6498796979907624438782153)
            ·
              refine ⟨4874097734930718329086615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6498796979907624438782153 4874097734930718329086615)
              ·
                refine ⟨7311146602396077493629923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4874097734930718329086615 7311146602396077493629923)
                ·
                  refine ⟨10966719903594116240444885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7311146602396077493629923 10966719903594116240444885)
                  ·
                    refine ⟨257032497740487099385427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10966719903594116240444885 257032497740487099385427)
                    ·
                      rfl

theorem cell23_1501707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 7].length) (baseStart_1501707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501707 prefixEnd_1501707 := by exact prefixLift 1501707
  have htrace : WordTrace (prefixWord ++ tailWord_1501707) baseStart_1501707 baseEnd_1501707 := by
    simpa [prefixWord, tailWord_1501707, baseEnd_1501707] using wordTrace_append hprefix tailTrace_1501707
  have hstable : (prefixWord ++ tailWord_1501707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501707).length < 2 ^ (prefixWord ++ tailWord_1501707).sum := by decide
  have hdescent : baseEnd_1501707 < baseStart_1501707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501717 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_1501717 : Nat := 118140960795 + 1501717 * 2 ^ 59
def prefixEnd_1501717 : Nat := 4983230072969 + 3 ^ 40 * 1501717 * 2
def baseEnd_1501717 : Nat := 771102628028006259031235

theorem tailTrace_1501717 : CollatzResearch.WordTrace tailWord_1501717 prefixEnd_1501717 771102628028006259031235 := by
  unfold tailWord_1501717
  simp only [CollatzResearch.WordTrace]
  refine ⟨54772118700543256689863405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36514745800362171126575603 54772118700543256689863405)
  ·
    refine ⟨20539544512703721258698777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54772118700543256689863405 20539544512703721258698777)
    ·
      refine ⟨15404658384527790944024083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20539544512703721258698777 15404658384527790944024083)
      ·
        refine ⟨23106987576791686416036125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15404658384527790944024083 23106987576791686416036125)
        ·
          refine ⟨8665120341296882406013547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23106987576791686416036125 8665120341296882406013547)
          ·
            refine ⟨12997680511945323609020321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8665120341296882406013547 12997680511945323609020321)
            ·
              refine ⟨9748260383958992706765241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12997680511945323609020321 9748260383958992706765241)
              ·
                refine ⟨7311195287969244530073931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9748260383958992706765241 7311195287969244530073931)
                ·
                  refine ⟨10966792931953866795110897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7311195287969244530073931 10966792931953866795110897)
                  ·
                    refine ⟨8225094698965400096333173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10966792931953866795110897 8225094698965400096333173)
                    ·
                      refine ⟨771102628028006259031235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8225094698965400096333173 771102628028006259031235)
                      ·
                        rfl

theorem cell23_1501717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_1501717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501717 prefixEnd_1501717 := by exact prefixLift 1501717
  have htrace : WordTrace (prefixWord ++ tailWord_1501717) baseStart_1501717 baseEnd_1501717 := by
    simpa [prefixWord, tailWord_1501717, baseEnd_1501717] using wordTrace_append hprefix tailTrace_1501717
  have hstable : (prefixWord ++ tailWord_1501717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501717).length < 2 ^ (prefixWord ++ tailWord_1501717).sum := by decide
  have hdescent : baseEnd_1501717 < baseStart_1501717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501724 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 2, 5]
def baseStart_1501724 : Nat := 118140960795 + 1501724 * 2 ^ 59
def prefixEnd_1501724 : Nat := 4983230072969 + 3 ^ 40 * 1501724 * 2
def baseEnd_1501724 : Nat := 257035407464195910547901

theorem tailTrace_1501724 : CollatzResearch.WordTrace tailWord_1501724 prefixEnd_1501724 257035407464195910547901 := by
  unfold tailWord_1501724
  simp only [CollatzResearch.WordTrace]
  refine ⟨27386187005758948442684113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36514916007678597923578817 27386187005758948442684113)
  ·
    refine ⟨20539640254319211332013085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27386187005758948442684113 20539640254319211332013085)
    ·
      refine ⟨7702365095369704249504907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20539640254319211332013085 7702365095369704249504907)
      ·
        refine ⟨11553547643054556374257361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7702365095369704249504907 11553547643054556374257361)
        ·
          refine ⟨8665160732290917280693021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11553547643054556374257361 8665160732290917280693021)
          ·
            refine ⟨3249435274609093980259883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8665160732290917280693021 3249435274609093980259883)
            ·
              refine ⟨4874152911913640970389825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249435274609093980259883 4874152911913640970389825)
              ·
                refine ⟨3655614683935230727792369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4874152911913640970389825 3655614683935230727792369)
                ·
                  refine ⟨2741711012951423045844277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3655614683935230727792369 2741711012951423045844277)
                  ·
                    refine ⟨257035407464195910547901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2741711012951423045844277 257035407464195910547901)
                    ·
                      rfl

theorem cell23_1501724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_1501724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501724 prefixEnd_1501724 := by exact prefixLift 1501724
  have htrace : WordTrace (prefixWord ++ tailWord_1501724) baseStart_1501724 baseEnd_1501724 := by
    simpa [prefixWord, tailWord_1501724, baseEnd_1501724] using wordTrace_append hprefix tailTrace_1501724
  have hstable : (prefixWord ++ tailWord_1501724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501724).length < 2 ^ (prefixWord ++ tailWord_1501724).sum := by decide
  have hdescent : baseEnd_1501724 < baseStart_1501724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501728 : List Nat := [2, 1, 1, 6, 2, 1, 3, 2, 5]
def baseStart_1501728 : Nat := 118140960795 + 1501728 * 2 ^ 59
def prefixEnd_1501728 : Nat := 4983230072969 + 3 ^ 40 * 1501728 * 2
def baseEnd_1501728 : Nat := 85678697368356190665965

theorem tailTrace_1501728 : CollatzResearch.WordTrace tailWord_1501728 prefixEnd_1501728 85678697368356190665965 := by
  unfold tailWord_1501728
  simp only [CollatzResearch.WordTrace]
  refine ⟨27386259951751702784256919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36515013269002270379009225 27386259951751702784256919)
  ·
    refine ⟨41079389927627554176385379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27386259951751702784256919 41079389927627554176385379)
    ·
      refine ⟨61619084891441331264578069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41079389927627554176385379 61619084891441331264578069)
      ·
        refine ⟨2888394604286312403027097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61619084891441331264578069 2888394604286312403027097)
        ·
          refine ⟨2166295953214734302270323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2888394604286312403027097 2166295953214734302270323)
          ·
            refine ⟨3249443929822101453405485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2166295953214734302270323 3249443929822101453405485)
            ·
              refine ⟨1218541473683288045027057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3249443929822101453405485 1218541473683288045027057)
              ·
                refine ⟨913906105262466033770293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1218541473683288045027057 913906105262466033770293)
                ·
                  refine ⟨85678697368356190665965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 913906105262466033770293 85678697368356190665965)
                  ·
                    rfl

theorem cell23_1501728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 5].length) (baseStart_1501728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501728 prefixEnd_1501728 := by exact prefixLift 1501728
  have htrace : WordTrace (prefixWord ++ tailWord_1501728) baseStart_1501728 baseEnd_1501728 := by
    simpa [prefixWord, tailWord_1501728, baseEnd_1501728] using wordTrace_append hprefix tailTrace_1501728
  have hstable : (prefixWord ++ tailWord_1501728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501728).length < 2 ^ (prefixWord ++ tailWord_1501728).sum := by decide
  have hdescent : baseEnd_1501728 < baseStart_1501728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501744 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 2, 4, 2]
def baseStart_1501744 : Nat := 118140960795 + 1501744 * 2 ^ 59
def prefixEnd_1501744 : Nat := 4983230072969 + 3 ^ 40 * 1501744 * 2
def baseEnd_1501744 : Nat := 771116492005677653393611

theorem tailTrace_1501744 : CollatzResearch.WordTrace tailWord_1501744 prefixEnd_1501744 771116492005677653393611 := by
  unfold tailWord_1501744
  simp only [CollatzResearch.WordTrace]
  refine ⟨27386551735722720150548143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36515402314296960200730857 27386551735722720150548143)
  ·
    refine ⟨41079827603584080225822215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27386551735722720150548143 41079827603584080225822215)
    ·
      refine ⟨61619741405376120338733323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41079827603584080225822215 61619741405376120338733323)
      ·
        refine ⟨92429612108064180508099985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61619741405376120338733323 92429612108064180508099985)
        ·
          refine ⟨69322209081048135381074989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92429612108064180508099985 69322209081048135381074989)
          ·
            refine ⟨25995828405393050767903121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69322209081048135381074989 25995828405393050767903121)
            ·
              refine ⟨19496871304044788075927341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25995828405393050767903121 19496871304044788075927341)
              ·
                refine ⟨7311326739016795528472753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19496871304044788075927341 7311326739016795528472753)
                ·
                  refine ⟨5483495054262596646354565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7311326739016795528472753 5483495054262596646354565)
                  ·
                    refine ⟨1028155322674236871191481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5483495054262596646354565 1028155322674236871191481)
                    ·
                      refine ⟨771116492005677653393611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1028155322674236871191481 771116492005677653393611)
                      ·
                        rfl

theorem cell23_1501744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 2, 4, 2].length) (baseStart_1501744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501744 prefixEnd_1501744 := by exact prefixLift 1501744
  have htrace : WordTrace (prefixWord ++ tailWord_1501744) baseStart_1501744 baseEnd_1501744 := by
    simpa [prefixWord, tailWord_1501744, baseEnd_1501744] using wordTrace_append hprefix tailTrace_1501744
  have hstable : (prefixWord ++ tailWord_1501744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501744).length < 2 ^ (prefixWord ++ tailWord_1501744).sum := by decide
  have hdescent : baseEnd_1501744 < baseStart_1501744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501758 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_1501758 : Nat := 118140960795 + 1501758 * 2 ^ 59
def prefixEnd_1501758 : Nat := 4983230072969 + 3 ^ 40 * 1501758 * 2
def baseEnd_1501758 : Nat := 257041226911613532872849

theorem tailTrace_1501758 : CollatzResearch.WordTrace tailWord_1501758 prefixEnd_1501758 257041226911613532872849 := by
  unfold tailWord_1501758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6846701761674340086513241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36515742728929813794737285 6846701761674340086513241)
  ·
    refine ⟨5135026321255755064884931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6846701761674340086513241 5135026321255755064884931)
    ·
      refine ⟨7702539481883632597327397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5135026321255755064884931 7702539481883632597327397)
      ·
        refine ⟨1444226152853181111998887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7702539481883632597327397 1444226152853181111998887)
        ·
          refine ⟨2166339229279771667998331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1444226152853181111998887 2166339229279771667998331)
          ·
            refine ⟨3249508843919657501997497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2166339229279771667998331 3249508843919657501997497)
            ·
              refine ⟨2437131632939743126498123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3249508843919657501997497 2437131632939743126498123)
              ·
                refine ⟨3655697449409614689747185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2437131632939743126498123 3655697449409614689747185)
                ·
                  refine ⟨2741773087057211017310389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3655697449409614689747185 2741773087057211017310389)
                  ·
                    refine ⟨257041226911613532872849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2741773087057211017310389 257041226911613532872849)
                    ·
                      rfl

theorem cell23_1501758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_1501758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501758 prefixEnd_1501758 := by exact prefixLift 1501758
  have htrace : WordTrace (prefixWord ++ tailWord_1501758) baseStart_1501758 baseEnd_1501758 := by
    simpa [prefixWord, tailWord_1501758, baseEnd_1501758] using wordTrace_append hprefix tailTrace_1501758
  have hstable : (prefixWord ++ tailWord_1501758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501758).length < 2 ^ (prefixWord ++ tailWord_1501758).sum := by decide
  have hdescent : baseEnd_1501758 < baseStart_1501758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501761 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_1501761 : Nat := 118140960795 + 1501761 * 2 ^ 59
def prefixEnd_1501761 : Nat := 4983230072969 + 3 ^ 40 * 1501761 * 2
def baseEnd_1501761 : Nat := 771125221176804086881033

theorem tailTrace_1501761 : CollatzResearch.WordTrace tailWord_1501761 prefixEnd_1501761 771125221176804086881033 := by
  unfold tailWord_1501761
  simp only [CollatzResearch.WordTrace]
  refine ⟨54773723512383852204465137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36515815674922568136310091 54773723512383852204465137)
  ·
    refine ⟨41080292634287889153348853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54773723512383852204465137 41080292634287889153348853)
    ·
      refine ⟨3851277434464489608126455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41080292634287889153348853 3851277434464489608126455)
      ·
        refine ⟨5776916151696734412189683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3851277434464489608126455 5776916151696734412189683)
        ·
          refine ⟨8665374227545101618284525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5776916151696734412189683 8665374227545101618284525)
          ·
            refine ⟨3249515335329413106856697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8665374227545101618284525 3249515335329413106856697)
            ·
              refine ⟨2437136501497059830142523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3249515335329413106856697 2437136501497059830142523)
              ·
                refine ⟨3655704752245589745213785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2437136501497059830142523 3655704752245589745213785)
                ·
                  refine ⟨2741778564184192308910339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3655704752245589745213785 2741778564184192308910339)
                  ·
                    refine ⟨4112667846276288463365509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2741778564184192308910339 4112667846276288463365509)
                    ·
                      refine ⟨771125221176804086881033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4112667846276288463365509 771125221176804086881033)
                      ·
                        rfl

theorem cell23_1501761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_1501761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501761 prefixEnd_1501761 := by exact prefixLift 1501761
  have htrace : WordTrace (prefixWord ++ tailWord_1501761) baseStart_1501761 baseEnd_1501761 := by
    simpa [prefixWord, tailWord_1501761, baseEnd_1501761] using wordTrace_append hprefix tailTrace_1501761
  have hstable : (prefixWord ++ tailWord_1501761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501761).length < 2 ^ (prefixWord ++ tailWord_1501761).sum := by decide
  have hdescent : baseEnd_1501761 < baseStart_1501761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501871 : List Nat := [1, 1, 2, 1, 2, 5, 1, 4, 1, 2, 3]
def baseStart_1501871 : Nat := 118140960795 + 1501871 * 2 ^ 59
def prefixEnd_1501871 : Nat := 4983230072969 + 3 ^ 40 * 1501871 * 2
def baseEnd_1501871 : Nat := 771181704048798656505527

theorem tailTrace_1501871 : CollatzResearch.WordTrace tailWord_1501871 prefixEnd_1501871 771181704048798656505527 := by
  unfold tailWord_1501871
  simp only [CollatzResearch.WordTrace]
  refine ⟨54777735541985340990969467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36518490361323560660646311 54777735541985340990969467)
  ·
    refine ⟨82166603312978011486454201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54777735541985340990969467 82166603312978011486454201)
    ·
      refine ⟨61624952484733508614840651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82166603312978011486454201 61624952484733508614840651)
      ·
        refine ⟨92437428727100262922260977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61624952484733508614840651 92437428727100262922260977)
        ·
          refine ⟨69328071545325197191695733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92437428727100262922260977 69328071545325197191695733)
          ·
            refine ⟨6499506707374237236721475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69328071545325197191695733 6499506707374237236721475)
            ·
              refine ⟨9749260061061355855082213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6499506707374237236721475 9749260061061355855082213)
              ·
                refine ⟨1827986261449004222827915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9749260061061355855082213 1827986261449004222827915)
                ·
                  refine ⟨2741979392173506334241873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1827986261449004222827915 2741979392173506334241873)
                  ·
                    refine ⟨2056484544130129750681405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2741979392173506334241873 2056484544130129750681405)
                    ·
                      refine ⟨771181704048798656505527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2056484544130129750681405 771181704048798656505527)
                      ·
                        rfl

theorem cell23_1501871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 2, 3].length) (baseStart_1501871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501871 prefixEnd_1501871 := by exact prefixLift 1501871
  have htrace : WordTrace (prefixWord ++ tailWord_1501871) baseStart_1501871 baseEnd_1501871 := by
    simpa [prefixWord, tailWord_1501871, baseEnd_1501871] using wordTrace_append hprefix tailTrace_1501871
  have hstable : (prefixWord ++ tailWord_1501871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501871).length < 2 ^ (prefixWord ++ tailWord_1501871).sum := by decide
  have hdescent : baseEnd_1501871 < baseStart_1501871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501944 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 2, 1, 5]
def baseStart_1501944 : Nat := 118140960795 + 1501944 * 2 ^ 59
def prefixEnd_1501944 : Nat := 4983230072969 + 3 ^ 40 * 1501944 * 2
def baseEnd_1501944 : Nat := 771219188136576870892691

theorem tailTrace_1501944 : CollatzResearch.WordTrace tailWord_1501944 prefixEnd_1501944 771219188136576870892691 := by
  unfold tailWord_1501944
  simp only [CollatzResearch.WordTrace]
  refine ⟨27390199035360437229188443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36520265380480582972251257 27390199035360437229188443)
  ·
    refine ⟨41085298553040655843782665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27390199035360437229188443 41085298553040655843782665)
    ·
      refine ⟨30813973914780491882836999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41085298553040655843782665 30813973914780491882836999)
      ·
        refine ⟨46220960872170737824255499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30813973914780491882836999 46220960872170737824255499)
        ·
          refine ⟨69331441308256106736383249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46220960872170737824255499 69331441308256106736383249)
          ·
            refine ⟨51998580981192080052287437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69331441308256106736383249 51998580981192080052287437)
            ·
              refine ⟨19499467867947030019607789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51998580981192080052287437 19499467867947030019607789)
              ·
                refine ⟨7312300450480136257352921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19499467867947030019607789 7312300450480136257352921)
                ·
                  refine ⟨5484225337860102193014691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7312300450480136257352921 5484225337860102193014691)
                  ·
                    refine ⟨8226338006790153289522037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5484225337860102193014691 8226338006790153289522037)
                    ·
                      refine ⟨771219188136576870892691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8226338006790153289522037 771219188136576870892691)
                      ·
                        rfl

theorem cell23_1501944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_1501944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501944 prefixEnd_1501944 := by exact prefixLift 1501944
  have htrace : WordTrace (prefixWord ++ tailWord_1501944) baseStart_1501944 baseEnd_1501944 := by
    simpa [prefixWord, tailWord_1501944, baseEnd_1501944] using wordTrace_append hprefix tailTrace_1501944
  have hstable : (prefixWord ++ tailWord_1501944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501944).length < 2 ^ (prefixWord ++ tailWord_1501944).sum := by decide
  have hdescent : baseEnd_1501944 < baseStart_1501944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501964 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 7]
def baseStart_1501964 : Nat := 118140960795 + 1501964 * 2 ^ 59
def prefixEnd_1501964 : Nat := 4983230072969 + 3 ^ 40 * 1501964 * 2
def baseEnd_1501964 : Nat := 85692161972185199182511

theorem tailTrace_1501964 : CollatzResearch.WordTrace tailWord_1501964 prefixEnd_1501964 85692161972185199182511 := by
  unfold tailWord_1501964
  simp only [CollatzResearch.WordTrace]
  refine ⟨27390563765324208937052473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36520751687098945249403297 27390563765324208937052473)
  ·
    refine ⟨20542922823993156702789355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27390563765324208937052473 20542922823993156702789355)
    ·
      refine ⟨30814384235989735054184033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20542922823993156702789355 30814384235989735054184033)
      ·
        refine ⟨23110788176992301290638025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30814384235989735054184033 23110788176992301290638025)
        ·
          refine ⟨17333091132744225967978519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23110788176992301290638025 17333091132744225967978519)
          ·
            refine ⟨25999636699116338951967779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17333091132744225967978519 25999636699116338951967779)
            ·
              refine ⟨38999455048674508427951669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25999636699116338951967779 38999455048674508427951669)
              ·
                refine ⟨3656198910813235165120469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38999455048674508427951669 3656198910813235165120469)
                ·
                  refine ⟨85692161972185199182511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3656198910813235165120469 85692161972185199182511)
                  ·
                    rfl

theorem cell23_1501964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 7].length) (baseStart_1501964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501964 prefixEnd_1501964 := by exact prefixLift 1501964
  have htrace : WordTrace (prefixWord ++ tailWord_1501964) baseStart_1501964 baseEnd_1501964 := by
    simpa [prefixWord, tailWord_1501964, baseEnd_1501964] using wordTrace_append hprefix tailTrace_1501964
  have hstable : (prefixWord ++ tailWord_1501964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501964).length < 2 ^ (prefixWord ++ tailWord_1501964).sum := by decide
  have hdescent : baseEnd_1501964 < baseStart_1501964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501975 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 1, 4, 2]
def baseStart_1501975 : Nat := 118140960795 + 1501975 * 2 ^ 59
def prefixEnd_1501975 : Nat := 4983230072969 + 3 ^ 40 * 1501975 * 2
def baseEnd_1501975 : Nat := 771235106036866249605049

theorem tailTrace_1501975 : CollatzResearch.WordTrace tailWord_1501975 prefixEnd_1501975 771235106036866249605049 := by
  unfold tailWord_1501975
  simp only [CollatzResearch.WordTrace]
  refine ⟨54781528733608566752755379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36521019155739044501836919 54781528733608566752755379)
  ·
    refine ⟨82172293100412850129133069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54781528733608566752755379 82172293100412850129133069)
    ·
      refine ⟨30814609912654818798424901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82172293100412850129133069 30814609912654818798424901)
      ·
        refine ⟨5777739358622778524704669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30814609912654818798424901 5777739358622778524704669)
        ·
          refine ⟨2166652259483541946764251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5777739358622778524704669 2166652259483541946764251)
          ·
            refine ⟨3249978389225312920146377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2166652259483541946764251 3249978389225312920146377)
            ·
              refine ⟨2437483791918984690109783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3249978389225312920146377 2437483791918984690109783)
              ·
                refine ⟨3656225687878477035164675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2437483791918984690109783 3656225687878477035164675)
                ·
                  refine ⟨5484338531817715552747013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3656225687878477035164675 5484338531817715552747013)
                  ·
                    refine ⟨1028313474715821666140065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5484338531817715552747013 1028313474715821666140065)
                    ·
                      refine ⟨771235106036866249605049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1028313474715821666140065 771235106036866249605049)
                      ·
                        rfl

theorem cell23_1501975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_1501975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1501975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1501975 prefixEnd_1501975 := by exact prefixLift 1501975
  have htrace : WordTrace (prefixWord ++ tailWord_1501975) baseStart_1501975 baseEnd_1501975 := by
    simpa [prefixWord, tailWord_1501975, baseEnd_1501975] using wordTrace_append hprefix tailTrace_1501975
  have hstable : (prefixWord ++ tailWord_1501975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501975).length < 2 ^ (prefixWord ++ tailWord_1501975).sum := by decide
  have hdescent : baseEnd_1501975 < baseStart_1501975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502088 : List Nat := [2, 1, 3, 3, 2, 2, 1, 3, 6]
def baseStart_1502088 : Nat := 118140960795 + 1502088 * 2 ^ 59
def prefixEnd_1502088 : Nat := 4983230072969 + 3 ^ 40 * 1502088 * 2
def baseEnd_1502088 : Nat := 85699236594536034165781

theorem tailTrace_1502088 : CollatzResearch.WordTrace tailWord_1502088 prefixEnd_1502088 85699236594536034165781 := by
  unfold tailWord_1502088
  simp only [CollatzResearch.WordTrace]
  refine ⟨27392825091099593525809459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36523766788132791367745945 27392825091099593525809459)
  ·
    refine ⟨41089237636649390288714189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27392825091099593525809459 41089237636649390288714189)
    ·
      refine ⟨15408464113743521358267821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41089237636649390288714189 15408464113743521358267821)
      ·
        refine ⟨5778174042653820509350433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15408464113743521358267821 5778174042653820509350433)
        ·
          refine ⟨4333630531990365382012825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5778174042653820509350433 4333630531990365382012825)
          ·
            refine ⟨3250222898992774036509619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4333630531990365382012825 3250222898992774036509619)
            ·
              refine ⟨4875334348489161054764429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3250222898992774036509619 4875334348489161054764429)
              ·
                refine ⟨1828250380683435395536661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4875334348489161054764429 1828250380683435395536661)
                ·
                  refine ⟨85699236594536034165781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1828250380683435395536661 85699236594536034165781)
                  ·
                    rfl

theorem cell23_1502088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 6].length) (baseStart_1502088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502088 prefixEnd_1502088 := by exact prefixLift 1502088
  have htrace : WordTrace (prefixWord ++ tailWord_1502088) baseStart_1502088 baseEnd_1502088 := by
    simpa [prefixWord, tailWord_1502088, baseEnd_1502088] using wordTrace_append hprefix tailTrace_1502088
  have hstable : (prefixWord ++ tailWord_1502088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502088).length < 2 ^ (prefixWord ++ tailWord_1502088).sum := by decide
  have hdescent : baseEnd_1502088 < baseStart_1502088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502151 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_1502151 : Nat := 118140960795 + 1502151 * 2 ^ 59
def prefixEnd_1502151 : Nat := 4983230072969 + 3 ^ 40 * 1502151 * 2
def baseEnd_1502151 : Nat := 771325478632057561004239

theorem tailTrace_1502151 : CollatzResearch.WordTrace tailWord_1502151 prefixEnd_1502151 771325478632057561004239 := by
  unfold tailWord_1502151
  simp only [CollatzResearch.WordTrace]
  refine ⟨54787947980970948811162307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36525298653980632540774871 54787947980970948811162307)
  ·
    refine ⟨82181921971456423216743461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54787947980970948811162307 82181921971456423216743461)
    ·
      refine ⟨15409110369648079353139399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82181921971456423216743461 15409110369648079353139399)
      ·
        refine ⟨23113665554472119029709099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15409110369648079353139399 23113665554472119029709099)
        ·
          refine ⟨34670498331708178544563649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23113665554472119029709099 34670498331708178544563649)
          ·
            refine ⟨26002873748781133908422737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34670498331708178544563649 26002873748781133908422737)
            ·
              refine ⟨19502155311585850431317053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26002873748781133908422737 19502155311585850431317053)
              ·
                refine ⟨7313308241844693911743895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19502155311585850431317053 7313308241844693911743895)
                ·
                  refine ⟨10969962362767040867615843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7313308241844693911743895 10969962362767040867615843)
                  ·
                    refine ⟨16454943544150561301423765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10969962362767040867615843 16454943544150561301423765)
                    ·
                      refine ⟨771325478632057561004239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16454943544150561301423765 771325478632057561004239)
                      ·
                        rfl

theorem cell23_1502151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_1502151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502151 prefixEnd_1502151 := by exact prefixLift 1502151
  have htrace : WordTrace (prefixWord ++ tailWord_1502151) baseStart_1502151 baseEnd_1502151 := by
    simpa [prefixWord, tailWord_1502151, baseEnd_1502151] using wordTrace_append hprefix tailTrace_1502151
  have hstable : (prefixWord ++ tailWord_1502151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502151).length < 2 ^ (prefixWord ++ tailWord_1502151).sum := by decide
  have hdescent : baseEnd_1502151 < baseStart_1502151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502155 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 5, 2, 2]
def baseStart_1502155 : Nat := 118140960795 + 1502155 * 2 ^ 59
def prefixEnd_1502155 : Nat := 4983230072969 + 3 ^ 40 * 1502155 * 2
def baseEnd_1502155 : Nat := 771327532554675545354221

theorem tailTrace_1502155 : CollatzResearch.WordTrace tailWord_1502155 prefixEnd_1502155 771327532554675545354221 := by
  unfold tailWord_1502155
  simp only [CollatzResearch.WordTrace]
  refine ⟨54788093872956457494307919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36525395915304304996205279 54788093872956457494307919)
  ·
    refine ⟨82182140809434686241461879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54788093872956457494307919 82182140809434686241461879)
    ·
      refine ⟨123273211214152029362192819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82182140809434686241461879 123273211214152029362192819)
      ·
        refine ⟨184909816821228044043289229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123273211214152029362192819 184909816821228044043289229)
        ·
          refine ⟨69341181307960516516233461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184909816821228044043289229 69341181307960516516233461)
          ·
            refine ⟨6500735747621298423396887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69341181307960516516233461 6500735747621298423396887)
            ·
              refine ⟨9751103621431947635095331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6500735747621298423396887 9751103621431947635095331)
              ·
                refine ⟨14626655432147921452642997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9751103621431947635095331 14626655432147921452642997)
                ·
                  refine ⟨1371248946763867636185281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14626655432147921452642997 1371248946763867636185281)
                  ·
                    refine ⟨1028436710072900727138961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1371248946763867636185281 1028436710072900727138961)
                    ·
                      refine ⟨771327532554675545354221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1028436710072900727138961 771327532554675545354221)
                      ·
                        rfl

theorem cell23_1502155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 2, 2].length) (baseStart_1502155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502155 prefixEnd_1502155 := by exact prefixLift 1502155
  have htrace : WordTrace (prefixWord ++ tailWord_1502155) baseStart_1502155 baseEnd_1502155 := by
    simpa [prefixWord, tailWord_1502155, baseEnd_1502155] using wordTrace_append hprefix tailTrace_1502155
  have hstable : (prefixWord ++ tailWord_1502155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502155).length < 2 ^ (prefixWord ++ tailWord_1502155).sum := by decide
  have hdescent : baseEnd_1502155 < baseStart_1502155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502166 : List Nat := [5, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_1502166 : Nat := 118140960795 + 1502166 * 2 ^ 59
def prefixEnd_1502166 : Nat := 4983230072969 + 3 ^ 40 * 1502166 * 2
def baseEnd_1502166 : Nat := 771333180841875002316671

theorem tailTrace_1502166 : CollatzResearch.WordTrace tailWord_1502166 prefixEnd_1502166 771333180841875002316671 := by
  unfold tailWord_1502166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3424280942244787898309897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36525663383944404248638901 3424280942244787898309897)
  ·
    refine ⟨2568210706683590923732423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3424280942244787898309897 2568210706683590923732423)
    ·
      refine ⟨3852316060025386385598635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2568210706683590923732423 3852316060025386385598635)
      ·
        refine ⟨5778474090038079578397953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3852316060025386385598635 5778474090038079578397953)
        ·
          refine ⟨4333855567528559683798465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5778474090038079578397953 4333855567528559683798465)
          ·
            refine ⟨3250391675646419762848849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4333855567528559683798465 3250391675646419762848849)
            ·
              refine ⟨2437793756734814822136637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3250391675646419762848849 2437793756734814822136637)
              ·
                refine ⟨914172658775555558301239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2437793756734814822136637 914172658775555558301239)
                ·
                  refine ⟨1371258988163333337451859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 914172658775555558301239 1371258988163333337451859)
                  ·
                    refine ⟨2056888482245000006177789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1371258988163333337451859 2056888482245000006177789)
                    ·
                      refine ⟨771333180841875002316671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2056888482245000006177789 771333180841875002316671)
                      ·
                        rfl

theorem cell23_1502166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_1502166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502166 prefixEnd_1502166 := by exact prefixLift 1502166
  have htrace : WordTrace (prefixWord ++ tailWord_1502166) baseStart_1502166 baseEnd_1502166 := by
    simpa [prefixWord, tailWord_1502166, baseEnd_1502166] using wordTrace_append hprefix tailTrace_1502166
  have hstable : (prefixWord ++ tailWord_1502166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502166).length < 2 ^ (prefixWord ++ tailWord_1502166).sum := by decide
  have hdescent : baseEnd_1502166 < baseStart_1502166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502168 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 1, 2, 4]
def baseStart_1502168 : Nat := 118140960795 + 1502168 * 2 ^ 59
def prefixEnd_1502168 : Nat := 4983230072969 + 3 ^ 40 * 1502168 * 2
def baseEnd_1502168 : Nat := 771334207803183994491661

theorem tailTrace_1502168 : CollatzResearch.WordTrace tailWord_1502168 prefixEnd_1502168 771334207803183994491661 := by
  unfold tailWord_1502168
  simp only [CollatzResearch.WordTrace]
  refine ⟨27394284010954680357265579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36525712014606240476354105 27394284010954680357265579)
  ·
    refine ⟨41091426016432020535898369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27394284010954680357265579 41091426016432020535898369)
    ·
      refine ⟨30818569512324015401923777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41091426016432020535898369 30818569512324015401923777)
      ·
        refine ⟨23113927134243011551442833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30818569512324015401923777 23113927134243011551442833)
        ·
          refine ⟨17335445350682258663582125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23113927134243011551442833 17335445350682258663582125)
          ·
            refine ⟨6500792006505846998843297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17335445350682258663582125 6500792006505846998843297)
            ·
              refine ⟨4875594004879385249132473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6500792006505846998843297 4875594004879385249132473)
              ·
                refine ⟨3656695503659538936849355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4875594004879385249132473 3656695503659538936849355)
                ·
                  refine ⟨5485043255489308405274033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3656695503659538936849355 5485043255489308405274033)
                  ·
                    refine ⟨4113782441616981303955525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5485043255489308405274033 4113782441616981303955525)
                    ·
                      refine ⟨771334207803183994491661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4113782441616981303955525 771334207803183994491661)
                      ·
                        rfl

theorem cell23_1502168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_1502168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502168 prefixEnd_1502168 := by exact prefixLift 1502168
  have htrace : WordTrace (prefixWord ++ tailWord_1502168) baseStart_1502168 baseEnd_1502168 := by
    simpa [prefixWord, tailWord_1502168, baseEnd_1502168] using wordTrace_append hprefix tailTrace_1502168
  have hstable : (prefixWord ++ tailWord_1502168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502168).length < 2 ^ (prefixWord ++ tailWord_1502168).sum := by decide
  have hdescent : baseEnd_1502168 < baseStart_1502168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502218 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_1502218 : Nat := 118140960795 + 1502218 * 2 ^ 59
def prefixEnd_1502218 : Nat := 4983230072969 + 3 ^ 40 * 1502218 * 2
def baseEnd_1502218 : Nat := 771359881835908798866431

theorem tailTrace_1502218 : CollatzResearch.WordTrace tailWord_1502218 prefixEnd_1502218 771359881835908798866431 := by
  unfold tailWord_1502218
  simp only [CollatzResearch.WordTrace]
  refine ⟨13697597917932054813462827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36526927781152146169234205 13697597917932054813462827)
  ·
    refine ⟨20546396876898082220194241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13697597917932054813462827 20546396876898082220194241)
    ·
      refine ⟨15409797657673561665145681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20546396876898082220194241 15409797657673561665145681)
      ·
        refine ⟨11557348243255171248859261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15409797657673561665145681 11557348243255171248859261)
        ·
          refine ⟨4334005591220689218322223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11557348243255171248859261 4334005591220689218322223)
          ·
            refine ⟨6501008386831033827483335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4334005591220689218322223 6501008386831033827483335)
            ·
              refine ⟨9751512580246550741225003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6501008386831033827483335 9751512580246550741225003)
              ·
                refine ⟨14627268870369826111837505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9751512580246550741225003 14627268870369826111837505)
                ·
                  refine ⟨10970451652777369583878129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14627268870369826111837505 10970451652777369583878129)
                  ·
                    refine ⟨8227838739583027187908597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10970451652777369583878129 8227838739583027187908597)
                    ·
                      refine ⟨771359881835908798866431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8227838739583027187908597 771359881835908798866431)
                      ·
                        rfl

theorem cell23_1502218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_1502218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502218 prefixEnd_1502218 := by exact prefixLift 1502218
  have htrace : WordTrace (prefixWord ++ tailWord_1502218) baseStart_1502218 baseEnd_1502218 := by
    simpa [prefixWord, tailWord_1502218, baseEnd_1502218] using wordTrace_append hprefix tailTrace_1502218
  have hstable : (prefixWord ++ tailWord_1502218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502218).length < 2 ^ (prefixWord ++ tailWord_1502218).sum := by decide
  have hdescent : baseEnd_1502218 < baseStart_1502218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502232 : List Nat := [2, 1, 2, 3, 2, 2, 2, 3, 1, 3, 2]
def baseStart_1502232 : Nat := 118140960795 + 1502232 * 2 ^ 59
def prefixEnd_1502232 : Nat := 4983230072969 + 3 ^ 40 * 1502232 * 2
def baseEnd_1502232 : Nat := 771367070565071744091367

theorem tailTrace_1502232 : CollatzResearch.WordTrace tailWord_1502232 prefixEnd_1502232 771367070565071744091367 := by
  unfold tailWord_1502232
  simp only [CollatzResearch.WordTrace]
  refine ⟨27395451146838749822430475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36527268195784999763240633 27395451146838749822430475)
  ·
    refine ⟨41093176720258124733645713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27395451146838749822430475 41093176720258124733645713)
    ·
      refine ⟨30819882540193593550234285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41093176720258124733645713 30819882540193593550234285)
      ·
        refine ⟨11557455952572597581337857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30819882540193593550234285 11557455952572597581337857)
        ·
          refine ⟨8668091964429448186003393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11557455952572597581337857 8668091964429448186003393)
          ·
            refine ⟨6501068973322086139502545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8668091964429448186003393 6501068973322086139502545)
            ·
              refine ⟨4875801729991564604626909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6501068973322086139502545 4875801729991564604626909)
              ·
                refine ⟨1828425648746836726735091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4875801729991564604626909 1828425648746836726735091)
                ·
                  refine ⟨2742638473120255090102637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828425648746836726735091 2742638473120255090102637)
                  ·
                    refine ⟨1028489427420095658788489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2742638473120255090102637 1028489427420095658788489)
                    ·
                      refine ⟨771367070565071744091367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1028489427420095658788489 771367070565071744091367)
                      ·
                        rfl

theorem cell23_1502232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_1502232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502232 prefixEnd_1502232 := by exact prefixLift 1502232
  have htrace : WordTrace (prefixWord ++ tailWord_1502232) baseStart_1502232 baseEnd_1502232 := by
    simpa [prefixWord, tailWord_1502232, baseEnd_1502232] using wordTrace_append hprefix tailTrace_1502232
  have hstable : (prefixWord ++ tailWord_1502232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502232).length < 2 ^ (prefixWord ++ tailWord_1502232).sum := by decide
  have hdescent : baseEnd_1502232 < baseStart_1502232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502258 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_1502258 : Nat := 118140960795 + 1502258 * 2 ^ 59
def prefixEnd_1502258 : Nat := 4983230072969 + 3 ^ 40 * 1502258 * 2
def baseEnd_1502258 : Nat := 771380421062088642366247

theorem tailTrace_1502258 : CollatzResearch.WordTrace tailWord_1502258 prefixEnd_1502258 771380421062088642366247 := by
  unfold tailWord_1502258
  simp only [CollatzResearch.WordTrace]
  refine ⟨13697962647895826521326857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36527900394388870723538285 13697962647895826521326857)
  ·
    refine ⟨10273471985921869890995143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13697962647895826521326857 10273471985921869890995143)
    ·
      refine ⟨15410207978882804836492715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10273471985921869890995143 15410207978882804836492715)
      ·
        refine ⟨23115311968324207254739073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15410207978882804836492715 23115311968324207254739073)
        ·
          refine ⟨17336483976243155441054305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23115311968324207254739073 17336483976243155441054305)
          ·
            refine ⟨13002362982182366580790729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17336483976243155441054305 13002362982182366580790729)
            ·
              refine ⟨9751772236636774935593047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13002362982182366580790729 9751772236636774935593047)
              ·
                refine ⟨14627658354955162403389571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9751772236636774935593047 14627658354955162403389571)
                ·
                  refine ⟨21941487532432743605084357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14627658354955162403389571 21941487532432743605084357)
                  ·
                    refine ⟨4114028912331139425953317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21941487532432743605084357 4114028912331139425953317)
                    ·
                      refine ⟨771380421062088642366247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4114028912331139425953317 771380421062088642366247)
                      ·
                        rfl

theorem cell23_1502258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_1502258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502258 prefixEnd_1502258 := by exact prefixLift 1502258
  have htrace : WordTrace (prefixWord ++ tailWord_1502258) baseStart_1502258 baseEnd_1502258 := by
    simpa [prefixWord, tailWord_1502258, baseEnd_1502258] using wordTrace_append hprefix tailTrace_1502258
  have hstable : (prefixWord ++ tailWord_1502258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502258).length < 2 ^ (prefixWord ++ tailWord_1502258).sum := by decide
  have hdescent : baseEnd_1502258 < baseStart_1502258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502298 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 4, 5]
def baseStart_1502298 : Nat := 118140960795 + 1502298 * 2 ^ 59
def prefixEnd_1502298 : Nat := 4983230072969 + 3 ^ 40 * 1502298 * 2
def baseEnd_1502298 : Nat := 257133653429422828622021

theorem tailTrace_1502298 : CollatzResearch.WordTrace tailWord_1502298 prefixEnd_1502298 257133653429422828622021 := by
  unfold tailWord_1502298
  simp only [CollatzResearch.WordTrace]
  refine ⟨13698327377859598229190887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36528873007625595277842365 13698327377859598229190887)
  ·
    refine ⟨20547491066789397343786331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13698327377859598229190887 20547491066789397343786331)
    ·
      refine ⟨30821236600184096015679497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20547491066789397343786331 30821236600184096015679497)
      ·
        refine ⟨23115927450138072011759623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30821236600184096015679497 23115927450138072011759623)
        ·
          refine ⟨34673891175207108017639435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23115927450138072011759623 34673891175207108017639435)
          ·
            refine ⟨52010836762810662026459153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34673891175207108017639435 52010836762810662026459153)
            ·
              refine ⟨39008127572107996519844365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52010836762810662026459153 39008127572107996519844365)
              ·
                refine ⟨14628047839540498694941637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39008127572107996519844365 14628047839540498694941637)
                ·
                  refine ⟨2742758969913843505301557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14628047839540498694941637 2742758969913843505301557)
                  ·
                    refine ⟨257133653429422828622021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2742758969913843505301557 257133653429422828622021)
                    ·
                      rfl

theorem cell23_1502298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_1502298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502298 prefixEnd_1502298 := by exact prefixLift 1502298
  have htrace : WordTrace (prefixWord ++ tailWord_1502298) baseStart_1502298 baseEnd_1502298 := by
    simpa [prefixWord, tailWord_1502298, baseEnd_1502298] using wordTrace_append hprefix tailTrace_1502298
  have hstable : (prefixWord ++ tailWord_1502298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502298).length < 2 ^ (prefixWord ++ tailWord_1502298).sum := by decide
  have hdescent : baseEnd_1502298 < baseStart_1502298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502305 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 2, 5, 2]
def baseStart_1502305 : Nat := 118140960795 + 1502305 * 2 ^ 59
def prefixEnd_1502305 : Nat := 4983230072969 + 3 ^ 40 * 1502305 * 2
def baseEnd_1502305 : Nat := 771404554652849958478531

theorem tailTrace_1502305 : CollatzResearch.WordTrace tailWord_1502305 prefixEnd_1502305 771404554652849958478531 := by
  unfold tailWord_1502305
  simp only [CollatzResearch.WordTrace]
  refine ⟨54793564822413033112268369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36529043214942022074845579 54793564822413033112268369)
  ·
    refine ⟨41095173616809774834201277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54793564822413033112268369 41095173616809774834201277)
    ·
      refine ⟨15410690106303665562825479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41095173616809774834201277 15410690106303665562825479)
      ·
        refine ⟨23116035159455498344238219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15410690106303665562825479 23116035159455498344238219)
        ·
          refine ⟨34674052739183247516357329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23116035159455498344238219 34674052739183247516357329)
          ·
            refine ⟨26005539554387435637267997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34674052739183247516357329 26005539554387435637267997)
            ·
              refine ⟨9752077332895288363975499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26005539554387435637267997 9752077332895288363975499)
              ·
                refine ⟨14628115999342932545963249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9752077332895288363975499 14628115999342932545963249)
                ·
                  refine ⟨10971086999507199409472437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14628115999342932545963249 10971086999507199409472437)
                  ·
                    refine ⟨1028539406203799944638041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10971086999507199409472437 1028539406203799944638041)
                    ·
                      refine ⟨771404554652849958478531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1028539406203799944638041 771404554652849958478531)
                      ·
                        rfl

theorem cell23_1502305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_1502305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502305 prefixEnd_1502305 := by exact prefixLift 1502305
  have htrace : WordTrace (prefixWord ++ tailWord_1502305) baseStart_1502305 baseEnd_1502305 := by
    simpa [prefixWord, tailWord_1502305, baseEnd_1502305] using wordTrace_append hprefix tailTrace_1502305
  have hstable : (prefixWord ++ tailWord_1502305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502305).length < 2 ^ (prefixWord ++ tailWord_1502305).sum := by decide
  have hdescent : baseEnd_1502305 < baseStart_1502305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502348 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 1, 6, 4]
def baseStart_1502348 : Nat := 118140960795 + 1502348 * 2 ^ 59
def prefixEnd_1502348 : Nat := 4983230072969 + 3 ^ 40 * 1502348 * 2
def baseEnd_1502348 : Nat := 771426634320993290240833

theorem tailTrace_1502348 : CollatzResearch.WordTrace tailWord_1502348 prefixEnd_1502348 771426634320993290240833 := by
  unfold tailWord_1502348
  simp only [CollatzResearch.WordTrace]
  refine ⟨27397566580628625728041849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36530088774171500970722465 27397566580628625728041849)
  ·
    refine ⟨20548174935471469296031387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27397566580628625728041849 20548174935471469296031387)
    ·
      refine ⟨30822262403207203944047081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20548174935471469296031387 30822262403207203944047081)
      ·
        refine ⟨23116696802405402958035311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30822262403207203944047081 23116696802405402958035311)
        ·
          refine ⟨34675045203608104437052967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23116696802405402958035311 34675045203608104437052967)
          ·
            refine ⟨52012567805412156655579451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34675045203608104437052967 52012567805412156655579451)
            ·
              refine ⟨78018851708118234983369177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52012567805412156655579451 78018851708118234983369177)
              ·
                refine ⟨58514138781088676237526883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78018851708118234983369177 58514138781088676237526883)
                ·
                  refine ⟨87771208171633014356290325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58514138781088676237526883 87771208171633014356290325)
                  ·
                    refine ⟨4114275383045297547951109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87771208171633014356290325 4114275383045297547951109)
                    ·
                      refine ⟨771426634320993290240833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4114275383045297547951109 771426634320993290240833)
                      ·
                        rfl

theorem cell23_1502348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_1502348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502348 prefixEnd_1502348 := by exact prefixLift 1502348
  have htrace : WordTrace (prefixWord ++ tailWord_1502348) baseStart_1502348 baseEnd_1502348 := by
    simpa [prefixWord, tailWord_1502348, baseEnd_1502348] using wordTrace_append hprefix tailTrace_1502348
  have hstable : (prefixWord ++ tailWord_1502348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502348).length < 2 ^ (prefixWord ++ tailWord_1502348).sum := by decide
  have hdescent : baseEnd_1502348 < baseStart_1502348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502355 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 3]
def baseStart_1502355 : Nat := 118140960795 + 1502355 * 2 ^ 59
def prefixEnd_1502355 : Nat := 4983230072969 + 3 ^ 40 * 1502355 * 2
def baseEnd_1502355 : Nat := 771430228685574762853301

theorem tailTrace_1502355 : CollatzResearch.WordTrace tailWord_1502355 prefixEnd_1502355 771430228685574762853301 := by
  unfold tailWord_1502355
  simp only [CollatzResearch.WordTrace]
  refine ⟨54795388472231891651588519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36530258981487927767725679 54795388472231891651588519)
  ·
    refine ⟨82193082708347837477382779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54795388472231891651588519 82193082708347837477382779)
    ·
      refine ⟨123289624062521756216074169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82193082708347837477382779 123289624062521756216074169)
      ·
        refine ⟨92467218046891317162055627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123289624062521756216074169 92467218046891317162055627)
        ·
          refine ⟨138700827070336975743083441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92467218046891317162055627 138700827070336975743083441)
          ·
            refine ⟨104025620302752731807312581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138700827070336975743083441 104025620302752731807312581)
            ·
              refine ⟨19504803806766137213871109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104025620302752731807312581 19504803806766137213871109)
              ·
                refine ⟨3657150713768650727600833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19504803806766137213871109 3657150713768650727600833)
                ·
                  refine ⟨2742863035326488045700625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3657150713768650727600833 2742863035326488045700625)
                  ·
                    refine ⟨2057147276494866034275469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2742863035326488045700625 2057147276494866034275469)
                    ·
                      refine ⟨771430228685574762853301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2057147276494866034275469 771430228685574762853301)
                      ·
                        rfl

theorem cell23_1502355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 3].length) (baseStart_1502355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502355 prefixEnd_1502355 := by exact prefixLift 1502355
  have htrace : WordTrace (prefixWord ++ tailWord_1502355) baseStart_1502355 baseEnd_1502355 := by
    simpa [prefixWord, tailWord_1502355, baseEnd_1502355] using wordTrace_append hprefix tailTrace_1502355
  have hstable : (prefixWord ++ tailWord_1502355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502355).length < 2 ^ (prefixWord ++ tailWord_1502355).sum := by decide
  have hdescent : baseEnd_1502355 < baseStart_1502355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502362 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 3, 4]
def baseStart_1502362 : Nat := 118140960795 + 1502362 * 2 ^ 59
def prefixEnd_1502362 : Nat := 4983230072969 + 3 ^ 40 * 1502362 * 2
def baseEnd_1502362 : Nat := 257144607683385411821923

theorem tailTrace_1502362 : CollatzResearch.WordTrace tailWord_1502362 prefixEnd_1502362 257144607683385411821923 := by
  unfold tailWord_1502362
  simp only [CollatzResearch.WordTrace]
  refine ⟨13698910945801632961773335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36530429188804354564728893 13698910945801632961773335)
  ·
    refine ⟨20548366418702449442660003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13698910945801632961773335 20548366418702449442660003)
    ·
      refine ⟨30822549628053674163990005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20548366418702449442660003 30822549628053674163990005)
      ·
        refine ⟨2889614027630031952874063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30822549628053674163990005 2889614027630031952874063)
        ·
          refine ⟨4334421041445047929311095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2889614027630031952874063 4334421041445047929311095)
          ·
            refine ⟨6501631562167571893966643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4334421041445047929311095 6501631562167571893966643)
            ·
              refine ⟨9752447343251357840949965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6501631562167571893966643 9752447343251357840949965)
              ·
                refine ⟨3657167753719259190356237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9752447343251357840949965 3657167753719259190356237)
                ·
                  refine ⟨1371437907644722196383589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3657167753719259190356237 1371437907644722196383589)
                  ·
                    refine ⟨257144607683385411821923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1371437907644722196383589 257144607683385411821923)
                    ·
                      rfl

theorem cell23_1502362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_1502362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502362 prefixEnd_1502362 := by exact prefixLift 1502362
  have htrace : WordTrace (prefixWord ++ tailWord_1502362) baseStart_1502362 baseEnd_1502362 := by
    simpa [prefixWord, tailWord_1502362, baseEnd_1502362] using wordTrace_append hprefix tailTrace_1502362
  have hstable : (prefixWord ++ tailWord_1502362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502362).length < 2 ^ (prefixWord ++ tailWord_1502362).sum := by decide
  have hdescent : baseEnd_1502362 < baseStart_1502362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502396 : List Nat := [2, 2, 2, 3, 2, 3, 1, 3, 1, 4]
def baseStart_1502396 : Nat := 118140960795 + 1502396 * 2 ^ 59
def prefixEnd_1502396 : Nat := 4983230072969 + 3 ^ 40 * 1502396 * 2
def baseEnd_1502396 : Nat := 257150427130803034146871

theorem tailTrace_1502396 : CollatzResearch.WordTrace tailWord_1502396 prefixEnd_1502396 257150427130803034146871 := by
  unfold tailWord_1502396
  simp only [CollatzResearch.WordTrace]
  refine ⟨27398441932541677826915521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36531255910055570435887361 27398441932541677826915521)
  ·
    refine ⟨20548831449406258370186641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27398441932541677826915521 20548831449406258370186641)
    ·
      refine ⟨15411623587054693777639981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20548831449406258370186641 15411623587054693777639981)
      ·
        refine ⟨5779358845145510166614993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15411623587054693777639981 5779358845145510166614993)
        ·
          refine ⟨4334519133859132624961245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5779358845145510166614993 4334519133859132624961245)
          ·
            refine ⟨1625444675197174734360467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4334519133859132624961245 1625444675197174734360467)
            ·
              refine ⟨2438167012795762101540701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1625444675197174734360467 2438167012795762101540701)
              ·
                refine ⟨914312629798410788077763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2438167012795762101540701 914312629798410788077763)
                ·
                  refine ⟨1371468944697616182116645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 914312629798410788077763 1371468944697616182116645)
                  ·
                    refine ⟨257150427130803034146871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1371468944697616182116645 257150427130803034146871)
                    ·
                      rfl

theorem cell23_1502396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_1502396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502396 prefixEnd_1502396 := by exact prefixLift 1502396
  have htrace : WordTrace (prefixWord ++ tailWord_1502396) baseStart_1502396 baseEnd_1502396 := by
    simpa [prefixWord, tailWord_1502396, baseEnd_1502396] using wordTrace_append hprefix tailTrace_1502396
  have hstable : (prefixWord ++ tailWord_1502396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502396).length < 2 ^ (prefixWord ++ tailWord_1502396).sum := by decide
  have hdescent : baseEnd_1502396 < baseStart_1502396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502413 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_1502413 : Nat := 118140960795 + 1502413 * 2 ^ 59
def prefixEnd_1502413 : Nat := 4983230072969 + 3 ^ 40 * 1502413 * 2
def baseEnd_1502413 : Nat := 257153336854511845309345

theorem tailTrace_1502413 : CollatzResearch.WordTrace tailWord_1502413 prefixEnd_1502413 257153336854511845309345 := by
  unfold tailWord_1502413
  simp only [CollatzResearch.WordTrace]
  refine ⟨54797503906021767557199893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36531669270681178371466595 54797503906021767557199893)
  ·
    refine ⟨2568632995594770354243745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54797503906021767557199893 2568632995594770354243745)
    ·
      refine ⟨1926474746696077765682809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2568632995594770354243745 1926474746696077765682809)
      ·
        refine ⟨1444856060022058324262107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1926474746696077765682809 1444856060022058324262107)
        ·
          refine ⟨2167284090033087486393161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1444856060022058324262107 2167284090033087486393161)
          ·
            refine ⟨1625463067524815614794871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2167284090033087486393161 1625463067524815614794871)
            ·
              refine ⟨2438194601287223422192307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1625463067524815614794871 2438194601287223422192307)
              ·
                refine ⟨3657291901930835133288461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2438194601287223422192307 3657291901930835133288461)
                ·
                  refine ⟨1371484463224063174983173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3657291901930835133288461 1371484463224063174983173)
                  ·
                    refine ⟨257153336854511845309345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1371484463224063174983173 257153336854511845309345)
                    ·
                      rfl

theorem cell23_1502413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_1502413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502413 prefixEnd_1502413 := by exact prefixLift 1502413
  have htrace : WordTrace (prefixWord ++ tailWord_1502413) baseStart_1502413 baseEnd_1502413 := by
    simpa [prefixWord, tailWord_1502413, baseEnd_1502413] using wordTrace_append hprefix tailTrace_1502413
  have hstable : (prefixWord ++ tailWord_1502413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502413).length < 2 ^ (prefixWord ++ tailWord_1502413).sum := by decide
  have hdescent : baseEnd_1502413 < baseStart_1502413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502425 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 3, 1, 4]
def baseStart_1502425 : Nat := 118140960795 + 1502425 * 2 ^ 59
def prefixEnd_1502425 : Nat := 4983230072969 + 3 ^ 40 * 1502425 * 2
def baseEnd_1502425 : Nat := 771466172331389488977979

theorem tailTrace_1502425 : CollatzResearch.WordTrace tailWord_1502425 prefixEnd_1502425 771466172331389488977979 := by
  unfold tailWord_1502425
  simp only [CollatzResearch.WordTrace]
  refine ⟨54797941581978293606636729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36531961054652195737757819 54797941581978293606636729)
  ·
    refine ⟨41098456186483720204977547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54797941581978293606636729 41098456186483720204977547)
    ·
      refine ⟨61647684279725580307466321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41098456186483720204977547 61647684279725580307466321)
      ·
        refine ⟨46235763209794185230599741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61647684279725580307466321 46235763209794185230599741)
        ·
          refine ⟨17338411203672819461474903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46235763209794185230599741 17338411203672819461474903)
          ·
            refine ⟨26007616805509229192212355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17338411203672819461474903 26007616805509229192212355)
            ·
              refine ⟨39011425208263843788318533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26007616805509229192212355 39011425208263843788318533)
              ·
                refine ⟨7314642226549470710309725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39011425208263843788318533 7314642226549470710309725)
                ·
                  refine ⟨2742990834956051516366147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7314642226549470710309725 2742990834956051516366147)
                  ·
                    refine ⟨4114486252434077274549221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2742990834956051516366147 4114486252434077274549221)
                    ·
                      refine ⟨771466172331389488977979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4114486252434077274549221 771466172331389488977979)
                      ·
                        rfl

theorem cell23_1502425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_1502425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502425 prefixEnd_1502425 := by exact prefixLift 1502425
  have htrace : WordTrace (prefixWord ++ tailWord_1502425) baseStart_1502425 baseEnd_1502425 := by
    simpa [prefixWord, tailWord_1502425, baseEnd_1502425] using wordTrace_append hprefix tailTrace_1502425
  have hstable : (prefixWord ++ tailWord_1502425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502425).length < 2 ^ (prefixWord ++ tailWord_1502425).sum := by decide
  have hdescent : baseEnd_1502425 < baseStart_1502425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502442 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_1502442 : Nat := 118140960795 + 1502442 * 2 ^ 59
def prefixEnd_1502442 : Nat := 4983230072969 + 3 ^ 40 * 1502442 * 2
def baseEnd_1502442 : Nat := 771474901502515922465401

theorem tailTrace_1502442 : CollatzResearch.WordTrace tailWord_1502442 prefixEnd_1502442 771474901502515922465401 := by
  unfold tailWord_1502442
  simp only [CollatzResearch.WordTrace]
  refine ⟨13699640405729176377501395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36532374415277803673337053 13699640405729176377501395)
  ·
    refine ⟨20549460608593764566252093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13699640405729176377501395 20549460608593764566252093)
    ·
      refine ⟨7706047728222661712344535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20549460608593764566252093 7706047728222661712344535)
      ·
        refine ⟨11559071592333992568516803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7706047728222661712344535 11559071592333992568516803)
        ·
          refine ⟨17338607388500988852775205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11559071592333992568516803 17338607388500988852775205)
          ·
            refine ⟨3250988885343935409895351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17338607388500988852775205 3250988885343935409895351)
            ·
              refine ⟨4876483328015903114843027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3250988885343935409895351 4876483328015903114843027)
              ·
                refine ⟨7314724992023854672264541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4876483328015903114843027 7314724992023854672264541)
                ·
                  refine ⟨2743021872008945502099203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7314724992023854672264541 2743021872008945502099203)
                  ·
                    refine ⟨4114532808013418253148805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2743021872008945502099203 4114532808013418253148805)
                    ·
                      refine ⟨771474901502515922465401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4114532808013418253148805 771474901502515922465401)
                      ·
                        rfl

theorem cell23_1502442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_1502442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502442 prefixEnd_1502442 := by exact prefixLift 1502442
  have htrace : WordTrace (prefixWord ++ tailWord_1502442) baseStart_1502442 baseEnd_1502442 := by
    simpa [prefixWord, tailWord_1502442, baseEnd_1502442] using wordTrace_append hprefix tailTrace_1502442
  have hstable : (prefixWord ++ tailWord_1502442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502442).length < 2 ^ (prefixWord ++ tailWord_1502442).sum := by decide
  have hdescent : baseEnd_1502442 < baseStart_1502442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502455 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 4]
def baseStart_1502455 : Nat := 118140960795 + 1502455 * 2 ^ 59
def prefixEnd_1502455 : Nat := 4983230072969 + 3 ^ 40 * 1502455 * 2
def baseEnd_1502455 : Nat := 771481576751024371602841

theorem tailTrace_1502455 : CollatzResearch.WordTrace tailWord_1502455 prefixEnd_1502455 771481576751024371602841 := by
  unfold tailWord_1502455
  simp only [CollatzResearch.WordTrace]
  refine ⟨54799035771869608730228819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36532690514579739153485879 54799035771869608730228819)
  ·
    refine ⟨82198553657804413095343229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54799035771869608730228819 82198553657804413095343229)
    ·
      refine ⟨30824457621676654910753711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82198553657804413095343229 30824457621676654910753711)
      ·
        refine ⟨46236686432514982366130567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30824457621676654910753711 46236686432514982366130567)
        ·
          refine ⟨69355029648772473549195851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46236686432514982366130567 69355029648772473549195851)
          ·
            refine ⟨104032544473158710323793777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69355029648772473549195851 104032544473158710323793777)
            ·
              refine ⟨78024408354869032742845333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104032544473158710323793777 78024408354869032742845333)
              ·
                refine ⟨3657394141634485909820875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78024408354869032742845333 3657394141634485909820875)
                ·
                  refine ⟨5486091212451728864731313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3657394141634485909820875 5486091212451728864731313)
                  ·
                    refine ⟨4114568409338796648548485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5486091212451728864731313 4114568409338796648548485)
                    ·
                      refine ⟨771481576751024371602841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4114568409338796648548485 771481576751024371602841)
                      ·
                        rfl

theorem cell23_1502455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_1502455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1502455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1502455 prefixEnd_1502455 := by exact prefixLift 1502455
  have htrace : WordTrace (prefixWord ++ tailWord_1502455) baseStart_1502455 baseEnd_1502455 := by
    simpa [prefixWord, tailWord_1502455, baseEnd_1502455] using wordTrace_append hprefix tailTrace_1502455
  have hstable : (prefixWord ++ tailWord_1502455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502455).length < 2 ^ (prefixWord ++ tailWord_1502455).sum := by decide
  have hdescent : baseEnd_1502455 < baseStart_1502455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
