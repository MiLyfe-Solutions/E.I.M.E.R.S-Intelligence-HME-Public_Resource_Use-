import V185TrunkScan23Chunk1059

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6274685 : List Nat := [1, 4, 1, 1, 4, 1, 4, 1, 6]
def baseStart_6274685 : Nat := 118140960795 + 6274685 * 2 ^ 59
def prefixEnd_6274685 : Nat := 4983230072969 + 3 ^ 40 * 6274685 * 2
def baseEnd_6274685 : Nat := 357992151172987555531195

theorem tailTrace_6274685 : CollatzResearch.WordTrace tailWord_6274685 prefixEnd_6274685 357992151172987555531195 := by
  unfold tailWord_6274685
  simp only [CollatzResearch.WordTrace]
  refine ⟨228856563272895350726217509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152571042181930233817478339 228856563272895350726217509)
  ·
    refine ⟨42910605613667878261165783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228856563272895350726217509 42910605613667878261165783)
    ·
      refine ⟨64365908420501817391748675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42910605613667878261165783 64365908420501817391748675)
      ·
        refine ⟨96548862630752726087623013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64365908420501817391748675 96548862630752726087623013)
        ·
          refine ⟨18102911743266136141429315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96548862630752726087623013 18102911743266136141429315)
          ·
            refine ⟨27154367614899204212143973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18102911743266136141429315 27154367614899204212143973)
            ·
              refine ⟨5091443927793600789776995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27154367614899204212143973 5091443927793600789776995)
              ·
                refine ⟨7637165891690401184665493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5091443927793600789776995 7637165891690401184665493)
                ·
                  refine ⟨357992151172987555531195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7637165891690401184665493 357992151172987555531195)
                  ·
                    rfl

theorem cell23_6274685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_6274685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274685 prefixEnd_6274685 := by exact prefixLift 6274685
  have htrace : WordTrace (prefixWord ++ tailWord_6274685) baseStart_6274685 baseEnd_6274685 := by
    simpa [prefixWord, tailWord_6274685, baseEnd_6274685] using wordTrace_append hprefix tailTrace_6274685
  have hstable : (prefixWord ++ tailWord_6274685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274685).length < 2 ^ (prefixWord ++ tailWord_6274685).sum := by decide
  have hdescent : baseEnd_6274685 < baseStart_6274685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274738 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_6274738 : Nat := 118140960795 + 6274738 * 2 ^ 59
def prefixEnd_6274738 : Nat := 4983230072969 + 3 ^ 40 * 6274738 * 2
def baseEnd_6274738 : Nat := 3221956575031576292418011

theorem tailTrace_6274738 : CollatzResearch.WordTrace tailWord_6274738 prefixEnd_6274738 3221956575031576292418011 := by
  unfold tailWord_6274738
  simp only [CollatzResearch.WordTrace]
  refine ⟨57214624085425835194474217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152572330894468893851931245 57214624085425835194474217)
  ·
    refine ⟨42910968064069376395855663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57214624085425835194474217 42910968064069376395855663)
    ·
      refine ⟨64366452096104064593783495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42910968064069376395855663 64366452096104064593783495)
      ·
        refine ⟨96549678144156096890675243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64366452096104064593783495 96549678144156096890675243)
        ·
          refine ⟨144824517216234145336012865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96549678144156096890675243 144824517216234145336012865)
          ·
            refine ⟨108618387912175609002009649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144824517216234145336012865 108618387912175609002009649)
            ·
              refine ⟨81463790934131706751507237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108618387912175609002009649 81463790934131706751507237)
              ·
                refine ⟨15274460800149695015907607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81463790934131706751507237 15274460800149695015907607)
                ·
                  refine ⟨22911691200224542523861411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15274460800149695015907607 22911691200224542523861411)
                  ·
                    refine ⟨34367536800336813785792117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22911691200224542523861411 34367536800336813785792117)
                    ·
                      refine ⟨3221956575031576292418011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34367536800336813785792117 3221956575031576292418011)
                      ·
                        rfl

theorem cell23_6274738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_6274738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274738 prefixEnd_6274738 := by exact prefixLift 6274738
  have htrace : WordTrace (prefixWord ++ tailWord_6274738) baseStart_6274738 baseEnd_6274738 := by
    simpa [prefixWord, tailWord_6274738, baseEnd_6274738] using wordTrace_append hprefix tailTrace_6274738
  have hstable : (prefixWord ++ tailWord_6274738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274738).length < 2 ^ (prefixWord ++ tailWord_6274738).sum := by decide
  have hdescent : baseEnd_6274738 < baseStart_6274738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274745 : List Nat := [1, 2, 1, 4, 1, 1, 4, 3, 2, 4]
def baseStart_6274745 : Nat := 118140960795 + 6274745 * 2 ^ 59
def prefixEnd_6274745 : Nat := 4983230072969 + 3 ^ 40 * 6274745 * 2
def baseEnd_6274745 : Nat := 1073986723132052588343493

theorem tailTrace_6274745 : CollatzResearch.WordTrace tailWord_6274745 prefixEnd_6274745 1073986723132052588343493 := by
  unfold tailWord_6274745
  simp only [CollatzResearch.WordTrace]
  refine ⟨228858751652677980973401689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152572501101785320648934459 228858751652677980973401689)
  ·
    refine ⟨171644063739508485730051267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228858751652677980973401689 171644063739508485730051267)
    ·
      refine ⟨257466095609262728595076901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171644063739508485730051267 257466095609262728595076901)
      ·
        refine ⟨48274892926736761611576919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257466095609262728595076901 48274892926736761611576919)
        ·
          refine ⟨72412339390105142417365379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48274892926736761611576919 72412339390105142417365379)
          ·
            refine ⟨108618509085157713626048069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72412339390105142417365379 108618509085157713626048069)
            ·
              refine ⟨20365970453467071304884013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108618509085157713626048069 20365970453467071304884013)
              ·
                refine ⟨7637238920050151739331505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20365970453467071304884013 7637238920050151739331505)
                ·
                  refine ⟨5727929190037613804498629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7637238920050151739331505 5727929190037613804498629)
                  ·
                    refine ⟨1073986723132052588343493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5727929190037613804498629 1073986723132052588343493)
                    ·
                      rfl

theorem cell23_6274745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 4].length) (baseStart_6274745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274745 prefixEnd_6274745 := by exact prefixLift 6274745
  have htrace : WordTrace (prefixWord ++ tailWord_6274745) baseStart_6274745 baseEnd_6274745 := by
    simpa [prefixWord, tailWord_6274745, baseEnd_6274745] using wordTrace_append hprefix tailTrace_6274745
  have hstable : (prefixWord ++ tailWord_6274745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274745).length < 2 ^ (prefixWord ++ tailWord_6274745).sum := by decide
  have hdescent : baseEnd_6274745 < baseStart_6274745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274752 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 3, 2, 2]
def baseStart_6274752 : Nat := 118140960795 + 6274752 * 2 ^ 59
def prefixEnd_6274752 : Nat := 4983230072969 + 3 ^ 40 * 6274752 * 2
def baseEnd_6274752 : Nat := 3221963763760739237642947

theorem tailTrace_6274752 : CollatzResearch.WordTrace tailWord_6274752 prefixEnd_6274752 3221963763760739237642947 := by
  unfold tailWord_6274752
  simp only [CollatzResearch.WordTrace]
  refine ⟨114429503481826310584453255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152572671309101747445937673 114429503481826310584453255)
  ·
    refine ⟨171644255222739465876679883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114429503481826310584453255 171644255222739465876679883)
    ·
      refine ⟨257466382834109198815019825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171644255222739465876679883 257466382834109198815019825)
      ·
        refine ⟨193099787125581899111264869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257466382834109198815019825 193099787125581899111264869)
        ·
          refine ⟨36206210086046606083362163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193099787125581899111264869 36206210086046606083362163)
          ·
            refine ⟨54309315129069909125043245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36206210086046606083362163 54309315129069909125043245)
            ·
              refine ⟨20365993173401215921891217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54309315129069909125043245 20365993173401215921891217)
              ·
                refine ⟨15274494880050911941418413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20365993173401215921891217 15274494880050911941418413)
                ·
                  refine ⟨5727935580019091978031905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15274494880050911941418413 5727935580019091978031905)
                  ·
                    refine ⟨4295951685014318983523929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5727935580019091978031905 4295951685014318983523929)
                    ·
                      refine ⟨3221963763760739237642947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4295951685014318983523929 3221963763760739237642947)
                      ·
                        rfl

theorem cell23_6274752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 3, 2, 2].length) (baseStart_6274752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274752 prefixEnd_6274752 := by exact prefixLift 6274752
  have htrace : WordTrace (prefixWord ++ tailWord_6274752) baseStart_6274752 baseEnd_6274752 := by
    simpa [prefixWord, tailWord_6274752, baseEnd_6274752] using wordTrace_append hprefix tailTrace_6274752
  have hstable : (prefixWord ++ tailWord_6274752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274752).length < 2 ^ (prefixWord ++ tailWord_6274752).sum := by decide
  have hdescent : baseEnd_6274752 < baseStart_6274752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274768 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 3]
def baseStart_6274768 : Nat := 118140960795 + 6274768 * 2 ^ 59
def prefixEnd_6274768 : Nat := 4983230072969 + 3 ^ 40 * 6274768 * 2
def baseEnd_6274768 : Nat := 3221971979451211175042873

theorem tailTrace_6274768 : CollatzResearch.WordTrace tailWord_6274768 prefixEnd_6274768 3221971979451211175042873 := by
  unfold tailWord_6274768
  simp only [CollatzResearch.WordTrace]
  refine ⟨114429795265797327950744479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152573060354396437267659305 114429795265797327950744479)
  ·
    refine ⟨171644692898695991926116719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114429795265797327950744479 171644692898695991926116719)
    ·
      refine ⟨257467039348043987889175079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171644692898695991926116719 257467039348043987889175079)
      ·
        refine ⟨386200559022065981833762619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257467039348043987889175079 386200559022065981833762619)
        ·
          refine ⟨579300838533098972750643929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386200559022065981833762619 579300838533098972750643929)
          ·
            refine ⟨434475628899824229562982947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 579300838533098972750643929 434475628899824229562982947)
            ·
              refine ⟨651713443349736344344474421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434475628899824229562982947 651713443349736344344474421)
              ·
                refine ⟨61098135314037782282294477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 651713443349736344344474421 61098135314037782282294477)
                ·
                  refine ⟨22911800742764168355860429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61098135314037782282294477 22911800742764168355860429)
                  ·
                    refine ⟨8591925278536563133447661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22911800742764168355860429 8591925278536563133447661)
                    ·
                      refine ⟨3221971979451211175042873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8591925278536563133447661 3221971979451211175042873)
                      ·
                        rfl

theorem cell23_6274768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 3].length) (baseStart_6274768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274768 prefixEnd_6274768 := by exact prefixLift 6274768
  have htrace : WordTrace (prefixWord ++ tailWord_6274768) baseStart_6274768 baseEnd_6274768 := by
    simpa [prefixWord, tailWord_6274768, baseEnd_6274768] using wordTrace_append hprefix tailTrace_6274768
  have hstable : (prefixWord ++ tailWord_6274768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274768).length < 2 ^ (prefixWord ++ tailWord_6274768).sum := by decide
  have hdescent : baseEnd_6274768 < baseStart_6274768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274769 : List Nat := [1, 2, 2, 1, 2, 4, 1, 5, 1, 2, 2]
def baseStart_6274769 : Nat := 118140960795 + 6274769 * 2 ^ 59
def prefixEnd_6274769 : Nat := 4983230072969 + 3 ^ 40 * 6274769 * 2
def baseEnd_6274769 : Nat := 3221972492931865671130369

theorem tailTrace_6274769 : CollatzResearch.WordTrace tailWord_6274769 prefixEnd_6274769 3221972492931865671130369 := by
  unfold tailWord_6274769
  simp only [CollatzResearch.WordTrace]
  refine ⟨228859627004591033072275361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152573084669727355381516907 228859627004591033072275361)
  ·
    refine ⟨171644720253443274804206521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228859627004591033072275361 171644720253443274804206521)
    ·
      refine ⟨128733540190082456103154891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171644720253443274804206521 128733540190082456103154891)
      ·
        refine ⟨193100310285123684154732337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128733540190082456103154891 193100310285123684154732337)
        ·
          refine ⟨144825232713842763116049253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193100310285123684154732337 144825232713842763116049253)
          ·
            refine ⟨27154731133845518084259235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144825232713842763116049253 27154731133845518084259235)
            ·
              refine ⟨40732096700768277126388853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27154731133845518084259235 40732096700768277126388853)
              ·
                refine ⟨3818634065697025980598955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40732096700768277126388853 3818634065697025980598955)
                ·
                  refine ⟨5727951098545538970898433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3818634065697025980598955 5727951098545538970898433)
                  ·
                    refine ⟨4295963323909154228173825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5727951098545538970898433 4295963323909154228173825)
                    ·
                      refine ⟨3221972492931865671130369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4295963323909154228173825 3221972492931865671130369)
                      ·
                        rfl

theorem cell23_6274769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 1, 2, 2].length) (baseStart_6274769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274769 prefixEnd_6274769 := by exact prefixLift 6274769
  have htrace : WordTrace (prefixWord ++ tailWord_6274769) baseStart_6274769 baseEnd_6274769 := by
    simpa [prefixWord, tailWord_6274769, baseEnd_6274769] using wordTrace_append hprefix tailTrace_6274769
  have hstable : (prefixWord ++ tailWord_6274769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274769).length < 2 ^ (prefixWord ++ tailWord_6274769).sum := by decide
  have hdescent : baseEnd_6274769 < baseStart_6274769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274795 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 5, 3, 2]
def baseStart_6274795 : Nat := 118140960795 + 6274795 * 2 ^ 59
def prefixEnd_6274795 : Nat := 4983230072969 + 3 ^ 40 * 6274795 * 2
def baseEnd_6274795 : Nat := 3221985843428882569405249

theorem tailTrace_6274795 : CollatzResearch.WordTrace tailWord_6274795 prefixEnd_6274795 3221985843428882569405249 := by
  unfold tailWord_6274795
  simp only [CollatzResearch.WordTrace]
  refine ⟨228860575302496839512721839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152573716868331226341814559 228860575302496839512721839)
  ·
    refine ⟨343290862953745259269082759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228860575302496839512721839 343290862953745259269082759)
    ·
      refine ⟨514936294430617888903624139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343290862953745259269082759 514936294430617888903624139)
      ·
        refine ⟨772404441645926833355436209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514936294430617888903624139 772404441645926833355436209)
        ·
          refine ⟨579303331234445125016577157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 772404441645926833355436209 579303331234445125016577157)
          ·
            refine ⟨108619374606458460940608217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 579303331234445125016577157 108619374606458460940608217)
            ·
              refine ⟨81464530954843845705456163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108619374606458460940608217 81464530954843845705456163)
              ·
                refine ⟨122196796432265768558184245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81464530954843845705456163 122196796432265768558184245)
                ·
                  refine ⟨11455949665524915802329773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122196796432265768558184245 11455949665524915802329773)
                  ·
                    refine ⟨4295981124571843425873665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11455949665524915802329773 4295981124571843425873665)
                    ·
                      refine ⟨3221985843428882569405249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4295981124571843425873665 3221985843428882569405249)
                      ·
                        rfl

theorem cell23_6274795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 3, 2].length) (baseStart_6274795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274795 prefixEnd_6274795 := by exact prefixLift 6274795
  have htrace : WordTrace (prefixWord ++ tailWord_6274795) baseStart_6274795 baseEnd_6274795 := by
    simpa [prefixWord, tailWord_6274795, baseEnd_6274795] using wordTrace_append hprefix tailTrace_6274795
  have hstable : (prefixWord ++ tailWord_6274795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274795).length < 2 ^ (prefixWord ++ tailWord_6274795).sum := by decide
  have hdescent : baseEnd_6274795 < baseStart_6274795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274825 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 3, 4, 2]
def baseStart_6274825 : Nat := 118140960795 + 6274825 * 2 ^ 59
def prefixEnd_6274825 : Nat := 4983230072969 + 3 ^ 40 * 6274825 * 2
def baseEnd_6274825 : Nat := 3222001247848517452030111

theorem tailTrace_6274825 : CollatzResearch.WordTrace tailWord_6274825 prefixEnd_6274825 3222001247848517452030111 := by
  unfold tailWord_6274825
  simp only [CollatzResearch.WordTrace]
  refine ⟨228861669492388154636313929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152574446328258769757542619 228861669492388154636313929)
  ·
    refine ⟨171646252119291115977235447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228861669492388154636313929 171646252119291115977235447)
    ·
      refine ⟨257469378178936673965853171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171646252119291115977235447 257469378178936673965853171)
      ·
        refine ⟨386204067268405010948779757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257469378178936673965853171 386204067268405010948779757)
        ·
          refine ⟨144826525225651879105792409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386204067268405010948779757 144826525225651879105792409)
          ·
            refine ⟨108619893919238909329344307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144826525225651879105792409 108619893919238909329344307)
            ·
              refine ⟨162929840878858363994016461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108619893919238909329344307 162929840878858363994016461)
              ·
                refine ⟨61098690329571886497756173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162929840878858363994016461 61098690329571886497756173)
                ·
                  refine ⟨22912008873589457436658565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61098690329571886497756173 22912008873589457436658565)
                  ·
                    refine ⟨4296001663798023269373481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22912008873589457436658565 4296001663798023269373481)
                    ·
                      refine ⟨3222001247848517452030111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4296001663798023269373481 3222001247848517452030111)
                      ·
                        rfl

theorem cell23_6274825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 4, 2].length) (baseStart_6274825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274825 prefixEnd_6274825 := by exact prefixLift 6274825
  have htrace : WordTrace (prefixWord ++ tailWord_6274825) baseStart_6274825 baseEnd_6274825 := by
    simpa [prefixWord, tailWord_6274825, baseEnd_6274825] using wordTrace_append hprefix tailTrace_6274825
  have hstable : (prefixWord ++ tailWord_6274825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274825).length < 2 ^ (prefixWord ++ tailWord_6274825).sum := by decide
  have hdescent : baseEnd_6274825 < baseStart_6274825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274828 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 1, 3, 5]
def baseStart_6274828 : Nat := 118140960795 + 6274828 * 2 ^ 59
def prefixEnd_6274828 : Nat := 4983230072969 + 3 ^ 40 * 6274828 * 2
def baseEnd_6274828 : Nat := 3222002788290480940292597

theorem tailTrace_6274828 : CollatzResearch.WordTrace tailWord_6274828 prefixEnd_6274828 3222002788290480940292597 := by
  unfold tailWord_6274828
  simp only [CollatzResearch.WordTrace]
  refine ⟨114430889455688643074336569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152574519274251524099115425 114430889455688643074336569)
  ·
    refine ⟨85823167091766482305752427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114430889455688643074336569 85823167091766482305752427)
    ·
      refine ⟨128734750637649723458628641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85823167091766482305752427 128734750637649723458628641)
      ·
        refine ⟨96551062978237292593971481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128734750637649723458628641 96551062978237292593971481)
        ·
          refine ⟨72413297233677969445478611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96551062978237292593971481 72413297233677969445478611)
          ·
            refine ⟨108619945850516954168217917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72413297233677969445478611 108619945850516954168217917)
            ·
              refine ⟨40732479693943857813081719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108619945850516954168217917 40732479693943857813081719)
              ·
                refine ⟨61098719540915786719622579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40732479693943857813081719 61098719540915786719622579)
                ·
                  refine ⟨91648079311373680079433869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61098719540915786719622579 91648079311373680079433869)
                  ·
                    refine ⟨34368029741765130029787701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91648079311373680079433869 34368029741765130029787701)
                    ·
                      refine ⟨3222002788290480940292597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34368029741765130029787701 3222002788290480940292597)
                      ·
                        rfl

theorem cell23_6274828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_6274828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274828 prefixEnd_6274828 := by exact prefixLift 6274828
  have htrace : WordTrace (prefixWord ++ tailWord_6274828) baseStart_6274828 baseEnd_6274828 := by
    simpa [prefixWord, tailWord_6274828, baseEnd_6274828] using wordTrace_append hprefix tailTrace_6274828
  have hstable : (prefixWord ++ tailWord_6274828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274828).length < 2 ^ (prefixWord ++ tailWord_6274828).sum := by decide
  have hdescent : baseEnd_6274828 < baseStart_6274828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274893 : List Nat := [1, 6, 1, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_6274893 : Nat := 118140960795 + 6274893 * 2 ^ 59
def prefixEnd_6274893 : Nat := 4983230072969 + 3 ^ 40 * 6274893 * 2
def baseEnd_6274893 : Nat := 3222036164533023185979799

theorem tailTrace_6274893 : CollatzResearch.WordTrace tailWord_6274893 prefixEnd_6274893 3222036164533023185979799 := by
  unfold tailWord_6274893
  simp only [CollatzResearch.WordTrace]
  refine ⟨228864149656141802249789333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152576099770761201499859555 228864149656141802249789333)
  ·
    refine ⟨10728007015131646980458875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 228864149656141802249789333 10728007015131646980458875)
    ·
      refine ⟨16092010522697470470688313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10728007015131646980458875 16092010522697470470688313)
      ·
        refine ⟨12069007892023102853016235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16092010522697470470688313 12069007892023102853016235)
        ·
          refine ⟨18103511838034654279524353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12069007892023102853016235 18103511838034654279524353)
          ·
            refine ⟨13577633878525990709643265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18103511838034654279524353 13577633878525990709643265)
            ·
              refine ⟨10183225408894493032232449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13577633878525990709643265 10183225408894493032232449)
              ·
                refine ⟨7637419056670869774174337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10183225408894493032232449 7637419056670869774174337)
                ·
                  refine ⟨5728064292503152330630753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7637419056670869774174337 5728064292503152330630753)
                  ·
                    refine ⟨4296048219377364247973065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5728064292503152330630753 4296048219377364247973065)
                    ·
                      refine ⟨3222036164533023185979799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4296048219377364247973065 3222036164533023185979799)
                      ·
                        rfl

theorem cell23_6274893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_6274893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274893 prefixEnd_6274893 := by exact prefixLift 6274893
  have htrace : WordTrace (prefixWord ++ tailWord_6274893) baseStart_6274893 baseEnd_6274893 := by
    simpa [prefixWord, tailWord_6274893, baseEnd_6274893] using wordTrace_append hprefix tailTrace_6274893
  have hstable : (prefixWord ++ tailWord_6274893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274893).length < 2 ^ (prefixWord ++ tailWord_6274893).sum := by decide
  have hdescent : baseEnd_6274893 < baseStart_6274893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274992 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 8, 3, 2]
def baseStart_6274992 : Nat := 118140960795 + 6274992 * 2 ^ 59
def prefixEnd_6274992 : Nat := 4983230072969 + 3 ^ 40 * 6274992 * 2
def baseEnd_6274992 : Nat := 3222086999117818298641843

theorem tailTrace_6274992 : CollatzResearch.WordTrace tailWord_6274992 prefixEnd_6274992 3222086999117818298641843 := by
  unfold tailWord_6274992
  simp only [CollatzResearch.WordTrace]
  refine ⟨114433880241391571078821615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152578506988522094771762153 114433880241391571078821615)
  ·
    refine ⟨171650820362087356618232423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114433880241391571078821615 171650820362087356618232423)
    ·
      refine ⟨257476230543131034927348635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171650820362087356618232423 257476230543131034927348635)
      ·
        refine ⟨386214345814696552391022953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257476230543131034927348635 386214345814696552391022953)
        ·
          refine ⟨289660759361022414293267215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386214345814696552391022953 289660759361022414293267215)
          ·
            refine ⟨434491139041533621439900823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289660759361022414293267215 434491139041533621439900823)
            ·
              refine ⟨651736708562300432159851235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434491139041533621439900823 651736708562300432159851235)
              ·
                refine ⟨977605062843450648239776853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651736708562300432159851235 977605062843450648239776853)
                ·
                  refine ⟨11456309330196687284059885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 977605062843450648239776853 11456309330196687284059885)
                  ·
                    refine ⟨4296115998823757731522457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11456309330196687284059885 4296115998823757731522457)
                    ·
                      refine ⟨3222086999117818298641843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4296115998823757731522457 3222086999117818298641843)
                      ·
                        rfl

theorem cell23_6274992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 8, 3, 2].length) (baseStart_6274992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274992 prefixEnd_6274992 := by exact prefixLift 6274992
  have htrace : WordTrace (prefixWord ++ tailWord_6274992) baseStart_6274992 baseEnd_6274992 := by
    simpa [prefixWord, tailWord_6274992, baseEnd_6274992] using wordTrace_append hprefix tailTrace_6274992
  have hstable : (prefixWord ++ tailWord_6274992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274992).length < 2 ^ (prefixWord ++ tailWord_6274992).sum := by decide
  have hdescent : baseEnd_6274992 < baseStart_6274992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275016 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 3, 1, 3]
def baseStart_6275016 : Nat := 118140960795 + 6275016 * 2 ^ 59
def prefixEnd_6275016 : Nat := 4983230072969 + 3 ^ 40 * 6275016 * 2
def baseEnd_6275016 : Nat := 3222099322653526204741733

theorem tailTrace_6275016 : CollatzResearch.WordTrace tailWord_6275016 prefixEnd_6275016 3222099322653526204741733 := by
  unfold tailWord_6275016
  simp only [CollatzResearch.WordTrace]
  refine ⟨114434317917348097128258451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152579090556464129504344601 114434317917348097128258451)
  ·
    refine ⟨171651476876022145692387677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114434317917348097128258451 171651476876022145692387677)
    ·
      refine ⟨64369303828508304634645379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171651476876022145692387677 64369303828508304634645379)
      ·
        refine ⟨96553955742762456951968069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64369303828508304634645379 96553955742762456951968069)
        ·
          refine ⟨18103866701767960678494013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96553955742762456951968069 18103866701767960678494013)
          ·
            refine ⟨6788950013162985254435255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18103866701767960678494013 6788950013162985254435255)
            ·
              refine ⟨10183425019744477881652883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6788950013162985254435255 10183425019744477881652883)
              ·
                refine ⟨15275137529616716822479325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10183425019744477881652883 15275137529616716822479325)
                ·
                  refine ⟨5728176573606268808429747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15275137529616716822479325 5728176573606268808429747)
                  ·
                    refine ⟨8592264860409403212644621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5728176573606268808429747 8592264860409403212644621)
                    ·
                      refine ⟨3222099322653526204741733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8592264860409403212644621 3222099322653526204741733)
                      ·
                        rfl

theorem cell23_6275016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_6275016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275016 prefixEnd_6275016 := by exact prefixLift 6275016
  have htrace : WordTrace (prefixWord ++ tailWord_6275016) baseStart_6275016 baseEnd_6275016 := by
    simpa [prefixWord, tailWord_6275016, baseEnd_6275016] using wordTrace_append hprefix tailTrace_6275016
  have hstable : (prefixWord ++ tailWord_6275016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275016).length < 2 ^ (prefixWord ++ tailWord_6275016).sum := by decide
  have hdescent : baseEnd_6275016 < baseStart_6275016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275022 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_6275022 : Nat := 118140960795 + 6275022 * 2 ^ 59
def prefixEnd_6275022 : Nat := 4983230072969 + 3 ^ 40 * 6275022 * 2
def baseEnd_6275022 : Nat := 3222102403537453181266705

theorem tailTrace_6275022 : CollatzResearch.WordTrace tailWord_6275022 prefixEnd_6275022 3222102403537453181266705 := by
  unfold tailWord_6275022
  simp only [CollatzResearch.WordTrace]
  refine ⟨28608606834084307160154415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152579236448449638187490213 28608606834084307160154415)
  ·
    refine ⟨42912910251126460740231623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28608606834084307160154415 42912910251126460740231623)
    ·
      refine ⟨64369365376689691110347435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42912910251126460740231623 64369365376689691110347435)
      ·
        refine ⟨96554048065034536665521153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64369365376689691110347435 96554048065034536665521153)
        ·
          refine ⟨72415536048775902499140865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96554048065034536665521153 72415536048775902499140865)
          ·
            refine ⟨54311652036581926874355649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72415536048775902499140865 54311652036581926874355649)
            ·
              refine ⟨40733739027436445155766737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54311652036581926874355649 40733739027436445155766737)
              ·
                refine ⟨30550304270577333866825053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40733739027436445155766737 30550304270577333866825053)
                ·
                  refine ⟨11456364101466500200059395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30550304270577333866825053 11456364101466500200059395)
                  ·
                    refine ⟨17184546152199750300089093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11456364101466500200059395 17184546152199750300089093)
                    ·
                      refine ⟨3222102403537453181266705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17184546152199750300089093 3222102403537453181266705)
                      ·
                        rfl

theorem cell23_6275022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_6275022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275022 prefixEnd_6275022 := by exact prefixLift 6275022
  have htrace : WordTrace (prefixWord ++ tailWord_6275022) baseStart_6275022 baseEnd_6275022 := by
    simpa [prefixWord, tailWord_6275022, baseEnd_6275022] using wordTrace_append hprefix tailTrace_6275022
  have hstable : (prefixWord ++ tailWord_6275022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275022).length < 2 ^ (prefixWord ++ tailWord_6275022).sum := by decide
  have hdescent : baseEnd_6275022 < baseStart_6275022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275025 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 3, 1, 5]
def baseStart_6275025 : Nat := 118140960795 + 6275025 * 2 ^ 59
def prefixEnd_6275025 : Nat := 4983230072969 + 3 ^ 40 * 6275025 * 2
def baseEnd_6275025 : Nat := 3222103943979416669529191

theorem tailTrace_6275025 : CollatzResearch.WordTrace tailWord_6275025 prefixEnd_6275025 3222103943979416669529191 := by
  unfold tailWord_6275025
  simp only [CollatzResearch.WordTrace]
  refine ⟨228868964091663588793594529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152579309394442392529063019 228868964091663588793594529)
  ·
    refine ⟨171651723068747691595195897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228868964091663588793594529 171651723068747691595195897)
    ·
      refine ⟨128738792301560768696396923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171651723068747691595195897 128738792301560768696396923)
      ·
        refine ⟨193108188452341153044595385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128738792301560768696396923 193108188452341153044595385)
        ·
          refine ⟨144831141339255864783446539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193108188452341153044595385 144831141339255864783446539)
          ·
            refine ⟨217246712008883797175169809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144831141339255864783446539 217246712008883797175169809)
            ·
              refine ⟨162935034006662847881377357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217246712008883797175169809 162935034006662847881377357)
              ·
                refine ⟨61100637752498567955516509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162935034006662847881377357 61100637752498567955516509)
                ·
                  refine ⟨22912739157186962983318691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61100637752498567955516509 22912739157186962983318691)
                  ·
                    refine ⟨34369108735780444474978037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22912739157186962983318691 34369108735780444474978037)
                    ·
                      refine ⟨3222103943979416669529191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34369108735780444474978037 3222103943979416669529191)
                      ·
                        rfl

theorem cell23_6275025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_6275025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275025 prefixEnd_6275025 := by exact prefixLift 6275025
  have htrace : WordTrace (prefixWord ++ tailWord_6275025) baseStart_6275025 baseEnd_6275025 := by
    simpa [prefixWord, tailWord_6275025, baseEnd_6275025] using wordTrace_append hprefix tailTrace_6275025
  have hstable : (prefixWord ++ tailWord_6275025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275025).length < 2 ^ (prefixWord ++ tailWord_6275025).sum := by decide
  have hdescent : baseEnd_6275025 < baseStart_6275025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275039 : List Nat := [1, 1, 2, 3, 4, 1, 3, 2, 1, 1, 4]
def baseStart_6275039 : Nat := 118140960795 + 6275039 * 2 ^ 59
def prefixEnd_6275039 : Nat := 4983230072969 + 3 ^ 40 * 6275039 * 2
def baseEnd_6275039 : Nat := 3222111132708579614754127

theorem tailTrace_6275039 : CollatzResearch.WordTrace tailWord_6275039 prefixEnd_6275039 3222111132708579614754127 := by
  unfold tailWord_6275039
  simp only [CollatzResearch.WordTrace]
  refine ⟨228869474713612869184604171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152579649809075246123069447 228869474713612869184604171)
  ·
    refine ⟨343304212070419303776906257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228869474713612869184604171 343304212070419303776906257)
    ·
      refine ⟨257478159052814477832679693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343304212070419303776906257 257478159052814477832679693)
      ·
        refine ⟨96554309644805429187254885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257478159052814477832679693 96554309644805429187254885)
        ·
          refine ⟨18103933058401017972610291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96554309644805429187254885 18103933058401017972610291)
          ·
            refine ⟨27155899587601526958915437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18103933058401017972610291 27155899587601526958915437)
            ·
              refine ⟨10183462345350572609593289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27155899587601526958915437 10183462345350572609593289)
              ·
                refine ⟨7637596759012929457194967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10183462345350572609593289 7637596759012929457194967)
                ·
                  refine ⟨11456395138519394185792451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7637596759012929457194967 11456395138519394185792451)
                  ·
                    refine ⟨17184592707779091278688677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11456395138519394185792451 17184592707779091278688677)
                    ·
                      refine ⟨3222111132708579614754127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17184592707779091278688677 3222111132708579614754127)
                      ·
                        rfl

theorem cell23_6275039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_6275039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275039 prefixEnd_6275039 := by exact prefixLift 6275039
  have htrace : WordTrace (prefixWord ++ tailWord_6275039) baseStart_6275039 baseEnd_6275039 := by
    simpa [prefixWord, tailWord_6275039, baseEnd_6275039] using wordTrace_append hprefix tailTrace_6275039
  have hstable : (prefixWord ++ tailWord_6275039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275039).length < 2 ^ (prefixWord ++ tailWord_6275039).sum := by decide
  have hdescent : baseEnd_6275039 < baseStart_6275039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275053 : List Nat := [1, 5, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_6275053 : Nat := 118140960795 + 6275053 * 2 ^ 59
def prefixEnd_6275053 : Nat := 4983230072969 + 3 ^ 40 * 6275053 * 2
def baseEnd_6275053 : Nat := 1074039440479247519993021

theorem tailTrace_6275053 : CollatzResearch.WordTrace tailWord_6275053 prefixEnd_6275053 1074039440479247519993021 := by
  unfold tailWord_6275053
  simp only [CollatzResearch.WordTrace]
  refine ⟨228869985335562149575613813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152579990223708099717075875 228869985335562149575613813)
  ·
    refine ⟨21456561125208951522713795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228869985335562149575613813 21456561125208951522713795)
    ·
      refine ⟨32184841687813427284070693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21456561125208951522713795 32184841687813427284070693)
      ·
        refine ⟨6034657816465017615763255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32184841687813427284070693 6034657816465017615763255)
        ·
          refine ⟨9051986724697526423644883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6034657816465017615763255 9051986724697526423644883)
          ·
            refine ⟨13577980087046289635467325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9051986724697526423644883 13577980087046289635467325)
            ·
              refine ⟨5091742532642358613300247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13577980087046289635467325 5091742532642358613300247)
              ·
                refine ⟨7637613798963537919950371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5091742532642358613300247 7637613798963537919950371)
                ·
                  refine ⟨11456420698445306879925557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7637613798963537919950371 11456420698445306879925557)
                  ·
                    refine ⟨1074039440479247519993021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11456420698445306879925557 1074039440479247519993021)
                    ·
                      rfl

theorem cell23_6275053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_6275053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275053 prefixEnd_6275053 := by exact prefixLift 6275053
  have htrace : WordTrace (prefixWord ++ tailWord_6275053) baseStart_6275053 baseEnd_6275053 := by
    simpa [prefixWord, tailWord_6275053, baseEnd_6275053] using wordTrace_append hprefix tailTrace_6275053
  have hstable : (prefixWord ++ tailWord_6275053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275053).length < 2 ^ (prefixWord ++ tailWord_6275053).sum := by decide
  have hdescent : baseEnd_6275053 < baseStart_6275053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275062 : List Nat := [5, 1, 1, 1, 4, 11]
def baseStart_6275062 : Nat := 118140960795 + 6275062 * 2 ^ 59
def prefixEnd_6275062 : Nat := 4983230072969 + 3 ^ 40 * 6275062 * 2
def baseEnd_6275062 : Nat := 13259765196558160595747

theorem tailTrace_6275062 : CollatzResearch.WordTrace tailWord_6275062 prefixEnd_6275062 13259765196558160595747 := by
  unfold tailWord_6275062
  simp only [CollatzResearch.WordTrace]
  refine ⟨14304394599533096507043215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152580209061686362741794293 14304394599533096507043215)
  ·
    refine ⟨21456591899299644760564823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14304394599533096507043215 21456591899299644760564823)
    ·
      refine ⟨32184887848949467140847235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21456591899299644760564823 32184887848949467140847235)
      ·
        refine ⟨48277331773424200711270853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32184887848949467140847235 48277331773424200711270853)
        ·
          refine ⟨9051999707517037633363285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48277331773424200711270853 9051999707517037633363285)
          ·
            refine ⟨13259765196558160595747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9051999707517037633363285 13259765196558160595747)
            ·
              rfl

theorem cell23_6275062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 11].length) (baseStart_6275062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275062 prefixEnd_6275062 := by exact prefixLift 6275062
  have htrace : WordTrace (prefixWord ++ tailWord_6275062) baseStart_6275062 baseEnd_6275062 := by
    simpa [prefixWord, tailWord_6275062, baseEnd_6275062] using wordTrace_append hprefix tailTrace_6275062
  have hstable : (prefixWord ++ tailWord_6275062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275062).length < 2 ^ (prefixWord ++ tailWord_6275062).sum := by decide
  have hdescent : baseEnd_6275062 < baseStart_6275062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275073 : List Nat := [1, 2, 4, 1, 2, 1, 3, 4, 1, 2, 2]
def baseStart_6275073 : Nat := 118140960795 + 6275073 * 2 ^ 59
def prefixEnd_6275073 : Nat := 4983230072969 + 3 ^ 40 * 6275073 * 2
def baseEnd_6275073 : Nat := 3222128591050832481728971

theorem tailTrace_6275073 : CollatzResearch.WordTrace tailWord_6275073 prefixEnd_6275073 3222128591050832481728971 := by
  unfold tailWord_6275073
  simp only [CollatzResearch.WordTrace]
  refine ⟨228870714795489692991341873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152580476530326461994227915 228870714795489692991341873)
  ·
    refine ⟨171653036096617269743506405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228870714795489692991341873 171653036096617269743506405)
    ·
      refine ⟨32184944268115738076907451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171653036096617269743506405 32184944268115738076907451)
      ·
        refine ⟨48277416402173607115361177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32184944268115738076907451 48277416402173607115361177)
        ·
          refine ⟨36208062301630205336520883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48277416402173607115361177 36208062301630205336520883)
          ·
            refine ⟨54312093452445308004781325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36208062301630205336520883 54312093452445308004781325)
            ·
              refine ⟨20367035044666990501792997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54312093452445308004781325 20367035044666990501792997)
              ·
                refine ⟨3818819070875060719086187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20367035044666990501792997 3818819070875060719086187)
                ·
                  refine ⟨5728228606312591078629281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3818819070875060719086187 5728228606312591078629281)
                  ·
                    refine ⟨4296171454734443308971961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5728228606312591078629281 4296171454734443308971961)
                    ·
                      refine ⟨3222128591050832481728971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4296171454734443308971961 3222128591050832481728971)
                      ·
                        rfl

theorem cell23_6275073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_6275073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275073 prefixEnd_6275073 := by exact prefixLift 6275073
  have htrace : WordTrace (prefixWord ++ tailWord_6275073) baseStart_6275073 baseEnd_6275073 := by
    simpa [prefixWord, tailWord_6275073, baseEnd_6275073] using wordTrace_append hprefix tailTrace_6275073
  have hstable : (prefixWord ++ tailWord_6275073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275073).length < 2 ^ (prefixWord ++ tailWord_6275073).sum := by decide
  have hdescent : baseEnd_6275073 < baseStart_6275073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275122 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 2, 6]
def baseStart_6275122 : Nat := 118140960795 + 6275122 * 2 ^ 59
def prefixEnd_6275122 : Nat := 4983230072969 + 3 ^ 40 * 6275122 * 2
def baseEnd_6275122 : Nat := 1074051250534300930005415

theorem tailTrace_6275122 : CollatzResearch.WordTrace tailWord_6275122 prefixEnd_6275122 1074051250534300930005415 := by
  unfold tailWord_6275122
  simp only [CollatzResearch.WordTrace]
  refine ⟨57218125493078043589968905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152581667981541449573250413 57218125493078043589968905)
  ·
    refine ⟨42913594119808532692476679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57218125493078043589968905 42913594119808532692476679)
    ·
      refine ⟨64370391179712799038715019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42913594119808532692476679 64370391179712799038715019)
      ·
        refine ⟨96555586769569198558072529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64370391179712799038715019 96555586769569198558072529)
        ·
          refine ⟨72416690077176898918554397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96555586769569198558072529 72416690077176898918554397)
          ·
            refine ⟨27156258778941337094457899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72416690077176898918554397 27156258778941337094457899)
            ·
              refine ⟨40734388168412005641686849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27156258778941337094457899 40734388168412005641686849)
              ·
                refine ⟨30550791126309004231265137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40734388168412005641686849 30550791126309004231265137)
                ·
                  refine ⟨22913093344731753173448853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30550791126309004231265137 22913093344731753173448853)
                  ·
                    refine ⟨1074051250534300930005415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22913093344731753173448853 1074051250534300930005415)
                    ·
                      rfl

theorem cell23_6275122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_6275122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275122 prefixEnd_6275122 := by exact prefixLift 6275122
  have htrace : WordTrace (prefixWord ++ tailWord_6275122) baseStart_6275122 baseEnd_6275122 := by
    simpa [prefixWord, tailWord_6275122, baseEnd_6275122] using wordTrace_append hprefix tailTrace_6275122
  have hstable : (prefixWord ++ tailWord_6275122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275122).length < 2 ^ (prefixWord ++ tailWord_6275122).sum := by decide
  have hdescent : baseEnd_6275122 < baseStart_6275122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275149 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_6275149 : Nat := 118140960795 + 6275149 * 2 ^ 59
def prefixEnd_6275149 : Nat := 4983230072969 + 3 ^ 40 * 6275149 * 2
def baseEnd_6275149 : Nat := 3222167615580574184378621

theorem tailTrace_6275149 : CollatzResearch.WordTrace tailWord_6275149 prefixEnd_6275149 3222167615580574184378621 := by
  unfold tailWord_6275149
  simp only [CollatzResearch.WordTrace]
  refine ⟨228873486743214357971108501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152582324495476238647405667 228873486743214357971108501)
  ·
    refine ⟨10728444691088173029895711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 228873486743214357971108501 10728444691088173029895711)
    ·
      refine ⟨16092667036632259544843567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10728444691088173029895711 16092667036632259544843567)
      ·
        refine ⟨24139000554948389317265351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16092667036632259544843567 24139000554948389317265351)
        ·
          refine ⟨36208500832422583975898027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24139000554948389317265351 36208500832422583975898027)
          ·
            refine ⟨54312751248633875963847041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36208500832422583975898027 54312751248633875963847041)
            ·
              refine ⟨40734563436475406972885281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54312751248633875963847041 40734563436475406972885281)
              ·
                refine ⟨30550922577356555229663961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40734563436475406972885281 30550922577356555229663961)
                ·
                  refine ⟨22913191933017416422247971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30550922577356555229663961 22913191933017416422247971)
                  ·
                    refine ⟨34369787899526124633371957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22913191933017416422247971 34369787899526124633371957)
                    ·
                      refine ⟨3222167615580574184378621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34369787899526124633371957 3222167615580574184378621)
                      ·
                        rfl

theorem cell23_6275149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_6275149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275149 prefixEnd_6275149 := by exact prefixLift 6275149
  have htrace : WordTrace (prefixWord ++ tailWord_6275149) baseStart_6275149 baseEnd_6275149 := by
    simpa [prefixWord, tailWord_6275149, baseEnd_6275149] using wordTrace_append hprefix tailTrace_6275149
  have hstable : (prefixWord ++ tailWord_6275149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275149).length < 2 ^ (prefixWord ++ tailWord_6275149).sum := by decide
  have hdescent : baseEnd_6275149 < baseStart_6275149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275219 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 4, 4, 2]
def baseStart_6275219 : Nat := 118140960795 + 6275219 * 2 ^ 59
def prefixEnd_6275219 : Nat := 4983230072969 + 3 ^ 40 * 6275219 * 2
def baseEnd_6275219 : Nat := 3222203559226388910503299

theorem tailTrace_6275219 : CollatzResearch.WordTrace tailWord_6275219 prefixEnd_6275219 3222203559226388910503299 := by
  unfold tailWord_6275219
  simp only [CollatzResearch.WordTrace]
  refine ⟨228876039852960759926156711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152584026568640506617437807 228876039852960759926156711)
  ·
    refine ⟨343314059779441139889235067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228876039852960759926156711 343314059779441139889235067)
    ·
      refine ⟨514971089669161709833852601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343314059779441139889235067 514971089669161709833852601)
      ·
        refine ⟨386228317251871282375389451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514971089669161709833852601 386228317251871282375389451)
        ·
          refine ⟨579342475877806923563084177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386228317251871282375389451 579342475877806923563084177)
          ·
            refine ⟨434506856908355192672313133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 579342475877806923563084177 434506856908355192672313133)
            ·
              refine ⟨162940071340633197252117425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 434506856908355192672313133 162940071340633197252117425)
              ·
                refine ⟨122205053505474897939088069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162940071340633197252117425 122205053505474897939088069)
                ·
                  refine ⟨22913447532276543363579013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122205053505474897939088069 22913447532276543363579013)
                  ·
                    refine ⟨4296271412301851880671065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22913447532276543363579013 4296271412301851880671065)
                    ·
                      refine ⟨3222203559226388910503299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4296271412301851880671065 3222203559226388910503299)
                      ·
                        rfl

theorem cell23_6275219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 4, 2].length) (baseStart_6275219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275219 prefixEnd_6275219 := by exact prefixLift 6275219
  have htrace : WordTrace (prefixWord ++ tailWord_6275219) baseStart_6275219 baseEnd_6275219 := by
    simpa [prefixWord, tailWord_6275219, baseEnd_6275219] using wordTrace_append hprefix tailTrace_6275219
  have hstable : (prefixWord ++ tailWord_6275219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275219).length < 2 ^ (prefixWord ++ tailWord_6275219).sum := by decide
  have hdescent : baseEnd_6275219 < baseStart_6275219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275293 : List Nat := [1, 4, 3, 2, 1, 3, 1, 2, 6]
def baseStart_6275293 : Nat := 118140960795 + 6275293 * 2 ^ 59
def prefixEnd_6275293 : Nat := 4983230072969 + 3 ^ 40 * 6275293 * 2
def baseEnd_6275293 : Nat := 358026839643869068997551

theorem tailTrace_6275293 : CollatzResearch.WordTrace tailWord_6275293 prefixEnd_6275293 358026839643869068997551 := by
  unfold tailWord_6275293
  simp only [CollatzResearch.WordTrace]
  refine ⟨228878738854692670564350533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152585825903128447042900355 228878738854692670564350533)
  ·
    refine ⟨42914763535254875730815725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228878738854692670564350533 42914763535254875730815725)
    ·
      refine ⟨16093036325720578399055897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42914763535254875730815725 16093036325720578399055897)
      ·
        refine ⟨12069777244290433799291923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16093036325720578399055897 12069777244290433799291923)
        ·
          refine ⟨18104665866435650698937885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12069777244290433799291923 18104665866435650698937885)
          ·
            refine ⟨6789249699913369012101707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18104665866435650698937885 6789249699913369012101707)
            ·
              refine ⟨10183874549870053518152561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6789249699913369012101707 10183874549870053518152561)
              ·
                refine ⟨7637905912402540138614421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10183874549870053518152561 7637905912402540138614421)
                ·
                  refine ⟨358026839643869068997551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7637905912402540138614421 358026839643869068997551)
                  ·
                    rfl

theorem cell23_6275293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_6275293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275293 prefixEnd_6275293 := by exact prefixLift 6275293
  have htrace : WordTrace (prefixWord ++ tailWord_6275293) baseStart_6275293 baseEnd_6275293 := by
    simpa [prefixWord, tailWord_6275293, baseEnd_6275293] using wordTrace_append hprefix tailTrace_6275293
  have hstable : (prefixWord ++ tailWord_6275293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275293).length < 2 ^ (prefixWord ++ tailWord_6275293).sum := by decide
  have hdescent : baseEnd_6275293 < baseStart_6275293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275296 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 4, 3, 2]
def baseStart_6275296 : Nat := 118140960795 + 6275296 * 2 ^ 59
def prefixEnd_6275296 : Nat := 4983230072969 + 3 ^ 40 * 6275296 * 2
def baseEnd_6275296 : Nat := 3222243097236785109240445

theorem tailTrace_6275296 : CollatzResearch.WordTrace tailWord_6275296 prefixEnd_6275296 3222243097236785109240445 := by
  unfold tailWord_6275296
  simp only [CollatzResearch.WordTrace]
  refine ⟨114439424136840901038354871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152585898849121201384473161 114439424136840901038354871)
  ·
    refine ⟨171659136205261351557532307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114439424136840901038354871 171659136205261351557532307)
    ·
      refine ⟨257488704307892027336298461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171659136205261351557532307 257488704307892027336298461)
      ·
        refine ⟨96558264115459510251111923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257488704307892027336298461 96558264115459510251111923)
        ·
          refine ⟨144837396173189265376667885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96558264115459510251111923 144837396173189265376667885)
          ·
            refine ⟨54314023564945974516250457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144837396173189265376667885 54314023564945974516250457)
            ·
              refine ⟨40735517673709480887187843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54314023564945974516250457 40735517673709480887187843)
              ·
                refine ⟨61103276510564221330781765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40735517673709480887187843 61103276510564221330781765)
                ·
                  refine ⟨11456864345730791499521581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61103276510564221330781765 11456864345730791499521581)
                  ·
                    refine ⟨4296324129649046812320593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11456864345730791499521581 4296324129649046812320593)
                    ·
                      refine ⟨3222243097236785109240445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4296324129649046812320593 3222243097236785109240445)
                      ·
                        rfl

theorem cell23_6275296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_6275296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275296 prefixEnd_6275296 := by exact prefixLift 6275296
  have htrace : WordTrace (prefixWord ++ tailWord_6275296) baseStart_6275296 baseEnd_6275296 := by
    simpa [prefixWord, tailWord_6275296, baseEnd_6275296] using wordTrace_append hprefix tailTrace_6275296
  have hstable : (prefixWord ++ tailWord_6275296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275296).length < 2 ^ (prefixWord ++ tailWord_6275296).sum := by decide
  have hdescent : baseEnd_6275296 < baseStart_6275296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275303 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_6275303 : Nat := 118140960795 + 6275303 * 2 ^ 59
def prefixEnd_6275303 : Nat := 4983230072969 + 3 ^ 40 * 6275303 * 2
def baseEnd_6275303 : Nat := 3222246691601366581852913

theorem tailTrace_6275303 : CollatzResearch.WordTrace tailWord_6275303 prefixEnd_6275303 3222246691601366581852913 := by
  unfold tailWord_6275303
  simp only [CollatzResearch.WordTrace]
  refine ⟨228879103584656442272214563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152586069056437628181476375 228879103584656442272214563)
  ·
    refine ⟨343318655376984663408321845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228879103584656442272214563 343318655376984663408321845)
    ·
      refine ⟨32186123941592312194530173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 343318655376984663408321845 32186123941592312194530173)
      ·
        refine ⟨12069796478097117072948815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32186123941592312194530173 12069796478097117072948815)
        ·
          refine ⟨18104694717145675609423223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12069796478097117072948815 18104694717145675609423223)
          ·
            refine ⟨27157042075718513414134835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18104694717145675609423223 27157042075718513414134835)
            ·
              refine ⟨40735563113577770121202253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27157042075718513414134835 40735563113577770121202253)
              ·
                refine ⟨15275836167591663795450845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40735563113577770121202253 15275836167591663795450845)
                ·
                  refine ⟨5728438562846873923294067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15275836167591663795450845 5728438562846873923294067)
                  ·
                    refine ⟨8592657844270310884941101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5728438562846873923294067 8592657844270310884941101)
                    ·
                      refine ⟨3222246691601366581852913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8592657844270310884941101 3222246691601366581852913)
                      ·
                        rfl

theorem cell23_6275303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_6275303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275303 prefixEnd_6275303 := by exact prefixLift 6275303
  have htrace : WordTrace (prefixWord ++ tailWord_6275303) baseStart_6275303 baseEnd_6275303 := by
    simpa [prefixWord, tailWord_6275303, baseEnd_6275303] using wordTrace_append hprefix tailTrace_6275303
  have hstable : (prefixWord ++ tailWord_6275303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275303).length < 2 ^ (prefixWord ++ tailWord_6275303).sum := by decide
  have hdescent : baseEnd_6275303 < baseStart_6275303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275319 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 8, 4]
def baseStart_6275319 : Nat := 118140960795 + 6275319 * 2 ^ 59
def prefixEnd_6275319 : Nat := 4983230072969 + 3 ^ 40 * 6275319 * 2
def baseEnd_6275319 : Nat := 1074084969097279506417613

theorem tailTrace_6275319 : CollatzResearch.WordTrace tailWord_6275319 prefixEnd_6275319 1074084969097279506417613 := by
  unfold tailWord_6275319
  simp only [CollatzResearch.WordTrace]
  refine ⟨228879687152598477004797011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152586458101732318003198007 228879687152598477004797011)
  ·
    refine ⟨343319530728897715507195517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228879687152598477004797011 343319530728897715507195517)
    ·
      refine ⟨128744824023336643315198319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343319530728897715507195517 128744824023336643315198319)
      ·
        refine ⟨193117236035004964972797479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128744824023336643315198319 193117236035004964972797479)
        ·
          refine ⟨289675854052507447459196219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193117236035004964972797479 289675854052507447459196219)
          ·
            refine ⟨434513781078761171188794329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289675854052507447459196219 434513781078761171188794329)
            ·
              refine ⟨325885335809070878391595747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434513781078761171188794329 325885335809070878391595747)
              ·
                refine ⟨488828003713606317587393621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325885335809070878391595747 488828003713606317587393621)
                ·
                  refine ⟨5728453168518824034227269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 488828003713606317587393621 5728453168518824034227269)
                  ·
                    refine ⟨1074084969097279506417613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5728453168518824034227269 1074084969097279506417613)
                    ·
                      rfl

theorem cell23_6275319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_6275319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275319 prefixEnd_6275319 := by exact prefixLift 6275319
  have htrace : WordTrace (prefixWord ++ tailWord_6275319) baseStart_6275319 baseEnd_6275319 := by
    simpa [prefixWord, tailWord_6275319, baseEnd_6275319] using wordTrace_append hprefix tailTrace_6275319
  have hstable : (prefixWord ++ tailWord_6275319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275319).length < 2 ^ (prefixWord ++ tailWord_6275319).sum := by decide
  have hdescent : baseEnd_6275319 < baseStart_6275319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275329 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_6275329 : Nat := 118140960795 + 6275329 * 2 ^ 59
def prefixEnd_6275329 : Nat := 4983230072969 + 3 ^ 40 * 6275329 * 2
def baseEnd_6275329 : Nat := 3222260042098383480127793

theorem tailTrace_6275329 : CollatzResearch.WordTrace tailWord_6275329 prefixEnd_6275329 3222260042098383480127793 := by
  unfold tailWord_6275329
  simp only [CollatzResearch.WordTrace]
  refine ⟨228880051882562248712661041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152586701255041499141774027 228880051882562248712661041)
  ·
    refine ⟨171660038911921686534495781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228880051882562248712661041 171660038911921686534495781)
    ·
      refine ⟨32186257295985316225217959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171660038911921686534495781 32186257295985316225217959)
      ·
        refine ⟨48279385943977974337826939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32186257295985316225217959 48279385943977974337826939)
        ·
          refine ⟨72419078915966961506740409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48279385943977974337826939 72419078915966961506740409)
          ·
            refine ⟨54314309186975221130055307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72419078915966961506740409 54314309186975221130055307)
            ·
              refine ⟨81471463780462831695082961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54314309186975221130055307 81471463780462831695082961)
              ·
                refine ⟨61103597835347123771312221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81471463780462831695082961 61103597835347123771312221)
                ·
                  refine ⟨22913849188255171414242083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61103597835347123771312221 22913849188255171414242083)
                  ·
                    refine ⟨34370773782382757121363125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22913849188255171414242083 34370773782382757121363125)
                    ·
                      refine ⟨3222260042098383480127793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34370773782382757121363125 3222260042098383480127793)
                      ·
                        rfl

theorem cell23_6275329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_6275329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275329 prefixEnd_6275329 := by exact prefixLift 6275329
  have htrace : WordTrace (prefixWord ++ tailWord_6275329) baseStart_6275329 baseEnd_6275329 := by
    simpa [prefixWord, tailWord_6275329, baseEnd_6275329] using wordTrace_append hprefix tailTrace_6275329
  have hstable : (prefixWord ++ tailWord_6275329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275329).length < 2 ^ (prefixWord ++ tailWord_6275329).sum := by decide
  have hdescent : baseEnd_6275329 < baseStart_6275329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275336 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 4, 4]
def baseStart_6275336 : Nat := 118140960795 + 6275336 * 2 ^ 59
def prefixEnd_6275336 : Nat := 4983230072969 + 3 ^ 40 * 6275336 * 2
def baseEnd_6275336 : Nat := 1074087878820988317580087

theorem tailTrace_6275336 : CollatzResearch.WordTrace tailWord_6275336 prefixEnd_6275336 1074087878820988317580087 := by
  unfold tailWord_6275336
  simp only [CollatzResearch.WordTrace]
  refine ⟨114440153596768444454082931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152586871462357925938777241 114440153596768444454082931)
  ·
    refine ⟨171660230395152666681124397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114440153596768444454082931 171660230395152666681124397)
    ·
      refine ⟨64372586398182250005421649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171660230395152666681124397 64372586398182250005421649)
      ·
        refine ⟨48279439798636687504066237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64372586398182250005421649 48279439798636687504066237)
        ·
          refine ⟨18104789924488757814024839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48279439798636687504066237 18104789924488757814024839)
          ·
            refine ⟨27157184886733136721037259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18104789924488757814024839 27157184886733136721037259)
            ·
              refine ⟨40735777330099705081555889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27157184886733136721037259 40735777330099705081555889)
              ·
                refine ⟨30551832997574778811166917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40735777330099705081555889 30551832997574778811166917)
                ·
                  refine ⟨5728468687045271027093797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30551832997574778811166917 5728468687045271027093797)
                  ·
                    refine ⟨1074087878820988317580087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5728468687045271027093797 1074087878820988317580087)
                    ·
                      rfl

theorem cell23_6275336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_6275336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275336 prefixEnd_6275336 := by exact prefixLift 6275336
  have htrace : WordTrace (prefixWord ++ tailWord_6275336) baseStart_6275336 baseEnd_6275336 := by
    simpa [prefixWord, tailWord_6275336, baseEnd_6275336] using wordTrace_append hprefix tailTrace_6275336
  have hstable : (prefixWord ++ tailWord_6275336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275336).length < 2 ^ (prefixWord ++ tailWord_6275336).sum := by decide
  have hdescent : baseEnd_6275336 < baseStart_6275336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275339 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 4]
def baseStart_6275339 : Nat := 118140960795 + 6275339 * 2 ^ 59
def prefixEnd_6275339 : Nat := 4983230072969 + 3 ^ 40 * 6275339 * 2
def baseEnd_6275339 : Nat := 3222265176904928441002747

theorem tailTrace_6275339 : CollatzResearch.WordTrace tailWord_6275339 prefixEnd_6275339 3222265176904928441002747 := by
  unfold tailWord_6275339
  simp only [CollatzResearch.WordTrace]
  refine ⟨228880416612526020420525071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152586944408350680280350047 228880416612526020420525071)
  ·
    refine ⟨343320624918789030630787607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228880416612526020420525071 343320624918789030630787607)
    ·
      refine ⟨514980937378183545946181411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343320624918789030630787607 514980937378183545946181411)
      ·
        refine ⟨772471406067275318919272117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514980937378183545946181411 772471406067275318919272117)
        ·
          refine ⟨72419194318807061148681761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 772471406067275318919272117 72419194318807061148681761)
          ·
            refine ⟨54314395739105295861511321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72419194318807061148681761 54314395739105295861511321)
            ·
              refine ⟨40735796804328971896133491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54314395739105295861511321 40735796804328971896133491)
              ·
                refine ⟨61103695206493457844200237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40735796804328971896133491 61103695206493457844200237)
                ·
                  refine ⟨22913885702435046691575089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61103695206493457844200237 22913885702435046691575089)
                  ·
                    refine ⟨17185414276826285018681317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22913885702435046691575089 17185414276826285018681317)
                    ·
                      refine ⟨3222265176904928441002747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17185414276826285018681317 3222265176904928441002747)
                      ·
                        rfl

theorem cell23_6275339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 4].length) (baseStart_6275339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275339 prefixEnd_6275339 := by exact prefixLift 6275339
  have htrace : WordTrace (prefixWord ++ tailWord_6275339) baseStart_6275339 baseEnd_6275339 := by
    simpa [prefixWord, tailWord_6275339, baseEnd_6275339] using wordTrace_append hprefix tailTrace_6275339
  have hstable : (prefixWord ++ tailWord_6275339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275339).length < 2 ^ (prefixWord ++ tailWord_6275339).sum := by decide
  have hdescent : baseEnd_6275339 < baseStart_6275339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275360 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 3, 2, 2]
def baseStart_6275360 : Nat := 118140960795 + 6275360 * 2 ^ 59
def prefixEnd_6275360 : Nat := 4983230072969 + 3 ^ 40 * 6275360 * 2
def baseEnd_6275360 : Nat := 3222275959998672858840151

theorem tailTrace_6275360 : CollatzResearch.WordTrace tailWord_6275360 prefixEnd_6275360 3222275959998672858840151 := by
  unfold tailWord_6275360
  simp only [CollatzResearch.WordTrace]
  refine ⟨114440591272724970503519767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152587455030299960671359689 114440591272724970503519767)
  ·
    refine ⟨171660886909087455755279651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114440591272724970503519767 171660886909087455755279651)
    ·
      refine ⟨257491330363631183632919477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171660886909087455755279651 257491330363631183632919477)
      ·
        refine ⟨24139812221590423465586201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 257491330363631183632919477 24139812221590423465586201)
        ·
          refine ⟨18104859166192817599189651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24139812221590423465586201 18104859166192817599189651)
          ·
            refine ⟨27157288749289226398784477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18104859166192817599189651 27157288749289226398784477)
            ·
              refine ⟨10183983280983459899544179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27157288749289226398784477 10183983280983459899544179)
              ·
                refine ⟨15275974921475189849316269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10183983280983459899544179 15275974921475189849316269)
                ·
                  refine ⟨5728490595553196193493601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15275974921475189849316269 5728490595553196193493601)
                  ·
                    refine ⟨4296367946664897145120201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5728490595553196193493601 4296367946664897145120201)
                    ·
                      refine ⟨3222275959998672858840151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4296367946664897145120201 3222275959998672858840151)
                      ·
                        rfl

theorem cell23_6275360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_6275360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275360 prefixEnd_6275360 := by exact prefixLift 6275360
  have htrace : WordTrace (prefixWord ++ tailWord_6275360) baseStart_6275360 baseEnd_6275360 := by
    simpa [prefixWord, tailWord_6275360, baseEnd_6275360] using wordTrace_append hprefix tailTrace_6275360
  have hstable : (prefixWord ++ tailWord_6275360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275360).length < 2 ^ (prefixWord ++ tailWord_6275360).sum := by decide
  have hdescent : baseEnd_6275360 < baseStart_6275360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275370 : List Nat := [3, 1, 4, 2, 2, 1, 1, 3, 2, 4]
def baseStart_6275370 : Nat := 118140960795 + 6275370 * 2 ^ 59
def prefixEnd_6275370 : Nat := 4983230072969 + 3 ^ 40 * 6275370 * 2
def baseEnd_6275370 : Nat := 1074093698268405939905035

theorem tailTrace_6275370 : CollatzResearch.WordTrace tailWord_6275370 prefixEnd_6275370 1074093698268405939905035 := by
  unfold tailWord_6275370
  simp only [CollatzResearch.WordTrace]
  refine ⟨57220386818853428178725891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152587698183609141809935709 57220386818853428178725891)
  ·
    refine ⟨85830580228280142268088837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57220386818853428178725891 85830580228280142268088837)
    ·
      refine ⟨16093233792802526675266657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85830580228280142268088837 16093233792802526675266657)
      ·
        refine ⟨12069925344601895006449993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16093233792802526675266657 12069925344601895006449993)
        ·
          refine ⟨9052444008451421254837495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12069925344601895006449993 9052444008451421254837495)
          ·
            refine ⟨13578666012677131882256243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9052444008451421254837495 13578666012677131882256243)
            ·
              refine ⟨20367999019015697823384365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13578666012677131882256243 20367999019015697823384365)
              ·
                refine ⟨7637999632130886683769137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20367999019015697823384365 7637999632130886683769137)
                ·
                  refine ⟨5728499724098165012826853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7637999632130886683769137 5728499724098165012826853)
                  ·
                    refine ⟨1074093698268405939905035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5728499724098165012826853 1074093698268405939905035)
                    ·
                      rfl

theorem cell23_6275370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_6275370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275370 prefixEnd_6275370 := by exact prefixLift 6275370
  have htrace : WordTrace (prefixWord ++ tailWord_6275370) baseStart_6275370 baseEnd_6275370 := by
    simpa [prefixWord, tailWord_6275370, baseEnd_6275370] using wordTrace_append hprefix tailTrace_6275370
  have hstable : (prefixWord ++ tailWord_6275370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275370).length < 2 ^ (prefixWord ++ tailWord_6275370).sum := by decide
  have hdescent : baseEnd_6275370 < baseStart_6275370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275376 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 6, 1, 3]
def baseStart_6275376 : Nat := 118140960795 + 6275376 * 2 ^ 59
def prefixEnd_6275376 : Nat := 4983230072969 + 3 ^ 40 * 6275376 * 2
def baseEnd_6275376 : Nat := 3222284175689144796240077

theorem tailTrace_6275376 : CollatzResearch.WordTrace tailWord_6275376 prefixEnd_6275376 3222284175689144796240077 := by
  unfold tailWord_6275376
  simp only [CollatzResearch.WordTrace]
  refine ⟨114440883056695987869810991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152587844075594650493081321 114440883056695987869810991)
  ·
    refine ⟨171661324585043981804716487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114440883056695987869810991 171661324585043981804716487)
    ·
      refine ⟨257491986877565972707074731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171661324585043981804716487 257491986877565972707074731)
      ·
        refine ⟨386237980316348959060612097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257491986877565972707074731 386237980316348959060612097)
        ·
          refine ⟨289678485237261719295459073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386237980316348959060612097 289678485237261719295459073)
          ·
            refine ⟨217258863927946289471594305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289678485237261719295459073 217258863927946289471594305)
            ·
              refine ⟨162944147945959717103695729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217258863927946289471594305 162944147945959717103695729)
              ·
                refine ⟨122208110959469787827771797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162944147945959717103695729 122208110959469787827771797)
                ·
                  refine ⟨5728505201225146304426803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122208110959469787827771797 5728505201225146304426803)
                  ·
                    refine ⟨8592757801837719456640205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5728505201225146304426803 8592757801837719456640205)
                    ·
                      refine ⟨3222284175689144796240077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8592757801837719456640205 3222284175689144796240077)
                      ·
                        rfl

theorem cell23_6275376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 6, 1, 3].length) (baseStart_6275376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275376 prefixEnd_6275376 := by exact prefixLift 6275376
  have htrace : WordTrace (prefixWord ++ tailWord_6275376) baseStart_6275376 baseEnd_6275376 := by
    simpa [prefixWord, tailWord_6275376, baseEnd_6275376] using wordTrace_append hprefix tailTrace_6275376
  have hstable : (prefixWord ++ tailWord_6275376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275376).length < 2 ^ (prefixWord ++ tailWord_6275376).sum := by decide
  have hdescent : baseEnd_6275376 < baseStart_6275376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275380 : List Nat := [2, 5, 1, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_6275380 : Nat := 118140960795 + 6275380 * 2 ^ 59
def prefixEnd_6275380 : Nat := 4983230072969 + 3 ^ 40 * 6275380 * 2
def baseEnd_6275380 : Nat := 3222286229611762780590059

theorem tailTrace_6275380 : CollatzResearch.WordTrace tailWord_6275380 prefixEnd_6275380 3222286229611762780590059 := by
  unfold tailWord_6275380
  simp only [CollatzResearch.WordTrace]
  refine ⟨114440956002688742211383797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152587941336918322948511729 114440956002688742211383797)
  ·
    refine ⟨10728839625252069582317231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114440956002688742211383797 10728839625252069582317231)
    ·
      refine ⟨16093259437878104373475847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10728839625252069582317231 16093259437878104373475847)
      ·
        refine ⟨24139889156817156560213771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16093259437878104373475847 24139889156817156560213771)
        ·
          refine ⟨36209833735225734840320657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24139889156817156560213771 36209833735225734840320657)
          ·
            refine ⟨27157375301419301130240493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36209833735225734840320657 27157375301419301130240493)
            ·
              refine ⟨10184015738032237923840185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27157375301419301130240493 10184015738032237923840185)
              ·
                refine ⟨7638011803524178442880139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10184015738032237923840185 7638011803524178442880139)
                ·
                  refine ⟨11457017705286267664320209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7638011803524178442880139 11457017705286267664320209)
                  ·
                    refine ⟨8592763278964700748240157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11457017705286267664320209 8592763278964700748240157)
                    ·
                      refine ⟨3222286229611762780590059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8592763278964700748240157 3222286229611762780590059)
                      ·
                        rfl

theorem cell23_6275380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_6275380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275380 prefixEnd_6275380 := by exact prefixLift 6275380
  have htrace : WordTrace (prefixWord ++ tailWord_6275380) baseStart_6275380 baseEnd_6275380 := by
    simpa [prefixWord, tailWord_6275380, baseEnd_6275380] using wordTrace_append hprefix tailTrace_6275380
  have hstable : (prefixWord ++ tailWord_6275380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275380).length < 2 ^ (prefixWord ++ tailWord_6275380).sum := by decide
  have hdescent : baseEnd_6275380 < baseStart_6275380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275426 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_6275426 : Nat := 118140960795 + 6275426 * 2 ^ 59
def prefixEnd_6275426 : Nat := 4983230072969 + 3 ^ 40 * 6275426 * 2
def baseEnd_6275426 : Nat := 1074103283240623200204949

theorem tailTrace_6275426 : CollatzResearch.WordTrace tailWord_6275426 prefixEnd_6275426 1074103283240623200204949 := by
  unfold tailWord_6275426
  simp only [CollatzResearch.WordTrace]
  refine ⟨57220897440802708569735533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152589059842140556185961421 57220897440802708569735533)
  ·
    refine ⟨21457836540301015713650825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57220897440802708569735533 21457836540301015713650825)
    ·
      refine ⟨16093377405225761785238119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21457836540301015713650825 16093377405225761785238119)
      ·
        refine ⟨24140066107838642677857179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16093377405225761785238119 24140066107838642677857179)
        ·
          refine ⟨36210099161757964016785769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24140066107838642677857179 36210099161757964016785769)
          ·
            refine ⟨27157574371318473012589327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36210099161757964016785769 27157574371318473012589327)
            ·
              refine ⟨40736361556977709518883991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27157574371318473012589327 40736361556977709518883991)
              ·
                refine ⟨61104542335466564278325987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40736361556977709518883991 61104542335466564278325987)
                ·
                  refine ⟨91656813503199846417488981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61104542335466564278325987 91656813503199846417488981)
                  ·
                    refine ⟨1074103283240623200204949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91656813503199846417488981 1074103283240623200204949)
                    ·
                      rfl

theorem cell23_6275426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_6275426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275426 prefixEnd_6275426 := by exact prefixLift 6275426
  have htrace : WordTrace (prefixWord ++ tailWord_6275426) baseStart_6275426 baseEnd_6275426 := by
    simpa [prefixWord, tailWord_6275426, baseEnd_6275426] using wordTrace_append hprefix tailTrace_6275426
  have hstable : (prefixWord ++ tailWord_6275426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275426).length < 2 ^ (prefixWord ++ tailWord_6275426).sum := by decide
  have hdescent : baseEnd_6275426 < baseStart_6275426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275433 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 1, 4, 2]
def baseStart_6275433 : Nat := 118140960795 + 6275433 * 2 ^ 59
def prefixEnd_6275433 : Nat := 4983230072969 + 3 ^ 40 * 6275433 * 2
def baseEnd_6275433 : Nat := 3222313444086451073227315

theorem tailTrace_6275433 : CollatzResearch.WordTrace tailWord_6275433 prefixEnd_6275433 3222313444086451073227315 := by
  unfold tailWord_6275433
  simp only [CollatzResearch.WordTrace]
  refine ⟨228883845074185474474446953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152589230049456982982964635 228883845074185474474446953)
  ·
    refine ⟨171662883805639105855835215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228883845074185474474446953 171662883805639105855835215)
    ·
      refine ⟨257494325708458658783752823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171662883805639105855835215 257494325708458658783752823)
      ·
        refine ⟨386241488562687988175629235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257494325708458658783752823 386241488562687988175629235)
        ·
          refine ⟨579362232844031982263443853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386241488562687988175629235 579362232844031982263443853)
          ·
            refine ⟨217260837316511993348791445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 579362232844031982263443853 217260837316511993348791445)
            ·
              refine ⟨10184101749211499688224599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 217260837316511993348791445 10184101749211499688224599)
              ·
                refine ⟨15276152623817249532336899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10184101749211499688224599 15276152623817249532336899)
                ·
                  refine ⟨22914228935725874298505349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15276152623817249532336899 22914228935725874298505349)
                  ·
                    refine ⟨4296417925448601430969753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22914228935725874298505349 4296417925448601430969753)
                    ·
                      refine ⟨3222313444086451073227315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4296417925448601430969753 3222313444086451073227315)
                      ·
                        rfl

theorem cell23_6275433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 4, 2].length) (baseStart_6275433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275433 prefixEnd_6275433 := by exact prefixLift 6275433
  have htrace : WordTrace (prefixWord ++ tailWord_6275433) baseStart_6275433 baseEnd_6275433 := by
    simpa [prefixWord, tailWord_6275433, baseEnd_6275433] using wordTrace_append hprefix tailTrace_6275433
  have hstable : (prefixWord ++ tailWord_6275433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275433).length < 2 ^ (prefixWord ++ tailWord_6275433).sum := by decide
  have hdescent : baseEnd_6275433 < baseStart_6275433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275449 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 7]
def baseStart_6275449 : Nat := 118140960795 + 6275449 * 2 ^ 59
def prefixEnd_6275449 : Nat := 4983230072969 + 3 ^ 40 * 6275449 * 2
def baseEnd_6275449 : Nat := 3222321659776923010627241

theorem tailTrace_6275449 : CollatzResearch.WordTrace tailWord_6275449 prefixEnd_6275449 3222321659776923010627241 := by
  unfold tailWord_6275449
  simp only [CollatzResearch.WordTrace]
  refine ⟨228884428642127509207029401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152589619094751672804686267 228884428642127509207029401)
  ·
    refine ⟨171663321481595631905272051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228884428642127509207029401 171663321481595631905272051)
    ·
      refine ⟨257494982222393447857908077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171663321481595631905272051 257494982222393447857908077)
      ·
        refine ⟨96560618333397542946715529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257494982222393447857908077 96560618333397542946715529)
        ·
          refine ⟨72420463750048157210036647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96560618333397542946715529 72420463750048157210036647)
          ·
            refine ⟨108630695625072235815054971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72420463750048157210036647 108630695625072235815054971)
            ·
              refine ⟨162946043437608353722582457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108630695625072235815054971 162946043437608353722582457)
              ·
                refine ⟨122209532578206265291936843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162946043437608353722582457 122209532578206265291936843)
                ·
                  refine ⟨183314298867309397937905265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122209532578206265291936843 183314298867309397937905265)
                  ·
                    refine ⟨137485724150482048453428949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 183314298867309397937905265 137485724150482048453428949)
                    ·
                      refine ⟨3222321659776923010627241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137485724150482048453428949 3222321659776923010627241)
                      ·
                        rfl

theorem cell23_6275449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_6275449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275449 prefixEnd_6275449 := by exact prefixLift 6275449
  have htrace : WordTrace (prefixWord ++ tailWord_6275449) baseStart_6275449 baseEnd_6275449 := by
    simpa [prefixWord, tailWord_6275449, baseEnd_6275449] using wordTrace_append hprefix tailTrace_6275449
  have hstable : (prefixWord ++ tailWord_6275449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275449).length < 2 ^ (prefixWord ++ tailWord_6275449).sum := by decide
  have hdescent : baseEnd_6275449 < baseStart_6275449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275467 : List Nat := [1, 1, 1, 1, 4, 6, 1, 2, 2, 2, 2]
def baseStart_6275467 : Nat := 118140960795 + 6275467 * 2 ^ 59
def prefixEnd_6275467 : Nat := 4983230072969 + 3 ^ 40 * 6275467 * 2
def baseEnd_6275467 : Nat := 3222330902428703940202159

theorem tailTrace_6275467 : CollatzResearch.WordTrace tailWord_6275467 prefixEnd_6275467 3222330902428703940202159 := by
  unfold tailWord_6275467
  simp only [CollatzResearch.WordTrace]
  refine ⟨228885085156062298281184655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152590056770708198854123103 228885085156062298281184655)
  ·
    refine ⟨343327627734093447421776983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228885085156062298281184655 343327627734093447421776983)
    ·
      refine ⟨514991441601140171132665475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343327627734093447421776983 514991441601140171132665475)
      ·
        refine ⟨772487162401710256698998213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514991441601140171132665475 772487162401710256698998213)
        ·
          refine ⟨144841342950320673131062165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 772487162401710256698998213 144841342950320673131062165)
          ·
            refine ⟨6789437950796281553018539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 144841342950320673131062165 6789437950796281553018539)
            ·
              refine ⟨10184156926194422329527809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6789437950796281553018539 10184156926194422329527809)
              ·
                refine ⟨7638117694645816747145857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10184156926194422329527809 7638117694645816747145857)
                ·
                  refine ⟨5728588270984362560359393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7638117694645816747145857 5728588270984362560359393)
                  ·
                    refine ⟨4296441203238271920269545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5728588270984362560359393 4296441203238271920269545)
                    ·
                      refine ⟨3222330902428703940202159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4296441203238271920269545 3222330902428703940202159)
                      ·
                        rfl

theorem cell23_6275467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 2, 2].length) (baseStart_6275467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275467 prefixEnd_6275467 := by exact prefixLift 6275467
  have htrace : WordTrace (prefixWord ++ tailWord_6275467) baseStart_6275467 baseEnd_6275467 := by
    simpa [prefixWord, tailWord_6275467, baseEnd_6275467] using wordTrace_append hprefix tailTrace_6275467
  have hstable : (prefixWord ++ tailWord_6275467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275467).length < 2 ^ (prefixWord ++ tailWord_6275467).sum := by decide
  have hdescent : baseEnd_6275467 < baseStart_6275467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275478 : List Nat := [5, 3, 1, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_6275478 : Nat := 118140960795 + 6275478 * 2 ^ 59
def prefixEnd_6275478 : Nat := 4983230072969 + 3 ^ 40 * 6275478 * 2
def baseEnd_6275478 : Nat := 3222336550715903397164609

theorem tailTrace_6275478 : CollatzResearch.WordTrace tailWord_6275478 prefixEnd_6275478 3222336550715903397164609 := by
  unfold tailWord_6275478
  simp only [CollatzResearch.WordTrace]
  refine ⟨14305342897438902947489693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152590324239348298106556725 14305342897438902947489693)
  ·
    refine ⟨5364503586539588605308635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14305342897438902947489693 5364503586539588605308635)
    ·
      refine ⟨8046755379809382907962953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5364503586539588605308635 8046755379809382907962953)
      ·
        refine ⟨6035066534857037180972215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8046755379809382907962953 6035066534857037180972215)
        ·
          refine ⟨9052599802285555771458323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6035066534857037180972215 9052599802285555771458323)
          ·
            refine ⟨13578899703428333657187485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9052599802285555771458323 13578899703428333657187485)
            ·
              refine ⟨5092087388785625121445307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13578899703428333657187485 5092087388785625121445307)
              ·
                refine ⟨7638131083178437682167961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5092087388785625121445307 7638131083178437682167961)
                ·
                  refine ⟨5728598312383828261625971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7638131083178437682167961 5728598312383828261625971)
                  ·
                    refine ⟨8592897468575742392438957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5728598312383828261625971 8592897468575742392438957)
                    ·
                      refine ⟨3222336550715903397164609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8592897468575742392438957 3222336550715903397164609)
                      ·
                        rfl

theorem cell23_6275478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_6275478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275478 prefixEnd_6275478 := by exact prefixLift 6275478
  have htrace : WordTrace (prefixWord ++ tailWord_6275478) baseStart_6275478 baseEnd_6275478 := by
    simpa [prefixWord, tailWord_6275478, baseEnd_6275478] using wordTrace_append hprefix tailTrace_6275478
  have hstable : (prefixWord ++ tailWord_6275478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275478).length < 2 ^ (prefixWord ++ tailWord_6275478).sum := by decide
  have hdescent : baseEnd_6275478 < baseStart_6275478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275506 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_6275506 : Nat := 118140960795 + 6275506 * 2 ^ 59
def prefixEnd_6275506 : Nat := 4983230072969 + 3 ^ 40 * 6275506 * 2
def baseEnd_6275506 : Nat := 3222350928174229287614479

theorem tailTrace_6275506 : CollatzResearch.WordTrace tailWord_6275506 prefixEnd_6275506 3222350928174229287614479 := by
  unfold tailWord_6275506
  simp only [CollatzResearch.WordTrace]
  refine ⟨57221626900730251985463593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152591005068614005294569581 57221626900730251985463593)
  ·
    refine ⟨42916220175547688989097695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57221626900730251985463593 42916220175547688989097695)
    ·
      refine ⟨64374330263321533483646543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42916220175547688989097695 64374330263321533483646543)
      ·
        refine ⟨96561495394982300225469815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64374330263321533483646543 96561495394982300225469815)
        ·
          refine ⟨144842243092473450338204723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96561495394982300225469815 144842243092473450338204723)
          ·
            refine ⟨217263364638710175507307085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144842243092473450338204723 217263364638710175507307085)
            ·
              refine ⟨81473761739516315815240157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217263364638710175507307085 81473761739516315815240157)
              ·
                refine ⟨30552660652318618430715059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81473761739516315815240157 30552660652318618430715059)
                ·
                  refine ⟨45828990978477927646072589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30552660652318618430715059 45828990978477927646072589)
                  ·
                    refine ⟨17185871616929222867277221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45828990978477927646072589 17185871616929222867277221)
                    ·
                      refine ⟨3222350928174229287614479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17185871616929222867277221 3222350928174229287614479)
                      ·
                        rfl

theorem cell23_6275506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_6275506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275506 prefixEnd_6275506 := by exact prefixLift 6275506
  have htrace : WordTrace (prefixWord ++ tailWord_6275506) baseStart_6275506 baseEnd_6275506 := by
    simpa [prefixWord, tailWord_6275506, baseEnd_6275506] using wordTrace_append hprefix tailTrace_6275506
  have hstable : (prefixWord ++ tailWord_6275506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275506).length < 2 ^ (prefixWord ++ tailWord_6275506).sum := by decide
  have hdescent : baseEnd_6275506 < baseStart_6275506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275560 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_6275560 : Nat := 118140960795 + 6275560 * 2 ^ 59
def prefixEnd_6275560 : Nat := 4983230072969 + 3 ^ 40 * 6275560 * 2
def baseEnd_6275560 : Nat := 3222378656129572076339231

theorem tailTrace_6275560 : CollatzResearch.WordTrace tailWord_6275560 prefixEnd_6275560 3222378656129572076339231 := by
  unfold tailWord_6275560
  simp only [CollatzResearch.WordTrace]
  refine ⟨114444238572362687582160067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152592318096483583442880089 114444238572362687582160067)
  ·
    refine ⟨171666357858544031373240101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114444238572362687582160067 171666357858544031373240101)
    ·
      refine ⟨32187442098477005882482519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171666357858544031373240101 32187442098477005882482519)
      ·
        refine ⟨48281163147715508823723779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32187442098477005882482519 48281163147715508823723779)
        ·
          refine ⟨72421744721573263235585669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48281163147715508823723779 72421744721573263235585669)
          ·
            refine ⟨13579077135294986856672313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72421744721573263235585669 13579077135294986856672313)
            ·
              refine ⟨10184307851471240142504235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13579077135294986856672313 10184307851471240142504235)
              ·
                refine ⟨15276461777206860213756353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10184307851471240142504235 15276461777206860213756353)
                ·
                  refine ⟨11457346332905145160317265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15276461777206860213756353 11457346332905145160317265)
                  ·
                    refine ⟨8593009749678858870237949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11457346332905145160317265 8593009749678858870237949)
                    ·
                      refine ⟨3222378656129572076339231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8593009749678858870237949 3222378656129572076339231)
                      ·
                        rfl

theorem cell23_6275560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_6275560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275560 prefixEnd_6275560 := by exact prefixLift 6275560
  have htrace : WordTrace (prefixWord ++ tailWord_6275560) baseStart_6275560 baseEnd_6275560 := by
    simpa [prefixWord, tailWord_6275560, baseEnd_6275560] using wordTrace_append hprefix tailTrace_6275560
  have hstable : (prefixWord ++ tailWord_6275560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275560).length < 2 ^ (prefixWord ++ tailWord_6275560).sum := by decide
  have hdescent : baseEnd_6275560 < baseStart_6275560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275597 : List Nat := [1, 7, 1, 1, 1, 1, 2, 3, 6]
def baseStart_6275597 : Nat := 118140960795 + 6275597 * 2 ^ 59
def prefixEnd_6275597 : Nat := 4983230072969 + 3 ^ 40 * 6275597 * 2
def baseEnd_6275597 : Nat := 358044183879309825730729

theorem tailTrace_6275597 : CollatzResearch.WordTrace tailWord_6275597 prefixEnd_6275597 358044183879309825730729 := by
  unfold tailWord_6275597
  simp only [CollatzResearch.WordTrace]
  refine ⟨228889826645591330483417045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152593217763727553655611363 228889826645591330483417045)
  ·
    refine ⟨5364605312006046808205087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 228889826645591330483417045 5364605312006046808205087)
    ·
      refine ⟨8046907968009070212307631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5364605312006046808205087 8046907968009070212307631)
      ·
        refine ⟨12070361952013605318461447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8046907968009070212307631 12070361952013605318461447)
        ·
          refine ⟨18105542928020407977692171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12070361952013605318461447 18105542928020407977692171)
          ·
            refine ⟨27158314392030611966538257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18105542928020407977692171 27158314392030611966538257)
            ·
              refine ⟨20368735794022958974903693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27158314392030611966538257 20368735794022958974903693)
              ·
                refine ⟨7638275922758609615588885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20368735794022958974903693 7638275922758609615588885)
                ·
                  refine ⟨358044183879309825730729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7638275922758609615588885 358044183879309825730729)
                  ·
                    rfl

theorem cell23_6275597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_6275597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275597 prefixEnd_6275597 := by exact prefixLift 6275597
  have htrace : WordTrace (prefixWord ++ tailWord_6275597) baseStart_6275597 baseEnd_6275597 := by
    simpa [prefixWord, tailWord_6275597, baseEnd_6275597] using wordTrace_append hprefix tailTrace_6275597
  have hstable : (prefixWord ++ tailWord_6275597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275597).length < 2 ^ (prefixWord ++ tailWord_6275597).sum := by decide
  have hdescent : baseEnd_6275597 < baseStart_6275597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275624 : List Nat := [2, 1, 5, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_6275624 : Nat := 118140960795 + 6275624 * 2 ^ 59
def prefixEnd_6275624 : Nat := 4983230072969 + 3 ^ 40 * 6275624 * 2
def baseEnd_6275624 : Nat := 3222411518891459825938937

theorem tailTrace_6275624 : CollatzResearch.WordTrace tailWord_6275624 prefixEnd_6275624 3222411518891459825938937 := by
  unfold tailWord_6275624
  simp only [CollatzResearch.WordTrace]
  refine ⟨114445405708246757047324963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152593874277662342729766617 114445405708246757047324963)
  ·
    refine ⟨171668108562370135570987445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114445405708246757047324963 171668108562370135570987445)
    ·
      refine ⟨16093885177722200209780073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171668108562370135570987445 16093885177722200209780073)
      ·
        refine ⟨12070413883291650157335055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16093885177722200209780073 12070413883291650157335055)
        ·
          refine ⟨18105620824937475236002583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12070413883291650157335055 18105620824937475236002583)
          ·
            refine ⟨27158431237406212854003875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18105620824937475236002583 27158431237406212854003875)
            ·
              refine ⟨40737646856109319281005813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27158431237406212854003875 40737646856109319281005813)
              ·
                refine ⟨3819154392760248682594295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40737646856109319281005813 3819154392760248682594295)
                ·
                  refine ⟨5728731589140373023891443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3819154392760248682594295 5728731589140373023891443)
                  ·
                    refine ⟨8593097383710559535837165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5728731589140373023891443 8593097383710559535837165)
                    ·
                      refine ⟨3222411518891459825938937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8593097383710559535837165 3222411518891459825938937)
                      ·
                        rfl

theorem cell23_6275624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_6275624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275624 prefixEnd_6275624 := by exact prefixLift 6275624
  have htrace : WordTrace (prefixWord ++ tailWord_6275624) baseStart_6275624 baseEnd_6275624 := by
    simpa [prefixWord, tailWord_6275624, baseEnd_6275624] using wordTrace_append hprefix tailTrace_6275624
  have hstable : (prefixWord ++ tailWord_6275624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275624).length < 2 ^ (prefixWord ++ tailWord_6275624).sum := by decide
  have hdescent : baseEnd_6275624 < baseStart_6275624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275647 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 3, 2, 2]
def baseStart_6275647 : Nat := 118140960795 + 6275647 * 2 ^ 59
def prefixEnd_6275647 : Nat := 4983230072969 + 3 ^ 40 * 6275647 * 2
def baseEnd_6275647 : Nat := 3222423328946513235951331

theorem tailTrace_6275647 : CollatzResearch.WordTrace tailWord_6275647 prefixEnd_6275647 3222423328946513235951331 := by
  unfold tailWord_6275647
  simp only [CollatzResearch.WordTrace]
  refine ⟨228891650295410189022737195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152594433530273459348491463 228891650295410189022737195)
  ·
    refine ⟨343337475443115283534105793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228891650295410189022737195 343337475443115283534105793)
    ·
      refine ⟨257503106582336462650579345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343337475443115283534105793 257503106582336462650579345)
      ·
        refine ⟨193127329936752346987934509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257503106582336462650579345 193127329936752346987934509)
        ·
          refine ⟨72422748726282130120475441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193127329936752346987934509 72422748726282130120475441)
          ·
            refine ⟨54317061544711597590356581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72422748726282130120475441 54317061544711597590356581)
            ·
              refine ⟨10184449039633424548191859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54317061544711597590356581 10184449039633424548191859)
              ·
                refine ⟨15276673559450136822287789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10184449039633424548191859 15276673559450136822287789)
                ·
                  refine ⟨5728752584793801308357921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15276673559450136822287789 5728752584793801308357921)
                  ·
                    refine ⟨4296564438595350981268441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5728752584793801308357921 4296564438595350981268441)
                    ·
                      refine ⟨3222423328946513235951331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4296564438595350981268441 3222423328946513235951331)
                      ·
                        rfl

theorem cell23_6275647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 2, 2].length) (baseStart_6275647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275647 prefixEnd_6275647 := by exact prefixLift 6275647
  have htrace : WordTrace (prefixWord ++ tailWord_6275647) baseStart_6275647 baseEnd_6275647 := by
    simpa [prefixWord, tailWord_6275647, baseEnd_6275647] using wordTrace_append hprefix tailTrace_6275647
  have hstable : (prefixWord ++ tailWord_6275647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275647).length < 2 ^ (prefixWord ++ tailWord_6275647).sum := by decide
  have hdescent : baseEnd_6275647 < baseStart_6275647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275680 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 4, 1, 3]
def baseStart_6275680 : Nat := 118140960795 + 6275680 * 2 ^ 59
def prefixEnd_6275680 : Nat := 4983230072969 + 3 ^ 40 * 6275680 * 2
def baseEnd_6275680 : Nat := 3222440273808111606838679

theorem tailTrace_6275680 : CollatzResearch.WordTrace tailWord_6275680 prefixEnd_6275680 3222440273808111606838679 := by
  unfold tailWord_6275680
  simp only [CollatzResearch.WordTrace]
  refine ⟨114446426952145317829344247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152595235936193757105792329 114446426952145317829344247)
  ·
    refine ⟨171669640428217976744016371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114446426952145317829344247 171669640428217976744016371)
    ·
      refine ⟨257504460642326965116024557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171669640428217976744016371 257504460642326965116024557)
      ·
        refine ⟨96564172740872611918509209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257504460642326965116024557 96564172740872611918509209)
        ·
          refine ⟨72423129555654458938881907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96564172740872611918509209 72423129555654458938881907)
          ·
            refine ⟨108634694333481688408322861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72423129555654458938881907 108634694333481688408322861)
            ·
              refine ⟨40738010375055633153121073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108634694333481688408322861 40738010375055633153121073)
              ·
                refine ⟨30553507781291724864840805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40738010375055633153121073 30553507781291724864840805)
                ·
                  refine ⟨5728782708992198412157651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30553507781291724864840805 5728782708992198412157651)
                  ·
                    refine ⟨8593174063488297618236477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5728782708992198412157651 8593174063488297618236477)
                    ·
                      refine ⟨3222440273808111606838679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8593174063488297618236477 3222440273808111606838679)
                      ·
                        rfl

theorem cell23_6275680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_6275680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275680 prefixEnd_6275680 := by exact prefixLift 6275680
  have htrace : WordTrace (prefixWord ++ tailWord_6275680) baseStart_6275680 baseEnd_6275680 := by
    simpa [prefixWord, tailWord_6275680, baseEnd_6275680] using wordTrace_append hprefix tailTrace_6275680
  have hstable : (prefixWord ++ tailWord_6275680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275680).length < 2 ^ (prefixWord ++ tailWord_6275680).sum := by decide
  have hdescent : baseEnd_6275680 < baseStart_6275680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275681 : List Nat := [1, 2, 3, 1, 1, 6, 1, 3, 1, 2, 2]
def baseStart_6275681 : Nat := 118140960795 + 6275681 * 2 ^ 59
def prefixEnd_6275681 : Nat := 4983230072969 + 3 ^ 40 * 6275681 * 2
def baseEnd_6275681 : Nat := 3222440787288766102926175

theorem tailTrace_6275681 : CollatzResearch.WordTrace tailWord_6275681 prefixEnd_6275681 3222440787288766102926175 := by
  unfold tailWord_6275681
  simp only [CollatzResearch.WordTrace]
  refine ⟨228892890377287012829474897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152595260251524675219649931 228892890377287012829474897)
  ·
    refine ⟨171669667782965259622106173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228892890377287012829474897 171669667782965259622106173)
    ·
      refine ⟨64376125418611972358289815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171669667782965259622106173 64376125418611972358289815)
      ·
        refine ⟨96564188127917958537434723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64376125418611972358289815 96564188127917958537434723)
        ·
          refine ⟨144846282191876937806152085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96564188127917958537434723 144846282191876937806152085)
          ·
            refine ⟨6789669477744231459663379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 144846282191876937806152085 6789669477744231459663379)
            ·
              refine ⟨10184504216616347189495069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6789669477744231459663379 10184504216616347189495069)
              ·
                refine ⟨3819189081231130196060651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10184504216616347189495069 3819189081231130196060651)
                ·
                  refine ⟨5728783621846695294090977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3819189081231130196060651 5728783621846695294090977)
                  ·
                    refine ⟨4296587716385021470568233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5728783621846695294090977 4296587716385021470568233)
                    ·
                      refine ⟨3222440787288766102926175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4296587716385021470568233 3222440787288766102926175)
                      ·
                        rfl

theorem cell23_6275681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_6275681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275681 prefixEnd_6275681 := by exact prefixLift 6275681
  have htrace : WordTrace (prefixWord ++ tailWord_6275681) baseStart_6275681 baseEnd_6275681 := by
    simpa [prefixWord, tailWord_6275681, baseEnd_6275681] using wordTrace_append hprefix tailTrace_6275681
  have hstable : (prefixWord ++ tailWord_6275681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275681).length < 2 ^ (prefixWord ++ tailWord_6275681).sum := by decide
  have hdescent : baseEnd_6275681 < baseStart_6275681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275698 : List Nat := [3, 2, 1, 2, 4, 1, 3, 2, 1, 2, 2]
def baseStart_6275698 : Nat := 118140960795 + 6275698 * 2 ^ 59
def prefixEnd_6275698 : Nat := 4983230072969 + 3 ^ 40 * 6275698 * 2
def baseEnd_6275698 : Nat := 3222449516459892536413597

theorem tailTrace_6275698 : CollatzResearch.WordTrace tailWord_6275698 prefixEnd_6275698 3222449516459892536413597 := by
  unfold tailWord_6275698
  simp only [CollatzResearch.WordTrace]
  refine ⟨57223377604556356183210937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152595673612150283155229165 57223377604556356183210937)
  ·
    refine ⟨42917533203417267137408203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57223377604556356183210937 42917533203417267137408203)
    ·
      refine ⟨64376299805125900706112305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42917533203417267137408203 64376299805125900706112305)
      ·
        refine ⟨48282224853844425529584229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64376299805125900706112305 48282224853844425529584229)
        ·
          refine ⟨9052917160095829786797043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48282224853844425529584229 9052917160095829786797043)
          ·
            refine ⟨13579375740143744680195565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9052917160095829786797043 13579375740143744680195565)
            ·
              refine ⟨5092265902553904255073337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13579375740143744680195565 5092265902553904255073337)
              ·
                refine ⟨3819199426915428191305003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5092265902553904255073337 3819199426915428191305003)
                ·
                  refine ⟨5728799140373142286957505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3819199426915428191305003 5728799140373142286957505)
                  ·
                    refine ⟨4296599355279856715218129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5728799140373142286957505 4296599355279856715218129)
                    ·
                      refine ⟨3222449516459892536413597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4296599355279856715218129 3222449516459892536413597)
                      ·
                        rfl

theorem cell23_6275698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_6275698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275698 prefixEnd_6275698 := by exact prefixLift 6275698
  have htrace : WordTrace (prefixWord ++ tailWord_6275698) baseStart_6275698 baseEnd_6275698 := by
    simpa [prefixWord, tailWord_6275698, baseEnd_6275698] using wordTrace_append hprefix tailTrace_6275698
  have hstable : (prefixWord ++ tailWord_6275698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275698).length < 2 ^ (prefixWord ++ tailWord_6275698).sum := by decide
  have hdescent : baseEnd_6275698 < baseStart_6275698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275713 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 1, 8]
def baseStart_6275713 : Nat := 118140960795 + 6275713 * 2 ^ 59
def prefixEnd_6275713 : Nat := 4983230072969 + 3 ^ 40 * 6275713 * 2
def baseEnd_6275713 : Nat := 1074152406223236659242009

theorem tailTrace_6275713 : CollatzResearch.WordTrace tailWord_6275713 prefixEnd_6275713 1074152406223236659242009 := by
  unfold tailWord_6275713
  simp only [CollatzResearch.WordTrace]
  refine ⟨228894057513171082294639793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152596038342114054863093195 228894057513171082294639793)
  ·
    refine ⟨171670543134878311720979845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228894057513171082294639793 171670543134878311720979845)
    ·
      refine ⟨32188226837789683447683721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171670543134878311720979845 32188226837789683447683721)
      ·
        refine ⟨24141170128342262585762791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32188226837789683447683721 24141170128342262585762791)
        ·
          refine ⟨36211755192513393878644187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24141170128342262585762791 36211755192513393878644187)
          ·
            refine ⟨54317632788770090817966281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36211755192513393878644187 54317632788770090817966281)
            ·
              refine ⟨40738224591577568113474711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54317632788770090817966281 40738224591577568113474711)
              ·
                refine ⟨61107336887366352170212067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40738224591577568113474711 61107336887366352170212067)
                ·
                  refine ⟨91661005331049528255318101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61107336887366352170212067 91661005331049528255318101)
                  ·
                    refine ⟨1074152406223236659242009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91661005331049528255318101 1074152406223236659242009)
                    ·
                      rfl

theorem cell23_6275713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_6275713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275713 prefixEnd_6275713 := by exact prefixLift 6275713
  have htrace : WordTrace (prefixWord ++ tailWord_6275713) baseStart_6275713 baseEnd_6275713 := by
    simpa [prefixWord, tailWord_6275713, baseEnd_6275713] using wordTrace_append hprefix tailTrace_6275713
  have hstable : (prefixWord ++ tailWord_6275713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275713).length < 2 ^ (prefixWord ++ tailWord_6275713).sum := by decide
  have hdescent : baseEnd_6275713 < baseStart_6275713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275723 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 3]
def baseStart_6275723 : Nat := 118140960795 + 6275723 * 2 ^ 59
def prefixEnd_6275723 : Nat := 4983230072969 + 3 ^ 40 * 6275723 * 2
def baseEnd_6275723 : Nat := 3222462353476254938600981

theorem tailTrace_6275723 : CollatzResearch.WordTrace tailWord_6275723 prefixEnd_6275723 3222462353476254938600981 := by
  unfold tailWord_6275723
  simp only [CollatzResearch.WordTrace]
  refine ⟨228894422243134854002503823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152596281495423236001669215 228894422243134854002503823)
  ·
    refine ⟨343341633364702281003755735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228894422243134854002503823 343341633364702281003755735)
    ·
      refine ⟨515012450047053421505633603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343341633364702281003755735 515012450047053421505633603)
      ·
        refine ⟨772518675070580132258450405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515012450047053421505633603 772518675070580132258450405)
        ·
          refine ⟨144847251575733774798459451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 772518675070580132258450405 144847251575733774798459451)
          ·
            refine ⟨217270877363600662197689177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144847251575733774798459451 217270877363600662197689177)
            ·
              refine ⟨162953158022700496648266883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217270877363600662197689177 162953158022700496648266883)
              ·
                refine ⟨244429737034050744972400325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162953158022700496648266883 244429737034050744972400325)
                ·
                  refine ⟨45830575693884514682325061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 244429737034050744972400325 45830575693884514682325061)
                  ·
                    refine ⟨8593232942603346502935949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45830575693884514682325061 8593232942603346502935949)
                    ·
                      refine ⟨3222462353476254938600981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8593232942603346502935949 3222462353476254938600981)
                      ·
                        rfl

theorem cell23_6275723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 3].length) (baseStart_6275723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275723 prefixEnd_6275723 := by exact prefixLift 6275723
  have htrace : WordTrace (prefixWord ++ tailWord_6275723) baseStart_6275723 baseEnd_6275723 := by
    simpa [prefixWord, tailWord_6275723, baseEnd_6275723] using wordTrace_append hprefix tailTrace_6275723
  have hstable : (prefixWord ++ tailWord_6275723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275723).length < 2 ^ (prefixWord ++ tailWord_6275723).sum := by decide
  have hdescent : baseEnd_6275723 < baseStart_6275723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275733 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_6275733 : Nat := 118140960795 + 6275733 * 2 ^ 59
def prefixEnd_6275733 : Nat := 4983230072969 + 3 ^ 40 * 6275733 * 2
def baseEnd_6275733 : Nat := 3222467488282799899475935

theorem tailTrace_6275733 : CollatzResearch.WordTrace tailWord_6275733 prefixEnd_6275733 3222467488282799899475935 := by
  unfold tailWord_6275733
  simp only [CollatzResearch.WordTrace]
  refine ⟨228894786973098625710367853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152596524648732417140245235 228894786973098625710367853)
  ·
    refine ⟨85835545114911984641387945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228894786973098625710367853 85835545114911984641387945)
    ·
      refine ⟨64376658836183988481040959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85835545114911984641387945 64376658836183988481040959)
      ·
        refine ⟨96564988254275982721561439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64376658836183988481040959 96564988254275982721561439)
        ·
          refine ⟨144847482381413974082342159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96564988254275982721561439 144847482381413974082342159)
          ·
            refine ⟨217271223572120961123513239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144847482381413974082342159 217271223572120961123513239)
            ·
              refine ⟨325906835358181441685269859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217271223572120961123513239 325906835358181441685269859)
              ·
                refine ⟨488860253037272162527904789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325906835358181441685269859 488860253037272162527904789)
                ·
                  refine ⟨22915324361122132618495537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 488860253037272162527904789 22915324361122132618495537)
                  ·
                    refine ⟨17186493270841599463871653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22915324361122132618495537 17186493270841599463871653)
                    ·
                      refine ⟨3222467488282799899475935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17186493270841599463871653 3222467488282799899475935)
                      ·
                        rfl

theorem cell23_6275733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_6275733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275733 prefixEnd_6275733 := by exact prefixLift 6275733
  have htrace : WordTrace (prefixWord ++ tailWord_6275733) baseStart_6275733 baseEnd_6275733 := by
    simpa [prefixWord, tailWord_6275733, baseEnd_6275733] using wordTrace_append hprefix tailTrace_6275733
  have hstable : (prefixWord ++ tailWord_6275733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275733).length < 2 ^ (prefixWord ++ tailWord_6275733).sum := by decide
  have hdescent : baseEnd_6275733 < baseStart_6275733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275740 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_6275740 : Nat := 118140960795 + 6275740 * 2 ^ 59
def prefixEnd_6275740 : Nat := 4983230072969 + 3 ^ 40 * 6275740 * 2
def baseEnd_6275740 : Nat := 3222471082647381372088403

theorem tailTrace_6275740 : CollatzResearch.WordTrace tailWord_6275740 prefixEnd_6275740 3222471082647381372088403 := by
  unfold tailWord_6275740
  simp only [CollatzResearch.WordTrace]
  refine ⟨114447521142036632952936337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152596694856048843937248449 114447521142036632952936337)
  ·
    refine ⟨85835640856527474714702253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114447521142036632952936337 85835640856527474714702253)
    ·
      refine ⟨32188365321197803018013345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85835640856527474714702253 32188365321197803018013345)
      ·
        refine ⟨24141273990898352263510009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32188365321197803018013345 24141273990898352263510009)
        ·
          refine ⟨18105955493173764197632507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24141273990898352263510009 18105955493173764197632507)
          ·
            refine ⟨27158933239760646296448761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18105955493173764197632507 27158933239760646296448761)
            ·
              refine ⟨20369199929820484722336571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27158933239760646296448761 20369199929820484722336571)
              ·
                refine ⟨30553799894730727083504857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20369199929820484722336571 30553799894730727083504857)
                ·
                  refine ⟨22915349921048045312628643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30553799894730727083504857 22915349921048045312628643)
                  ·
                    refine ⟨34373024881572067968942965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22915349921048045312628643 34373024881572067968942965)
                    ·
                      refine ⟨3222471082647381372088403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34373024881572067968942965 3222471082647381372088403)
                      ·
                        rfl

theorem cell23_6275740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_6275740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275740 prefixEnd_6275740 := by exact prefixLift 6275740
  have htrace : WordTrace (prefixWord ++ tailWord_6275740) baseStart_6275740 baseEnd_6275740 := by
    simpa [prefixWord, tailWord_6275740, baseEnd_6275740] using wordTrace_append hprefix tailTrace_6275740
  have hstable : (prefixWord ++ tailWord_6275740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275740).length < 2 ^ (prefixWord ++ tailWord_6275740).sum := by decide
  have hdescent : baseEnd_6275740 < baseStart_6275740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275770 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3]
def baseStart_6275770 : Nat := 118140960795 + 6275770 * 2 ^ 59
def prefixEnd_6275770 : Nat := 4983230072969 + 3 ^ 40 * 6275770 * 2
def baseEnd_6275770 : Nat := 3222486487067016254713265

theorem tailTrace_6275770 : CollatzResearch.WordTrace tailWord_6275770 prefixEnd_6275770 3222486487067016254713265 := by
  unfold tailWord_6275770
  simp only [CollatzResearch.WordTrace]
  refine ⟨57224034118491145257366191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152597424315976387352976509 57224034118491145257366191)
  ·
    refine ⟨85836051177736717886049287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57224034118491145257366191 85836051177736717886049287)
    ·
      refine ⟨128754076766605076829073931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85836051177736717886049287 128754076766605076829073931)
      ·
        refine ⟨193131115149907615243610897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128754076766605076829073931 193131115149907615243610897)
        ·
          refine ⟨144848336362430711432708173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193131115149907615243610897 144848336362430711432708173)
          ·
            refine ⟨54318126135911516787265565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144848336362430711432708173 54318126135911516787265565)
            ·
              refine ⟨20369297300966818795224587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54318126135911516787265565 20369297300966818795224587)
              ·
                refine ⟨30553945951450228192836881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20369297300966818795224587 30553945951450228192836881)
                ·
                  refine ⟨22915459463587671144627661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30553945951450228192836881 22915459463587671144627661)
                  ·
                    refine ⟨8593297298845376679235373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22915459463587671144627661 8593297298845376679235373)
                    ·
                      refine ⟨3222486487067016254713265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8593297298845376679235373 3222486487067016254713265)
                      ·
                        rfl

theorem cell23_6275770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_6275770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275770 prefixEnd_6275770 := by exact prefixLift 6275770
  have htrace : WordTrace (prefixWord ++ tailWord_6275770) baseStart_6275770 baseEnd_6275770 := by
    simpa [prefixWord, tailWord_6275770, baseEnd_6275770] using wordTrace_append hprefix tailTrace_6275770
  have hstable : (prefixWord ++ tailWord_6275770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275770).length < 2 ^ (prefixWord ++ tailWord_6275770).sum := by decide
  have hdescent : baseEnd_6275770 < baseStart_6275770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275783 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_6275783 : Nat := 118140960795 + 6275783 * 2 ^ 59
def prefixEnd_6275783 : Nat := 4983230072969 + 3 ^ 40 * 6275783 * 2
def baseEnd_6275783 : Nat := 3222493162315524703850705

theorem tailTrace_6275783 : CollatzResearch.WordTrace tailWord_6275783 prefixEnd_6275783 3222493162315524703850705 := by
  unfold tailWord_6275783
  simp only [CollatzResearch.WordTrace]
  refine ⟨228896610622917484249688003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152597740415278322833125335 228896610622917484249688003)
  ·
    refine ⟨343344915934376226374532005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228896610622917484249688003 343344915934376226374532005)
    ·
      refine ⟨64377171737695542445224751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 343344915934376226374532005 64377171737695542445224751)
      ·
        refine ⟨96565757606543313667837127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64377171737695542445224751 96565757606543313667837127)
        ·
          refine ⟨144848636409814970501755691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96565757606543313667837127 144848636409814970501755691)
          ·
            refine ⟨217272954614722455752633537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144848636409814970501755691 217272954614722455752633537)
            ·
              refine ⟨162954715961041841814475153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217272954614722455752633537 162954715961041841814475153)
              ·
                refine ⟨122216036970781381360856365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162954715961041841814475153 122216036970781381360856365)
                ·
                  refine ⟨45831013864043018010321137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122216036970781381360856365 45831013864043018010321137)
                  ·
                    refine ⟨34373260398032263507740853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45831013864043018010321137 34373260398032263507740853)
                    ·
                      refine ⟨3222493162315524703850705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34373260398032263507740853 3222493162315524703850705)
                      ·
                        rfl

theorem cell23_6275783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_6275783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275783 prefixEnd_6275783 := by exact prefixLift 6275783
  have htrace : WordTrace (prefixWord ++ tailWord_6275783) baseStart_6275783 baseEnd_6275783 := by
    simpa [prefixWord, tailWord_6275783, baseEnd_6275783] using wordTrace_append hprefix tailTrace_6275783
  have hstable : (prefixWord ++ tailWord_6275783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275783).length < 2 ^ (prefixWord ++ tailWord_6275783).sum := by decide
  have hdescent : baseEnd_6275783 < baseStart_6275783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275790 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 1, 7]
def baseStart_6275790 : Nat := 118140960795 + 6275790 * 2 ^ 59
def prefixEnd_6275790 : Nat := 4983230072969 + 3 ^ 40 * 6275790 * 2
def baseEnd_6275790 : Nat := 1074165585560035392154391

theorem tailTrace_6275790 : CollatzResearch.WordTrace tailWord_6275790 prefixEnd_6275790 1074165585560035392154391 := by
  unfold tailWord_6275790
  simp only [CollatzResearch.WordTrace]
  refine ⟨28612108241736515555649103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152597910622594749630128549 28612108241736515555649103)
  ·
    refine ⟨42918162362604773333473655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28612108241736515555649103 42918162362604773333473655)
    ·
      refine ⟨64377243543907160000210483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42918162362604773333473655 64377243543907160000210483)
      ·
        refine ⟨96565865315860740000315725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64377243543907160000210483 96565865315860740000315725)
        ·
          refine ⟨36212199493447777500118397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96565865315860740000315725 36212199493447777500118397)
          ·
            refine ⟨13579574810042916562544399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36212199493447777500118397 13579574810042916562544399)
            ·
              refine ⟨20369362215064374843816599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13579574810042916562544399 20369362215064374843816599)
              ·
                refine ⟨30554043322596562265724899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20369362215064374843816599 30554043322596562265724899)
                ·
                  refine ⟨45831064983894843398587349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30554043322596562265724899 45831064983894843398587349)
                  ·
                    refine ⟨1074165585560035392154391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45831064983894843398587349 1074165585560035392154391)
                    ·
                      rfl

theorem cell23_6275790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_6275790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275790 prefixEnd_6275790 := by exact prefixLift 6275790
  have htrace : WordTrace (prefixWord ++ tailWord_6275790) baseStart_6275790 baseEnd_6275790 := by
    simpa [prefixWord, tailWord_6275790, baseEnd_6275790] using wordTrace_append hprefix tailTrace_6275790
  have hstable : (prefixWord ++ tailWord_6275790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275790).length < 2 ^ (prefixWord ++ tailWord_6275790).sum := by decide
  have hdescent : baseEnd_6275790 < baseStart_6275790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275794 : List Nat := [3, 2, 2, 2, 3, 1, 2, 3, 5]
def baseStart_6275794 : Nat := 118140960795 + 6275794 * 2 ^ 59
def prefixEnd_6275794 : Nat := 4983230072969 + 3 ^ 40 * 6275794 * 2
def baseEnd_6275794 : Nat := 358055423400302684534795

theorem tailTrace_6275794 : CollatzResearch.WordTrace tailWord_6275794 prefixEnd_6275794 358055423400302684534795 := by
  unfold tailWord_6275794
  simp only [CollatzResearch.WordTrace]
  refine ⟨57224252956469408282084609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152598007883918422085558957 57224252956469408282084609)
  ·
    refine ⟨42918189717352056211563457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57224252956469408282084609 42918189717352056211563457)
    ·
      refine ⟨32188642288014042158672593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42918189717352056211563457 32188642288014042158672593)
      ·
        refine ⟨24141481716010531619004445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32188642288014042158672593 24141481716010531619004445)
        ·
          refine ⟨9053055643503949357126667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24141481716010531619004445 9053055643503949357126667)
          ·
            refine ⟨13579583465255924035690001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9053055643503949357126667 13579583465255924035690001)
            ·
              refine ⟨10184687598941943026767501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13579583465255924035690001 10184687598941943026767501)
              ·
                refine ⟨3819257849603228635037813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10184687598941943026767501 3819257849603228635037813)
                ·
                  refine ⟨358055423400302684534795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3819257849603228635037813 358055423400302684534795)
                  ·
                    rfl

theorem cell23_6275794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_6275794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275794 prefixEnd_6275794 := by exact prefixLift 6275794
  have htrace : WordTrace (prefixWord ++ tailWord_6275794) baseStart_6275794 baseEnd_6275794 := by
    simpa [prefixWord, tailWord_6275794, baseEnd_6275794] using wordTrace_append hprefix tailTrace_6275794
  have hstable : (prefixWord ++ tailWord_6275794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275794).length < 2 ^ (prefixWord ++ tailWord_6275794).sum := by decide
  have hdescent : baseEnd_6275794 < baseStart_6275794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275847 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 3]
def baseStart_6275847 : Nat := 118140960795 + 6275847 * 2 ^ 59
def prefixEnd_6275847 : Nat := 4983230072969 + 3 ^ 40 * 6275847 * 2
def baseEnd_6275847 : Nat := 3222526025077412453450411

theorem tailTrace_6275847 : CollatzResearch.WordTrace tailWord_6275847 prefixEnd_6275847 3222526025077412453450411 := by
  unfold tailWord_6275847
  simp only [CollatzResearch.WordTrace]
  refine ⟨228898944894685623180017795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152599296596457082120011863 228898944894685623180017795)
  ·
    refine ⟨343348417342028434770026693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228898944894685623180017795 343348417342028434770026693)
    ·
      refine ⟨64377828251630331519380005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 343348417342028434770026693 64377828251630331519380005)
      ·
        refine ⟨12070842797180687159883751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64377828251630331519380005 12070842797180687159883751)
        ·
          refine ⟨18106264195771030739825627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12070842797180687159883751 18106264195771030739825627)
          ·
            refine ⟨27159396293656546109738441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18106264195771030739825627 27159396293656546109738441)
            ·
              refine ⟨20369547220242409582303831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27159396293656546109738441 20369547220242409582303831)
              ·
                refine ⟨30554320830363614373455747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20369547220242409582303831 30554320830363614373455747)
                ·
                  refine ⟨45831481245545421560183621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30554320830363614373455747 45831481245545421560183621)
                  ·
                    refine ⟨8593402733539766542534429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45831481245545421560183621 8593402733539766542534429)
                    ·
                      refine ⟨3222526025077412453450411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8593402733539766542534429 3222526025077412453450411)
                      ·
                        rfl

theorem cell23_6275847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_6275847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275847 prefixEnd_6275847 := by exact prefixLift 6275847
  have htrace : WordTrace (prefixWord ++ tailWord_6275847) baseStart_6275847 baseEnd_6275847 := by
    simpa [prefixWord, tailWord_6275847, baseEnd_6275847] using wordTrace_append hprefix tailTrace_6275847
  have hstable : (prefixWord ++ tailWord_6275847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275847).length < 2 ^ (prefixWord ++ tailWord_6275847).sum := by decide
  have hdescent : baseEnd_6275847 < baseStart_6275847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275871 : List Nat := [1, 1, 2, 4, 2, 3, 3, 2, 1, 4]
def baseStart_6275871 : Nat := 118140960795 + 6275871 * 2 ^ 59
def prefixEnd_6275871 : Nat := 4983230072969 + 3 ^ 40 * 6275871 * 2
def baseEnd_6275871 : Nat := 1074179449537706786516767

theorem tailTrace_6275871 : CollatzResearch.WordTrace tailWord_6275871 prefixEnd_6275871 1074179449537706786516767 := by
  unfold tailWord_6275871
  simp only [CollatzResearch.WordTrace]
  refine ⟨228899820246598675278891467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152599880164399116852594311 228899820246598675278891467)
  ·
    refine ⟨343349730369898012918337201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228899820246598675278891467 343349730369898012918337201)
    ·
      refine ⟨257512297777423509688752901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343349730369898012918337201 257512297777423509688752901)
      ·
        refine ⟨48283555833266908066641169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257512297777423509688752901 48283555833266908066641169)
        ·
          refine ⟨36212666874950181049980877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48283555833266908066641169 36212666874950181049980877)
          ·
            refine ⟨13579750078106317893742829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36212666874950181049980877 13579750078106317893742829)
            ·
              refine ⟨5092406279289869210153561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13579750078106317893742829 5092406279289869210153561)
              ·
                refine ⟨3819304709467401907615171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5092406279289869210153561 3819304709467401907615171)
                ·
                  refine ⟨5728957064201102861422757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3819304709467401907615171 5728957064201102861422757)
                  ·
                    refine ⟨1074179449537706786516767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5728957064201102861422757 1074179449537706786516767)
                    ·
                      rfl

theorem cell23_6275871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 1, 4].length) (baseStart_6275871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275871 prefixEnd_6275871 := by exact prefixLift 6275871
  have htrace : WordTrace (prefixWord ++ tailWord_6275871) baseStart_6275871 baseEnd_6275871 := by
    simpa [prefixWord, tailWord_6275871, baseEnd_6275871] using wordTrace_append hprefix tailTrace_6275871
  have hstable : (prefixWord ++ tailWord_6275871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275871).length < 2 ^ (prefixWord ++ tailWord_6275871).sum := by decide
  have hdescent : baseEnd_6275871 < baseStart_6275871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275944 : List Nat := [2, 1, 4, 2, 1, 2, 2, 3, 2, 4]
def baseStart_6275944 : Nat := 118140960795 + 6275944 * 2 ^ 59
def prefixEnd_6275944 : Nat := 4983230072969 + 3 ^ 40 * 6275944 * 2
def baseEnd_6275944 : Nat := 1074191944233632857979155

theorem tailTrace_6275944 : CollatzResearch.WordTrace tailWord_6275944 prefixEnd_6275944 1074191944233632857979155 := by
  unfold tailWord_6275944
  simp only [CollatzResearch.WordTrace]
  refine ⟨114451241387667104373149443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152601655183556139164199257 114451241387667104373149443)
  ·
    refine ⟨171676862081500656559724165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114451241387667104373149443 171676862081500656559724165)
    ·
      refine ⟨32189411640281373104948281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171676862081500656559724165 32189411640281373104948281)
      ·
        refine ⟨24142058730211029828711211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32189411640281373104948281 24142058730211029828711211)
        ·
          refine ⟨36213088095316544743066817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24142058730211029828711211 36213088095316544743066817)
          ·
            refine ⟨27159816071487408557300113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36213088095316544743066817 27159816071487408557300113)
            ·
              refine ⟨20369862053615556417975085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27159816071487408557300113 20369862053615556417975085)
              ·
                refine ⟨7638698270105833656740657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20369862053615556417975085 7638698270105833656740657)
                ·
                  refine ⟨5729023702579375242555493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7638698270105833656740657 5729023702579375242555493)
                  ·
                    refine ⟨1074191944233632857979155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5729023702579375242555493 1074191944233632857979155)
                    ·
                      rfl

theorem cell23_6275944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_6275944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275944 prefixEnd_6275944 := by exact prefixLift 6275944
  have htrace : WordTrace (prefixWord ++ tailWord_6275944) baseStart_6275944 baseEnd_6275944 := by
    simpa [prefixWord, tailWord_6275944, baseEnd_6275944] using wordTrace_append hprefix tailTrace_6275944
  have hstable : (prefixWord ++ tailWord_6275944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275944).length < 2 ^ (prefixWord ++ tailWord_6275944).sum := by decide
  have hdescent : baseEnd_6275944 < baseStart_6275944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6275967 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 3]
def baseStart_6275967 : Nat := 118140960795 + 6275967 * 2 ^ 59
def prefixEnd_6275967 : Nat := 4983230072969 + 3 ^ 40 * 6275967 * 2
def baseEnd_6275967 : Nat := 3222587642755951983949859

theorem tailTrace_6275967 : CollatzResearch.WordTrace tailWord_6275967 prefixEnd_6275967 3222587642755951983949859 := by
  unfold tailWord_6275967
  simp only [CollatzResearch.WordTrace]
  refine ⟨228903321654250883674386155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152602214436167255782924103 228903321654250883674386155)
  ·
    refine ⟨343354982481376325511579233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228903321654250883674386155 343354982481376325511579233)
    ·
      refine ⟨257516236861032244133684425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343354982481376325511579233 257516236861032244133684425)
      ·
        refine ⟨193137177645774183100263319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257516236861032244133684425 193137177645774183100263319)
        ·
          refine ⟨289705766468661274650394979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193137177645774183100263319 289705766468661274650394979)
          ·
            refine ⟨434558649702991911975592469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289705766468661274650394979 434558649702991911975592469)
            ·
              refine ⟨20369936704827745873855897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 434558649702991911975592469 20369936704827745873855897)
              ·
                refine ⟨15277452528620809405391923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20369936704827745873855897 15277452528620809405391923)
                ·
                  refine ⟨22916178792931214108087885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15277452528620809405391923 22916178792931214108087885)
                  ·
                    refine ⟨8593567047349205290532957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22916178792931214108087885 8593567047349205290532957)
                    ·
                      refine ⟨3222587642755951983949859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8593567047349205290532957 3222587642755951983949859)
                      ·
                        rfl

theorem cell23_6275967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_6275967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6275967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6275967 prefixEnd_6275967 := by exact prefixLift 6275967
  have htrace : WordTrace (prefixWord ++ tailWord_6275967) baseStart_6275967 baseEnd_6275967 := by
    simpa [prefixWord, tailWord_6275967, baseEnd_6275967] using wordTrace_append hprefix tailTrace_6275967
  have hstable : (prefixWord ++ tailWord_6275967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6275967).length < 2 ^ (prefixWord ++ tailWord_6275967).sum := by decide
  have hdescent : baseEnd_6275967 < baseStart_6275967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6275967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276001 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 1, 3, 3]
def baseStart_6276001 : Nat := 118140960795 + 6276001 * 2 ^ 59
def prefixEnd_6276001 : Nat := 4983230072969 + 3 ^ 40 * 6276001 * 2
def baseEnd_6276001 : Nat := 3222605101098204850924703

theorem tailTrace_6276001 : CollatzResearch.WordTrace tailWord_6276001 prefixEnd_6276001 3222605101098204850924703 := by
  unfold tailWord_6276001
  simp only [CollatzResearch.WordTrace]
  refine ⟨228904561736127707481123857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152603041157418471654082571 228904561736127707481123857)
  ·
    refine ⟨171678421302095780610842893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228904561736127707481123857 171678421302095780610842893)
    ·
      refine ⟨64379407988285917729066085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171678421302095780610842893 64379407988285917729066085)
      ·
        refine ⟨12071138997803609574199891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64379407988285917729066085 12071138997803609574199891)
        ·
          refine ⟨18106708496705414361299837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12071138997803609574199891 18106708496705414361299837)
          ·
            refine ⟨6790015686264530385487439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18106708496705414361299837 6790015686264530385487439)
            ·
              refine ⟨10185023529396795578231159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6790015686264530385487439 10185023529396795578231159)
              ·
                refine ⟨15277535294095193367346739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10185023529396795578231159 15277535294095193367346739)
                ·
                  refine ⟨22916302941142790051020109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15277535294095193367346739 22916302941142790051020109)
                  ·
                    refine ⟨8593613602928546269132541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22916302941142790051020109 8593613602928546269132541)
                    ·
                      refine ⟨3222605101098204850924703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8593613602928546269132541 3222605101098204850924703)
                      ·
                        rfl

theorem cell23_6276001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_6276001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276001 prefixEnd_6276001 := by exact prefixLift 6276001
  have htrace : WordTrace (prefixWord ++ tailWord_6276001) baseStart_6276001 baseEnd_6276001 := by
    simpa [prefixWord, tailWord_6276001, baseEnd_6276001] using wordTrace_append hprefix tailTrace_6276001
  have hstable : (prefixWord ++ tailWord_6276001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276001).length < 2 ^ (prefixWord ++ tailWord_6276001).sum := by decide
  have hdescent : baseEnd_6276001 < baseStart_6276001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276047 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 7]
def baseStart_6276047 : Nat := 118140960795 + 6276047 * 2 ^ 59
def prefixEnd_6276047 : Nat := 4983230072969 + 3 ^ 40 * 6276047 * 2
def baseEnd_6276047 : Nat := 358069857912034630105499

theorem tailTrace_6276047 : CollatzResearch.WordTrace tailWord_6276047 prefixEnd_6276047 358069857912034630105499 := by
  unfold tailWord_6276047
  simp only [CollatzResearch.WordTrace]
  refine ⟨228906239493961057337298395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152604159662640704891532263 228906239493961057337298395)
  ·
    refine ⟨343359359240941586005947593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228906239493961057337298395 343359359240941586005947593)
    ·
      refine ⟨257519519430706189504460695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343359359240941586005947593 257519519430706189504460695)
      ·
        refine ⟨386279279146059284256691043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257519519430706189504460695 386279279146059284256691043)
        ·
          refine ⟨579418918719088926385036565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386279279146059284256691043 579418918719088926385036565)
          ·
            refine ⟨27160261814957293424298589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 579418918719088926385036565 27160261814957293424298589)
            ·
              refine ⟨10185098180608985034111971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27160261814957293424298589 10185098180608985034111971)
              ·
                refine ⟨15277647270913477551167957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10185098180608985034111971 15277647270913477551167957)
                ·
                  refine ⟨358069857912034630105499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15277647270913477551167957 358069857912034630105499)
                  ·
                    rfl

theorem cell23_6276047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 7].length) (baseStart_6276047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276047 prefixEnd_6276047 := by exact prefixLift 6276047
  have htrace : WordTrace (prefixWord ++ tailWord_6276047) baseStart_6276047 baseEnd_6276047 := by
    simpa [prefixWord, tailWord_6276047, baseEnd_6276047] using wordTrace_append hprefix tailTrace_6276047
  have hstable : (prefixWord ++ tailWord_6276047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276047).length < 2 ^ (prefixWord ++ tailWord_6276047).sum := by decide
  have hdescent : baseEnd_6276047 < baseStart_6276047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276058 : List Nat := [3, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2]
def baseStart_6276058 : Nat := 118140960795 + 6276058 * 2 ^ 59
def prefixEnd_6276058 : Nat := 4983230072969 + 3 ^ 40 * 6276058 * 2
def baseEnd_6276058 : Nat := 3222634369495511127911941

theorem tailTrace_6276058 : CollatzResearch.WordTrace tailWord_6276058 prefixEnd_6276058 3222634369495511127911941 := by
  unfold tailWord_6276058
  simp only [CollatzResearch.WordTrace]
  refine ⟨57226660174230301553987207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152604427131280804143965885 57226660174230301553987207)
  ·
    refine ⟨85839990261345452330980811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57226660174230301553987207 85839990261345452330980811)
    ·
      refine ⟨128759985392018178496471217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85839990261345452330980811 128759985392018178496471217)
      ·
        refine ⟨96569989044013633872353413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128759985392018178496471217 96569989044013633872353413)
        ·
          refine ⟨18106872945752556351066265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96569989044013633872353413 18106872945752556351066265)
          ·
            refine ⟨13580154709314417263299699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18106872945752556351066265 13580154709314417263299699)
            ·
              refine ⟨20370232063971625894949549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13580154709314417263299699 20370232063971625894949549)
              ·
                refine ⟨7638837023989359710606081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20370232063971625894949549 7638837023989359710606081)
                ·
                  refine ⟨5729127767992019782954561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7638837023989359710606081 5729127767992019782954561)
                  ·
                    refine ⟨4296845825994014837215921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5729127767992019782954561 4296845825994014837215921)
                    ·
                      refine ⟨3222634369495511127911941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4296845825994014837215921 3222634369495511127911941)
                      ·
                        rfl

theorem cell23_6276058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_6276058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276058 prefixEnd_6276058 := by exact prefixLift 6276058
  have htrace : WordTrace (prefixWord ++ tailWord_6276058) baseStart_6276058 baseEnd_6276058 := by
    simpa [prefixWord, tailWord_6276058, baseEnd_6276058] using wordTrace_append hprefix tailTrace_6276058
  have hstable : (prefixWord ++ tailWord_6276058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276058).length < 2 ^ (prefixWord ++ tailWord_6276058).sum := by decide
  have hdescent : baseEnd_6276058 < baseStart_6276058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276128 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 2, 5]
def baseStart_6276128 : Nat := 118140960795 + 6276128 * 2 ^ 59
def prefixEnd_6276128 : Nat := 4983230072969 + 3 ^ 40 * 6276128 * 2
def baseEnd_6276128 : Nat := 1074223437713775284678873

theorem tailTrace_6276128 : CollatzResearch.WordTrace tailWord_6276128 prefixEnd_6276128 1074223437713775284678873 := by
  unfold tailWord_6276128
  simp only [CollatzResearch.WordTrace]
  refine ⟨114454596903333804085498519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152606129204445072113998025 114454596903333804085498519)
  ·
    refine ⟨171681895355000706128247779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114454596903333804085498519 171681895355000706128247779)
    ·
      refine ⟨257522843032501059192371669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171681895355000706128247779 257522843032501059192371669)
      ·
        refine ⟨6035691633574243574821211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 257522843032501059192371669 6035691633574243574821211)
        ·
          refine ⟨9053537450361365362231817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6035691633574243574821211 9053537450361365362231817)
          ·
            refine ⟨6790153087771024021673863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9053537450361365362231817 6790153087771024021673863)
            ·
              refine ⟨10185229631656536032510795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6790153087771024021673863 10185229631656536032510795)
              ·
                refine ⟨15277844447484804048766193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10185229631656536032510795 15277844447484804048766193)
                ·
                  refine ⟨11458383335613603036574645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15277844447484804048766193 11458383335613603036574645)
                  ·
                    refine ⟨1074223437713775284678873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11458383335613603036574645 1074223437713775284678873)
                    ·
                      rfl

theorem cell23_6276128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 2, 5].length) (baseStart_6276128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276128 prefixEnd_6276128 := by exact prefixLift 6276128
  have htrace : WordTrace (prefixWord ++ tailWord_6276128) baseStart_6276128 baseEnd_6276128 := by
    simpa [prefixWord, tailWord_6276128, baseEnd_6276128] using wordTrace_append hprefix tailTrace_6276128
  have hstable : (prefixWord ++ tailWord_6276128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276128).length < 2 ^ (prefixWord ++ tailWord_6276128).sum := by decide
  have hdescent : baseEnd_6276128 < baseStart_6276128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276131 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 2, 1, 4]
def baseStart_6276131 : Nat := 118140960795 + 6276131 * 2 ^ 59
def prefixEnd_6276131 : Nat := 4983230072969 + 3 ^ 40 * 6276131 * 2
def baseEnd_6276131 : Nat := 3222671853583289342299105

theorem tailTrace_6276131 : CollatzResearch.WordTrace tailWord_6276131 prefixEnd_6276131 3222671853583289342299105 := by
  unfold tailWord_6276131
  simp only [CollatzResearch.WordTrace]
  refine ⟨228909303225656739683356247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152606202150437826455570831 228909303225656739683356247)
  ·
    refine ⟨343363954838485109525034371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228909303225656739683356247 343363954838485109525034371)
    ·
      refine ⟨515045932257727664287551557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343363954838485109525034371 515045932257727664287551557)
      ·
        refine ⟨96571112298323937053915917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 515045932257727664287551557 96571112298323937053915917)
        ·
          refine ⟨36214167111871476395218469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96571112298323937053915917 36214167111871476395218469)
          ·
            refine ⟨6790156333475901824103463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36214167111871476395218469 6790156333475901824103463)
            ·
              refine ⟨10185234500213852736155195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6790156333475901824103463 10185234500213852736155195)
              ·
                refine ⟨15277851750320779104232793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10185234500213852736155195 15277851750320779104232793)
                ·
                  refine ⟨11458388812740584328174595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15277851750320779104232793 11458388812740584328174595)
                  ·
                    refine ⟨17187583219110876492261893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11458388812740584328174595 17187583219110876492261893)
                    ·
                      refine ⟨3222671853583289342299105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17187583219110876492261893 3222671853583289342299105)
                      ·
                        rfl

theorem cell23_6276131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_6276131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276131 prefixEnd_6276131 := by exact prefixLift 6276131
  have htrace : WordTrace (prefixWord ++ tailWord_6276131) baseStart_6276131 baseEnd_6276131 := by
    simpa [prefixWord, tailWord_6276131, baseEnd_6276131] using wordTrace_append hprefix tailTrace_6276131
  have hstable : (prefixWord ++ tailWord_6276131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276131).length < 2 ^ (prefixWord ++ tailWord_6276131).sum := by decide
  have hdescent : baseEnd_6276131 < baseStart_6276131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276148 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_6276148 : Nat := 118140960795 + 6276148 * 2 ^ 59
def prefixEnd_6276148 : Nat := 4983230072969 + 3 ^ 40 * 6276148 * 2
def baseEnd_6276148 : Nat := 3222680582754415775786527

theorem tailTrace_6276148 : CollatzResearch.WordTrace tailWord_6276148 prefixEnd_6276148 3222680582754415775786527 := by
  unfold tailWord_6276148
  simp only [CollatzResearch.WordTrace]
  refine ⟨114454961633297575793362549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152606615511063434391150065 114454961633297575793362549)
  ·
    refine ⟨10730152653121647730627739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114454961633297575793362549 10730152653121647730627739)
    ·
      refine ⟨16095228979682471595941609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10730152653121647730627739 16095228979682471595941609)
      ·
        refine ⟨12071421734761853696956207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16095228979682471595941609 12071421734761853696956207)
        ·
          refine ⟨18107132602142780545434311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12071421734761853696956207 18107132602142780545434311)
          ·
            refine ⟨27160698903214170818151467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18107132602142780545434311 27160698903214170818151467)
            ·
              refine ⟨40741048354821256227227201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27160698903214170818151467 40741048354821256227227201)
              ·
                refine ⟨30555786266115942170420401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40741048354821256227227201 30555786266115942170420401)
                ·
                  refine ⟨22916839699586956627815301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30555786266115942170420401 22916839699586956627815301)
                  ·
                    refine ⟨4296907443672554367715369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22916839699586956627815301 4296907443672554367715369)
                    ·
                      refine ⟨3222680582754415775786527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4296907443672554367715369 3222680582754415775786527)
                      ·
                        rfl

theorem cell23_6276148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_6276148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276148 prefixEnd_6276148 := by exact prefixLift 6276148
  have htrace : WordTrace (prefixWord ++ tailWord_6276148) baseStart_6276148 baseEnd_6276148 := by
    simpa [prefixWord, tailWord_6276148, baseEnd_6276148] using wordTrace_append hprefix tailTrace_6276148
  have hstable : (prefixWord ++ tailWord_6276148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276148).length < 2 ^ (prefixWord ++ tailWord_6276148).sum := by decide
  have hdescent : baseEnd_6276148 < baseStart_6276148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276154 : List Nat := [3, 1, 1, 1, 3, 1, 5, 2, 6]
def baseStart_6276154 : Nat := 118140960795 + 6276154 * 2 ^ 59
def prefixEnd_6276154 : Nat := 4983230072969 + 3 ^ 40 * 6276154 * 2
def baseEnd_6276154 : Nat := 358075962626482528034611

theorem tailTrace_6276154 : CollatzResearch.WordTrace tailWord_6276154 prefixEnd_6276154 358075962626482528034611 := by
  unfold tailWord_6276154
  simp only [CollatzResearch.WordTrace]
  refine ⟨57227535526143353652860879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152606761403048943074295677 57227535526143353652860879)
  ·
    refine ⟨85841303289215030479291319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57227535526143353652860879 85841303289215030479291319)
    ·
      refine ⟨128761954933822545718936979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85841303289215030479291319 128761954933822545718936979)
      ·
        refine ⟨193142932400733818578405469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128761954933822545718936979 193142932400733818578405469)
        ·
          refine ⟨72428599650275181966902051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193142932400733818578405469 72428599650275181966902051)
          ·
            refine ⟨108642899475412772950353077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72428599650275181966902051 108642899475412772950353077)
            ·
              refine ⟨10185271825819947464095601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108642899475412772950353077 10185271825819947464095601)
              ·
                refine ⟨7638953869364960598071701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10185271825819947464095601 7638953869364960598071701)
                ·
                  refine ⟨358075962626482528034611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7638953869364960598071701 358075962626482528034611)
                  ·
                    rfl

theorem cell23_6276154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 6].length) (baseStart_6276154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276154 prefixEnd_6276154 := by exact prefixLift 6276154
  have htrace : WordTrace (prefixWord ++ tailWord_6276154) baseStart_6276154 baseEnd_6276154 := by
    simpa [prefixWord, tailWord_6276154, baseEnd_6276154] using wordTrace_append hprefix tailTrace_6276154
  have hstable : (prefixWord ++ tailWord_6276154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276154).length < 2 ^ (prefixWord ++ tailWord_6276154).sum := by decide
  have hdescent : baseEnd_6276154 < baseStart_6276154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276158 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_6276158 : Nat := 118140960795 + 6276158 * 2 ^ 59
def prefixEnd_6276158 : Nat := 4983230072969 + 3 ^ 40 * 6276158 * 2
def baseEnd_6276158 : Nat := 1074228572520320245553827

theorem tailTrace_6276158 : CollatzResearch.WordTrace tailWord_6276158 prefixEnd_6276158 1074228572520320245553827 := by
  unfold tailWord_6276158
  simp only [CollatzResearch.WordTrace]
  refine ⟨28613785999569865411823641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152606858664372615529726085 28613785999569865411823641)
  ·
    refine ⟨21460339499677399058867731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28613785999569865411823641 21460339499677399058867731)
    ·
      refine ⟨32190509249516098588301597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21460339499677399058867731 32190509249516098588301597)
      ·
        refine ⟨12071440968568536970613099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32190509249516098588301597 12071440968568536970613099)
        ·
          refine ⟨18107161452852805455919649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12071440968568536970613099 18107161452852805455919649)
          ·
            refine ⟨13580371089639604091939737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18107161452852805455919649 13580371089639604091939737)
            ·
              refine ⟨10185278317229703068954803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13580371089639604091939737 10185278317229703068954803)
              ·
                refine ⟨15277917475844554603432205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10185278317229703068954803 15277917475844554603432205)
                ·
                  refine ⟨5729219053441707976287077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15277917475844554603432205 5729219053441707976287077)
                  ·
                    refine ⟨1074228572520320245553827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5729219053441707976287077 1074228572520320245553827)
                    ·
                      rfl

theorem cell23_6276158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_6276158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276158 prefixEnd_6276158 := by exact prefixLift 6276158
  have htrace : WordTrace (prefixWord ++ tailWord_6276158) baseStart_6276158 baseEnd_6276158 := by
    simpa [prefixWord, tailWord_6276158, baseEnd_6276158] using wordTrace_append hprefix tailTrace_6276158
  have hstable : (prefixWord ++ tailWord_6276158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276158).length < 2 ^ (prefixWord ++ tailWord_6276158).sum := by decide
  have hdescent : baseEnd_6276158 < baseStart_6276158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276177 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 7]
def baseStart_6276177 : Nat := 118140960795 + 6276177 * 2 ^ 59
def prefixEnd_6276177 : Nat := 4983230072969 + 3 ^ 40 * 6276177 * 2
def baseEnd_6276177 : Nat := 3222695473693396162323893

theorem tailTrace_6276177 : CollatzResearch.WordTrace tailWord_6276177 prefixEnd_6276177 3222695473693396162323893 := by
  unfold tailWord_6276177
  simp only [CollatzResearch.WordTrace]
  refine ⟨228910980983490089539530785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152607320655660059693020523 228910980983490089539530785)
  ·
    refine ⟨171683235737617567154648089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228910980983490089539530785 171683235737617567154648089)
    ·
      refine ⟨128762426803213175365986067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171683235737617567154648089 128762426803213175365986067)
      ·
        refine ⟨193143640204819763048979101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128762426803213175365986067 193143640204819763048979101)
        ·
          refine ⟨72428865076807411143367163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193143640204819763048979101 72428865076807411143367163)
          ·
            refine ⟨108643297615211116715050745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72428865076807411143367163 108643297615211116715050745)
            ·
              refine ⟨81482473211408337536288059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108643297615211116715050745 81482473211408337536288059)
              ·
                refine ⟨122223709817112506304432089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81482473211408337536288059 122223709817112506304432089)
                ·
                  refine ⟨91667782362834379728324067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122223709817112506304432089 91667782362834379728324067)
                  ·
                    refine ⟨137501673544251569592486101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91667782362834379728324067 137501673544251569592486101)
                    ·
                      refine ⟨3222695473693396162323893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137501673544251569592486101 3222695473693396162323893)
                      ·
                        rfl

theorem cell23_6276177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_6276177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276177 prefixEnd_6276177 := by exact prefixLift 6276177
  have htrace : WordTrace (prefixWord ++ tailWord_6276177) baseStart_6276177 baseEnd_6276177 := by
    simpa [prefixWord, tailWord_6276177, baseEnd_6276177] using wordTrace_append hprefix tailTrace_6276177
  have hstable : (prefixWord ++ tailWord_6276177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276177).length < 2 ^ (prefixWord ++ tailWord_6276177).sum := by decide
  have hdescent : baseEnd_6276177 < baseStart_6276177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276181 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 3, 1, 3]
def baseStart_6276181 : Nat := 118140960795 + 6276181 * 2 ^ 59
def prefixEnd_6276181 : Nat := 4983230072969 + 3 ^ 40 * 6276181 * 2
def baseEnd_6276181 : Nat := 3222697527616014146673875

theorem tailTrace_6276181 : CollatzResearch.WordTrace tailWord_6276181 prefixEnd_6276181 3222697527616014146673875 := by
  unfold tailWord_6276181
  simp only [CollatzResearch.WordTrace]
  refine ⟨228911126875475598222676397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152607417916983732148450931 228911126875475598222676397)
  ·
    refine ⟨85841672578303349333503649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228911126875475598222676397 85841672578303349333503649)
    ·
      refine ⟨64381254433727512000127737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85841672578303349333503649 64381254433727512000127737)
      ·
        refine ⟨48285940825295634000095803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64381254433727512000127737 48285940825295634000095803)
        ·
          refine ⟨72428911237943451000143705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48285940825295634000095803 72428911237943451000143705)
          ·
            refine ⟨54321683428457588250107779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72428911237943451000143705 54321683428457588250107779)
            ·
              refine ⟨81482525142686382375161669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54321683428457588250107779 81482525142686382375161669)
              ·
                refine ⟨15277973464253696695342813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81482525142686382375161669 15277973464253696695342813)
                ·
                  refine ⟨5729240049095136260753555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15277973464253696695342813 5729240049095136260753555)
                  ·
                    refine ⟨8593860073642704391130333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5729240049095136260753555 8593860073642704391130333)
                    ·
                      refine ⟨3222697527616014146673875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8593860073642704391130333 3222697527616014146673875)
                      ·
                        rfl

theorem cell23_6276181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_6276181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276181 prefixEnd_6276181 := by exact prefixLift 6276181
  have htrace : WordTrace (prefixWord ++ tailWord_6276181) baseStart_6276181 baseEnd_6276181 := by
    simpa [prefixWord, tailWord_6276181, baseEnd_6276181] using wordTrace_append hprefix tailTrace_6276181
  have hstable : (prefixWord ++ tailWord_6276181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276181).length < 2 ^ (prefixWord ++ tailWord_6276181).sum := by decide
  have hdescent : baseEnd_6276181 < baseStart_6276181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276191 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 2, 3, 2]
def baseStart_6276191 : Nat := 118140960795 + 6276191 * 2 ^ 59
def prefixEnd_6276191 : Nat := 4983230072969 + 3 ^ 40 * 6276191 * 2
def baseEnd_6276191 : Nat := 3222702662422559107548829

theorem tailTrace_6276191 : CollatzResearch.WordTrace tailWord_6276191 prefixEnd_6276191 3222702662422559107548829 := by
  unfold tailWord_6276191
  simp only [CollatzResearch.WordTrace]
  refine ⟨228911491605439369930540427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152607661070292913287026951 228911491605439369930540427)
  ·
    refine ⟨343367237408159054895810641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228911491605439369930540427 343367237408159054895810641)
    ·
      refine ⟨257525428056119291171857981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343367237408159054895810641 257525428056119291171857981)
      ·
        refine ⟨96572035521044734189446743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257525428056119291171857981 96572035521044734189446743)
        ·
          refine ⟨144858053281567101284170115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96572035521044734189446743 144858053281567101284170115)
          ·
            refine ⟨217287079922350651926255173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144858053281567101284170115 217287079922350651926255173)
            ·
              refine ⟨40741327485440747236172845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217287079922350651926255173 40741327485440747236172845)
              ·
                refine ⟨15277997807040280213564817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40741327485440747236172845 15277997807040280213564817)
                ·
                  refine ⟨11458498355280210160173613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15277997807040280213564817 11458498355280210160173613)
                  ·
                    refine ⟨4296936883230078810065105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11458498355280210160173613 4296936883230078810065105)
                    ·
                      refine ⟨3222702662422559107548829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4296936883230078810065105 3222702662422559107548829)
                      ·
                        rfl

theorem cell23_6276191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_6276191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276191 prefixEnd_6276191 := by exact prefixLift 6276191
  have htrace : WordTrace (prefixWord ++ tailWord_6276191) baseStart_6276191 baseEnd_6276191 := by
    simpa [prefixWord, tailWord_6276191, baseEnd_6276191] using wordTrace_append hprefix tailTrace_6276191
  have hstable : (prefixWord ++ tailWord_6276191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276191).length < 2 ^ (prefixWord ++ tailWord_6276191).sum := by decide
  have hdescent : baseEnd_6276191 < baseStart_6276191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276215 : List Nat := [1, 1, 3, 1, 1, 4, 5, 2, 1, 1, 3]
def baseStart_6276215 : Nat := 118140960795 + 6276215 * 2 ^ 59
def prefixEnd_6276215 : Nat := 4983230072969 + 3 ^ 40 * 6276215 * 2
def baseEnd_6276215 : Nat := 3222714985958267013648719

theorem tailTrace_6276215 : CollatzResearch.WordTrace tailWord_6276215 prefixEnd_6276215 3222714985958267013648719 := by
  unfold tailWord_6276215
  simp only [CollatzResearch.WordTrace]
  refine ⟨228912366957352422029414099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152608244638234948019609399 228912366957352422029414099)
  ·
    refine ⟨343368550436028633044121149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228912366957352422029414099 343368550436028633044121149)
    ·
      refine ⟨128763206413510737391545431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343368550436028633044121149 128763206413510737391545431)
      ·
        refine ⟨193144809620266106087318147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128763206413510737391545431 193144809620266106087318147)
        ·
          refine ⟨289717214430399159130977221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193144809620266106087318147 289717214430399159130977221)
          ·
            refine ⟨54321977705699842337058229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 289717214430399159130977221 54321977705699842337058229)
            ·
              refine ⟨5092685409909360219099209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54321977705699842337058229 5092685409909360219099209)
              ·
                refine ⟨3819514057432020164324407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5092685409909360219099209 3819514057432020164324407)
                ·
                  refine ⟨5729271086148030246486611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3819514057432020164324407 5729271086148030246486611)
                  ·
                    refine ⟨8593906629222045369729917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5729271086148030246486611 8593906629222045369729917)
                    ·
                      refine ⟨3222714985958267013648719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8593906629222045369729917 3222714985958267013648719)
                      ·
                        rfl

theorem cell23_6276215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 1, 1, 3].length) (baseStart_6276215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276215 prefixEnd_6276215 := by exact prefixLift 6276215
  have htrace : WordTrace (prefixWord ++ tailWord_6276215) baseStart_6276215 baseEnd_6276215 := by
    simpa [prefixWord, tailWord_6276215, baseEnd_6276215] using wordTrace_append hprefix tailTrace_6276215
  have hstable : (prefixWord ++ tailWord_6276215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276215).length < 2 ^ (prefixWord ++ tailWord_6276215).sum := by decide
  have hdescent : baseEnd_6276215 < baseStart_6276215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276224 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 5]
def baseStart_6276224 : Nat := 118140960795 + 6276224 * 2 ^ 59
def prefixEnd_6276224 : Nat := 4983230072969 + 3 ^ 40 * 6276224 * 2
def baseEnd_6276224 : Nat := 3222719607284157478436177

theorem tailTrace_6276224 : CollatzResearch.WordTrace tailWord_6276224 prefixEnd_6276224 3222719607284157478436177 := by
  unfold tailWord_6276224
  simp only [CollatzResearch.WordTrace]
  refine ⟨114456347607159908283245863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152608463476213211044327817 114456347607159908283245863)
  ·
    refine ⟨171684521410739862424868795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114456347607159908283245863 171684521410739862424868795)
    ·
      refine ⟨257526782116109793637303193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171684521410739862424868795 257526782116109793637303193)
      ·
        refine ⟨193145086587082345227977395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257526782116109793637303193 193145086587082345227977395)
        ·
          refine ⟨289717629880623517841966093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193145086587082345227977395 289717629880623517841966093)
          ·
            refine ⟨108644111205233819190737285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289717629880623517841966093 108644111205233819190737285)
            ·
              refine ⟨20370770850981341098263241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108644111205233819190737285 20370770850981341098263241)
              ·
                refine ⟨15278078138236005823697431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20370770850981341098263241 15278078138236005823697431)
                ·
                  refine ⟨22917117207354008735546147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15278078138236005823697431 22917117207354008735546147)
                  ·
                    refine ⟨34375675811031013103319221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22917117207354008735546147 34375675811031013103319221)
                    ·
                      refine ⟨3222719607284157478436177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34375675811031013103319221 3222719607284157478436177)
                      ·
                        rfl

theorem cell23_6276224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_6276224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276224 prefixEnd_6276224 := by exact prefixLift 6276224
  have htrace : WordTrace (prefixWord ++ tailWord_6276224) baseStart_6276224 baseEnd_6276224 := by
    simpa [prefixWord, tailWord_6276224, baseEnd_6276224] using wordTrace_append hprefix tailTrace_6276224
  have hstable : (prefixWord ++ tailWord_6276224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276224).length < 2 ^ (prefixWord ++ tailWord_6276224).sum := by decide
  have hdescent : baseEnd_6276224 < baseStart_6276224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276234 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_6276234 : Nat := 118140960795 + 6276234 * 2 ^ 59
def prefixEnd_6276234 : Nat := 4983230072969 + 3 ^ 40 * 6276234 * 2
def baseEnd_6276234 : Nat := 3222724742090702439311131

theorem tailTrace_6276234 : CollatzResearch.WordTrace tailWord_6276234 prefixEnd_6276234 3222724742090702439311131 := by
  unfold tailWord_6276234
  simp only [CollatzResearch.WordTrace]
  refine ⟨57228264986070897068588939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152608706629522392182903837 57228264986070897068588939)
  ·
    refine ⟨85842397479106345602883409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57228264986070897068588939 85842397479106345602883409)
    ·
      refine ⟨64381798109329759202162557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85842397479106345602883409 64381798109329759202162557)
      ·
        refine ⟨24143174290998659700810959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64381798109329759202162557 24143174290998659700810959)
        ·
          refine ⟨36214761436497989551216439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24143174290998659700810959 36214761436497989551216439)
          ·
            refine ⟨54322142154746984326824659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36214761436497989551216439 54322142154746984326824659)
            ·
              refine ⟨81483213232120476490236989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54322142154746984326824659 81483213232120476490236989)
              ·
                refine ⟨30556204962045178683838871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81483213232120476490236989 30556204962045178683838871)
                ·
                  refine ⟨45834307443067768025758307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30556204962045178683838871 45834307443067768025758307)
                  ·
                    refine ⟨68751461164601652038637461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45834307443067768025758307 68751461164601652038637461)
                    ·
                      refine ⟨3222724742090702439311131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68751461164601652038637461 3222724742090702439311131)
                      ·
                        rfl

theorem cell23_6276234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_6276234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276234 prefixEnd_6276234 := by exact prefixLift 6276234
  have htrace : WordTrace (prefixWord ++ tailWord_6276234) baseStart_6276234 baseEnd_6276234 := by
    simpa [prefixWord, tailWord_6276234, baseEnd_6276234] using wordTrace_append hprefix tailTrace_6276234
  have hstable : (prefixWord ++ tailWord_6276234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276234).length < 2 ^ (prefixWord ++ tailWord_6276234).sum := by decide
  have hdescent : baseEnd_6276234 < baseStart_6276234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276238 : List Nat := [4, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4]
def baseStart_6276238 : Nat := 118140960795 + 6276238 * 2 ^ 59
def prefixEnd_6276238 : Nat := 4983230072969 + 3 ^ 40 * 6276238 * 2
def baseEnd_6276238 : Nat := 3222726796013320423661113

theorem tailTrace_6276238 : CollatzResearch.WordTrace tailWord_6276238 prefixEnd_6276238 3222726796013320423661113 := by
  unfold tailWord_6276238
  simp only [CollatzResearch.WordTrace]
  refine ⟨28614150729533637119687671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152608803890846064638334245 28614150729533637119687671)
  ·
    refine ⟨42921226094300455679531507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28614150729533637119687671 42921226094300455679531507)
    ·
      refine ⟨64381839141450683519297261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42921226094300455679531507 64381839141450683519297261)
      ·
        refine ⟨24143189678044006319736473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64381839141450683519297261 24143189678044006319736473)
        ·
          refine ⟨18107392258533004739802355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24143189678044006319736473 18107392258533004739802355)
          ·
            refine ⟨27161088387799507109703533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18107392258533004739802355 27161088387799507109703533)
            ·
              refine ⟨10185408145424815166138825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27161088387799507109703533 10185408145424815166138825)
              ·
                refine ⟨7639056109068611374604119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10185408145424815166138825 7639056109068611374604119)
                ·
                  refine ⟨11458584163602917061906179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7639056109068611374604119 11458584163602917061906179)
                  ·
                    refine ⟨17187876245404375592859269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11458584163602917061906179 17187876245404375592859269)
                    ·
                      refine ⟨3222726796013320423661113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17187876245404375592859269 3222726796013320423661113)
                      ·
                        rfl

theorem cell23_6276238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_6276238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276238 prefixEnd_6276238 := by exact prefixLift 6276238
  have htrace : WordTrace (prefixWord ++ tailWord_6276238) baseStart_6276238 baseEnd_6276238 := by
    simpa [prefixWord, tailWord_6276238, baseEnd_6276238] using wordTrace_append hprefix tailTrace_6276238
  have hstable : (prefixWord ++ tailWord_6276238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276238).length < 2 ^ (prefixWord ++ tailWord_6276238).sum := by decide
  have hdescent : baseEnd_6276238 < baseStart_6276238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276255 : List Nat := [1, 1, 2, 6, 2, 1, 3, 1, 1, 1, 4]
def baseStart_6276255 : Nat := 118140960795 + 6276255 * 2 ^ 59
def prefixEnd_6276255 : Nat := 4983230072969 + 3 ^ 40 * 6276255 * 2
def baseEnd_6276255 : Nat := 3222735525184446857148535

theorem tailTrace_6276255 : CollatzResearch.WordTrace tailWord_6276255 prefixEnd_6276255 3222735525184446857148535 := by
  unfold tailWord_6276255
  simp only [CollatzResearch.WordTrace]
  refine ⟨228913825877207508860870219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152609217251471672573913479 228913825877207508860870219)
  ·
    refine ⟨343370738815811263291305329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228913825877207508860870219 343370738815811263291305329)
    ·
      refine ⟨257528054111858447468478997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343370738815811263291305329 257528054111858447468478997)
      ·
        refine ⟨12071627536493364725084953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 257528054111858447468478997 12071627536493364725084953)
        ·
          refine ⟨9053720652370023543813715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12071627536493364725084953 9053720652370023543813715)
          ·
            refine ⟨13580580978555035315720573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9053720652370023543813715 13580580978555035315720573)
            ·
              refine ⟨5092717866958138243395215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13580580978555035315720573 5092717866958138243395215)
              ·
                refine ⟨7639076800437207365092823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5092717866958138243395215 7639076800437207365092823)
                ·
                  refine ⟨11458615200655811047639235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7639076800437207365092823 11458615200655811047639235)
                  ·
                    refine ⟨17187922800983716571458853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11458615200655811047639235 17187922800983716571458853)
                    ·
                      refine ⟨3222735525184446857148535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17187922800983716571458853 3222735525184446857148535)
                      ·
                        rfl

theorem cell23_6276255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_6276255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276255 prefixEnd_6276255 := by exact prefixLift 6276255
  have htrace : WordTrace (prefixWord ++ tailWord_6276255) baseStart_6276255 baseEnd_6276255 := by
    simpa [prefixWord, tailWord_6276255, baseEnd_6276255] using wordTrace_append hprefix tailTrace_6276255
  have hstable : (prefixWord ++ tailWord_6276255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276255).length < 2 ^ (prefixWord ++ tailWord_6276255).sum := by decide
  have hdescent : baseEnd_6276255 < baseStart_6276255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276271 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 4, 1, 3]
def baseStart_6276271 : Nat := 118140960795 + 6276271 * 2 ^ 59
def prefixEnd_6276271 : Nat := 4983230072969 + 3 ^ 40 * 6276271 * 2
def baseEnd_6276271 : Nat := 3222743740874918794548461

theorem tailTrace_6276271 : CollatzResearch.WordTrace tailWord_6276271 prefixEnd_6276271 3222743740874918794548461 := by
  unfold tailWord_6276271
  simp only [CollatzResearch.WordTrace]
  refine ⟨228914409445149543593452667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152609606296766362395635111 228914409445149543593452667)
  ·
    refine ⟨343371614167724315390179001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228914409445149543593452667 343371614167724315390179001)
    ·
      refine ⟨257528710625793236542634251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343371614167724315390179001 257528710625793236542634251)
      ·
        refine ⟨386293065938689854813951377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257528710625793236542634251 386293065938689854813951377)
        ·
          refine ⟨289719799454017391110463533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386293065938689854813951377 289719799454017391110463533)
          ·
            refine ⟨108644924795256521666423825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289719799454017391110463533 108644924795256521666423825)
            ·
              refine ⟨81483693596442391249817869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108644924795256521666423825 81483693596442391249817869)
              ·
                refine ⟨30556385098665896718681701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81483693596442391249817869 30556385098665896718681701)
                ·
                  refine ⟨5729322205999855634752819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30556385098665896718681701 5729322205999855634752819)
                  ·
                    refine ⟨8593983308999783452129229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5729322205999855634752819 8593983308999783452129229)
                    ·
                      refine ⟨3222743740874918794548461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8593983308999783452129229 3222743740874918794548461)
                      ·
                        rfl

theorem cell23_6276271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 1, 3].length) (baseStart_6276271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276271 prefixEnd_6276271 := by exact prefixLift 6276271
  have htrace : WordTrace (prefixWord ++ tailWord_6276271) baseStart_6276271 baseEnd_6276271 := by
    simpa [prefixWord, tailWord_6276271, baseEnd_6276271] using wordTrace_append hprefix tailTrace_6276271
  have hstable : (prefixWord ++ tailWord_6276271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276271).length < 2 ^ (prefixWord ++ tailWord_6276271).sum := by decide
  have hdescent : baseEnd_6276271 < baseStart_6276271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276274 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 2, 7]
def baseStart_6276274 : Nat := 118140960795 + 6276274 * 2 ^ 59
def prefixEnd_6276274 : Nat := 4983230072969 + 3 ^ 40 * 6276274 * 2
def baseEnd_6276274 : Nat := 1074248427105627427603649

theorem tailTrace_6276274 : CollatzResearch.WordTrace tailWord_6276274 prefixEnd_6276274 1074248427105627427603649 := by
  unfold tailWord_6276274
  simp only [CollatzResearch.WordTrace]
  refine ⟨57228629716034668776452969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152609679242759116737207917 57228629716034668776452969)
  ·
    refine ⟨42921472287026001582339727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57228629716034668776452969 42921472287026001582339727)
    ·
      refine ⟨64382208430539002373509591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42921472287026001582339727 64382208430539002373509591)
      ·
        refine ⟨96573312645808503560264387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64382208430539002373509591 96573312645808503560264387)
        ·
          refine ⟨144859968968712755340396581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96573312645808503560264387 144859968968712755340396581)
          ·
            refine ⟨27161244181633641626324359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144859968968712755340396581 27161244181633641626324359)
            ·
              refine ⟨40741866272450462439486539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27161244181633641626324359 40741866272450462439486539)
              ·
                refine ⟨61112799408675693659229809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40741866272450462439486539 61112799408675693659229809)
                ·
                  refine ⟨45834599556506770244422357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61112799408675693659229809 45834599556506770244422357)
                  ·
                    refine ⟨1074248427105627427603649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45834599556506770244422357 1074248427105627427603649)
                    ·
                      rfl

theorem cell23_6276274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_6276274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276274 prefixEnd_6276274 := by exact prefixLift 6276274
  have htrace : WordTrace (prefixWord ++ tailWord_6276274) baseStart_6276274 baseEnd_6276274 := by
    simpa [prefixWord, tailWord_6276274, baseEnd_6276274] using wordTrace_append hprefix tailTrace_6276274
  have hstable : (prefixWord ++ tailWord_6276274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276274).length < 2 ^ (prefixWord ++ tailWord_6276274).sum := by decide
  have hdescent : baseEnd_6276274 < baseStart_6276274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276288 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 3]
def baseStart_6276288 : Nat := 118140960795 + 6276288 * 2 ^ 59
def prefixEnd_6276288 : Nat := 4983230072969 + 3 ^ 40 * 6276288 * 2
def baseEnd_6276288 : Nat := 3222752470046045228035883

theorem tailTrace_6276288 : CollatzResearch.WordTrace tailWord_6276288 prefixEnd_6276288 3222752470046045228035883 := by
  unfold tailWord_6276288
  simp only [CollatzResearch.WordTrace]
  refine ⟨114457514743043977748410759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152610019657391970331214345 114457514743043977748410759)
  ·
    refine ⟨171686272114565966622616139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114457514743043977748410759 171686272114565966622616139)
    ·
      refine ⟨257529408171848949933924209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171686272114565966622616139 257529408171848949933924209)
      ·
        refine ⟨193147056128886712450443157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257529408171848949933924209 193147056128886712450443157)
        ·
          refine ⟨9053768256041564646114523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 193147056128886712450443157 9053768256041564646114523)
          ·
            refine ⟨13580652384062346969171785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9053768256041564646114523 13580652384062346969171785)
            ·
              refine ⟨10185489288046760226878839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13580652384062346969171785 10185489288046760226878839)
              ·
                refine ⟨15278233932070140340318259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10185489288046760226878839 15278233932070140340318259)
                ·
                  refine ⟨22917350898105210510477389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15278233932070140340318259 22917350898105210510477389)
                  ·
                    refine ⟨8594006586789453941429021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22917350898105210510477389 8594006586789453941429021)
                    ·
                      refine ⟨3222752470046045228035883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8594006586789453941429021 3222752470046045228035883)
                      ·
                        rfl

theorem cell23_6276288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_6276288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276288 prefixEnd_6276288 := by exact prefixLift 6276288
  have htrace : WordTrace (prefixWord ++ tailWord_6276288) baseStart_6276288 baseEnd_6276288 := by
    simpa [prefixWord, tailWord_6276288, baseEnd_6276288] using wordTrace_append hprefix tailTrace_6276288
  have hstable : (prefixWord ++ tailWord_6276288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276288).length < 2 ^ (prefixWord ++ tailWord_6276288).sum := by decide
  have hdescent : baseEnd_6276288 < baseStart_6276288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276298 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 3, 3, 2]
def baseStart_6276298 : Nat := 118140960795 + 6276298 * 2 ^ 59
def prefixEnd_6276298 : Nat := 4983230072969 + 3 ^ 40 * 6276298 * 2
def baseEnd_6276298 : Nat := 3222757604852590188910837

theorem tailTrace_6276298 : CollatzResearch.WordTrace tailWord_6276298 prefixEnd_6276298 3222757604852590188910837 := by
  unfold tailWord_6276298
  simp only [CollatzResearch.WordTrace]
  refine ⟨57228848554012931801171387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152610262810701151469790365 57228848554012931801171387)
  ·
    refine ⟨85843272831019397701757081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57228848554012931801171387 85843272831019397701757081)
    ·
      refine ⟨64382454623264548276317811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85843272831019397701757081 64382454623264548276317811)
      ·
        refine ⟨96573681934896822414476717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64382454623264548276317811 96573681934896822414476717)
        ·
          refine ⟨36215130725586308405428769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96573681934896822414476717 36215130725586308405428769)
          ·
            refine ⟨27161348044189731304071577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36215130725586308405428769 27161348044189731304071577)
            ·
              refine ⟨20371011033142298478053683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27161348044189731304071577 20371011033142298478053683)
              ·
                refine ⟨30556516549713447717080525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20371011033142298478053683 30556516549713447717080525)
                ·
                  refine ⟨11458693706142542893905197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30556516549713447717080525 11458693706142542893905197)
                  ·
                    refine ⟨4297010139803453585214449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11458693706142542893905197 4297010139803453585214449)
                    ·
                      refine ⟨3222757604852590188910837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4297010139803453585214449 3222757604852590188910837)
                      ·
                        rfl

theorem cell23_6276298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_6276298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276298 prefixEnd_6276298 := by exact prefixLift 6276298
  have htrace : WordTrace (prefixWord ++ tailWord_6276298) baseStart_6276298 baseEnd_6276298 := by
    simpa [prefixWord, tailWord_6276298, baseEnd_6276298] using wordTrace_append hprefix tailTrace_6276298
  have hstable : (prefixWord ++ tailWord_6276298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276298).length < 2 ^ (prefixWord ++ tailWord_6276298).sum := by decide
  have hdescent : baseEnd_6276298 < baseStart_6276298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276314 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5]
def baseStart_6276314 : Nat := 118140960795 + 6276314 * 2 ^ 59
def prefixEnd_6276314 : Nat := 4983230072969 + 3 ^ 40 * 6276314 * 2
def baseEnd_6276314 : Nat := 3222765820543062126310763

theorem tailTrace_6276314 : CollatzResearch.WordTrace tailWord_6276314 prefixEnd_6276314 3222765820543062126310763 := by
  unfold tailWord_6276314
  simp only [CollatzResearch.WordTrace]
  refine ⟨57228994445998440484316999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152610651855995841291511997 57228994445998440484316999)
  ·
    refine ⟨85843491668997660726475499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57228994445998440484316999 85843491668997660726475499)
    ·
      refine ⟨128765237503496491089713249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85843491668997660726475499 128765237503496491089713249)
      ·
        refine ⟨96573928127622368317284937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128765237503496491089713249 96573928127622368317284937)
        ·
          refine ⟨72430446095716776237963703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96573928127622368317284937 72430446095716776237963703)
          ·
            refine ⟨108645669143575164356945555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72430446095716776237963703 108645669143575164356945555)
            ·
              refine ⟨162968503715362746535418333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108645669143575164356945555 162968503715362746535418333)
              ·
                refine ⟨61113188893261029950781875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162968503715362746535418333 61113188893261029950781875)
                ·
                  refine ⟨91669783339891544926172813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61113188893261029950781875 91669783339891544926172813)
                  ·
                    refine ⟨34376168752459329347314805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91669783339891544926172813 34376168752459329347314805)
                    ·
                      refine ⟨3222765820543062126310763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34376168752459329347314805 3222765820543062126310763)
                      ·
                        rfl

theorem cell23_6276314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_6276314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276314 prefixEnd_6276314 := by exact prefixLift 6276314
  have htrace : WordTrace (prefixWord ++ tailWord_6276314) baseStart_6276314 baseEnd_6276314 := by
    simpa [prefixWord, tailWord_6276314, baseEnd_6276314] using wordTrace_append hprefix tailTrace_6276314
  have hstable : (prefixWord ++ tailWord_6276314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276314).length < 2 ^ (prefixWord ++ tailWord_6276314).sum := by decide
  have hdescent : baseEnd_6276314 < baseStart_6276314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276371 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 3, 7, 2]
def baseStart_6276371 : Nat := 118140960795 + 6276371 * 2 ^ 59
def prefixEnd_6276371 : Nat := 4983230072969 + 3 ^ 40 * 6276371 * 2
def baseEnd_6276371 : Nat := 3222795088940368403298001

theorem tailTrace_6276371 : CollatzResearch.WordTrace tailWord_6276371 prefixEnd_6276371 3222795088940368403298001 := by
  unfold tailWord_6276371
  simp only [CollatzResearch.WordTrace]
  refine ⟨228918056744787260672092967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152612037829858173781395311 228918056744787260672092967)
  ·
    refine ⟨343377085117180891008139451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228918056744787260672092967 343377085117180891008139451)
    ·
      refine ⟨515065627675771336512209177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343377085117180891008139451 515065627675771336512209177)
      ·
        refine ⟨386299220756828502384156883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515065627675771336512209177 386299220756828502384156883)
        ·
          refine ⟨579448831135242753576235325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386299220756828502384156883 579448831135242753576235325)
          ·
            refine ⟨217293311675716032591088247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 579448831135242753576235325 217293311675716032591088247)
            ·
              refine ⟨325939967513574048886632371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217293311675716032591088247 325939967513574048886632371)
              ·
                refine ⟨488909951270361073329948557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325939967513574048886632371 488909951270361073329948557)
                ·
                  refine ⟨183341231726385402498730709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488909951270361073329948557 183341231726385402498730709)
                  ·
                    refine ⟨4297060118587157871064001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 183341231726385402498730709 4297060118587157871064001)
                    ·
                      refine ⟨3222795088940368403298001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4297060118587157871064001 3222795088940368403298001)
                      ·
                        rfl

theorem cell23_6276371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 7, 2].length) (baseStart_6276371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276371 prefixEnd_6276371 := by exact prefixLift 6276371
  have htrace : WordTrace (prefixWord ++ tailWord_6276371) baseStart_6276371 baseEnd_6276371 := by
    simpa [prefixWord, tailWord_6276371, baseEnd_6276371] using wordTrace_append hprefix tailTrace_6276371
  have hstable : (prefixWord ++ tailWord_6276371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276371).length < 2 ^ (prefixWord ++ tailWord_6276371).sum := by decide
  have hdescent : baseEnd_6276371 < baseStart_6276371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276388 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 2, 5, 2]
def baseStart_6276388 : Nat := 118140960795 + 6276388 * 2 ^ 59
def prefixEnd_6276388 : Nat := 4983230072969 + 3 ^ 40 * 6276388 * 2
def baseEnd_6276388 : Nat := 3222803818111494836785423

theorem tailTrace_6276388 : CollatzResearch.WordTrace tailWord_6276388 prefixEnd_6276388 3222803818111494836785423 := by
  unfold tailWord_6276388
  simp only [CollatzResearch.WordTrace]
  refine ⟨114459338392862836287730909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152612451190483781716974545 114459338392862836287730909)
  ·
    refine ⟨42922251897323563607899091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114459338392862836287730909 42922251897323563607899091)
    ·
      refine ⟨64383377845985345411848637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42922251897323563607899091 64383377845985345411848637)
      ·
        refine ⟨24143766692244504529443239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64383377845985345411848637 24143766692244504529443239)
        ·
          refine ⟨36215650038366756794164859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24143766692244504529443239 36215650038366756794164859)
          ·
            refine ⟨54323475057550135191247289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36215650038366756794164859 54323475057550135191247289)
            ·
              refine ⟨40742606293162601393435467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54323475057550135191247289 40742606293162601393435467)
              ·
                refine ⟨61113909439743902090153201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40742606293162601393435467 61113909439743902090153201)
                ·
                  refine ⟨45835432079807926567614901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61113909439743902090153201 45835432079807926567614901)
                  ·
                    refine ⟨4297071757481993115713897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45835432079807926567614901 4297071757481993115713897)
                    ·
                      refine ⟨3222803818111494836785423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4297071757481993115713897 3222803818111494836785423)
                      ·
                        rfl

theorem cell23_6276388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_6276388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276388 prefixEnd_6276388 := by exact prefixLift 6276388
  have htrace : WordTrace (prefixWord ++ tailWord_6276388) baseStart_6276388 baseEnd_6276388 := by
    simpa [prefixWord, tailWord_6276388, baseEnd_6276388] using wordTrace_append hprefix tailTrace_6276388
  have hstable : (prefixWord ++ tailWord_6276388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276388).length < 2 ^ (prefixWord ++ tailWord_6276388).sum := by decide
  have hdescent : baseEnd_6276388 < baseStart_6276388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276421 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 1, 4, 3]
def baseStart_6276421 : Nat := 118140960795 + 6276421 * 2 ^ 59
def prefixEnd_6276421 : Nat := 4983230072969 + 3 ^ 40 * 6276421 * 2
def baseEnd_6276421 : Nat := 3222820762973093207672771

theorem tailTrace_6276421 : CollatzResearch.WordTrace tailWord_6276421 prefixEnd_6276421 3222820762973093207672771 := by
  unfold tailWord_6276421
  simp only [CollatzResearch.WordTrace]
  refine ⟨228919880394606119211413117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152613253596404079474275411 228919880394606119211413117)
  ·
    refine ⟨85844955147977294704279919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228919880394606119211413117 85844955147977294704279919)
    ·
      refine ⟨128767432721965942056419879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85844955147977294704279919 128767432721965942056419879)
      ·
        refine ⟨193151149082948913084629819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128767432721965942056419879 193151149082948913084629819)
        ·
          refine ⟨289726723624423369626944729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193151149082948913084629819 289726723624423369626944729)
          ·
            refine ⟨217295042718317527220208547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289726723624423369626944729 217295042718317527220208547)
            ·
              refine ⟨325942564077476290830312821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217295042718317527220208547 325942564077476290830312821)
              ·
                refine ⟨30557115382263402265341827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 325942564077476290830312821 30557115382263402265341827)
                ·
                  refine ⟨45835673073395103398012741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30557115382263402265341827 45835673073395103398012741)
                  ·
                    refine ⟨8594188701261581887127389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45835673073395103398012741 8594188701261581887127389)
                    ·
                      refine ⟨3222820762973093207672771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8594188701261581887127389 3222820762973093207672771)
                      ·
                        rfl

theorem cell23_6276421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_6276421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276421 prefixEnd_6276421 := by exact prefixLift 6276421
  have htrace : WordTrace (prefixWord ++ tailWord_6276421) baseStart_6276421 baseEnd_6276421 := by
    simpa [prefixWord, tailWord_6276421, baseEnd_6276421] using wordTrace_append hprefix tailTrace_6276421
  have hstable : (prefixWord ++ tailWord_6276421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276421).length < 2 ^ (prefixWord ++ tailWord_6276421).sum := by decide
  have hdescent : baseEnd_6276421 < baseStart_6276421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276441 : List Nat := [1, 2, 1, 2, 2, 2, 3, 4, 6]
def baseStart_6276441 : Nat := 118140960795 + 6276441 * 2 ^ 59
def prefixEnd_6276441 : Nat := 4983230072969 + 3 ^ 40 * 6276441 * 2
def baseEnd_6276441 : Nat := 358092336954020347713631

theorem tailTrace_6276441 : CollatzResearch.WordTrace tailWord_6276441 prefixEnd_6276441 358092336954020347713631 := by
  unfold tailWord_6276441
  simp only [CollatzResearch.WordTrace]
  refine ⟨228920609854533662627141177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152613739903022441751427451 228920609854533662627141177)
  ·
    refine ⟨171690457390900246970355883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228920609854533662627141177 171690457390900246970355883)
    ·
      refine ⟨257535686086350370455533825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171690457390900246970355883 257535686086350370455533825)
      ·
        refine ⟨193151764564762777841650369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257535686086350370455533825 193151764564762777841650369)
        ·
          refine ⟨144863823423572083381237777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193151764564762777841650369 144863823423572083381237777)
          ·
            refine ⟨108647867567679062535928333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144863823423572083381237777 108647867567679062535928333)
            ·
              refine ⟨40742950337879648450973125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108647867567679062535928333 40742950337879648450973125)
              ·
                refine ⟨7639303188352434084557461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40742950337879648450973125 7639303188352434084557461)
                ·
                  refine ⟨358092336954020347713631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7639303188352434084557461 358092336954020347713631)
                  ·
                    rfl

theorem cell23_6276441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 6].length) (baseStart_6276441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276441 prefixEnd_6276441 := by exact prefixLift 6276441
  have htrace : WordTrace (prefixWord ++ tailWord_6276441) baseStart_6276441 baseEnd_6276441 := by
    simpa [prefixWord, tailWord_6276441, baseEnd_6276441] using wordTrace_append hprefix tailTrace_6276441
  have hstable : (prefixWord ++ tailWord_6276441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276441).length < 2 ^ (prefixWord ++ tailWord_6276441).sum := by decide
  have hdescent : baseEnd_6276441 < baseStart_6276441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276462 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 3, 4]
def baseStart_6276462 : Nat := 118140960795 + 6276462 * 2 ^ 59
def prefixEnd_6276462 : Nat := 4983230072969 + 3 ^ 40 * 6276462 * 2
def baseEnd_6276462 : Nat := 1074280605226642515753361

theorem tailTrace_6276462 : CollatzResearch.WordTrace tailWord_6276462 prefixEnd_6276462 1074280605226642515753361 := by
  unfold tailWord_6276462
  simp only [CollatzResearch.WordTrace]
  refine ⟨28615171973432197901706955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152614250524971722142437093 28615171973432197901706955)
  ·
    refine ⟨42922757960148296852560433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28615171973432197901706955 42922757960148296852560433)
    ·
      refine ⟨32192068470111222639420325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42922757960148296852560433 32192068470111222639420325)
      ·
        refine ⟨6036012838145854244891311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32192068470111222639420325 6036012838145854244891311)
        ·
          refine ⟨9054019257218781367336967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6036012838145854244891311 9054019257218781367336967)
          ·
            refine ⟨13581028885828172051005451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9054019257218781367336967 13581028885828172051005451)
            ·
              refine ⟨20371543328742258076508177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13581028885828172051005451 20371543328742258076508177)
              ·
                refine ⟨15278657496556693557381133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20371543328742258076508177 15278657496556693557381133)
                ·
                  refine ⟨5729496561208760084017925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15278657496556693557381133 5729496561208760084017925)
                  ·
                    refine ⟨1074280605226642515753361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5729496561208760084017925 1074280605226642515753361)
                    ·
                      rfl

theorem cell23_6276462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_6276462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276462 prefixEnd_6276462 := by exact prefixLift 6276462
  have htrace : WordTrace (prefixWord ++ tailWord_6276462) baseStart_6276462 baseEnd_6276462 := by
    simpa [prefixWord, tailWord_6276462, baseEnd_6276462] using wordTrace_append hprefix tailTrace_6276462
  have hstable : (prefixWord ++ tailWord_6276462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276462).length < 2 ^ (prefixWord ++ tailWord_6276462).sum := by decide
  have hdescent : baseEnd_6276462 < baseStart_6276462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276471 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 3, 5]
def baseStart_6276471 : Nat := 118140960795 + 6276471 * 2 ^ 59
def prefixEnd_6276471 : Nat := 4983230072969 + 3 ^ 40 * 6276471 * 2
def baseEnd_6276471 : Nat := 1074282145668606004015847

theorem tailTrace_6276471 : CollatzResearch.WordTrace tailWord_6276471 prefixEnd_6276471 1074282145668606004015847 := by
  unfold tailWord_6276471
  simp only [CollatzResearch.WordTrace]
  refine ⟨228921704044424977750733267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152614469362949985167155511 228921704044424977750733267)
  ·
    refine ⟨343382556066637466626099901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228921704044424977750733267 343382556066637466626099901)
    ·
      refine ⟨128768458524989049984787463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343382556066637466626099901 128768458524989049984787463)
      ·
        refine ⟨193152687787483574977181195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128768458524989049984787463 193152687787483574977181195)
        ·
          refine ⟨289729031681225362465771793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193152687787483574977181195 289729031681225362465771793)
          ·
            refine ⟨217296773760919021849328845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289729031681225362465771793 217296773760919021849328845)
            ·
              refine ⟨81486290160344633193498317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217296773760919021849328845 81486290160344633193498317)
              ·
                refine ⟨30557358810129237447561869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81486290160344633193498317 30557358810129237447561869)
                ·
                  refine ⟨11459009553798464042835701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30557358810129237447561869 11459009553798464042835701)
                  ·
                    refine ⟨1074282145668606004015847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11459009553798464042835701 1074282145668606004015847)
                    ·
                      rfl

theorem cell23_6276471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_6276471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276471 prefixEnd_6276471 := by exact prefixLift 6276471
  have htrace : WordTrace (prefixWord ++ tailWord_6276471) baseStart_6276471 baseEnd_6276471 := by
    simpa [prefixWord, tailWord_6276471, baseEnd_6276471] using wordTrace_append hprefix tailTrace_6276471
  have hstable : (prefixWord ++ tailWord_6276471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276471).length < 2 ^ (prefixWord ++ tailWord_6276471).sum := by decide
  have hdescent : baseEnd_6276471 < baseStart_6276471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276501 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 3, 6]
def baseStart_6276501 : Nat := 118140960795 + 6276501 * 2 ^ 59
def prefixEnd_6276501 : Nat := 4983230072969 + 3 ^ 40 * 6276501 * 2
def baseEnd_6276501 : Nat := 1074287280475150964890801

theorem tailTrace_6276501 : CollatzResearch.WordTrace tailWord_6276501 prefixEnd_6276501 1074287280475150964890801 := by
  unfold tailWord_6276501
  simp only [CollatzResearch.WordTrace]
  refine ⟨228922798234316292874325357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152615198822877528582883571 228922798234316292874325357)
  ·
    refine ⟨85846049337868609827872009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228922798234316292874325357 85846049337868609827872009)
    ·
      refine ⟨64384537003401457370904007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85846049337868609827872009 64384537003401457370904007)
      ·
        refine ⟨96576805505102186056356011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64384537003401457370904007 96576805505102186056356011)
        ·
          refine ⟨144865208257653279084534017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96576805505102186056356011 144865208257653279084534017)
          ·
            refine ⟨108648906193239959313400513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144865208257653279084534017 108648906193239959313400513)
            ·
              refine ⟨81486679644929969485050385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108648906193239959313400513 81486679644929969485050385)
              ·
                refine ⟨61115009733697477113787789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81486679644929969485050385 61115009733697477113787789)
                ·
                  refine ⟨22918128650136553917670421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61115009733697477113787789 22918128650136553917670421)
                  ·
                    refine ⟨1074287280475150964890801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22918128650136553917670421 1074287280475150964890801)
                    ·
                      rfl

theorem cell23_6276501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_6276501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276501 prefixEnd_6276501 := by exact prefixLift 6276501
  have htrace : WordTrace (prefixWord ++ tailWord_6276501) baseStart_6276501 baseEnd_6276501 := by
    simpa [prefixWord, tailWord_6276501, baseEnd_6276501] using wordTrace_append hprefix tailTrace_6276501
  have hstable : (prefixWord ++ tailWord_6276501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276501).length < 2 ^ (prefixWord ++ tailWord_6276501).sum := by decide
  have hdescent : baseEnd_6276501 < baseStart_6276501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276548 : List Nat := [2, 3, 3, 2, 1, 1, 11]
def baseStart_6276548 : Nat := 118140960795 + 6276548 * 2 ^ 59
def prefixEnd_6276548 : Nat := 4983230072969 + 3 ^ 40 * 6276548 * 2
def baseEnd_6276548 : Nat := 39788715740940916182527

theorem tailTrace_6276548 : CollatzResearch.WordTrace tailWord_6276548 prefixEnd_6276548 39788715740940916182527 := by
  unfold tailWord_6276548
  simp only [CollatzResearch.WordTrace]
  refine ⟨114462256232573009950643149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152616341643430679934190865 114462256232573009950643149)
  ·
    refine ⟨42923346087214878731491181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114462256232573009950643149 42923346087214878731491181)
    ·
      refine ⟨16096254782705579524309193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42923346087214878731491181 16096254782705579524309193)
      ·
        refine ⟨12072191087029184643231895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16096254782705579524309193 12072191087029184643231895)
        ·
          refine ⟨18108286630543776964847843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12072191087029184643231895 18108286630543776964847843)
          ·
            refine ⟨27162429945815665447271765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18108286630543776964847843 27162429945815665447271765)
            ·
              refine ⟨39788715740940916182527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27162429945815665447271765 39788715740940916182527)
              ·
                rfl

theorem cell23_6276548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 11].length) (baseStart_6276548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276548 prefixEnd_6276548 := by exact prefixLift 6276548
  have htrace : WordTrace (prefixWord ++ tailWord_6276548) baseStart_6276548 baseEnd_6276548 := by
    simpa [prefixWord, tailWord_6276548, baseEnd_6276548] using wordTrace_append hprefix tailTrace_6276548
  have hstable : (prefixWord ++ tailWord_6276548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276548).length < 2 ^ (prefixWord ++ tailWord_6276548).sum := by decide
  have hdescent : baseEnd_6276548 < baseStart_6276548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276609 : List Nat := [1, 2, 4, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_6276609 : Nat := 118140960795 + 6276609 * 2 ^ 59
def prefixEnd_6276609 : Nat := 4983230072969 + 3 ^ 40 * 6276609 * 2
def baseEnd_6276609 : Nat := 3222917297336138472121907

theorem tailTrace_6276609 : CollatzResearch.WordTrace tailWord_6276609 prefixEnd_6276609 3222917297336138472121907 := by
  unfold tailWord_6276609
  simp only [CollatzResearch.WordTrace]
  refine ⟨228926737317925027319256881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152617824878616684879504587 228926737317925027319256881)
  ·
    refine ⟨171695052988443770489442661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228926737317925027319256881 171695052988443770489442661)
    ·
      refine ⟨32192822435333206966770499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171695052988443770489442661 32192822435333206966770499)
      ·
        refine ⟨48289233652999810450155749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32192822435333206966770499 48289233652999810450155749)
        ·
          refine ⟨9054231309937464459404203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48289233652999810450155749 9054231309937464459404203)
          ·
            refine ⟨13581346964906196689106305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9054231309937464459404203 13581346964906196689106305)
            ·
              refine ⟨10186010223679647516829729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13581346964906196689106305 10186010223679647516829729)
              ·
                refine ⟨7639507667759735637622297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10186010223679647516829729 7639507667759735637622297)
                ·
                  refine ⟨5729630750819801728216723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7639507667759735637622297 5729630750819801728216723)
                  ·
                    refine ⟨8594446126229702592325085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5729630750819801728216723 8594446126229702592325085)
                    ·
                      refine ⟨3222917297336138472121907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8594446126229702592325085 3222917297336138472121907)
                      ·
                        rfl

theorem cell23_6276609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_6276609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276609 prefixEnd_6276609 := by exact prefixLift 6276609
  have htrace : WordTrace (prefixWord ++ tailWord_6276609) baseStart_6276609 baseEnd_6276609 := by
    simpa [prefixWord, tailWord_6276609, baseEnd_6276609] using wordTrace_append hprefix tailTrace_6276609
  have hstable : (prefixWord ++ tailWord_6276609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276609).length < 2 ^ (prefixWord ++ tailWord_6276609).sum := by decide
  have hdescent : baseEnd_6276609 < baseStart_6276609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276610 : List Nat := [3, 4, 1, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_6276610 : Nat := 118140960795 + 6276610 * 2 ^ 59
def prefixEnd_6276610 : Nat := 4983230072969 + 3 ^ 40 * 6276610 * 2
def baseEnd_6276610 : Nat := 3222917810816792968209403

theorem tailTrace_6276610 : CollatzResearch.WordTrace tailWord_6276610 prefixEnd_6276610 3222917810816792968209403 := by
  unfold tailWord_6276610
  simp only [CollatzResearch.WordTrace]
  refine ⟨57231693447730351122510821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152617849193947602993362189 57231693447730351122510821)
  ·
    refine ⟨10730942521449440835470779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57231693447730351122510821 10730942521449440835470779)
    ·
      refine ⟨16096413782174161253206169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10730942521449440835470779 16096413782174161253206169)
      ·
        refine ⟨12072310336630620939904627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16096413782174161253206169 12072310336630620939904627)
        ·
          refine ⟨18108465504945931409856941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12072310336630620939904627 18108465504945931409856941)
          ·
            refine ⟨6790674564354724278696353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18108465504945931409856941 6790674564354724278696353)
            ·
              refine ⟨5093005923266043209022265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6790674564354724278696353 5093005923266043209022265)
              ·
                refine ⟨3819754442449532406766699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5093005923266043209022265 3819754442449532406766699)
                ·
                  refine ⟨5729631663674298610150049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3819754442449532406766699 5729631663674298610150049)
                  ·
                    refine ⟨4297223747755723957612537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5729631663674298610150049 4297223747755723957612537)
                    ·
                      refine ⟨3222917810816792968209403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4297223747755723957612537 3222917810816792968209403)
                      ·
                        rfl

theorem cell23_6276610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_6276610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276610 prefixEnd_6276610 := by exact prefixLift 6276610
  have htrace : WordTrace (prefixWord ++ tailWord_6276610) baseStart_6276610 baseEnd_6276610 := by
    simpa [prefixWord, tailWord_6276610, baseEnd_6276610] using wordTrace_append hprefix tailTrace_6276610
  have hstable : (prefixWord ++ tailWord_6276610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276610).length < 2 ^ (prefixWord ++ tailWord_6276610).sum := by decide
  have hdescent : baseEnd_6276610 < baseStart_6276610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276665 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 2, 3, 3]
def baseStart_6276665 : Nat := 118140960795 + 6276665 * 2 ^ 59
def prefixEnd_6276665 : Nat := 4983230072969 + 3 ^ 40 * 6276665 * 2
def baseEnd_6276665 : Nat := 3222946052252790253021649

theorem tailTrace_6276665 : CollatzResearch.WordTrace tailWord_6276665 prefixEnd_6276665 3222946052252790253021649 := by
  unfold tailWord_6276665
  simp only [CollatzResearch.WordTrace]
  refine ⟨228928779805722148883295449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152619186537148099255530299 228928779805722148883295449)
  ·
    refine ⟨171696584854291611662471587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228928779805722148883295449 171696584854291611662471587)
    ·
      refine ⟨257544877281437417493707381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171696584854291611662471587 257544877281437417493707381)
      ·
        refine ⟨24144832245134757890035067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 257544877281437417493707381 24144832245134757890035067)
        ·
          refine ⟨36217248367702136835052601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24144832245134757890035067 36217248367702136835052601)
          ·
            refine ⟨27162936275776602626289451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36217248367702136835052601 27162936275776602626289451)
            ·
              refine ⟨40744404413664903939434177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27162936275776602626289451 40744404413664903939434177)
              ·
                refine ⟨30558303310248677954575633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40744404413664903939434177 30558303310248677954575633)
                ·
                  refine ⟨22918727482686508465931725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30558303310248677954575633 22918727482686508465931725)
                  ·
                    refine ⟨8594522806007440674724397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22918727482686508465931725 8594522806007440674724397)
                    ·
                      refine ⟨3222946052252790253021649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8594522806007440674724397 3222946052252790253021649)
                      ·
                        rfl

theorem cell23_6276665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_6276665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276665 prefixEnd_6276665 := by exact prefixLift 6276665
  have htrace : WordTrace (prefixWord ++ tailWord_6276665) baseStart_6276665 baseEnd_6276665 := by
    simpa [prefixWord, tailWord_6276665, baseEnd_6276665] using wordTrace_append hprefix tailTrace_6276665
  have hstable : (prefixWord ++ tailWord_6276665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276665).length < 2 ^ (prefixWord ++ tailWord_6276665).sum := by decide
  have hdescent : baseEnd_6276665 < baseStart_6276665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276688 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 4]
def baseStart_6276688 : Nat := 118140960795 + 6276688 * 2 ^ 59
def prefixEnd_6276688 : Nat := 4983230072969 + 3 ^ 40 * 6276688 * 2
def baseEnd_6276688 : Nat := 3222957862307843663034043

theorem tailTrace_6276688 : CollatzResearch.WordTrace tailWord_6276688 prefixEnd_6276688 3222957862307843663034043 := by
  unfold tailWord_6276688
  simp only [CollatzResearch.WordTrace]
  refine ⟨114464809342319411905691359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152619745789759215874255145 114464809342319411905691359)
  ·
    refine ⟨171697214013479117858537039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114464809342319411905691359 171697214013479117858537039)
    ·
      refine ⟨257545821020218676787805559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171697214013479117858537039 257545821020218676787805559)
      ·
        refine ⟨386318731530328015181708339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257545821020218676787805559 386318731530328015181708339)
        ·
          refine ⟨579478097295492022772562509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386318731530328015181708339 579478097295492022772562509)
          ·
            refine ⟨217304286485809508539710941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 579478097295492022772562509 217304286485809508539710941)
            ·
              refine ⟨81489107432178565702391603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217304286485809508539710941 81489107432178565702391603)
              ·
                refine ⟨122233661148267848553587405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81489107432178565702391603 122233661148267848553587405)
                ·
                  refine ⟨45837622930600443207595277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122233661148267848553587405 45837622930600443207595277)
                  ·
                    refine ⟨17189108598975166202848229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45837622930600443207595277 17189108598975166202848229)
                    ·
                      refine ⟨3222957862307843663034043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17189108598975166202848229 3222957862307843663034043)
                      ·
                        rfl

theorem cell23_6276688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_6276688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276688 prefixEnd_6276688 := by exact prefixLift 6276688
  have htrace : WordTrace (prefixWord ++ tailWord_6276688) baseStart_6276688 baseEnd_6276688 := by
    simpa [prefixWord, tailWord_6276688, baseEnd_6276688] using wordTrace_append hprefix tailTrace_6276688
  have hstable : (prefixWord ++ tailWord_6276688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276688).length < 2 ^ (prefixWord ++ tailWord_6276688).sum := by decide
  have hdescent : baseEnd_6276688 < baseStart_6276688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276705 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_6276705 : Nat := 118140960795 + 6276705 * 2 ^ 59
def prefixEnd_6276705 : Nat := 4983230072969 + 3 ^ 40 * 6276705 * 2
def baseEnd_6276705 : Nat := 3222966591478970096521465

theorem tailTrace_6276705 : CollatzResearch.WordTrace tailWord_6276705 prefixEnd_6276705 3222966591478970096521465 := by
  unfold tailWord_6276705
  simp only [CollatzResearch.WordTrace]
  refine ⟨228930238725577235714751569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152620159150384823809834379 228930238725577235714751569)
  ·
    refine ⟨171697679044182926786063677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228930238725577235714751569 171697679044182926786063677)
    ·
      refine ⟨64386629641568597544773879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171697679044182926786063677 64386629641568597544773879)
      ·
        refine ⟨96579944462352896317160819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64386629641568597544773879 96579944462352896317160819)
        ·
          refine ⟨144869916693529344475741229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96579944462352896317160819 144869916693529344475741229)
          ·
            refine ⟨54326218760073504178402961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144869916693529344475741229 54326218760073504178402961)
            ·
              refine ⟨40744664070055128133802221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54326218760073504178402961 40744664070055128133802221)
              ·
                refine ⟨15279249026270673050175833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40744664070055128133802221 15279249026270673050175833)
                ·
                  refine ⟨11459436769703004787631875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15279249026270673050175833 11459436769703004787631875)
                  ·
                    refine ⟨17189155154554507181447813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11459436769703004787631875 17189155154554507181447813)
                    ·
                      refine ⟨3222966591478970096521465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17189155154554507181447813 3222966591478970096521465)
                      ·
                        rfl

theorem cell23_6276705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_6276705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276705 prefixEnd_6276705 := by exact prefixLift 6276705
  have htrace : WordTrace (prefixWord ++ tailWord_6276705) baseStart_6276705 baseEnd_6276705 := by
    simpa [prefixWord, tailWord_6276705, baseEnd_6276705] using wordTrace_append hprefix tailTrace_6276705
  have hstable : (prefixWord ++ tailWord_6276705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276705).length < 2 ^ (prefixWord ++ tailWord_6276705).sum := by decide
  have hdescent : baseEnd_6276705 < baseStart_6276705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276722 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_6276722 : Nat := 118140960795 + 6276722 * 2 ^ 59
def prefixEnd_6276722 : Nat := 4983230072969 + 3 ^ 40 * 6276722 * 2
def baseEnd_6276722 : Nat := 3222975320650096530008887

theorem tailTrace_6276722 : CollatzResearch.WordTrace tailWord_6276722 prefixEnd_6276722 3222975320650096530008887 := by
  unfold tailWord_6276722
  simp only [CollatzResearch.WordTrace]
  refine ⟨57232714691628911904530105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152620572511010431745413613 57232714691628911904530105)
  ·
    refine ⟨42924536018721683928397579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57232714691628911904530105 42924536018721683928397579)
    ·
      refine ⟨64386804028082525892596369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42924536018721683928397579 64386804028082525892596369)
      ·
        refine ⟨48290103021061894419447277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64386804028082525892596369 48290103021061894419447277)
        ·
          refine ⟨18108788632898210407292729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48290103021061894419447277 18108788632898210407292729)
          ·
            refine ⟨13581591474673657805469547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18108788632898210407292729 13581591474673657805469547)
            ·
              refine ⟨20372387212010486708204321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13581591474673657805469547 20372387212010486708204321)
              ·
                refine ⟨15279290409007865031153241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20372387212010486708204321 15279290409007865031153241)
                ·
                  refine ⟨11459467806755898773364931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15279290409007865031153241 11459467806755898773364931)
                  ·
                    refine ⟨17189201710133848160047397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11459467806755898773364931 17189201710133848160047397)
                    ·
                      refine ⟨3222975320650096530008887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17189201710133848160047397 3222975320650096530008887)
                      ·
                        rfl

theorem cell23_6276722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_6276722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276722 prefixEnd_6276722 := by exact prefixLift 6276722
  have htrace : WordTrace (prefixWord ++ tailWord_6276722) baseStart_6276722 baseEnd_6276722 := by
    simpa [prefixWord, tailWord_6276722, baseEnd_6276722] using wordTrace_append hprefix tailTrace_6276722
  have hstable : (prefixWord ++ tailWord_6276722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276722).length < 2 ^ (prefixWord ++ tailWord_6276722).sum := by decide
  have hdescent : baseEnd_6276722 < baseStart_6276722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276846 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 3, 2, 2]
def baseStart_6276846 : Nat := 118140960795 + 6276846 * 2 ^ 59
def prefixEnd_6276846 : Nat := 4983230072969 + 3 ^ 40 * 6276846 * 2
def baseEnd_6276846 : Nat := 3223038992251254044858317

theorem tailTrace_6276846 : CollatzResearch.WordTrace tailWord_6276846 prefixEnd_6276846 3223038992251254044858317 := by
  unfold tailWord_6276846
  simp only [CollatzResearch.WordTrace]
  refine ⟨28616922677258302099454299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152623587612044277863756261 28616922677258302099454299)
  ·
    refine ⟨42925384015887453149181449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28616922677258302099454299 42925384015887453149181449)
    ·
      refine ⟨32194038011915589861886087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42925384015887453149181449 32194038011915589861886087)
      ·
        refine ⟨48291057017873384792829131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32194038011915589861886087 48291057017873384792829131)
        ·
          refine ⟨72436585526810077189243697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48291057017873384792829131 72436585526810077189243697)
          ·
            refine ⟨54327439145107557891932773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72436585526810077189243697 54327439145107557891932773)
            ·
              refine ⟨10186394839707667104737395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54327439145107557891932773 10186394839707667104737395)
              ·
                refine ⟨15279592259561500657106093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10186394839707667104737395 15279592259561500657106093)
                ·
                  refine ⟨5729847097335562746414785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15279592259561500657106093 5729847097335562746414785)
                  ·
                    refine ⟨4297385323001672059811089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5729847097335562746414785 4297385323001672059811089)
                    ·
                      refine ⟨3223038992251254044858317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4297385323001672059811089 3223038992251254044858317)
                      ·
                        rfl

theorem cell23_6276846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_6276846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276846 prefixEnd_6276846 := by exact prefixLift 6276846
  have htrace : WordTrace (prefixWord ++ tailWord_6276846) baseStart_6276846 baseEnd_6276846 := by
    simpa [prefixWord, tailWord_6276846, baseEnd_6276846] using wordTrace_append hprefix tailTrace_6276846
  have hstable : (prefixWord ++ tailWord_6276846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276846).length < 2 ^ (prefixWord ++ tailWord_6276846).sum := by decide
  have hdescent : baseEnd_6276846 < baseStart_6276846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276865 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 2, 7]
def baseStart_6276865 : Nat := 118140960795 + 6276865 * 2 ^ 59
def prefixEnd_6276865 : Nat := 4983230072969 + 3 ^ 40 * 6276865 * 2
def baseEnd_6276865 : Nat := 1074349582794563156840243

theorem tailTrace_6276865 : CollatzResearch.WordTrace tailWord_6276865 prefixEnd_6276865 1074349582794563156840243 := by
  unfold tailWord_6276865
  simp only [CollatzResearch.WordTrace]
  refine ⟨228936074404997583040576049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152624049603331722027050699 228936074404997583040576049)
  ·
    refine ⟨171702055803748187280432037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228936074404997583040576049 171702055803748187280432037)
    ·
      refine ⟨32194135463202785115081007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171702055803748187280432037 32194135463202785115081007)
      ·
        refine ⟨48291203194804177672621511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32194135463202785115081007 48291203194804177672621511)
        ·
          refine ⟨72436804792206266508932267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48291203194804177672621511 72436804792206266508932267)
          ·
            refine ⟨108655207188309399763398401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72436804792206266508932267 108655207188309399763398401)
            ·
              refine ⟨81491405391232049822548801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108655207188309399763398401 81491405391232049822548801)
              ·
                refine ⟨61118554043424037366911601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81491405391232049822548801 61118554043424037366911601)
                ·
                  refine ⟨45838915532568028025183701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61118554043424037366911601 45838915532568028025183701)
                  ·
                    refine ⟨1074349582794563156840243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45838915532568028025183701 1074349582794563156840243)
                    ·
                      rfl

theorem cell23_6276865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_6276865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276865 prefixEnd_6276865 := by exact prefixLift 6276865
  have htrace : WordTrace (prefixWord ++ tailWord_6276865) baseStart_6276865 baseEnd_6276865 := by
    simpa [prefixWord, tailWord_6276865, baseEnd_6276865] using wordTrace_append hprefix tailTrace_6276865
  have hstable : (prefixWord ++ tailWord_6276865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276865).length < 2 ^ (prefixWord ++ tailWord_6276865).sum := by decide
  have hdescent : baseEnd_6276865 < baseStart_6276865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276866 : List Nat := [3, 4, 1, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_6276866 : Nat := 118140960795 + 6276866 * 2 ^ 59
def prefixEnd_6276866 : Nat := 4983230072969 + 3 ^ 40 * 6276866 * 2
def baseEnd_6276866 : Nat := 3223049261864343966608225

theorem tailTrace_6276866 : CollatzResearch.WordTrace tailWord_6276866 prefixEnd_6276866 3223049261864343966608225 := by
  unfold tailWord_6276866
  simp only [CollatzResearch.WordTrace]
  refine ⟨57234027719498490052840613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152624073918662640140908301 57234027719498490052840613)
  ·
    refine ⟨10731380197405966884907615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57234027719498490052840613 10731380197405966884907615)
    ·
      refine ⟨16097070296108950327361423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10731380197405966884907615 16097070296108950327361423)
      ·
        refine ⟨24145605444163425491042135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16097070296108950327361423 24145605444163425491042135)
        ·
          refine ⟨36218408166245138236563203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24145605444163425491042135 36218408166245138236563203)
          ·
            refine ⟨54327612249367707354844805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36218408166245138236563203 54327612249367707354844805)
            ·
              refine ⟨10186427296756445129033401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54327612249367707354844805 10186427296756445129033401)
              ·
                refine ⟨7639820472567333846775051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10186427296756445129033401 7639820472567333846775051)
                ·
                  refine ⟨11459730708851000770162577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7639820472567333846775051 11459730708851000770162577)
                  ·
                    refine ⟨8594798031638250577621933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11459730708851000770162577 8594798031638250577621933)
                    ·
                      refine ⟨3223049261864343966608225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8594798031638250577621933 3223049261864343966608225)
                      ·
                        rfl

theorem cell23_6276866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_6276866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276866 prefixEnd_6276866 := by exact prefixLift 6276866
  have htrace : WordTrace (prefixWord ++ tailWord_6276866) baseStart_6276866 baseEnd_6276866 := by
    simpa [prefixWord, tailWord_6276866, baseEnd_6276866] using wordTrace_append hprefix tailTrace_6276866
  have hstable : (prefixWord ++ tailWord_6276866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276866).length < 2 ^ (prefixWord ++ tailWord_6276866).sum := by decide
  have hdescent : baseEnd_6276866 < baseStart_6276866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276875 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 5]
def baseStart_6276875 : Nat := 118140960795 + 6276875 * 2 ^ 59
def prefixEnd_6276875 : Nat := 4983230072969 + 3 ^ 40 * 6276875 * 2
def baseEnd_6276875 : Nat := 3223053883190234431395683

theorem tailTrace_6276875 : CollatzResearch.WordTrace tailWord_6276875 prefixEnd_6276875 3223053883190234431395683 := by
  unfold tailWord_6276875
  simp only [CollatzResearch.WordTrace]
  refine ⟨228936439134961354748440079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152624292756640903165626719 228936439134961354748440079)
  ·
    refine ⟨343404658702442032122660119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228936439134961354748440079 343404658702442032122660119)
    ·
      refine ⟨515106988053663048183990179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343404658702442032122660119 515106988053663048183990179)
      ·
        refine ⟨772660482080494572275985269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515106988053663048183990179 772660482080494572275985269)
        ·
          refine ⟨72436920195046366150873619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 772660482080494572275985269 72436920195046366150873619)
          ·
            refine ⟨108655380292569549226310429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72436920195046366150873619 108655380292569549226310429)
            ·
              refine ⟨40745767609713580959866411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108655380292569549226310429 40745767609713580959866411)
              ·
                refine ⟨61118651414570371439799617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40745767609713580959866411 61118651414570371439799617)
                ·
                  refine ⟨45838988560927778579849713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61118651414570371439799617 45838988560927778579849713)
                  ·
                    refine ⟨34379241420695833934887285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45838988560927778579849713 34379241420695833934887285)
                    ·
                      refine ⟨3223053883190234431395683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34379241420695833934887285 3223053883190234431395683)
                      ·
                        rfl

theorem cell23_6276875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 5].length) (baseStart_6276875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276875 prefixEnd_6276875 := by exact prefixLift 6276875
  have htrace : WordTrace (prefixWord ++ tailWord_6276875) baseStart_6276875 baseEnd_6276875 := by
    simpa [prefixWord, tailWord_6276875, baseEnd_6276875] using wordTrace_append hprefix tailTrace_6276875
  have hstable : (prefixWord ++ tailWord_6276875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276875).length < 2 ^ (prefixWord ++ tailWord_6276875).sum := by decide
  have hdescent : baseEnd_6276875 < baseStart_6276875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276905 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 6, 1, 5]
def baseStart_6276905 : Nat := 118140960795 + 6276905 * 2 ^ 59
def prefixEnd_6276905 : Nat := 4983230072969 + 3 ^ 40 * 6276905 * 2
def baseEnd_6276905 : Nat := 3223069287609869314020545

theorem tailTrace_6276905 : CollatzResearch.WordTrace tailWord_6276905 prefixEnd_6276905 3223069287609869314020545 := by
  unfold tailWord_6276905
  simp only [CollatzResearch.WordTrace]
  refine ⟨228937533324852669872032169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152625022216568446581354779 228937533324852669872032169)
  ·
    refine ⟨171703149993639502404024127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228937533324852669872032169 171703149993639502404024127)
    ·
      refine ⟨257554724990459253606036191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171703149993639502404024127 257554724990459253606036191)
      ·
        refine ⟨386332087485688880409054287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257554724990459253606036191 386332087485688880409054287)
        ·
          refine ⟨579498131228533320613581431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386332087485688880409054287 579498131228533320613581431)
          ·
            refine ⟨869247196842799980920372147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579498131228533320613581431 869247196842799980920372147)
            ·
              refine ⟨1303870795264199971380558221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869247196842799980920372147 1303870795264199971380558221)
              ·
                refine ⟨488951548224074989267709333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1303870795264199971380558221 488951548224074989267709333)
                ·
                  refine ⟨22919603823003515121923875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 488951548224074989267709333 22919603823003515121923875)
                  ·
                    refine ⟨34379405734505272682885813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22919603823003515121923875 34379405734505272682885813)
                    ·
                      refine ⟨3223069287609869314020545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34379405734505272682885813 3223069287609869314020545)
                      ·
                        rfl

theorem cell23_6276905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_6276905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276905 prefixEnd_6276905 := by exact prefixLift 6276905
  have htrace : WordTrace (prefixWord ++ tailWord_6276905) baseStart_6276905 baseEnd_6276905 := by
    simpa [prefixWord, tailWord_6276905, baseEnd_6276905] using wordTrace_append hprefix tailTrace_6276905
  have hstable : (prefixWord ++ tailWord_6276905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276905).length < 2 ^ (prefixWord ++ tailWord_6276905).sum := by decide
  have hdescent : baseEnd_6276905 < baseStart_6276905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276913 : List Nat := [1, 2, 2, 3, 2, 4, 2, 1, 2, 1, 3]
def baseStart_6276913 : Nat := 118140960795 + 6276913 * 2 ^ 59
def prefixEnd_6276913 : Nat := 4983230072969 + 3 ^ 40 * 6276913 * 2
def baseEnd_6276913 : Nat := 3223073395455105282720509

theorem tailTrace_6276913 : CollatzResearch.WordTrace tailWord_6276913 prefixEnd_6276913 3223073395455105282720509 := by
  unfold tailWord_6276913
  simp only [CollatzResearch.WordTrace]
  refine ⟨228937825108823687238323393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152625216739215791492215595 228937825108823687238323393)
  ·
    refine ⟨171703368831617765428742545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228937825108823687238323393 171703368831617765428742545)
    ·
      refine ⟨128777526623713324071556909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171703368831617765428742545 128777526623713324071556909)
      ·
        refine ⟨48291572483892496526833841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128777526623713324071556909 48291572483892496526833841)
        ·
          refine ⟨36218679362919372395125381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48291572483892496526833841 36218679362919372395125381)
          ·
            refine ⟨6791002380547382324086009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36218679362919372395125381 6791002380547382324086009)
            ·
              refine ⟨5093251785410536743064507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6791002380547382324086009 5093251785410536743064507)
              ·
                refine ⟨7639877678115805114596761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5093251785410536743064507 7639877678115805114596761)
                ·
                  refine ⟨5729908258586853835947571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7639877678115805114596761 5729908258586853835947571)
                  ·
                    refine ⟨8594862387880280753921357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5729908258586853835947571 8594862387880280753921357)
                    ·
                      refine ⟨3223073395455105282720509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8594862387880280753921357 3223073395455105282720509)
                      ·
                        rfl

theorem cell23_6276913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_6276913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276913 prefixEnd_6276913 := by exact prefixLift 6276913
  have htrace : WordTrace (prefixWord ++ tailWord_6276913) baseStart_6276913 baseEnd_6276913 := by
    simpa [prefixWord, tailWord_6276913, baseEnd_6276913] using wordTrace_append hprefix tailTrace_6276913
  have hstable : (prefixWord ++ tailWord_6276913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276913).length < 2 ^ (prefixWord ++ tailWord_6276913).sum := by decide
  have hdescent : baseEnd_6276913 < baseStart_6276913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276919 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 6, 2, 2]
def baseStart_6276919 : Nat := 118140960795 + 6276919 * 2 ^ 59
def prefixEnd_6276919 : Nat := 4983230072969 + 3 ^ 40 * 6276919 * 2
def baseEnd_6276919 : Nat := 3223076476339032259245481

theorem tailTrace_6276919 : CollatzResearch.WordTrace tailWord_6276919 prefixEnd_6276919 3223076476339032259245481 := by
  unfold tailWord_6276919
  simp only [CollatzResearch.WordTrace]
  refine ⟨228938043946801950263041811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152625362631201300175361207 228938043946801950263041811)
  ·
    refine ⟨343407065920202925394562717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228938043946801950263041811 343407065920202925394562717)
    ·
      refine ⟨128777649720076097022961019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343407065920202925394562717 128777649720076097022961019)
      ·
        refine ⟨193166474580114145534441529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128777649720076097022961019 193166474580114145534441529)
        ·
          refine ⟨144874855935085609150831147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193166474580114145534441529 144874855935085609150831147)
          ·
            refine ⟨217312283902628413726246721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144874855935085609150831147 217312283902628413726246721)
            ·
              refine ⟨162984212926971310294685041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217312283902628413726246721 162984212926971310294685041)
              ·
                refine ⟨122238159695228482721013781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162984212926971310294685041 122238159695228482721013781)
                ·
                  refine ⟨5729913735713835127547521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122238159695228482721013781 5729913735713835127547521)
                  ·
                    refine ⟨4297435301785376345660641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5729913735713835127547521 4297435301785376345660641)
                    ·
                      refine ⟨3223076476339032259245481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4297435301785376345660641 3223076476339032259245481)
                      ·
                        rfl

theorem cell23_6276919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 2, 2].length) (baseStart_6276919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276919 prefixEnd_6276919 := by exact prefixLift 6276919
  have htrace : WordTrace (prefixWord ++ tailWord_6276919) baseStart_6276919 baseEnd_6276919 := by
    simpa [prefixWord, tailWord_6276919, baseEnd_6276919] using wordTrace_append hprefix tailTrace_6276919
  have hstable : (prefixWord ++ tailWord_6276919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276919).length < 2 ^ (prefixWord ++ tailWord_6276919).sum := by decide
  have hdescent : baseEnd_6276919 < baseStart_6276919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276922 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5]
def baseStart_6276922 : Nat := 118140960795 + 6276922 * 2 ^ 59
def prefixEnd_6276922 : Nat := 4983230072969 + 3 ^ 40 * 6276922 * 2
def baseEnd_6276922 : Nat := 3223078016780995747507967

theorem tailTrace_6276922 : CollatzResearch.WordTrace tailWord_6276922 prefixEnd_6276922 3223078016780995747507967 := by
  unfold tailWord_6276922
  simp only [CollatzResearch.WordTrace]
  refine ⟨57234538341447770443850255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152625435577194054516934013 57234538341447770443850255)
  ·
    refine ⟨85851807512171655665775383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57234538341447770443850255 85851807512171655665775383)
    ·
      refine ⟨128777711268257483498663075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85851807512171655665775383 128777711268257483498663075)
      ·
        refine ⟨193166566902386225247994613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128777711268257483498663075 193166566902386225247994613)
        ·
          refine ⟨18109365647098708616999495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193166566902386225247994613 18109365647098708616999495)
          ·
            refine ⟨27164048470648062925499243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18109365647098708616999495 27164048470648062925499243)
            ·
              refine ⟨40746072705972094388248865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27164048470648062925499243 40746072705972094388248865)
              ·
                refine ⟨30559554529479070791186649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40746072705972094388248865 30559554529479070791186649)
                ·
                  refine ⟨22919665897109303093389987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30559554529479070791186649 22919665897109303093389987)
                  ·
                    refine ⟨34379498845663954640084981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22919665897109303093389987 34379498845663954640084981)
                    ·
                      refine ⟨3223078016780995747507967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34379498845663954640084981 3223078016780995747507967)
                      ·
                        rfl

theorem cell23_6276922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_6276922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276922 prefixEnd_6276922 := by exact prefixLift 6276922
  have htrace : WordTrace (prefixWord ++ tailWord_6276922) baseStart_6276922 baseEnd_6276922 := by
    simpa [prefixWord, tailWord_6276922, baseEnd_6276922] using wordTrace_append hprefix tailTrace_6276922
  have hstable : (prefixWord ++ tailWord_6276922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276922).length < 2 ^ (prefixWord ++ tailWord_6276922).sum := by decide
  have hdescent : baseEnd_6276922 < baseStart_6276922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276959 : List Nat := [1, 1, 2, 3, 1, 5, 1, 4, 5]
def baseStart_6276959 : Nat := 118140960795 + 6276959 * 2 ^ 59
def prefixEnd_6276959 : Nat := 4983230072969 + 3 ^ 40 * 6276959 * 2
def baseEnd_6276959 : Nat := 358121890618356900305033

theorem tailTrace_6276959 : CollatzResearch.WordTrace tailWord_6276959 prefixEnd_6276959 358121890618356900305033 := by
  unfold tailWord_6276959
  simp only [CollatzResearch.WordTrace]
  refine ⟨228939502866657037094497931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152626335244438024729665287 228939502866657037094497931)
  ·
    refine ⟨343409254299985555641746897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228939502866657037094497931 343409254299985555641746897)
    ·
      refine ⟨257556940724989166731310173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343409254299985555641746897 257556940724989166731310173)
      ·
        refine ⟨96583852771870937524241315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257556940724989166731310173 96583852771870937524241315)
        ·
          refine ⟨144875779157806406286361973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96583852771870937524241315 144875779157806406286361973)
          ·
            refine ⟨13582104296044350589346435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 144875779157806406286361973 13582104296044350589346435)
            ·
              refine ⟨20373156444066525884019653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13582104296044350589346435 20373156444066525884019653)
              ·
                refine ⟨3819966833262473603253685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20373156444066525884019653 3819966833262473603253685)
                ·
                  refine ⟨358121890618356900305033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3819966833262473603253685 358121890618356900305033)
                  ·
                    rfl

theorem cell23_6276959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 5].length) (baseStart_6276959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276959 prefixEnd_6276959 := by exact prefixLift 6276959
  have htrace : WordTrace (prefixWord ++ tailWord_6276959) baseStart_6276959 baseEnd_6276959 := by
    simpa [prefixWord, tailWord_6276959, baseEnd_6276959] using wordTrace_append hprefix tailTrace_6276959
  have hstable : (prefixWord ++ tailWord_6276959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276959).length < 2 ^ (prefixWord ++ tailWord_6276959).sum := by decide
  have hdescent : baseEnd_6276959 < baseStart_6276959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276992 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 4]
def baseStart_6276992 : Nat := 118140960795 + 6276992 * 2 ^ 59
def prefixEnd_6276992 : Nat := 4983230072969 + 3 ^ 40 * 6276992 * 2
def baseEnd_6276992 : Nat := 3223113960426810473632645

theorem tailTrace_6276992 : CollatzResearch.WordTrace tailWord_6276992 prefixEnd_6276992 3223113960426810473632645 := by
  unfold tailWord_6276992
  simp only [CollatzResearch.WordTrace]
  refine ⟨114470353237768741865224615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152627137650358322486966153 114470353237768741865224615)
  ·
    refine ⟨171705529856653112797836923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114470353237768741865224615 171705529856653112797836923)
    ·
      refine ⟨257558294784979669196755385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171705529856653112797836923 257558294784979669196755385)
      ·
        refine ⟨193168721088734751897566539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257558294784979669196755385 193168721088734751897566539)
        ·
          refine ⟨289753081633102127846349809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193168721088734751897566539 289753081633102127846349809)
          ·
            refine ⟨217314811224826595884762357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289753081633102127846349809 217314811224826595884762357)
            ·
              refine ⟨20373263552327493364196471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 217314811224826595884762357 20373263552327493364196471)
              ·
                refine ⟨30559895328491240046294707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20373263552327493364196471 30559895328491240046294707)
                ·
                  refine ⟨45839842992736860069442061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30559895328491240046294707 45839842992736860069442061)
                  ·
                    refine ⟨17189941122276322526040773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45839842992736860069442061 17189941122276322526040773)
                    ·
                      refine ⟨3223113960426810473632645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17189941122276322526040773 3223113960426810473632645)
                      ·
                        rfl

theorem cell23_6276992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_6276992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276992 prefixEnd_6276992 := by exact prefixLift 6276992
  have htrace : WordTrace (prefixWord ++ tailWord_6276992) baseStart_6276992 baseEnd_6276992 := by
    simpa [prefixWord, tailWord_6276992, baseEnd_6276992] using wordTrace_append hprefix tailTrace_6276992
  have hstable : (prefixWord ++ tailWord_6276992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276992).length < 2 ^ (prefixWord ++ tailWord_6276992).sum := by decide
  have hdescent : baseEnd_6276992 < baseStart_6276992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6276993 : List Nat := [1, 2, 4, 4, 1, 1, 2, 3, 5]
def baseStart_6276993 : Nat := 118140960795 + 6276993 * 2 ^ 59
def prefixEnd_6276993 : Nat := 4983230072969 + 3 ^ 40 * 6276993 * 2
def baseEnd_6276993 : Nat := 358123830434162774413349

theorem tailTrace_6276993 : CollatzResearch.WordTrace tailWord_6276993 prefixEnd_6276993 358123830434162774413349 := by
  unfold tailWord_6276993
  simp only [CollatzResearch.WordTrace]
  refine ⟨228940742948533860901235633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152627161965689240600823755 228940742948533860901235633)
  ·
    refine ⟨171705557211400395675926725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228940742948533860901235633 171705557211400395675926725)
    ·
      refine ⟨32194791977137574189236261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171705557211400395675926725 32194791977137574189236261)
      ·
        refine ⟨6036523495713295160481799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32194791977137574189236261 6036523495713295160481799)
        ·
          refine ⟨9054785243569942740722699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6036523495713295160481799 9054785243569942740722699)
          ·
            refine ⟨13582177865354914111084049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9054785243569942740722699 13582177865354914111084049)
            ·
              refine ⟨10186633399016185583313037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13582177865354914111084049 10186633399016185583313037)
              ·
                refine ⟨3819987524631069593742389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10186633399016185583313037 3819987524631069593742389)
                ·
                  refine ⟨358123830434162774413349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3819987524631069593742389 358123830434162774413349)
                  ·
                    rfl

theorem cell23_6276993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 5].length) (baseStart_6276993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6276993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6276993 prefixEnd_6276993 := by exact prefixLift 6276993
  have htrace : WordTrace (prefixWord ++ tailWord_6276993) baseStart_6276993 baseEnd_6276993 := by
    simpa [prefixWord, tailWord_6276993, baseEnd_6276993] using wordTrace_append hprefix tailTrace_6276993
  have hstable : (prefixWord ++ tailWord_6276993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6276993).length < 2 ^ (prefixWord ++ tailWord_6276993).sum := by decide
  have hdescent : baseEnd_6276993 < baseStart_6276993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6276993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277009 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 2, 4, 2]
def baseStart_6277009 : Nat := 118140960795 + 6277009 * 2 ^ 59
def prefixEnd_6277009 : Nat := 4983230072969 + 3 ^ 40 * 6277009 * 2
def baseEnd_6277009 : Nat := 3223122689597936907120067

theorem tailTrace_6277009 : CollatzResearch.WordTrace tailWord_6277009 prefixEnd_6277009 3223122689597936907120067 := by
  unfold tailWord_6277009
  simp only [CollatzResearch.WordTrace]
  refine ⟨228941326516475895633818081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152627551010983930422545387 228941326516475895633818081)
  ·
    refine ⟨171705994887356921725363561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228941326516475895633818081 171705994887356921725363561)
    ·
      refine ⟨128779496165517691294022671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171705994887356921725363561 128779496165517691294022671)
      ·
        refine ⟨193169244248276536941034007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128779496165517691294022671 193169244248276536941034007)
        ·
          refine ⟨289753866372414805411551011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193169244248276536941034007 289753866372414805411551011)
          ·
            refine ⟨434630799558622208117326517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289753866372414805411551011 434630799558622208117326517)
            ·
              refine ⟨40746637458620832010999361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 434630799558622208117326517 40746637458620832010999361)
              ·
                refine ⟨30559978093965624008249521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40746637458620832010999361 30559978093965624008249521)
                ·
                  refine ⟨22919983570474218006187141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30559978093965624008249521 22919983570474218006187141)
                  ·
                    refine ⟨4297496919463915876160089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22919983570474218006187141 4297496919463915876160089)
                    ·
                      refine ⟨3223122689597936907120067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4297496919463915876160089 3223122689597936907120067)
                      ·
                        rfl

theorem cell23_6277009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 4, 2].length) (baseStart_6277009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277009 prefixEnd_6277009 := by exact prefixLift 6277009
  have htrace : WordTrace (prefixWord ++ tailWord_6277009) baseStart_6277009 baseEnd_6277009 := by
    simpa [prefixWord, tailWord_6277009, baseEnd_6277009] using wordTrace_append hprefix tailTrace_6277009
  have hstable : (prefixWord ++ tailWord_6277009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277009).length < 2 ^ (prefixWord ++ tailWord_6277009).sum := by decide
  have hdescent : baseEnd_6277009 < baseStart_6277009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277053 : List Nat := [1, 4, 1, 2, 3, 1, 3, 3, 1, 4]
def baseStart_6277053 : Nat := 118140960795 + 6277053 * 2 ^ 59
def prefixEnd_6277053 : Nat := 4983230072969 + 3 ^ 40 * 6277053 * 2
def baseEnd_6277053 : Nat := 1074381760915578244989955

theorem tailTrace_6277053 : CollatzResearch.WordTrace tailWord_6277053 prefixEnd_6277053 1074381760915578244989955 := by
  unfold tailWord_6277053
  simp only [CollatzResearch.WordTrace]
  refine ⟨228942931328316491148419813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152628620885544327432279875 228942931328316491148419813)
  ·
    refine ⟨42926799624059342090328715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228942931328316491148419813 42926799624059342090328715)
    ·
      refine ⟨64390199436089013135493073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42926799624059342090328715 64390199436089013135493073)
      ·
        refine ⟨48292649577066759851619805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64390199436089013135493073 48292649577066759851619805)
        ·
          refine ⟨18109743591400034944357427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48292649577066759851619805 18109743591400034944357427)
          ·
            refine ⟨27164615387100052416536141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18109743591400034944357427 27164615387100052416536141)
            ·
              refine ⟨10186730770162519656201053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27164615387100052416536141 10186730770162519656201053)
              ·
                refine ⟨3820024038810944871075395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10186730770162519656201053 3820024038810944871075395)
                ·
                  refine ⟨5730036058216417306613093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820024038810944871075395 5730036058216417306613093)
                  ·
                    refine ⟨1074381760915578244989955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5730036058216417306613093 1074381760915578244989955)
                    ·
                      rfl

theorem cell23_6277053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_6277053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277053 prefixEnd_6277053 := by exact prefixLift 6277053
  have htrace : WordTrace (prefixWord ++ tailWord_6277053) baseStart_6277053 baseEnd_6277053 := by
    simpa [prefixWord, tailWord_6277053, baseEnd_6277053] using wordTrace_append hprefix tailTrace_6277053
  have hstable : (prefixWord ++ tailWord_6277053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277053).length < 2 ^ (prefixWord ++ tailWord_6277053).sum := by decide
  have hdescent : baseEnd_6277053 < baseStart_6277053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277099 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 2, 6, 2]
def baseStart_6277099 : Nat := 118140960795 + 6277099 * 2 ^ 59
def prefixEnd_6277099 : Nat := 4983230072969 + 3 ^ 40 * 6277099 * 2
def baseEnd_6277099 : Nat := 3223168902856841554994653

theorem tailTrace_6277099 : CollatzResearch.WordTrace tailWord_6277099 prefixEnd_6277099 3223168902856841554994653 := by
  unfold tailWord_6277099
  simp only [CollatzResearch.WordTrace]
  refine ⟨228944609086149841004594351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152629739390766560669729567 228944609086149841004594351)
  ·
    refine ⟨343416913629224761506891527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228944609086149841004594351 343416913629224761506891527)
    ·
      refine ⟨515125370443837142260337291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343416913629224761506891527 515125370443837142260337291)
      ·
        refine ⟨772688055665755713390505937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515125370443837142260337291 772688055665755713390505937)
        ·
          refine ⟨579516041749316785042879453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 772688055665755713390505937 579516041749316785042879453)
          ·
            refine ⟨217318515655993794391079795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 579516041749316785042879453 217318515655993794391079795)
            ·
              refine ⟨325977773483990691586619693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217318515655993794391079795 325977773483990691586619693)
              ·
                refine ⟨122241665056496509344982385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325977773483990691586619693 122241665056496509344982385)
                ·
                  refine ⟨91681248792372382008736789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122241665056496509344982385 91681248792372382008736789)
                  ·
                    refine ⟨4297558537142455406659537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91681248792372382008736789 4297558537142455406659537)
                    ·
                      refine ⟨3223168902856841554994653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4297558537142455406659537 3223168902856841554994653)
                      ·
                        rfl

theorem cell23_6277099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 6, 2].length) (baseStart_6277099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277099 prefixEnd_6277099 := by exact prefixLift 6277099
  have htrace : WordTrace (prefixWord ++ tailWord_6277099) baseStart_6277099 baseEnd_6277099 := by
    simpa [prefixWord, tailWord_6277099, baseEnd_6277099] using wordTrace_append hprefix tailTrace_6277099
  have hstable : (prefixWord ++ tailWord_6277099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277099).length < 2 ^ (prefixWord ++ tailWord_6277099).sum := by decide
  have hdescent : baseEnd_6277099 < baseStart_6277099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277127 : List Nat := [1, 1, 4, 3, 1, 4, 2, 2, 1, 1, 3]
def baseStart_6277127 : Nat := 118140960795 + 6277127 * 2 ^ 59
def prefixEnd_6277127 : Nat := 4983230072969 + 3 ^ 40 * 6277127 * 2
def baseEnd_6277127 : Nat := 3223183280315167445444525

theorem tailTrace_6277127 : CollatzResearch.WordTrace tailWord_6277127 prefixEnd_6277127 3223183280315167445444525 := by
  unfold tailWord_6277127
  simp only [CollatzResearch.WordTrace]
  refine ⟨228945630330048401786613635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152630420220032267857742423 228945630330048401786613635)
  ·
    refine ⟨343418445495072602679920453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228945630330048401786613635 343418445495072602679920453)
    ·
      refine ⟨64390958530326113002485085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 343418445495072602679920453 64390958530326113002485085)
      ·
        refine ⟨24146609448872292375931907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64390958530326113002485085 24146609448872292375931907)
        ·
          refine ⟨36219914173308438563897861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24146609448872292375931907 36219914173308438563897861)
          ·
            refine ⟨6791233907495332230730849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36219914173308438563897861 6791233907495332230730849)
            ·
              refine ⟨5093425430621499173048137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6791233907495332230730849 5093425430621499173048137)
              ·
                refine ⟨3820069072966124379786103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5093425430621499173048137 3820069072966124379786103)
                ·
                  refine ⟨5730103609449186569679155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820069072966124379786103 5730103609449186569679155)
                  ·
                    refine ⟨8595155414173779854518733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5730103609449186569679155 8595155414173779854518733)
                    ·
                      refine ⟨3223183280315167445444525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8595155414173779854518733 3223183280315167445444525)
                      ·
                        rfl

theorem cell23_6277127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_6277127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277127 prefixEnd_6277127 := by exact prefixLift 6277127
  have htrace : WordTrace (prefixWord ++ tailWord_6277127) baseStart_6277127 baseEnd_6277127 := by
    simpa [prefixWord, tailWord_6277127, baseEnd_6277127] using wordTrace_append hprefix tailTrace_6277127
  have hstable : (prefixWord ++ tailWord_6277127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277127).length < 2 ^ (prefixWord ++ tailWord_6277127).sum := by decide
  have hdescent : baseEnd_6277127 < baseStart_6277127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277146 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4]
def baseStart_6277146 : Nat := 118140960795 + 6277146 * 2 ^ 59
def prefixEnd_6277146 : Nat := 4983230072969 + 3 ^ 40 * 6277146 * 2
def baseEnd_6277146 : Nat := 3223193036447602871106937

theorem tailTrace_6277146 : CollatzResearch.WordTrace tailWord_6277146 prefixEnd_6277146 3223193036447602871106937 := by
  unfold tailWord_6277146
  simp only [CollatzResearch.WordTrace]
  refine ⟨57236580829244892007888823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152630882211319712021036861 57236580829244892007888823)
  ·
    refine ⟨85854871243867338011833235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57236580829244892007888823 85854871243867338011833235)
    ·
      refine ⟨128782306865801007017749853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85854871243867338011833235 128782306865801007017749853)
      ·
        refine ⟨48293365074675377631656195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128782306865801007017749853 48293365074675377631656195)
        ·
          refine ⟨72440047612013066447484293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48293365074675377631656195 72440047612013066447484293)
          ·
            refine ⟨13582508927252449958903305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72440047612013066447484293 13582508927252449958903305)
            ·
              refine ⟨10186881695439337469177479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13582508927252449958903305 10186881695439337469177479)
              ·
                refine ⟨15280322543159006203766219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10186881695439337469177479 15280322543159006203766219)
                ·
                  refine ⟨22920483814738509305649329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15280322543159006203766219 22920483814738509305649329)
                  ·
                    refine ⟨17190362861053881979236997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22920483814738509305649329 17190362861053881979236997)
                    ·
                      refine ⟨3223193036447602871106937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17190362861053881979236997 3223193036447602871106937)
                      ·
                        rfl

theorem cell23_6277146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_6277146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277146 prefixEnd_6277146 := by exact prefixLift 6277146
  have htrace : WordTrace (prefixWord ++ tailWord_6277146) baseStart_6277146 baseEnd_6277146 := by
    simpa [prefixWord, tailWord_6277146, baseEnd_6277146] using wordTrace_append hprefix tailTrace_6277146
  have hstable : (prefixWord ++ tailWord_6277146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277146).length < 2 ^ (prefixWord ++ tailWord_6277146).sum := by decide
  have hdescent : baseEnd_6277146 < baseStart_6277146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277170 : List Nat := [3, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3]
def baseStart_6277170 : Nat := 118140960795 + 6277170 * 2 ^ 59
def prefixEnd_6277170 : Nat := 4983230072969 + 3 ^ 40 * 6277170 * 2
def baseEnd_6277170 : Nat := 3223205359983310777206827

theorem tailTrace_6277170 : CollatzResearch.WordTrace tailWord_6277170 prefixEnd_6277170 3223205359983310777206827 := by
  unfold tailWord_6277170
  simp only [CollatzResearch.WordTrace]
  refine ⟨57236799667223155032607241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152631465779261746753619309 57236799667223155032607241)
  ·
    refine ⟨42927599750417366274455431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57236799667223155032607241 42927599750417366274455431)
    ·
      refine ⟨64391399625626049411683147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42927599750417366274455431 64391399625626049411683147)
      ·
        refine ⟨96587099438439074117524721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64391399625626049411683147 96587099438439074117524721)
        ·
          refine ⟨72440324578829305588143541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96587099438439074117524721 72440324578829305588143541)
          ·
            refine ⟨6791280429265247398888457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72440324578829305588143541 6791280429265247398888457)
            ·
              refine ⟨5093460321948935549166343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6791280429265247398888457 5093460321948935549166343)
              ·
                refine ⟨7640190482923403323749515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5093460321948935549166343 7640190482923403323749515)
                ·
                  refine ⟨11460285724385104985624273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7640190482923403323749515 11460285724385104985624273)
                  ·
                    refine ⟨8595214293288828739218205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11460285724385104985624273 8595214293288828739218205)
                    ·
                      refine ⟨3223205359983310777206827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8595214293288828739218205 3223205359983310777206827)
                      ·
                        rfl

theorem cell23_6277170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_6277170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277170 prefixEnd_6277170 := by exact prefixLift 6277170
  have htrace : WordTrace (prefixWord ++ tailWord_6277170) baseStart_6277170 baseEnd_6277170 := by
    simpa [prefixWord, tailWord_6277170, baseEnd_6277170] using wordTrace_append hprefix tailTrace_6277170
  have hstable : (prefixWord ++ tailWord_6277170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277170).length < 2 ^ (prefixWord ++ tailWord_6277170).sum := by decide
  have hdescent : baseEnd_6277170 < baseStart_6277170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277183 : List Nat := [1, 1, 2, 2, 3, 1, 5, 2, 2, 1, 3]
def baseStart_6277183 : Nat := 118140960795 + 6277183 * 2 ^ 59
def prefixEnd_6277183 : Nat := 4983230072969 + 3 ^ 40 * 6277183 * 2
def baseEnd_6277183 : Nat := 3223212035231819226344267

theorem tailTrace_6277183 : CollatzResearch.WordTrace tailWord_6277183 prefixEnd_6277183 3223212035231819226344267 := by
  unfold tailWord_6277183
  simp only [CollatzResearch.WordTrace]
  refine ⟨228947672817845523350652203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152631781878563682233768135 228947672817845523350652203)
  ·
    refine ⟨343421509226768285025978305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228947672817845523350652203 343421509226768285025978305)
    ·
      refine ⟨257566131920076213769483729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343421509226768285025978305 257566131920076213769483729)
      ·
        refine ⟨193174598940057160327112797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257566131920076213769483729 193174598940057160327112797)
        ·
          refine ⟨72440474602521435122667299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193174598940057160327112797 72440474602521435122667299)
          ·
            refine ⟨108660711903782152684000949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72440474602521435122667299 108660711903782152684000949)
            ·
              refine ⟨10186941740979576814125089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108660711903782152684000949 10186941740979576814125089)
              ·
                refine ⟨7640206305734682610593817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10186941740979576814125089 7640206305734682610593817)
                ·
                  refine ⟨5730154729301011957945363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7640206305734682610593817 5730154729301011957945363)
                  ·
                    refine ⟨8595232093951517936918045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5730154729301011957945363 8595232093951517936918045)
                    ·
                      refine ⟨3223212035231819226344267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8595232093951517936918045 3223212035231819226344267)
                      ·
                        rfl

theorem cell23_6277183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 1, 3].length) (baseStart_6277183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277183 prefixEnd_6277183 := by exact prefixLift 6277183
  have htrace : WordTrace (prefixWord ++ tailWord_6277183) baseStart_6277183 baseEnd_6277183 := by
    simpa [prefixWord, tailWord_6277183, baseEnd_6277183] using wordTrace_append hprefix tailTrace_6277183
  have hstable : (prefixWord ++ tailWord_6277183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277183).length < 2 ^ (prefixWord ++ tailWord_6277183).sum := by decide
  have hdescent : baseEnd_6277183 < baseStart_6277183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277209 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 2, 1, 5]
def baseStart_6277209 : Nat := 118140960795 + 6277209 * 2 ^ 59
def prefixEnd_6277209 : Nat := 4983230072969 + 3 ^ 40 * 6277209 * 2
def baseEnd_6277209 : Nat := 3223225385728836124619147

theorem tailTrace_6277209 : CollatzResearch.WordTrace tailWord_6277209 prefixEnd_6277209 3223225385728836124619147 := by
  unfold tailWord_6277209
  simp only [CollatzResearch.WordTrace]
  refine ⟨228948621115751329791098681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152632414077167553194065787 228948621115751329791098681)
  ·
    refine ⟨171711465836813497343324011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228948621115751329791098681 171711465836813497343324011)
    ·
      refine ⟨257567198755220246014986017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171711465836813497343324011 257567198755220246014986017)
      ·
        refine ⟨193175399066415184511239513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257567198755220246014986017 193175399066415184511239513)
        ·
          refine ⟨144881549299811388383429635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193175399066415184511239513 144881549299811388383429635)
          ·
            refine ⟨217322323949717082575144453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144881549299811388383429635 217322323949717082575144453)
            ·
              refine ⟨40747935740571952982839585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217322323949717082575144453 40747935740571952982839585)
              ·
                refine ⟨30560951805428964737129689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40747935740571952982839585 30560951805428964737129689)
                ·
                  refine ⟨22920713854071723552847267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30560951805428964737129689 22920713854071723552847267)
                  ·
                    refine ⟨34381070781107585329270901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22920713854071723552847267 34381070781107585329270901)
                    ·
                      refine ⟨3223225385728836124619147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34381070781107585329270901 3223225385728836124619147)
                      ·
                        rfl

theorem cell23_6277209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_6277209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277209 prefixEnd_6277209 := by exact prefixLift 6277209
  have htrace : WordTrace (prefixWord ++ tailWord_6277209) baseStart_6277209 baseEnd_6277209 := by
    simpa [prefixWord, tailWord_6277209, baseEnd_6277209] using wordTrace_append hprefix tailTrace_6277209
  have hstable : (prefixWord ++ tailWord_6277209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277209).length < 2 ^ (prefixWord ++ tailWord_6277209).sum := by decide
  have hdescent : baseEnd_6277209 < baseStart_6277209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277219 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 4]
def baseStart_6277219 : Nat := 118140960795 + 6277219 * 2 ^ 59
def prefixEnd_6277219 : Nat := 4983230072969 + 3 ^ 40 * 6277219 * 2
def baseEnd_6277219 : Nat := 3223230520535381085494101

theorem tailTrace_6277219 : CollatzResearch.WordTrace tailWord_6277219 prefixEnd_6277219 3223230520535381085494101 := by
  unfold tailWord_6277219
  simp only [CollatzResearch.WordTrace]
  refine ⟨228948985845715101498962711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152632657230476734332641807 228948985845715101498962711)
  ·
    refine ⟨343423478768572652248444067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228948985845715101498962711 343423478768572652248444067)
    ·
      refine ⟨515135218152858978372666101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343423478768572652248444067 515135218152858978372666101)
      ·
        refine ⟨48293926701830529222437447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 515135218152858978372666101 48293926701830529222437447)
        ·
          refine ⟨72440890052745793833656171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48293926701830529222437447 72440890052745793833656171)
          ·
            refine ⟨108661335079118690750484257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72440890052745793833656171 108661335079118690750484257)
            ·
              refine ⟨81496001309339018062863193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108661335079118690750484257 81496001309339018062863193)
              ·
                refine ⟨61122000982004263547147395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81496001309339018062863193 61122000982004263547147395)
                ·
                  refine ⟨91683001473006395320721093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61122000982004263547147395 91683001473006395320721093)
                  ·
                    refine ⟨17190562776188699122635205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91683001473006395320721093 17190562776188699122635205)
                    ·
                      refine ⟨3223230520535381085494101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17190562776188699122635205 3223230520535381085494101)
                      ·
                        rfl

theorem cell23_6277219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_6277219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277219 prefixEnd_6277219 := by exact prefixLift 6277219
  have htrace : WordTrace (prefixWord ++ tailWord_6277219) baseStart_6277219 baseEnd_6277219 := by
    simpa [prefixWord, tailWord_6277219, baseEnd_6277219] using wordTrace_append hprefix tailTrace_6277219
  have hstable : (prefixWord ++ tailWord_6277219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277219).length < 2 ^ (prefixWord ++ tailWord_6277219).sum := by decide
  have hdescent : baseEnd_6277219 < baseStart_6277219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277223 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 6, 2, 2]
def baseStart_6277223 : Nat := 118140960795 + 6277223 * 2 ^ 59
def prefixEnd_6277223 : Nat := 4983230072969 + 3 ^ 40 * 6277223 * 2
def baseEnd_6277223 : Nat := 3223232574457999069844083

theorem tailTrace_6277223 : CollatzResearch.WordTrace tailWord_6277223 prefixEnd_6277223 3223232574457999069844083 := by
  unfold tailWord_6277223
  simp only [CollatzResearch.WordTrace]
  refine ⟨228949131737700610182108323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152632754491800406788072215 228949131737700610182108323)
  ·
    refine ⟨343423697606550915273162485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228949131737700610182108323 343423697606550915273162485)
    ·
      refine ⟨32195971650614148306858983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 343423697606550915273162485 32195971650614148306858983)
      ·
        refine ⟨48293957475921222460288475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32195971650614148306858983 48293957475921222460288475)
        ·
          refine ⟨72440936213881833690432713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48293957475921222460288475 72440936213881833690432713)
          ·
            refine ⟨54330702160411375267824535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72440936213881833690432713 54330702160411375267824535)
            ·
              refine ⟨81496053240617062901736803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54330702160411375267824535 81496053240617062901736803)
              ·
                refine ⟨122244079860925594352605205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81496053240617062901736803 122244079860925594352605205)
                ·
                  refine ⟨5730191243480887235278369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122244079860925594352605205 5730191243480887235278369)
                  ·
                    refine ⟨4297643432610665426458777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5730191243480887235278369 4297643432610665426458777)
                    ·
                      refine ⟨3223232574457999069844083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4297643432610665426458777 3223232574457999069844083)
                      ·
                        rfl

theorem cell23_6277223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_6277223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277223 prefixEnd_6277223 := by exact prefixLift 6277223
  have htrace : WordTrace (prefixWord ++ tailWord_6277223) baseStart_6277223 baseEnd_6277223 := by
    simpa [prefixWord, tailWord_6277223, baseEnd_6277223] using wordTrace_append hprefix tailTrace_6277223
  have hstable : (prefixWord ++ tailWord_6277223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277223).length < 2 ^ (prefixWord ++ tailWord_6277223).sum := by decide
  have hdescent : baseEnd_6277223 < baseStart_6277223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277269 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_6277269 : Nat := 118140960795 + 6277269 * 2 ^ 59
def prefixEnd_6277269 : Nat := 4983230072969 + 3 ^ 40 * 6277269 * 2
def baseEnd_6277269 : Nat := 3223256194568105889868871

theorem tailTrace_6277269 : CollatzResearch.WordTrace tailWord_6277269 prefixEnd_6277269 3223256194568105889868871 := by
  unfold tailWord_6277269
  simp only [CollatzResearch.WordTrace]
  refine ⟨228950809495533960038282861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152633872997022640025521907 228950809495533960038282861)
  ·
    refine ⟨85856553560825235014356073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228950809495533960038282861 85856553560825235014356073)
    ·
      refine ⟨64392415170618926260767055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85856553560825235014356073 64392415170618926260767055)
      ·
        refine ⟨96588622755928389391150583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64392415170618926260767055 96588622755928389391150583)
        ·
          refine ⟨144882934133892584086725875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96588622755928389391150583 144882934133892584086725875)
          ·
            refine ⟨217324401200838876130088813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144882934133892584086725875 217324401200838876130088813)
            ·
              refine ⟨81496650450314578548783305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217324401200838876130088813 81496650450314578548783305)
              ·
                refine ⟨61122487837735933911587479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81496650450314578548783305 61122487837735933911587479)
                ·
                  refine ⟨91683731756603900867381219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61122487837735933911587479 91683731756603900867381219)
                  ·
                    refine ⟨137525597634905851301071829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91683731756603900867381219 137525597634905851301071829)
                    ·
                      refine ⟨3223256194568105889868871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137525597634905851301071829 3223256194568105889868871)
                      ·
                        rfl

theorem cell23_6277269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_6277269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277269 prefixEnd_6277269 := by exact prefixLift 6277269
  have htrace : WordTrace (prefixWord ++ tailWord_6277269) baseStart_6277269 baseEnd_6277269 := by
    simpa [prefixWord, tailWord_6277269, baseEnd_6277269] using wordTrace_append hprefix tailTrace_6277269
  have hstable : (prefixWord ++ tailWord_6277269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277269).length < 2 ^ (prefixWord ++ tailWord_6277269).sum := by decide
  have hdescent : baseEnd_6277269 < baseStart_6277269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277293 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_6277293 : Nat := 118140960795 + 6277293 * 2 ^ 59
def prefixEnd_6277293 : Nat := 4983230072969 + 3 ^ 40 * 6277293 * 2
def baseEnd_6277293 : Nat := 1074422839367937931989587

theorem tailTrace_6277293 : CollatzResearch.WordTrace tailWord_6277293 prefixEnd_6277293 1074422839367937931989587 := by
  unfold tailWord_6277293
  simp only [CollatzResearch.WordTrace]
  refine ⟨228951684847447012137156533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152634456564964674758104355 228951684847447012137156533)
  ·
    refine ⟨21464220454448157387858425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228951684847447012137156533 21464220454448157387858425)
    ·
      refine ⟨16098165340836118040893819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21464220454448157387858425 16098165340836118040893819)
      ·
        refine ⟨24147248011254177061340729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16098165340836118040893819 24147248011254177061340729)
        ·
          refine ⟨18110436008440632796005547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24147248011254177061340729 18110436008440632796005547)
          ·
            refine ⟨27165654012660949194008321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18110436008440632796005547 27165654012660949194008321)
            ·
              refine ⟨20374240509495711895506241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27165654012660949194008321 20374240509495711895506241)
              ·
                refine ⟨15280680382121783921629681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20374240509495711895506241 15280680382121783921629681)
                ·
                  refine ⟨11460510286591337941222261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15280680382121783921629681 11460510286591337941222261)
                  ·
                    refine ⟨1074422839367937931989587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11460510286591337941222261 1074422839367937931989587)
                    ·
                      rfl

theorem cell23_6277293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_6277293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277293 prefixEnd_6277293 := by exact prefixLift 6277293
  have htrace : WordTrace (prefixWord ++ tailWord_6277293) baseStart_6277293 baseEnd_6277293 := by
    simpa [prefixWord, tailWord_6277293, baseEnd_6277293] using wordTrace_append hprefix tailTrace_6277293
  have hstable : (prefixWord ++ tailWord_6277293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277293).length < 2 ^ (prefixWord ++ tailWord_6277293).sum := by decide
  have hdescent : baseEnd_6277293 < baseStart_6277293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277297 : List Nat := [1, 2, 2, 5, 2, 2, 2, 2, 5]
def baseStart_6277297 : Nat := 118140960795 + 6277297 * 2 ^ 59
def prefixEnd_6277297 : Nat := 4983230072969 + 3 ^ 40 * 6277297 * 2
def baseEnd_6277297 : Nat := 358141174669603531146527

theorem tailTrace_6277297 : CollatzResearch.WordTrace tailWord_6277297 prefixEnd_6277297 358141174669603531146527 := by
  unfold tailWord_6277297
  simp only [CollatzResearch.WordTrace]
  refine ⟨228951830739432520820302145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152634553826288347213534763 228951830739432520820302145)
  ·
    refine ⟨171713873054574390615226609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228951830739432520820302145 171713873054574390615226609)
    ·
      refine ⟨128785404790930792961419957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171713873054574390615226609 128785404790930792961419957)
      ·
        refine ⟨12073631699149761840133121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128785404790930792961419957 12073631699149761840133121)
        ·
          refine ⟨9055223774362321380099841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12073631699149761840133121 9055223774362321380099841)
          ·
            refine ⟨6791417830771741035074881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9055223774362321380099841 6791417830771741035074881)
            ·
              refine ⟨5093563373078805776306161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6791417830771741035074881 5093563373078805776306161)
              ·
                refine ⟨3820172529809104332229621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5093563373078805776306161 3820172529809104332229621)
                ·
                  refine ⟨358141174669603531146527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3820172529809104332229621 358141174669603531146527)
                  ·
                    rfl

theorem cell23_6277297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 5].length) (baseStart_6277297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277297 prefixEnd_6277297 := by exact prefixLift 6277297
  have htrace : WordTrace (prefixWord ++ tailWord_6277297) baseStart_6277297 baseEnd_6277297 := by
    simpa [prefixWord, tailWord_6277297, baseEnd_6277297] using wordTrace_append hprefix tailTrace_6277297
  have hstable : (prefixWord ++ tailWord_6277297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277297).length < 2 ^ (prefixWord ++ tailWord_6277297).sum := by decide
  have hdescent : baseEnd_6277297 < baseStart_6277297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277299 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 5]
def baseStart_6277299 : Nat := 118140960795 + 6277299 * 2 ^ 59
def prefixEnd_6277299 : Nat := 4983230072969 + 3 ^ 40 * 6277299 * 2
def baseEnd_6277299 : Nat := 3223271598987740772493733

theorem tailTrace_6277299 : CollatzResearch.WordTrace tailWord_6277299 prefixEnd_6277299 3223271598987740772493733 := by
  unfold tailWord_6277299
  simp only [CollatzResearch.WordTrace]
  refine ⟨228951903685425275161874951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152634602456950183441249967 228951903685425275161874951)
  ·
    refine ⟨343427855528137912742812427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228951903685425275161874951 343427855528137912742812427)
    ·
      refine ⟨515141783292206869114218641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343427855528137912742812427 515141783292206869114218641)
      ·
        refine ⟨386356337469155151835663981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515141783292206869114218641 386356337469155151835663981)
        ·
          refine ⟨144883626550933181938373993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386356337469155151835663981 144883626550933181938373993)
          ·
            refine ⟨108662719913199886453780495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144883626550933181938373993 108662719913199886453780495)
            ·
              refine ⟨162994079869799829680670743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108662719913199886453780495 162994079869799829680670743)
              ·
                refine ⟨244491119804699744521006115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162994079869799829680670743 244491119804699744521006115)
                ·
                  refine ⟨366736679707049616781509173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244491119804699744521006115 366736679707049616781509173)
                  ·
                    refine ⟨34381563722535901573266485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 366736679707049616781509173 34381563722535901573266485)
                    ·
                      refine ⟨3223271598987740772493733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34381563722535901573266485 3223271598987740772493733)
                      ·
                        rfl

theorem cell23_6277299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_6277299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277299 prefixEnd_6277299 := by exact prefixLift 6277299
  have htrace : WordTrace (prefixWord ++ tailWord_6277299) baseStart_6277299 baseEnd_6277299 := by
    simpa [prefixWord, tailWord_6277299, baseEnd_6277299] using wordTrace_append hprefix tailTrace_6277299
  have hstable : (prefixWord ++ tailWord_6277299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277299).length < 2 ^ (prefixWord ++ tailWord_6277299).sum := by decide
  have hdescent : baseEnd_6277299 < baseStart_6277299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277319 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 12]
def baseStart_6277319 : Nat := 118140960795 + 6277319 * 2 ^ 59
def prefixEnd_6277319 : Nat := 4983230072969 + 3 ^ 40 * 6277319 * 2
def baseEnd_6277319 : Nat := 358142429844536743804849

theorem tailTrace_6277319 : CollatzResearch.WordTrace tailWord_6277319 prefixEnd_6277319 358142429844536743804849 := by
  unfold tailWord_6277319
  simp only [CollatzResearch.WordTrace]
  refine ⟨228952633145352818577603011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152635088763568545718402007 228952633145352818577603011)
  ·
    refine ⟨343428949718029227866404517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228952633145352818577603011 343428949718029227866404517)
    ·
      refine ⟨64392928072130480224950847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 343428949718029227866404517 64392928072130480224950847)
      ·
        refine ⟨96589392108195720337426271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64392928072130480224950847 96589392108195720337426271)
        ·
          refine ⟨144884088162293580506139407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96589392108195720337426271 144884088162293580506139407)
          ·
            refine ⟨217326132243440370759209111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144884088162293580506139407 217326132243440370759209111)
            ·
              refine ⟨325989198365160556138813667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217326132243440370759209111 325989198365160556138813667)
              ·
                refine ⟨488983797547740834208220501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325989198365160556138813667 488983797547740834208220501)
                ·
                  refine ⟨358142429844536743804849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 488983797547740834208220501 358142429844536743804849)
                  ·
                    rfl

theorem cell23_6277319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 12].length) (baseStart_6277319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277319 prefixEnd_6277319 := by exact prefixLift 6277319
  have htrace : WordTrace (prefixWord ++ tailWord_6277319) baseStart_6277319 baseEnd_6277319 := by
    simpa [prefixWord, tailWord_6277319, baseEnd_6277319] using wordTrace_append hprefix tailTrace_6277319
  have hstable : (prefixWord ++ tailWord_6277319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277319).length < 2 ^ (prefixWord ++ tailWord_6277319).sum := by decide
  have hdescent : baseEnd_6277319 < baseStart_6277319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277330 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_6277330 : Nat := 118140960795 + 6277330 * 2 ^ 59
def prefixEnd_6277330 : Nat := 4983230072969 + 3 ^ 40 * 6277330 * 2
def baseEnd_6277330 : Nat := 3223287516888030151206091

theorem tailTrace_6277330 : CollatzResearch.WordTrace tailWord_6277330 prefixEnd_6277330 3223287516888030151206091 := by
  unfold tailWord_6277330
  simp only [CollatzResearch.WordTrace]
  refine ⟨57238258587078241864063361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152635356232208644970835629 57238258587078241864063361)
  ·
    refine ⟨42928693940308681398047521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57238258587078241864063361 42928693940308681398047521)
    ·
      refine ⟨32196520455231511048535641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42928693940308681398047521 32196520455231511048535641)
      ·
        refine ⟨24147390341423633286401731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32196520455231511048535641 24147390341423633286401731)
        ·
          refine ⟨36221085512135449929602597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24147390341423633286401731 36221085512135449929602597)
          ·
            refine ⟨6791453533525396861800487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36221085512135449929602597 6791453533525396861800487)
            ·
              refine ⟨10187180300288095292700731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6791453533525396861800487 10187180300288095292700731)
              ·
                refine ⟨15280770450432142939051097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10187180300288095292700731 15280770450432142939051097)
                ·
                  refine ⟨11460577837824107204288323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15280770450432142939051097 11460577837824107204288323)
                  ·
                    refine ⟨17190866756736160806432485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11460577837824107204288323 17190866756736160806432485)
                    ·
                      refine ⟨3223287516888030151206091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17190866756736160806432485 3223287516888030151206091)
                      ·
                        rfl

theorem cell23_6277330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_6277330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277330 prefixEnd_6277330 := by exact prefixLift 6277330
  have htrace : WordTrace (prefixWord ++ tailWord_6277330) baseStart_6277330 baseEnd_6277330 := by
    simpa [prefixWord, tailWord_6277330, baseEnd_6277330] using wordTrace_append hprefix tailTrace_6277330
  have hstable : (prefixWord ++ tailWord_6277330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277330).length < 2 ^ (prefixWord ++ tailWord_6277330).sum := by decide
  have hdescent : baseEnd_6277330 < baseStart_6277330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277339 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 8]
def baseStart_6277339 : Nat := 118140960795 + 6277339 * 2 ^ 59
def prefixEnd_6277339 : Nat := 4983230072969 + 3 ^ 40 * 6277339 * 2
def baseEnd_6277339 : Nat := 3223292138213920615993549

theorem tailTrace_6277339 : CollatzResearch.WordTrace tailWord_6277339 prefixEnd_6277339 3223292138213920615993549 := by
  unfold tailWord_6277339
  simp only [CollatzResearch.WordTrace]
  refine ⟨228953362605280361993331071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152635575070186907995554047 228953362605280361993331071)
  ·
    refine ⟨343430043907920542989996607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228953362605280361993331071 343430043907920542989996607)
    ·
      refine ⟨515145065861880814484994911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343430043907920542989996607 515145065861880814484994911)
      ·
        refine ⟨772717598792821221727492367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515145065861880814484994911 772717598792821221727492367)
        ·
          refine ⟨1159076398189231832591238551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 772717598792821221727492367 1159076398189231832591238551)
          ·
            refine ⟨1738614597283847748886857827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159076398189231832591238551 1738614597283847748886857827)
            ·
              refine ⟨2607921895925771623330286741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738614597283847748886857827 2607921895925771623330286741)
              ·
                refine ⟨122246338871520544843607191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2607921895925771623330286741 122246338871520544843607191)
                ·
                  refine ⟨183369508307280817265410787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122246338871520544843607191 183369508307280817265410787)
                  ·
                    refine ⟨275054262460921225898116181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 183369508307280817265410787 275054262460921225898116181)
                    ·
                      refine ⟨3223292138213920615993549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 275054262460921225898116181 3223292138213920615993549)
                      ·
                        rfl

theorem cell23_6277339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 8].length) (baseStart_6277339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277339 prefixEnd_6277339 := by exact prefixLift 6277339
  have htrace : WordTrace (prefixWord ++ tailWord_6277339) baseStart_6277339 baseEnd_6277339 := by
    simpa [prefixWord, tailWord_6277339, baseEnd_6277339] using wordTrace_append hprefix tailTrace_6277339
  have hstable : (prefixWord ++ tailWord_6277339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277339).length < 2 ^ (prefixWord ++ tailWord_6277339).sum := by decide
  have hdescent : baseEnd_6277339 < baseStart_6277339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277390 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2]
def baseStart_6277390 : Nat := 118140960795 + 6277390 * 2 ^ 59
def prefixEnd_6277390 : Nat := 4983230072969 + 3 ^ 40 * 6277390 * 2
def baseEnd_6277390 : Nat := 3223318325727299916455815

theorem tailTrace_6277390 : CollatzResearch.WordTrace tailWord_6277390 prefixEnd_6277390 3223318325727299916455815 := by
  unfold tailWord_6277390
  simp only [CollatzResearch.WordTrace]
  refine ⟨28619402841011949712929703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152636815152063731802291749 28619402841011949712929703)
  ·
    refine ⟨42929104261517924569394555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28619402841011949712929703 42929104261517924569394555)
    ·
      refine ⟨64393656392276886854091833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42929104261517924569394555 64393656392276886854091833)
      ·
        refine ⟨48295242294207665140568875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64393656392276886854091833 48295242294207665140568875)
        ·
          refine ⟨72442863441311497710853313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48295242294207665140568875 72442863441311497710853313)
          ·
            refine ⟨54332147580983623283139985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72442863441311497710853313 54332147580983623283139985)
            ·
              refine ⟨40749110685737717462354989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54332147580983623283139985 40749110685737717462354989)
              ·
                refine ⟨15280916507151644048383121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40749110685737717462354989 15280916507151644048383121)
                ·
                  refine ⟨11460687380363733036287341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15280916507151644048383121 11460687380363733036287341)
                  ·
                    refine ⟨4297757767636399888607753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11460687380363733036287341 4297757767636399888607753)
                    ·
                      refine ⟨3223318325727299916455815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4297757767636399888607753 3223318325727299916455815)
                      ·
                        rfl

theorem cell23_6277390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_6277390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277390 prefixEnd_6277390 := by exact prefixLift 6277390
  have htrace : WordTrace (prefixWord ++ tailWord_6277390) baseStart_6277390 baseEnd_6277390 := by
    simpa [prefixWord, tailWord_6277390, baseEnd_6277390] using wordTrace_append hprefix tailTrace_6277390
  have hstable : (prefixWord ++ tailWord_6277390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277390).length < 2 ^ (prefixWord ++ tailWord_6277390).sum := by decide
  have hdescent : baseEnd_6277390 < baseStart_6277390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277397 : List Nat := [1, 3, 2, 1, 2, 1, 5, 3, 1, 1, 3]
def baseStart_6277397 : Nat := 118140960795 + 6277397 * 2 ^ 59
def prefixEnd_6277397 : Nat := 4983230072969 + 3 ^ 40 * 6277397 * 2
def baseEnd_6277397 : Nat := 3223321920091881389068283

theorem tailTrace_6277397 : CollatzResearch.WordTrace tailWord_6277397 prefixEnd_6277397 3223321920091881389068283 := by
  unfold tailWord_6277397
  simp only [CollatzResearch.WordTrace]
  refine ⟨228955478039070237898942445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152636985359380158599294963 228955478039070237898942445)
  ·
    refine ⟨85858304264651339212103417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228955478039070237898942445 85858304264651339212103417)
    ·
      refine ⟨64393728198488504409077563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85858304264651339212103417 64393728198488504409077563)
      ·
        refine ⟨96590592297732756613616345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64393728198488504409077563 96590592297732756613616345)
        ·
          refine ⟨72442944223299567460212259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96590592297732756613616345 72442944223299567460212259)
          ·
            refine ⟨108664416334949351190318389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72442944223299567460212259 108664416334949351190318389)
            ·
              refine ⟨10187289031401501674092349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108664416334949351190318389 10187289031401501674092349)
              ·
                refine ⟨3820233386775563127784631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10187289031401501674092349 3820233386775563127784631)
                ·
                  refine ⟨5730350080163344691676947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820233386775563127784631 5730350080163344691676947)
                  ·
                    refine ⟨8595525120245017037515421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5730350080163344691676947 8595525120245017037515421)
                    ·
                      refine ⟨3223321920091881389068283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8595525120245017037515421 3223321920091881389068283)
                      ·
                        rfl

theorem cell23_6277397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_6277397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277397 prefixEnd_6277397 := by exact prefixLift 6277397
  have htrace : WordTrace (prefixWord ++ tailWord_6277397) baseStart_6277397 baseEnd_6277397 := by
    simpa [prefixWord, tailWord_6277397, baseEnd_6277397] using wordTrace_append hprefix tailTrace_6277397
  have hstable : (prefixWord ++ tailWord_6277397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277397).length < 2 ^ (prefixWord ++ tailWord_6277397).sum := by decide
  have hdescent : baseEnd_6277397 < baseStart_6277397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277403 : List Nat := [1, 1, 1, 1, 1, 1, 8, 3, 1, 1, 4]
def baseStart_6277403 : Nat := 118140960795 + 6277403 * 2 ^ 59
def prefixEnd_6277403 : Nat := 4983230072969 + 3 ^ 40 * 6277403 * 2
def baseEnd_6277403 : Nat := 3223325000975808365593255

theorem tailTrace_6277403 : CollatzResearch.WordTrace tailWord_6277403 prefixEnd_6277403 3223325000975808365593255 := by
  unfold tailWord_6277403
  simp only [CollatzResearch.WordTrace]
  refine ⟨228955696877048500923660863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152637131251365667282440575 228955696877048500923660863)
  ·
    refine ⟨343433545315572751385491295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228955696877048500923660863 343433545315572751385491295)
    ·
      refine ⟨515150317973359127078236943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343433545315572751385491295 515150317973359127078236943)
      ·
        refine ⟨772725476960038690617355415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515150317973359127078236943 772725476960038690617355415)
        ·
          refine ⟨1159088215440058035926033123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 772725476960038690617355415 1159088215440058035926033123)
          ·
            refine ⟨1738632323160087053889049685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159088215440058035926033123 1738632323160087053889049685)
            ·
              refine ⟨20374597537032270162762301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1738632323160087053889049685 20374597537032270162762301)
              ·
                refine ⟨7640474076387101311035863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20374597537032270162762301 7640474076387101311035863)
                ·
                  refine ⟨11460711114580651966553795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7640474076387101311035863 11460711114580651966553795)
                  ·
                    refine ⟨17191066671870977949830693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11460711114580651966553795 17191066671870977949830693)
                    ·
                      refine ⟨3223325000975808365593255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17191066671870977949830693 3223325000975808365593255)
                      ·
                        rfl

theorem cell23_6277403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 1, 4].length) (baseStart_6277403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277403 prefixEnd_6277403 := by exact prefixLift 6277403
  have htrace : WordTrace (prefixWord ++ tailWord_6277403) baseStart_6277403 baseEnd_6277403 := by
    simpa [prefixWord, tailWord_6277403, baseEnd_6277403] using wordTrace_append hprefix tailTrace_6277403
  have hstable : (prefixWord ++ tailWord_6277403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277403).length < 2 ^ (prefixWord ++ tailWord_6277403).sum := by decide
  have hdescent : baseEnd_6277403 < baseStart_6277403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277433 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 1, 1, 6]
def baseStart_6277433 : Nat := 118140960795 + 6277433 * 2 ^ 59
def prefixEnd_6277433 : Nat := 4983230072969 + 3 ^ 40 * 6277433 * 2
def baseEnd_6277433 : Nat := 3223340405395443248218117

theorem tailTrace_6277433 : CollatzResearch.WordTrace tailWord_6277433 prefixEnd_6277433 3223340405395443248218117 := by
  unfold tailWord_6277433
  simp only [CollatzResearch.WordTrace]
  refine ⟨228956791066939816047252953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152637860711293210698168635 228956791066939816047252953)
  ·
    refine ⟨171717593300204862035439715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228956791066939816047252953 171717593300204862035439715)
    ·
      refine ⟨257576389950307293053159573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171717593300204862035439715 257576389950307293053159573)
      ·
        refine ⟨12073893278920654361866855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 257576389950307293053159573 12073893278920654361866855)
        ·
          refine ⟨18110839918380981542800283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12073893278920654361866855 18110839918380981542800283)
          ·
            refine ⟨27166259877571472314200425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18110839918380981542800283 27166259877571472314200425)
            ·
              refine ⟨20374694908178604235650319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27166259877571472314200425 20374694908178604235650319)
              ·
                refine ⟨30562042362267906353475479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20374694908178604235650319 30562042362267906353475479)
                ·
                  refine ⟨45843063543401859530213219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30562042362267906353475479 45843063543401859530213219)
                  ·
                    refine ⟨68764595315102789295319829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45843063543401859530213219 68764595315102789295319829)
                    ·
                      refine ⟨3223340405395443248218117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68764595315102789295319829 3223340405395443248218117)
                      ·
                        rfl

theorem cell23_6277433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_6277433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277433 prefixEnd_6277433 := by exact prefixLift 6277433
  have htrace : WordTrace (prefixWord ++ tailWord_6277433) baseStart_6277433 baseEnd_6277433 := by
    simpa [prefixWord, tailWord_6277433, baseEnd_6277433] using wordTrace_append hprefix tailTrace_6277433
  have hstable : (prefixWord ++ tailWord_6277433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277433).length < 2 ^ (prefixWord ++ tailWord_6277433).sum := by decide
  have hdescent : baseEnd_6277433 < baseStart_6277433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277457 : List Nat := [1, 2, 2, 1, 4, 3, 3, 1, 1, 2, 3]
def baseStart_6277457 : Nat := 118140960795 + 6277457 * 2 ^ 59
def prefixEnd_6277457 : Nat := 4983230072969 + 3 ^ 40 * 6277457 * 2
def baseEnd_6277457 : Nat := 3223352728931151154318007

theorem tailTrace_6277457 : CollatzResearch.WordTrace tailWord_6277457 prefixEnd_6277457 3223352728931151154318007 := by
  unfold tailWord_6277457
  simp only [CollatzResearch.WordTrace]
  refine ⟨228957666418852868146126625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152638444279235245430751083 228957666418852868146126625)
  ·
    refine ⟨171718249814139651109594969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228957666418852868146126625 171718249814139651109594969)
    ·
      refine ⟨128788687360604738332196227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171718249814139651109594969 128788687360604738332196227)
      ·
        refine ⟨193183031040907107498294341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128788687360604738332196227 193183031040907107498294341)
        ·
          refine ⟨36221818320170082655930189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193183031040907107498294341 36221818320170082655930189)
          ·
            refine ⟨13583181870063780995973821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36221818320170082655930189 13583181870063780995973821)
            ·
              refine ⟨5093693201273917873490183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13583181870063780995973821 5093693201273917873490183)
              ·
                refine ⟨7640539801910876810235275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5093693201273917873490183 7640539801910876810235275)
                ·
                  refine ⟨11460809702866315215352913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7640539801910876810235275 11460809702866315215352913)
                  ·
                    refine ⟨8595607277149736411514685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11460809702866315215352913 8595607277149736411514685)
                    ·
                      refine ⟨3223352728931151154318007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8595607277149736411514685 3223352728931151154318007)
                      ·
                        rfl

theorem cell23_6277457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 1, 2, 3].length) (baseStart_6277457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277457 prefixEnd_6277457 := by exact prefixLift 6277457
  have htrace : WordTrace (prefixWord ++ tailWord_6277457) baseStart_6277457 baseEnd_6277457 := by
    simpa [prefixWord, tailWord_6277457, baseEnd_6277457] using wordTrace_append hprefix tailTrace_6277457
  have hstable : (prefixWord ++ tailWord_6277457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277457).length < 2 ^ (prefixWord ++ tailWord_6277457).sum := by decide
  have hdescent : baseEnd_6277457 < baseStart_6277457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277544 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_6277544 : Nat := 118140960795 + 6277544 * 2 ^ 59
def prefixEnd_6277544 : Nat := 4983230072969 + 3 ^ 40 * 6277544 * 2
def baseEnd_6277544 : Nat := 3223397401748092313930107

theorem tailTrace_6277544 : CollatzResearch.WordTrace tailWord_6277544 prefixEnd_6277544 3223397401748092313930107 := by
  unfold tailWord_6277544
  simp only [CollatzResearch.WordTrace]
  refine ⟨114480419784768841002271843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152640559713025121336362457 114480419784768841002271843)
  ·
    refine ⟨171720629677153261503407765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114480419784768841002271843 171720629677153261503407765)
    ·
      refine ⟨8049404516116559132972239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 171720629677153261503407765 8049404516116559132972239)
      ·
        refine ⟨12074106774174838699458359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8049404516116559132972239 12074106774174838699458359)
        ·
          refine ⟨18111160161262258049187539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12074106774174838699458359 18111160161262258049187539)
          ·
            refine ⟨27166740241893387073781309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18111160161262258049187539 27166740241893387073781309)
            ·
              refine ⟨10187527590710020152667991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27166740241893387073781309 10187527590710020152667991)
              ·
                refine ⟨15281291386065030229001987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10187527590710020152667991 15281291386065030229001987)
                ·
                  refine ⟨22921937079097545343502981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15281291386065030229001987 22921937079097545343502981)
                  ·
                    refine ⟨4297863202330789751906809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22921937079097545343502981 4297863202330789751906809)
                    ·
                      refine ⟨3223397401748092313930107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4297863202330789751906809 3223397401748092313930107)
                      ·
                        rfl

theorem cell23_6277544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_6277544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277544 prefixEnd_6277544 := by exact prefixLift 6277544
  have htrace : WordTrace (prefixWord ++ tailWord_6277544) baseStart_6277544 baseEnd_6277544 := by
    simpa [prefixWord, tailWord_6277544, baseEnd_6277544] using wordTrace_append hprefix tailTrace_6277544
  have hstable : (prefixWord ++ tailWord_6277544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277544).length < 2 ^ (prefixWord ++ tailWord_6277544).sum := by decide
  have hdescent : baseEnd_6277544 < baseStart_6277544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277600 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 1, 6, 2]
def baseStart_6277600 : Nat := 118140960795 + 6277600 * 2 ^ 59
def prefixEnd_6277600 : Nat := 4983230072969 + 3 ^ 40 * 6277600 * 2
def baseEnd_6277600 : Nat := 3223426156664744094829849

theorem tailTrace_6277600 : CollatzResearch.WordTrace tailWord_6277600 prefixEnd_6277600 3223426156664744094829849 := by
  unfold tailWord_6277600
  simp only [CollatzResearch.WordTrace]
  refine ⟨114481441028667401784291127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152641921371556535712388169 114481441028667401784291127)
  ·
    refine ⟨171722161543001102676436691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114481441028667401784291127 171722161543001102676436691)
    ·
      refine ⟨257583242314501654014655037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171722161543001102676436691 257583242314501654014655037)
      ·
        refine ⟨96593715867938120255495639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257583242314501654014655037 96593715867938120255495639)
        ·
          refine ⟨144890573801907180383243459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96593715867938120255495639 144890573801907180383243459)
          ·
            refine ⟨217335860702860770574865189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144890573801907180383243459 217335860702860770574865189)
            ·
              refine ⟨40750473881786394482787223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217335860702860770574865189 40750473881786394482787223)
              ·
                refine ⟨61125710822679591724180835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40750473881786394482787223 61125710822679591724180835)
                ·
                  refine ⟨91688566234019387586271253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61125710822679591724180835 91688566234019387586271253)
                  ·
                    refine ⟨4297901542219658793106465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91688566234019387586271253 4297901542219658793106465)
                    ·
                      refine ⟨3223426156664744094829849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4297901542219658793106465 3223426156664744094829849)
                      ·
                        rfl

theorem cell23_6277600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_6277600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277600 prefixEnd_6277600 := by exact prefixLift 6277600
  have htrace : WordTrace (prefixWord ++ tailWord_6277600) baseStart_6277600 baseEnd_6277600 := by
    simpa [prefixWord, tailWord_6277600, baseEnd_6277600] using wordTrace_append hprefix tailTrace_6277600
  have hstable : (prefixWord ++ tailWord_6277600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277600).length < 2 ^ (prefixWord ++ tailWord_6277600).sum := by decide
  have hdescent : baseEnd_6277600 < baseStart_6277600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277644 : List Nat := [2, 2, 1, 2, 4, 2, 1, 4, 1, 4]
def baseStart_6277644 : Nat := 118140960795 + 6277644 * 2 ^ 59
def prefixEnd_6277644 : Nat := 4983230072969 + 3 ^ 40 * 6277644 * 2
def baseEnd_6277644 : Nat := 1074482916604513974226549

theorem tailTrace_6277644 : CollatzResearch.WordTrace tailWord_6277644 prefixEnd_6277644 1074482916604513974226549 := by
  unfold tailWord_6277644
  simp only [CollatzResearch.WordTrace]
  refine ⟨114482243434587699541591993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152642991246116932722122657 114482243434587699541591993)
  ·
    refine ⟨85861682575940774656193995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114482243434587699541591993 85861682575940774656193995)
    ·
      refine ⟨128792523863911161984290993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85861682575940774656193995 128792523863911161984290993)
      ·
        refine ⟨96594392897933371488218245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128792523863911161984290993 96594392897933371488218245)
        ·
          refine ⟨18111448668362507154040921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96594392897933371488218245 18111448668362507154040921)
          ·
            refine ⟨13583586501271880365530691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18111448668362507154040921 13583586501271880365530691)
            ·
              refine ⟨20375379751907820548296037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13583586501271880365530691 20375379751907820548296037)
              ·
                refine ⟨3820383703482716352805507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20375379751907820548296037 3820383703482716352805507)
                ·
                  refine ⟨5730575555224074529208261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820383703482716352805507 5730575555224074529208261)
                  ·
                    refine ⟨1074482916604513974226549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5730575555224074529208261 1074482916604513974226549)
                    ·
                      rfl

theorem cell23_6277644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 1, 4].length) (baseStart_6277644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277644 prefixEnd_6277644 := by exact prefixLift 6277644
  have htrace : WordTrace (prefixWord ++ tailWord_6277644) baseStart_6277644 baseEnd_6277644 := by
    simpa [prefixWord, tailWord_6277644, baseEnd_6277644] using wordTrace_append hprefix tailTrace_6277644
  have hstable : (prefixWord ++ tailWord_6277644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277644).length < 2 ^ (prefixWord ++ tailWord_6277644).sum := by decide
  have hdescent : baseEnd_6277644 < baseStart_6277644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277663 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 7]
def baseStart_6277663 : Nat := 118140960795 + 6277663 * 2 ^ 59
def prefixEnd_6277663 : Nat := 4983230072969 + 3 ^ 40 * 6277663 * 2
def baseEnd_6277663 : Nat := 3223458505945977348342059

theorem tailTrace_6277663 : CollatzResearch.WordTrace tailWord_6277663 prefixEnd_6277663 3223458505945977348342059 := by
  unfold tailWord_6277663
  simp only [CollatzResearch.WordTrace]
  refine ⟨228965179856106565328125643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152643453237404376885417095 228965179856106565328125643)
  ·
    refine ⟨343447769784159847992188465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228965179856106565328125643 343447769784159847992188465)
    ·
      refine ⟨257585827338119885994141349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343447769784159847992188465 257585827338119885994141349)
      ·
        refine ⟨48297342625897478623901503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257585827338119885994141349 48297342625897478623901503)
        ·
          refine ⟨72446013938846217935852255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48297342625897478623901503 72446013938846217935852255)
          ·
            refine ⟨108669020908269326903778383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72446013938846217935852255 108669020908269326903778383)
            ·
              refine ⟨163003531362403990355667575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108669020908269326903778383 163003531362403990355667575)
              ·
                refine ⟨244505297043605985533501363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163003531362403990355667575 244505297043605985533501363)
                ·
                  refine ⟨366757945565408978300252045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244505297043605985533501363 366757945565408978300252045)
                  ·
                    refine ⟨137534229587028366862594517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 366757945565408978300252045 137534229587028366862594517)
                    ·
                      refine ⟨3223458505945977348342059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137534229587028366862594517 3223458505945977348342059)
                      ·
                        rfl

theorem cell23_6277663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_6277663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277663 prefixEnd_6277663 := by exact prefixLift 6277663
  have htrace : WordTrace (prefixWord ++ tailWord_6277663) baseStart_6277663 baseEnd_6277663 := by
    simpa [prefixWord, tailWord_6277663, baseEnd_6277663] using wordTrace_append hprefix tailTrace_6277663
  have hstable : (prefixWord ++ tailWord_6277663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277663).length < 2 ^ (prefixWord ++ tailWord_6277663).sum := by decide
  have hdescent : baseEnd_6277663 < baseStart_6277663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277667 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 5, 1, 3]
def baseStart_6277667 : Nat := 118140960795 + 6277667 * 2 ^ 59
def prefixEnd_6277667 : Nat := 4983230072969 + 3 ^ 40 * 6277667 * 2
def baseEnd_6277667 : Nat := 3223460559868595332692041

theorem tailTrace_6277667 : CollatzResearch.WordTrace tailWord_6277667 prefixEnd_6277667 3223460559868595332692041 := by
  unfold tailWord_6277667
  simp only [CollatzResearch.WordTrace]
  refine ⟨228965325748092074011271255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152643550498728049340847503 228965325748092074011271255)
  ·
    refine ⟨343447988622138111016906883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228965325748092074011271255 343447988622138111016906883)
    ·
      refine ⟨515171982933207166525360325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343447988622138111016906883 515171982933207166525360325)
      ·
        refine ⟨96594746799976343723505061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 515171982933207166525360325 96594746799976343723505061)
        ·
          refine ⟨18111515024995564448157199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96594746799976343723505061 18111515024995564448157199)
          ·
            refine ⟨27167272537493346672235799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18111515024995564448157199 27167272537493346672235799)
            ·
              refine ⟨40750908806240020008353699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27167272537493346672235799 40750908806240020008353699)
              ·
                refine ⟨61126363209360030012530549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40750908806240020008353699 61126363209360030012530549)
                ·
                  refine ⟨5730596550877502813674739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61126363209360030012530549 5730596550877502813674739)
                  ·
                    refine ⟨8595894826316254220512109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5730596550877502813674739 8595894826316254220512109)
                    ·
                      refine ⟨3223460559868595332692041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8595894826316254220512109 3223460559868595332692041)
                      ·
                        rfl

theorem cell23_6277667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_6277667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277667 prefixEnd_6277667 := by exact prefixLift 6277667
  have htrace : WordTrace (prefixWord ++ tailWord_6277667) baseStart_6277667 baseEnd_6277667 := by
    simpa [prefixWord, tailWord_6277667, baseEnd_6277667] using wordTrace_append hprefix tailTrace_6277667
  have hstable : (prefixWord ++ tailWord_6277667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277667).length < 2 ^ (prefixWord ++ tailWord_6277667).sum := by decide
  have hdescent : baseEnd_6277667 < baseStart_6277667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277710 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_6277710 : Nat := 118140960795 + 6277710 * 2 ^ 59
def prefixEnd_6277710 : Nat := 4983230072969 + 3 ^ 40 * 6277710 * 2
def baseEnd_6277710 : Nat := 3223482639536738664454343

theorem tailTrace_6277710 : CollatzResearch.WordTrace tailWord_6277710 prefixEnd_6277710 3223482639536738664454343 := by
  unfold tailWord_6277710
  simp only [CollatzResearch.WordTrace]
  refine ⟨28620861760867036544385823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152644596057957528236724389 28620861760867036544385823)
  ·
    refine ⟨42931292641300554816578735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28620861760867036544385823 42931292641300554816578735)
    ·
      refine ⟨64396938961950832224868103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42931292641300554816578735 64396938961950832224868103)
      ·
        refine ⟨96595408442926248337302155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64396938961950832224868103 96595408442926248337302155)
        ·
          refine ⟨144893112664389372505953233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96595408442926248337302155 144893112664389372505953233)
          ·
            refine ⟨108669834498292029379464925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144893112664389372505953233 108669834498292029379464925)
            ·
              refine ⟨40751187936859511017299347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108669834498292029379464925 40751187936859511017299347)
              ·
                refine ⟨61126781905289266525949021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40751187936859511017299347 61126781905289266525949021)
                ·
                  refine ⟨22922543214483474947230883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61126781905289266525949021 22922543214483474947230883)
                  ·
                    refine ⟨34383814821725212420846325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22922543214483474947230883 34383814821725212420846325)
                    ·
                      refine ⟨3223482639536738664454343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34383814821725212420846325 3223482639536738664454343)
                      ·
                        rfl

theorem cell23_6277710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_6277710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277710 prefixEnd_6277710 := by exact prefixLift 6277710
  have htrace : WordTrace (prefixWord ++ tailWord_6277710) baseStart_6277710 baseEnd_6277710 := by
    simpa [prefixWord, tailWord_6277710, baseEnd_6277710] using wordTrace_append hprefix tailTrace_6277710
  have hstable : (prefixWord ++ tailWord_6277710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277710).length < 2 ^ (prefixWord ++ tailWord_6277710).sum := by decide
  have hdescent : baseEnd_6277710 < baseStart_6277710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277717 : List Nat := [1, 3, 2, 2, 1, 1, 2, 5, 2, 4]
def baseStart_6277717 : Nat := 118140960795 + 6277717 * 2 ^ 59
def prefixEnd_6277717 : Nat := 4983230072969 + 3 ^ 40 * 6277717 * 2
def baseEnd_6277717 : Nat := 1074495411300440045688937

theorem tailTrace_6277717 : CollatzResearch.WordTrace tailWord_6277717 prefixEnd_6277717 1074495411300440045688937 := by
  unfold tailWord_6277717
  simp only [CollatzResearch.WordTrace]
  refine ⟨228967149397910932550591405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152644766265273955033727603 228967149397910932550591405)
  ·
    refine ⟨85862681024216599706471777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228967149397910932550591405 85862681024216599706471777)
    ·
      refine ⟨64397010768162449779853833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85862681024216599706471777 64397010768162449779853833)
      ·
        refine ⟨48297758076121837334890375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64397010768162449779853833 48297758076121837334890375)
        ·
          refine ⟨72446637114182756002335563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48297758076121837334890375 72446637114182756002335563)
          ·
            refine ⟨108669955671274134003503345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72446637114182756002335563 108669955671274134003503345)
            ·
              refine ⟨81502466753455600502627509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108669955671274134003503345 81502466753455600502627509)
              ·
                refine ⟨7640856258136462547121329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81502466753455600502627509 7640856258136462547121329)
                ·
                  refine ⟨5730642193602346910340997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7640856258136462547121329 5730642193602346910340997)
                  ·
                    refine ⟨1074495411300440045688937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5730642193602346910340997 1074495411300440045688937)
                    ·
                      rfl

theorem cell23_6277717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_6277717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277717 prefixEnd_6277717 := by exact prefixLift 6277717
  have htrace : WordTrace (prefixWord ++ tailWord_6277717) baseStart_6277717 baseEnd_6277717 := by
    simpa [prefixWord, tailWord_6277717, baseEnd_6277717] using wordTrace_append hprefix tailTrace_6277717
  have hstable : (prefixWord ++ tailWord_6277717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277717).length < 2 ^ (prefixWord ++ tailWord_6277717).sum := by decide
  have hdescent : baseEnd_6277717 < baseStart_6277717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277723 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 9]
def baseStart_6277723 : Nat := 118140960795 + 6277723 * 2 ^ 59
def prefixEnd_6277723 : Nat := 4983230072969 + 3 ^ 40 * 6277723 * 2
def baseEnd_6277723 : Nat := 3223489314785247113591783

theorem tailTrace_6277723 : CollatzResearch.WordTrace tailWord_6277723 prefixEnd_6277723 3223489314785247113591783 := by
  unfold tailWord_6277723
  simp only [CollatzResearch.WordTrace]
  refine ⟨228967368235889195575309823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152644912157259463716873215 228967368235889195575309823)
  ·
    refine ⟨343451052353833793362964735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228967368235889195575309823 343451052353833793362964735)
    ·
      refine ⟨515176578530750690044447103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343451052353833793362964735 515176578530750690044447103)
      ·
        refine ⟨772764867796126035066670655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515176578530750690044447103 772764867796126035066670655)
        ·
          refine ⟨1159147301694189052600005983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 772764867796126035066670655 1159147301694189052600005983)
          ·
            refine ⟨1738720952541283578900008975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159147301694189052600005983 1738720952541283578900008975)
            ·
              refine ⟨2608081428811925368350013463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738720952541283578900008975 2608081428811925368350013463)
              ·
                refine ⟨3912122143217888052525020195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608081428811925368350013463 3912122143217888052525020195)
                ·
                  refine ⟨5868183214826832078787530293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3912122143217888052525020195 5868183214826832078787530293)
                  ·
                    refine ⟨550142176390015507386330965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5868183214826832078787530293 550142176390015507386330965)
                    ·
                      refine ⟨3223489314785247113591783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 550142176390015507386330965 3223489314785247113591783)
                      ·
                        rfl

theorem cell23_6277723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 9].length) (baseStart_6277723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277723 prefixEnd_6277723 := by exact prefixLift 6277723
  have htrace : WordTrace (prefixWord ++ tailWord_6277723) baseStart_6277723 baseEnd_6277723 := by
    simpa [prefixWord, tailWord_6277723, baseEnd_6277723] using wordTrace_append hprefix tailTrace_6277723
  have hstable : (prefixWord ++ tailWord_6277723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277723).length < 2 ^ (prefixWord ++ tailWord_6277723).sum := by decide
  have hdescent : baseEnd_6277723 < baseStart_6277723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277784 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 3, 3, 2]
def baseStart_6277784 : Nat := 118140960795 + 6277784 * 2 ^ 59
def prefixEnd_6277784 : Nat := 4983230072969 + 3 ^ 40 * 6277784 * 2
def baseEnd_6277784 : Nat := 3223520637105171374929003

theorem tailTrace_6277784 : CollatzResearch.WordTrace tailWord_6277784 prefixEnd_6277784 3223520637105171374929003 := by
  unfold tailWord_6277784
  simp only [CollatzResearch.WordTrace]
  refine ⟨114484796544334101496640203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152646395392445468662186937 114484796544334101496640203)
  ·
    refine ⟨171727194816501152244960305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114484796544334101496640203 171727194816501152244960305)
    ·
      refine ⟨128795396112375864183720229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171727194816501152244960305 128795396112375864183720229)
      ·
        refine ⟨24149136771070474534447543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128795396112375864183720229 24149136771070474534447543)
        ·
          refine ⟨36223705156605711801671315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24149136771070474534447543 36223705156605711801671315)
          ·
            refine ⟨54335557734908567702506973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36223705156605711801671315 54335557734908567702506973)
            ·
              refine ⟨20375834150590712888440115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54335557734908567702506973 20375834150590712888440115)
              ·
                refine ⟨30563751225886069332660173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20375834150590712888440115 30563751225886069332660173)
                ·
                  refine ⟨11461406709707275999747565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30563751225886069332660173 11461406709707275999747565)
                  ·
                    refine ⟨4298027516140228499905337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11461406709707275999747565 4298027516140228499905337)
                    ·
                      refine ⟨3223520637105171374929003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4298027516140228499905337 3223520637105171374929003)
                      ·
                        rfl

theorem cell23_6277784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_6277784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277784 prefixEnd_6277784 := by exact prefixLift 6277784
  have htrace : WordTrace (prefixWord ++ tailWord_6277784) baseStart_6277784 baseEnd_6277784 := by
    simpa [prefixWord, tailWord_6277784, baseEnd_6277784] using wordTrace_append hprefix tailTrace_6277784
  have hstable : (prefixWord ++ tailWord_6277784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277784).length < 2 ^ (prefixWord ++ tailWord_6277784).sum := by decide
  have hdescent : baseEnd_6277784 < baseStart_6277784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277809 : List Nat := [1, 2, 2, 6, 2, 1, 2, 2, 1, 2, 2]
def baseStart_6277809 : Nat := 118140960795 + 6277809 * 2 ^ 59
def prefixEnd_6277809 : Nat := 4983230072969 + 3 ^ 40 * 6277809 * 2
def baseEnd_6277809 : Nat := 3223533474121533777116389

theorem tailTrace_6277809 : CollatzResearch.WordTrace tailWord_6277809 prefixEnd_6277809 3223533474121533777116389 := by
  unfold tailWord_6277809
  simp only [CollatzResearch.WordTrace]
  refine ⟨228970504913577632262940481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152647003275718421508626987 228970504913577632262940481)
  ·
    refine ⟨171727878685183224197205361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228970504913577632262940481 171727878685183224197205361)
    ·
      refine ⟨128795909013887418147904021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171727878685183224197205361 128795909013887418147904021)
      ·
        refine ⟨6037308235025972725683001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 128795909013887418147904021 6037308235025972725683001)
        ·
          refine ⟨4527981176269479544262251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6037308235025972725683001 4527981176269479544262251)
          ·
            refine ⟨6791971764404219316393377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4527981176269479544262251 6791971764404219316393377)
            ·
              refine ⟨5093978823303164487295033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6791971764404219316393377 5093978823303164487295033)
              ·
                refine ⟨3820484117477373365471275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5093978823303164487295033 3820484117477373365471275)
                ·
                  refine ⟨5730726176216060048206913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820484117477373365471275 5730726176216060048206913)
                  ·
                    refine ⟨4298044632162045036155185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5730726176216060048206913 4298044632162045036155185)
                    ·
                      refine ⟨3223533474121533777116389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4298044632162045036155185 3223533474121533777116389)
                      ·
                        rfl

theorem cell23_6277809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_6277809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277809 prefixEnd_6277809 := by exact prefixLift 6277809
  have htrace : WordTrace (prefixWord ++ tailWord_6277809) baseStart_6277809 baseEnd_6277809 := by
    simpa [prefixWord, tailWord_6277809, baseEnd_6277809] using wordTrace_append hprefix tailTrace_6277809
  have hstable : (prefixWord ++ tailWord_6277809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277809).length < 2 ^ (prefixWord ++ tailWord_6277809).sum := by decide
  have hdescent : baseEnd_6277809 < baseStart_6277809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277810 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_6277810 : Nat := 118140960795 + 6277810 * 2 ^ 59
def prefixEnd_6277810 : Nat := 4983230072969 + 3 ^ 40 * 6277810 * 2
def baseEnd_6277810 : Nat := 3223533987602188273203883

theorem tailTrace_6277810 : CollatzResearch.WordTrace tailWord_6277810 prefixEnd_6277810 3223533987602188273203883 := by
  unfold tailWord_6277810
  simp only [CollatzResearch.WordTrace]
  refine ⟨57242635346643502358431721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152647027591049339622484589 57242635346643502358431721)
  ·
    refine ⟨42931976509982626768823791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57242635346643502358431721 42931976509982626768823791)
    ·
      refine ⟨64397964764973940153235687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42931976509982626768823791 64397964764973940153235687)
      ·
        refine ⟨96596947147460910229853531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64397964764973940153235687 96596947147460910229853531)
        ·
          refine ⟨144895420721191365344780297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96596947147460910229853531 144895420721191365344780297)
          ·
            refine ⟨108671565540893524008585223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144895420721191365344780297 108671565540893524008585223)
            ·
              refine ⟨163007348311340286012877835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108671565540893524008585223 163007348311340286012877835)
              ·
                refine ⟨244511022467010429019316753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163007348311340286012877835 244511022467010429019316753)
                ·
                  refine ⟨183383266850257821764487565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244511022467010429019316753 183383266850257821764487565)
                  ·
                    refine ⟨68768725068846683161682837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183383266850257821764487565 68768725068846683161682837)
                    ·
                      refine ⟨3223533987602188273203883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68768725068846683161682837 3223533987602188273203883)
                      ·
                        rfl

theorem cell23_6277810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_6277810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277810 prefixEnd_6277810 := by exact prefixLift 6277810
  have htrace : WordTrace (prefixWord ++ tailWord_6277810) baseStart_6277810 baseEnd_6277810 := by
    simpa [prefixWord, tailWord_6277810, baseEnd_6277810] using wordTrace_append hprefix tailTrace_6277810
  have hstable : (prefixWord ++ tailWord_6277810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277810).length < 2 ^ (prefixWord ++ tailWord_6277810).sum := by decide
  have hdescent : baseEnd_6277810 < baseStart_6277810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6277907 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 3]
def baseStart_6277907 : Nat := 118140960795 + 6277907 * 2 ^ 59
def prefixEnd_6277907 : Nat := 4983230072969 + 3 ^ 40 * 6277907 * 2
def baseEnd_6277907 : Nat := 3223583795225674393690937

theorem tailTrace_6277907 : CollatzResearch.WordTrace tailWord_6277907 prefixEnd_6277907 3223583795225674393690937 := by
  unfold tailWord_6277907
  simp only [CollatzResearch.WordTrace]
  refine ⟨228974079267222595000007975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152649386178148396666671983 228974079267222595000007975)
  ·
    refine ⟨343461118900833892500011963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228974079267222595000007975 343461118900833892500011963)
    ·
      refine ⟨515191678351250838750017945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343461118900833892500011963 515191678351250838750017945)
      ·
        refine ⟨386393758763438129062513459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515191678351250838750017945 386393758763438129062513459)
        ·
          refine ⟨579590638145157193593770189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386393758763438129062513459 579590638145157193593770189)
          ·
            refine ⟨217346489304433947597663821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 579590638145157193593770189 217346489304433947597663821)
            ·
              refine ⟨81504933489162730349123933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217346489304433947597663821 81504933489162730349123933)
              ·
                refine ⟨30564350058436023880921475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81504933489162730349123933 30564350058436023880921475)
                ·
                  refine ⟨45846525087654035821382213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30564350058436023880921475 45846525087654035821382213)
                  ·
                    refine ⟨8596223453935131716509165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45846525087654035821382213 8596223453935131716509165)
                    ·
                      refine ⟨3223583795225674393690937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8596223453935131716509165 3223583795225674393690937)
                      ·
                        rfl

theorem cell23_6277907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 3].length) (baseStart_6277907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6277907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6277907 prefixEnd_6277907 := by exact prefixLift 6277907
  have htrace : WordTrace (prefixWord ++ tailWord_6277907) baseStart_6277907 baseEnd_6277907 := by
    simpa [prefixWord, tailWord_6277907, baseEnd_6277907] using wordTrace_append hprefix tailTrace_6277907
  have hstable : (prefixWord ++ tailWord_6277907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6277907).length < 2 ^ (prefixWord ++ tailWord_6277907).sum := by decide
  have hdescent : baseEnd_6277907 < baseStart_6277907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6277907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278007 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 6]
def baseStart_6278007 : Nat := 118140960795 + 6278007 * 2 ^ 59
def prefixEnd_6278007 : Nat := 4983230072969 + 3 ^ 40 * 6278007 * 2
def baseEnd_6278007 : Nat := 3223635143291124002440477

theorem tailTrace_6278007 : CollatzResearch.WordTrace tailWord_6278007 prefixEnd_6278007 3223635143291124002440477 := by
  unfold tailWord_6278007
  simp only [CollatzResearch.WordTrace]
  refine ⟨228977726566860312078648275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152651817711240208052432183 228977726566860312078648275)
  ·
    refine ⟨343466589850290468117972413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228977726566860312078648275 343466589850290468117972413)
    ·
      refine ⟨128799971193858925544239655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343466589850290468117972413 128799971193858925544239655)
      ·
        refine ⟨193199956790788388316359483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128799971193858925544239655 193199956790788388316359483)
        ·
          refine ⟨289799935186182582474539225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193199956790788388316359483 289799935186182582474539225)
          ·
            refine ⟨217349951389636936855904419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289799935186182582474539225 217349951389636936855904419)
            ·
              refine ⟨326024927084455405283856629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217349951389636936855904419 326024927084455405283856629)
              ·
                refine ⟨30564836914167694245361559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 326024927084455405283856629 30564836914167694245361559)
                ·
                  refine ⟨45847255371251541368042339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30564836914167694245361559 45847255371251541368042339)
                  ·
                    refine ⟨68770883056877312052063509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45847255371251541368042339 68770883056877312052063509)
                    ·
                      refine ⟨3223635143291124002440477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68770883056877312052063509 3223635143291124002440477)
                      ·
                        rfl

theorem cell23_6278007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_6278007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278007 prefixEnd_6278007 := by exact prefixLift 6278007
  have htrace : WordTrace (prefixWord ++ tailWord_6278007) baseStart_6278007 baseEnd_6278007 := by
    simpa [prefixWord, tailWord_6278007, baseEnd_6278007] using wordTrace_append hprefix tailTrace_6278007
  have hstable : (prefixWord ++ tailWord_6278007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278007).length < 2 ^ (prefixWord ++ tailWord_6278007).sum := by decide
  have hdescent : baseEnd_6278007 < baseStart_6278007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278011 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 5, 2, 2]
def baseStart_6278011 : Nat := 118140960795 + 6278011 * 2 ^ 59
def prefixEnd_6278011 : Nat := 4983230072969 + 3 ^ 40 * 6278011 * 2
def baseEnd_6278011 : Nat := 3223637197213741986790459

theorem tailTrace_6278011 : CollatzResearch.WordTrace tailWord_6278011 prefixEnd_6278011 3223637197213741986790459 := by
  unfold tailWord_6278011
  simp only [CollatzResearch.WordTrace]
  refine ⟨228977872458845820761793887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152651914972563880507862591 228977872458845820761793887)
  ·
    refine ⟨343466808688268731142690831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228977872458845820761793887 343466808688268731142690831)
    ·
      refine ⟨515200213032403096714036247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343466808688268731142690831 515200213032403096714036247)
      ·
        refine ⟨772800319548604645071054371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515200213032403096714036247 772800319548604645071054371)
        ·
          refine ⟨1159200479322906967606581557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 772800319548604645071054371 1159200479322906967606581557)
          ·
            refine ⟨108675044936522528213117021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1159200479322906967606581557 108675044936522528213117021)
            ·
              refine ⟨40753141851195948079918883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108675044936522528213117021 40753141851195948079918883)
              ·
                refine ⟨61129712776793922119878325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40753141851195948079918883 61129712776793922119878325)
                ·
                  refine ⟨5730910572824430198738593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61129712776793922119878325 5730910572824430198738593)
                  ·
                    refine ⟨4298182929618322649053945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5730910572824430198738593 4298182929618322649053945)
                    ·
                      refine ⟨3223637197213741986790459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4298182929618322649053945 3223637197213741986790459)
                      ·
                        rfl

theorem cell23_6278011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 2, 2].length) (baseStart_6278011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278011 prefixEnd_6278011 := by exact prefixLift 6278011
  have htrace : WordTrace (prefixWord ++ tailWord_6278011) baseStart_6278011 baseEnd_6278011 := by
    simpa [prefixWord, tailWord_6278011, baseEnd_6278011] using wordTrace_append hprefix tailTrace_6278011
  have hstable : (prefixWord ++ tailWord_6278011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278011).length < 2 ^ (prefixWord ++ tailWord_6278011).sum := by decide
  have hdescent : baseEnd_6278011 < baseStart_6278011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278045 : List Nat := [1, 4, 2, 1, 2, 1, 1, 6, 1, 2, 2]
def baseStart_6278045 : Nat := 118140960795 + 6278045 * 2 ^ 59
def prefixEnd_6278045 : Nat := 4983230072969 + 3 ^ 40 * 6278045 * 2
def baseEnd_6278045 : Nat := 3223654655555994853765303

theorem tailTrace_6278045 : CollatzResearch.WordTrace tailWord_6278045 prefixEnd_6278045 3223654655555994853765303 := by
  unfold tailWord_6278045
  simp only [CollatzResearch.WordTrace]
  refine ⟨228979112540722644568531589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152652741693815096379021059 228979112540722644568531589)
  ·
    refine ⟨42933583601385495856599673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228979112540722644568531589 42933583601385495856599673)
    ·
      refine ⟨32200187701039121892449755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42933583601385495856599673 32200187701039121892449755)
      ·
        refine ⟨48300281551558682838674633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32200187701039121892449755 48300281551558682838674633)
        ·
          refine ⟨36225211163669012129005975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48300281551558682838674633 36225211163669012129005975)
          ·
            refine ⟨54337816745503518193508963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36225211163669012129005975 54337816745503518193508963)
            ·
              refine ⟨81506725118255277290263445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54337816745503518193508963 81506725118255277290263445)
              ·
                refine ⟨3820627739918216122981099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81506725118255277290263445 3820627739918216122981099)
                ·
                  refine ⟨5730941609877324184471649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820627739918216122981099 5730941609877324184471649)
                  ·
                    refine ⟨4298206207407993138353737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5730941609877324184471649 4298206207407993138353737)
                    ·
                      refine ⟨3223654655555994853765303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4298206207407993138353737 3223654655555994853765303)
                      ·
                        rfl

theorem cell23_6278045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_6278045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278045 prefixEnd_6278045 := by exact prefixLift 6278045
  have htrace : WordTrace (prefixWord ++ tailWord_6278045) baseStart_6278045 baseEnd_6278045 := by
    simpa [prefixWord, tailWord_6278045, baseEnd_6278045] using wordTrace_append hprefix tailTrace_6278045
  have hstable : (prefixWord ++ tailWord_6278045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278045).length < 2 ^ (prefixWord ++ tailWord_6278045).sum := by decide
  have hdescent : baseEnd_6278045 < baseStart_6278045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278055 : List Nat := [1, 1, 6, 1, 3, 1, 3, 1, 2, 4]
def baseStart_6278055 : Nat := 118140960795 + 6278055 * 2 ^ 59
def prefixEnd_6278055 : Nat := 4983230072969 + 3 ^ 40 * 6278055 * 2
def baseEnd_6278055 : Nat := 1074553263454179938213419

theorem tailTrace_6278055 : CollatzResearch.WordTrace tailWord_6278055 prefixEnd_6278055 1074553263454179938213419 := by
  unfold tailWord_6278055
  simp only [CollatzResearch.WordTrace]
  refine ⟨228979477270686416276395619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152652984847124277517597079 228979477270686416276395619)
  ·
    refine ⟨343469215906029624414593429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228979477270686416276395619 343469215906029624414593429)
    ·
      refine ⟨16100119495595138644434067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 343469215906029624414593429 16100119495595138644434067)
      ·
        refine ⟨24150179243392707966651101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16100119495595138644434067 24150179243392707966651101)
        ·
          refine ⟨9056317216272265487494163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24150179243392707966651101 9056317216272265487494163)
          ·
            refine ⟨13584475824408398231241245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9056317216272265487494163 13584475824408398231241245)
            ·
              refine ⟨5094178434153149336715467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13584475824408398231241245 5094178434153149336715467)
              ·
                refine ⟨7641267651229724005073201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5094178434153149336715467 7641267651229724005073201)
                ·
                  refine ⟨5730950738422293003804901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7641267651229724005073201 5730950738422293003804901)
                  ·
                    refine ⟨1074553263454179938213419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5730950738422293003804901 1074553263454179938213419)
                    ·
                      rfl

theorem cell23_6278055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_6278055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278055 prefixEnd_6278055 := by exact prefixLift 6278055
  have htrace : WordTrace (prefixWord ++ tailWord_6278055) baseStart_6278055 baseEnd_6278055 := by
    simpa [prefixWord, tailWord_6278055, baseEnd_6278055] using wordTrace_append hprefix tailTrace_6278055
  have hstable : (prefixWord ++ tailWord_6278055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278055).length < 2 ^ (prefixWord ++ tailWord_6278055).sum := by decide
  have hdescent : baseEnd_6278055 < baseStart_6278055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278067 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 8]
def baseStart_6278067 : Nat := 118140960795 + 6278067 * 2 ^ 59
def prefixEnd_6278067 : Nat := 4983230072969 + 3 ^ 40 * 6278067 * 2
def baseEnd_6278067 : Nat := 3223665952130393767690201

theorem tailTrace_6278067 : CollatzResearch.WordTrace tailWord_6278067 prefixEnd_6278067 3223665952130393767690201 := by
  unfold tailWord_6278067
  simp only [CollatzResearch.WordTrace]
  refine ⟨228979914946642942325832455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152653276631095294883888303 228979914946642942325832455)
  ·
    refine ⟨343469872419964413488748683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228979914946642942325832455 343469872419964413488748683)
    ·
      refine ⟨515204808629946620233123025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343469872419964413488748683 515204808629946620233123025)
      ·
        refine ⟨386403606472459965174842269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515204808629946620233123025 386403606472459965174842269)
        ·
          refine ⟨144901352427172486940565851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386403606472459965174842269 144901352427172486940565851)
          ·
            refine ⟨217352028640758730410848777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144901352427172486940565851 217352028640758730410848777)
            ·
              refine ⟨163014021480569047808136583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217352028640758730410848777 163014021480569047808136583)
              ·
                refine ⟨244521032220853571712204875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163014021480569047808136583 244521032220853571712204875)
                ·
                  refine ⟨366781548331280357568307313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244521032220853571712204875 366781548331280357568307313)
                  ·
                    refine ⟨275086161248460268176230485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 366781548331280357568307313 275086161248460268176230485)
                    ·
                      refine ⟨3223665952130393767690201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 275086161248460268176230485 3223665952130393767690201)
                      ·
                        rfl

theorem cell23_6278067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_6278067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278067 prefixEnd_6278067 := by exact prefixLift 6278067
  have htrace : WordTrace (prefixWord ++ tailWord_6278067) baseStart_6278067 baseEnd_6278067 := by
    simpa [prefixWord, tailWord_6278067, baseEnd_6278067] using wordTrace_append hprefix tailTrace_6278067
  have hstable : (prefixWord ++ tailWord_6278067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278067).length < 2 ^ (prefixWord ++ tailWord_6278067).sum := by decide
  have hdescent : baseEnd_6278067 < baseStart_6278067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278068 : List Nat := [2, 5, 2, 1, 1, 1, 4, 7]
def baseStart_6278068 : Nat := 118140960795 + 6278068 * 2 ^ 59
def prefixEnd_6278068 : Nat := 4983230072969 + 3 ^ 40 * 6278068 * 2
def baseEnd_6278068 : Nat := 119395054281890676436211

theorem tailTrace_6278068 : CollatzResearch.WordTrace tailWord_6278068 prefixEnd_6278068 119395054281890676436211 := by
  unfold tailWord_6278068
  simp only [CollatzResearch.WordTrace]
  refine ⟨114489975709819659748309429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152653300946426212997745905 114489975709819659748309429)
  ·
    refine ⟨10733435222795593101404009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114489975709819659748309429 10733435222795593101404009)
    ·
      refine ⟨8050076417096694826053007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10733435222795593101404009 8050076417096694826053007)
      ·
        refine ⟨12075114625645042239079511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8050076417096694826053007 12075114625645042239079511)
        ·
          refine ⟨18112671938467563358619267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12075114625645042239079511 18112671938467563358619267)
          ·
            refine ⟨27169007907701345037928901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18112671938467563358619267 27169007907701345037928901)
            ·
              refine ⟨5094188982694002194611669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27169007907701345037928901 5094188982694002194611669)
              ·
                refine ⟨119395054281890676436211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5094188982694002194611669 119395054281890676436211)
                ·
                  rfl

theorem cell23_6278068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 7].length) (baseStart_6278068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278068 prefixEnd_6278068 := by exact prefixLift 6278068
  have htrace : WordTrace (prefixWord ++ tailWord_6278068) baseStart_6278068 baseEnd_6278068 := by
    simpa [prefixWord, tailWord_6278068, baseEnd_6278068] using wordTrace_append hprefix tailTrace_6278068
  have hstable : (prefixWord ++ tailWord_6278068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278068).length < 2 ^ (prefixWord ++ tailWord_6278068).sum := by decide
  have hdescent : baseEnd_6278068 < baseStart_6278068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278071 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 3, 3, 2]
def baseStart_6278071 : Nat := 118140960795 + 6278071 * 2 ^ 59
def prefixEnd_6278071 : Nat := 4983230072969 + 3 ^ 40 * 6278071 * 2
def baseEnd_6278071 : Nat := 3223668006053011752040183

theorem tailTrace_6278071 : CollatzResearch.WordTrace tailWord_6278071 prefixEnd_6278071 3223668006053011752040183 := by
  unfold tailWord_6278071
  simp only [CollatzResearch.WordTrace]
  refine ⟨228980060838628451008978067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152653373892418967339318711 228980060838628451008978067)
  ·
    refine ⟨343470091257942676513467101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228980060838628451008978067 343470091257942676513467101)
    ·
      refine ⟨128801284221728503692550163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343470091257942676513467101 128801284221728503692550163)
      ·
        refine ⟨193201926332592755538825245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128801284221728503692550163 193201926332592755538825245)
        ·
          refine ⟨72450722374722283327059467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193201926332592755538825245 72450722374722283327059467)
          ·
            refine ⟨108676083562083424990589201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72450722374722283327059467 108676083562083424990589201)
            ·
              refine ⟨81507062671562568742941901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108676083562083424990589201 81507062671562568742941901)
              ·
                refine ⟨30565148501835963278603213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81507062671562568742941901 30565148501835963278603213)
                ·
                  refine ⟨11461930688188486229476205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30565148501835963278603213 11461930688188486229476205)
                  ·
                    refine ⟨4298224008070682336053577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11461930688188486229476205 4298224008070682336053577)
                    ·
                      refine ⟨3223668006053011752040183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4298224008070682336053577 3223668006053011752040183)
                      ·
                        rfl

theorem cell23_6278071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 3, 2].length) (baseStart_6278071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278071 prefixEnd_6278071 := by exact prefixLift 6278071
  have htrace : WordTrace (prefixWord ++ tailWord_6278071) baseStart_6278071 baseEnd_6278071 := by
    simpa [prefixWord, tailWord_6278071, baseEnd_6278071] using wordTrace_append hprefix tailTrace_6278071
  have hstable : (prefixWord ++ tailWord_6278071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278071).length < 2 ^ (prefixWord ++ tailWord_6278071).sum := by decide
  have hdescent : baseEnd_6278071 < baseStart_6278071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278141 : List Nat := [1, 4, 1, 1, 1, 2, 1, 7, 5]
def baseStart_6278141 : Nat := 118140960795 + 6278141 * 2 ^ 59
def prefixEnd_6278141 : Nat := 4983230072969 + 3 ^ 40 * 6278141 * 2
def baseEnd_6278141 : Nat := 358189327744314053129429

theorem tailTrace_6278141 : CollatzResearch.WordTrace tailWord_6278141 prefixEnd_6278141 358189327744314053129429 := by
  unfold tailWord_6278141
  simp only [CollatzResearch.WordTrace]
  refine ⟨228982613948374852964026277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152655075965583235309350851 228982613948374852964026277)
  ·
    refine ⟨42934240115320284930754927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228982613948374852964026277 42934240115320284930754927)
    ·
      refine ⟨64401360172980427396132391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42934240115320284930754927 64401360172980427396132391)
      ·
        refine ⟨96602040259470641094198587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64401360172980427396132391 96602040259470641094198587)
        ·
          refine ⟨144903060389205961641297881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96602040259470641094198587 144903060389205961641297881)
          ·
            refine ⟨108677295291904471230973411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144903060389205961641297881 108677295291904471230973411)
            ·
              refine ⟨163015942937856706846460117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108677295291904471230973411 163015942937856706846460117)
              ·
                refine ⟨3820686162606016566713909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 163015942937856706846460117 3820686162606016566713909)
                ·
                  refine ⟨358189327744314053129429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3820686162606016566713909 358189327744314053129429)
                  ·
                    rfl

theorem cell23_6278141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_6278141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278141 prefixEnd_6278141 := by exact prefixLift 6278141
  have htrace : WordTrace (prefixWord ++ tailWord_6278141) baseStart_6278141 baseEnd_6278141 := by
    simpa [prefixWord, tailWord_6278141, baseEnd_6278141] using wordTrace_append hprefix tailTrace_6278141
  have hstable : (prefixWord ++ tailWord_6278141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278141).length < 2 ^ (prefixWord ++ tailWord_6278141).sum := by decide
  have hdescent : baseEnd_6278141 < baseStart_6278141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278151 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 3]
def baseStart_6278151 : Nat := 118140960795 + 6278151 * 2 ^ 59
def prefixEnd_6278151 : Nat := 4983230072969 + 3 ^ 40 * 6278151 * 2
def baseEnd_6278151 : Nat := 3223709084505371439039815

theorem tailTrace_6278151 : CollatzResearch.WordTrace tailWord_6278151 prefixEnd_6278151 3223709084505371439039815 := by
  unfold tailWord_6278151
  simp only [CollatzResearch.WordTrace]
  refine ⟨228982978678338624671890307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152655319118892416447926871 228982978678338624671890307)
  ·
    refine ⟨343474468017507937007835461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228982978678338624671890307 343474468017507937007835461)
    ·
      refine ⟨64401462753282738188969149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 343474468017507937007835461 64401462753282738188969149)
      ·
        refine ⟨24150548532481026820863431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64401462753282738188969149 24150548532481026820863431)
        ·
          refine ⟨36225822798721540231295147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24150548532481026820863431 36225822798721540231295147)
          ·
            refine ⟨54338734198082310346942721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36225822798721540231295147 54338734198082310346942721)
            ·
              refine ⟨40754050648561732760207041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54338734198082310346942721 40754050648561732760207041)
              ·
                refine ⟨30565537986421299570155281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40754050648561732760207041 30565537986421299570155281)
                ·
                  refine ⟨22924153489815974677616461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30565537986421299570155281 22924153489815974677616461)
                  ·
                    refine ⟨8596557558680990504106173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22924153489815974677616461 8596557558680990504106173)
                    ·
                      refine ⟨3223709084505371439039815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8596557558680990504106173 3223709084505371439039815)
                      ·
                        rfl

theorem cell23_6278151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_6278151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278151 prefixEnd_6278151 := by exact prefixLift 6278151
  have htrace : WordTrace (prefixWord ++ tailWord_6278151) baseStart_6278151 baseEnd_6278151 := by
    simpa [prefixWord, tailWord_6278151, baseEnd_6278151] using wordTrace_append hprefix tailTrace_6278151
  have hstable : (prefixWord ++ tailWord_6278151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278151).length < 2 ^ (prefixWord ++ tailWord_6278151).sum := by decide
  have hdescent : baseEnd_6278151 < baseStart_6278151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278158 : List Nat := [4, 1, 1, 2, 2, 3, 1, 4, 5]
def baseStart_6278158 : Nat := 118140960795 + 6278158 * 2 ^ 59
def prefixEnd_6278158 : Nat := 4983230072969 + 3 ^ 40 * 6278158 * 2
def baseEnd_6278158 : Nat := 358190297652216990183587

theorem tailTrace_6278158 : CollatzResearch.WordTrace tailWord_6278158 prefixEnd_6278158 358190297652216990183587 := by
  unfold tailWord_6278158
  simp only [CollatzResearch.WordTrace]
  refine ⟨28622904248664158108424391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152655489326208843244930085 28622904248664158108424391)
  ·
    refine ⟨42934356372996237162636587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28622904248664158108424391 42934356372996237162636587)
    ·
      refine ⟨64401534559494355743954881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42934356372996237162636587 64401534559494355743954881)
      ·
        refine ⟨48301150919620766807966161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64401534559494355743954881 48301150919620766807966161)
        ·
          refine ⟨36225863189715575105974621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48301150919620766807966161 36225863189715575105974621)
          ·
            refine ⟨13584698696143340664740483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36225863189715575105974621 13584698696143340664740483)
            ·
              refine ⟨20377048044215010997110725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13584698696143340664740483 20377048044215010997110725)
              ·
                refine ⟨3820696508290314561958261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20377048044215010997110725 3820696508290314561958261)
                ·
                  refine ⟨358190297652216990183587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3820696508290314561958261 358190297652216990183587)
                  ·
                    rfl

theorem cell23_6278158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_6278158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278158 prefixEnd_6278158 := by exact prefixLift 6278158
  have htrace : WordTrace (prefixWord ++ tailWord_6278158) baseStart_6278158 baseEnd_6278158 := by
    simpa [prefixWord, tailWord_6278158, baseEnd_6278158] using wordTrace_append hprefix tailTrace_6278158
  have hstable : (prefixWord ++ tailWord_6278158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278158).length < 2 ^ (prefixWord ++ tailWord_6278158).sum := by decide
  have hdescent : baseEnd_6278158 < baseStart_6278158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278211 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 3]
def baseStart_6278211 : Nat := 118140960795 + 6278211 * 2 ^ 59
def prefixEnd_6278211 : Nat := 4983230072969 + 3 ^ 40 * 6278211 * 2
def baseEnd_6278211 : Nat := 3223739893344641204289539

theorem tailTrace_6278211 : CollatzResearch.WordTrace tailWord_6278211 prefixEnd_6278211 3223739893344641204289539 := by
  unfold tailWord_6278211
  simp only [CollatzResearch.WordTrace]
  refine ⟨228985167058121254919074487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152656778038747503279382991 228985167058121254919074487)
  ·
    refine ⟨343477750587181882378611731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228985167058121254919074487 343477750587181882378611731)
    ·
      refine ⟨515216625880772823567917597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343477750587181882378611731 515216625880772823567917597)
      ·
        refine ⟨193206234705289808837969099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 515216625880772823567917597 193206234705289808837969099)
        ·
          refine ⟨289809352057934713256953649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193206234705289808837969099 289809352057934713256953649)
          ·
            refine ⟨217357014043451034942715237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289809352057934713256953649 217357014043451034942715237)
            ·
              refine ⟨40754440133147069051759107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217357014043451034942715237 40754440133147069051759107)
              ·
                refine ⟨61131660199720603577638661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40754440133147069051759107 61131660199720603577638661)
                ·
                  refine ⟨11462186287447613170807249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61131660199720603577638661 11462186287447613170807249)
                  ·
                    refine ⟨8596639715585709878105437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11462186287447613170807249 8596639715585709878105437)
                    ·
                      refine ⟨3223739893344641204289539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8596639715585709878105437 3223739893344641204289539)
                      ·
                        rfl

theorem cell23_6278211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_6278211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278211 prefixEnd_6278211 := by exact prefixLift 6278211
  have htrace : WordTrace (prefixWord ++ tailWord_6278211) baseStart_6278211 baseEnd_6278211 := by
    simpa [prefixWord, tailWord_6278211, baseEnd_6278211] using wordTrace_append hprefix tailTrace_6278211
  have hstable : (prefixWord ++ tailWord_6278211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278211).length < 2 ^ (prefixWord ++ tailWord_6278211).sum := by decide
  have hdescent : baseEnd_6278211 < baseStart_6278211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278295 : List Nat := [1, 1, 3, 3, 3, 3, 1, 2, 1, 5]
def baseStart_6278295 : Nat := 118140960795 + 6278295 * 2 ^ 59
def prefixEnd_6278295 : Nat := 4983230072969 + 3 ^ 40 * 6278295 * 2
def baseEnd_6278295 : Nat := 1074594341906539625213051

theorem tailTrace_6278295 : CollatzResearch.WordTrace tailWord_6278295 prefixEnd_6278295 1074594341906539625213051 := by
  unfold tailWord_6278295
  simp only [CollatzResearch.WordTrace]
  refine ⟨228988230789816937265132339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152658820526544624843421559 228988230789816937265132339)
  ·
    refine ⟨343482346184725405897698509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228988230789816937265132339 343482346184725405897698509)
    ·
      refine ⟨128805879819272027211636941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343482346184725405897698509 128805879819272027211636941)
      ·
        refine ⟨48302204932227010204363853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128805879819272027211636941 48302204932227010204363853)
        ·
          refine ⟨18113326849585128826636445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48302204932227010204363853 18113326849585128826636445)
          ·
            refine ⟨6792497568594423309988667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18113326849585128826636445 6792497568594423309988667)
            ·
              refine ⟨10188746352891634964983001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6792497568594423309988667 10188746352891634964983001)
              ·
                refine ⟨7641559764668726223737251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10188746352891634964983001 7641559764668726223737251)
                ·
                  refine ⟨11462339647003089335605877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7641559764668726223737251 11462339647003089335605877)
                  ·
                    refine ⟨1074594341906539625213051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11462339647003089335605877 1074594341906539625213051)
                    ·
                      rfl

theorem cell23_6278295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_6278295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278295 prefixEnd_6278295 := by exact prefixLift 6278295
  have htrace : WordTrace (prefixWord ++ tailWord_6278295) baseStart_6278295 baseEnd_6278295 := by
    simpa [prefixWord, tailWord_6278295, baseEnd_6278295] using wordTrace_append hprefix tailTrace_6278295
  have hstable : (prefixWord ++ tailWord_6278295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278295).length < 2 ^ (prefixWord ++ tailWord_6278295).sum := by decide
  have hdescent : baseEnd_6278295 < baseStart_6278295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278302 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_6278302 : Nat := 118140960795 + 6278302 * 2 ^ 59
def prefixEnd_6278302 : Nat := 4983230072969 + 3 ^ 40 * 6278302 * 2
def baseEnd_6278302 : Nat := 3223786620084200348251621

theorem tailTrace_6278302 : CollatzResearch.WordTrace tailWord_6278302 prefixEnd_6278302 3223786620084200348251621 := by
  unfold tailWord_6278302
  simp only [CollatzResearch.WordTrace]
  refine ⟨28623560762598947182579645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152658990733861051640424773 28623560762598947182579645)
  ·
    refine ⟨10733835285974605193467367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28623560762598947182579645 10733835285974605193467367)
    ·
      refine ⟨16100752928961907790201051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10733835285974605193467367 16100752928961907790201051)
      ·
        refine ⟨24151129393442861685301577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16100752928961907790201051 24151129393442861685301577)
        ·
          refine ⟨18113347045082146263976183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24151129393442861685301577 18113347045082146263976183)
          ·
            refine ⟨27170020567623219395964275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18113347045082146263976183 27170020567623219395964275)
            ·
              refine ⟨40755030851434829093946413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27170020567623219395964275 40755030851434829093946413)
              ·
                refine ⟨15283136569288060910229905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40755030851434829093946413 15283136569288060910229905)
                ·
                  refine ⟨11462352426966045682672429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15283136569288060910229905 11462352426966045682672429)
                  ·
                    refine ⟨4298382160112267131002161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11462352426966045682672429 4298382160112267131002161)
                    ·
                      refine ⟨3223786620084200348251621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4298382160112267131002161 3223786620084200348251621)
                      ·
                        rfl

theorem cell23_6278302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_6278302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278302 prefixEnd_6278302 := by exact prefixLift 6278302
  have htrace : WordTrace (prefixWord ++ tailWord_6278302) baseStart_6278302 baseEnd_6278302 := by
    simpa [prefixWord, tailWord_6278302, baseEnd_6278302] using wordTrace_append hprefix tailTrace_6278302
  have hstable : (prefixWord ++ tailWord_6278302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278302).length < 2 ^ (prefixWord ++ tailWord_6278302).sum := by decide
  have hdescent : baseEnd_6278302 < baseStart_6278302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278308 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 1, 6]
def baseStart_6278308 : Nat := 118140960795 + 6278308 * 2 ^ 59
def prefixEnd_6278308 : Nat := 4983230072969 + 3 ^ 40 * 6278308 * 2
def baseEnd_6278308 : Nat := 1074596566989375774925531

theorem tailTrace_6278308 : CollatzResearch.WordTrace tailWord_6278308 prefixEnd_6278308 1074596566989375774925531 := by
  unfold tailWord_6278308
  simp only [CollatzResearch.WordTrace]
  refine ⟨114494352469384920242677789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152659136625846560323570385 114494352469384920242677789)
  ·
    refine ⟨42935382176019345091004171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114494352469384920242677789 42935382176019345091004171)
    ·
      refine ⟨64403073264029017636506257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42935382176019345091004171 64403073264029017636506257)
      ·
        refine ⟨48302304948021763227379693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64403073264029017636506257 48302304948021763227379693)
        ·
          refine ⟨18113364355508161210267385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48302304948021763227379693 18113364355508161210267385)
          ·
            refine ⟨13585023266631120907700539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18113364355508161210267385 13585023266631120907700539)
            ·
              refine ⟨20377534899946681361550809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13585023266631120907700539 20377534899946681361550809)
              ·
                refine ⟨15283151174960011021163107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20377534899946681361550809 15283151174960011021163107)
                ·
                  refine ⟨22924726762440016531744661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15283151174960011021163107 22924726762440016531744661)
                  ·
                    refine ⟨1074596566989375774925531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22924726762440016531744661 1074596566989375774925531)
                    ·
                      rfl

theorem cell23_6278308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_6278308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278308 prefixEnd_6278308 := by exact prefixLift 6278308
  have htrace : WordTrace (prefixWord ++ tailWord_6278308) baseStart_6278308 baseEnd_6278308 := by
    simpa [prefixWord, tailWord_6278308, baseEnd_6278308] using wordTrace_append hprefix tailTrace_6278308
  have hstable : (prefixWord ++ tailWord_6278308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278308).length < 2 ^ (prefixWord ++ tailWord_6278308).sum := by decide
  have hdescent : baseEnd_6278308 < baseStart_6278308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278321 : List Nat := [1, 2, 2, 5, 1, 12]
def baseStart_6278321 : Nat := 118140960795 + 6278321 * 2 ^ 59
def prefixEnd_6278321 : Nat := 4983230072969 + 3 ^ 40 * 6278321 * 2
def baseEnd_6278321 : Nat := 13266651753977924995531

theorem tailTrace_6278321 : CollatzResearch.WordTrace tailWord_6278321 prefixEnd_6278321 13266651753977924995531 := by
  unfold tailWord_6278321
  simp only [CollatzResearch.WordTrace]
  refine ⟨228989179087722743705578817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152659452725148495803719211 228989179087722743705578817)
  ·
    refine ⟨171741884315792057779184113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228989179087722743705578817 171741884315792057779184113)
    ·
      refine ⟨128806413236844043334388085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171741884315792057779184113 128806413236844043334388085)
      ·
        refine ⟨12075601240954129062598883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128806413236844043334388085 12075601240954129062598883)
        ·
          refine ⟨18113401861431193593898325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12075601240954129062598883 18113401861431193593898325)
          ·
            refine ⟨13266651753977924995531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18113401861431193593898325 13266651753977924995531)
            ·
              rfl

theorem cell23_6278321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 12].length) (baseStart_6278321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278321 prefixEnd_6278321 := by exact prefixLift 6278321
  have htrace : WordTrace (prefixWord ++ tailWord_6278321) baseStart_6278321 baseEnd_6278321 := by
    simpa [prefixWord, tailWord_6278321, baseEnd_6278321] using wordTrace_append hprefix tailTrace_6278321
  have hstable : (prefixWord ++ tailWord_6278321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278321).length < 2 ^ (prefixWord ++ tailWord_6278321).sum := by decide
  have hdescent : baseEnd_6278321 < baseStart_6278321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278361 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 2, 2, 5]
def baseStart_6278361 : Nat := 118140960795 + 6278361 * 2 ^ 59
def prefixEnd_6278361 : Nat := 4983230072969 + 3 ^ 40 * 6278361 * 2
def baseEnd_6278361 : Nat := 3223816915442815617413849

theorem tailTrace_6278361 : CollatzResearch.WordTrace tailWord_6278361 prefixEnd_6278361 3223816915442815617413849 := by
  unfold tailWord_6278361
  simp only [CollatzResearch.WordTrace]
  refine ⟨228990638007577830537034937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152660425338385220358023291 228990638007577830537034937)
  ·
    refine ⟨171742978505683372902776203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228990638007577830537034937 171742978505683372902776203)
    ·
      refine ⟨257614467758525059354164305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171742978505683372902776203 257614467758525059354164305)
      ·
        refine ⟨193210850818893794515623229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257614467758525059354164305 193210850818893794515623229)
        ·
          refine ⟨72454069057085172943358711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193210850818893794515623229 72454069057085172943358711)
          ·
            refine ⟨108681103585627759415038067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72454069057085172943358711 108681103585627759415038067)
            ·
              refine ⟨163021655378441639122557101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108681103585627759415038067 163021655378441639122557101)
              ·
                refine ⟨61133120766915614670958913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163021655378441639122557101 61133120766915614670958913)
                ·
                  refine ⟨45849840575186711003219185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61133120766915614670958913 45849840575186711003219185)
                  ·
                    refine ⟨34387380431390033252414389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45849840575186711003219185 34387380431390033252414389)
                    ·
                      refine ⟨3223816915442815617413849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34387380431390033252414389 3223816915442815617413849)
                      ·
                        rfl

theorem cell23_6278361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_6278361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278361 prefixEnd_6278361 := by exact prefixLift 6278361
  have htrace : WordTrace (prefixWord ++ tailWord_6278361) baseStart_6278361 baseEnd_6278361 := by
    simpa [prefixWord, tailWord_6278361, baseEnd_6278361] using wordTrace_append hprefix tailTrace_6278361
  have hstable : (prefixWord ++ tailWord_6278361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278361).length < 2 ^ (prefixWord ++ tailWord_6278361).sum := by decide
  have hdescent : baseEnd_6278361 < baseStart_6278361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278382 : List Nat := [4, 1, 2, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_6278382 : Nat := 118140960795 + 6278382 * 2 ^ 59
def prefixEnd_6278382 : Nat := 4983230072969 + 3 ^ 40 * 6278382 * 2
def baseEnd_6278382 : Nat := 3223827698536560035251253

theorem tailTrace_6278382 : CollatzResearch.WordTrace tailWord_6278382 prefixEnd_6278382 3223827698536560035251253 := by
  unfold tailWord_6278382
  simp only [CollatzResearch.WordTrace]
  refine ⟨28623925492562718890443675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152660935960334500749032933 28623925492562718890443675)
  ·
    refine ⟨42935888238844078335665513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28623925492562718890443675 42935888238844078335665513)
    ·
      refine ⟨32201916179133058751749135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42935888238844078335665513 32201916179133058751749135)
      ·
        refine ⟨48302874268699588127623703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32201916179133058751749135 48302874268699588127623703)
        ·
          refine ⟨72454311403049382191435555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48302874268699588127623703 72454311403049382191435555)
          ·
            refine ⟨108681467104574073287153333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72454311403049382191435555 108681467104574073287153333)
            ·
              refine ⟨10188887541053819370670625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108681467104574073287153333 10188887541053819370670625)
              ·
                refine ⟨7641665655790364528002969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10188887541053819370670625 7641665655790364528002969)
                ·
                  refine ⟨5731249241842773396002227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7641665655790364528002969 5731249241842773396002227)
                  ·
                    refine ⟨8596873862764160094003341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5731249241842773396002227 8596873862764160094003341)
                    ·
                      refine ⟨3223827698536560035251253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8596873862764160094003341 3223827698536560035251253)
                      ·
                        rfl

theorem cell23_6278382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_6278382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278382 prefixEnd_6278382 := by exact prefixLift 6278382
  have htrace : WordTrace (prefixWord ++ tailWord_6278382) baseStart_6278382 baseEnd_6278382 := by
    simpa [prefixWord, tailWord_6278382, baseEnd_6278382] using wordTrace_append hprefix tailTrace_6278382
  have hstable : (prefixWord ++ tailWord_6278382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278382).length < 2 ^ (prefixWord ++ tailWord_6278382).sum := by decide
  have hdescent : baseEnd_6278382 < baseStart_6278382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278391 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 5]
def baseStart_6278391 : Nat := 118140960795 + 6278391 * 2 ^ 59
def prefixEnd_6278391 : Nat := 4983230072969 + 3 ^ 40 * 6278391 * 2
def baseEnd_6278391 : Nat := 3223832319862450500038711

theorem tailTrace_6278391 : CollatzResearch.WordTrace tailWord_6278391 prefixEnd_6278391 3223832319862450500038711 := by
  unfold tailWord_6278391
  simp only [CollatzResearch.WordTrace]
  refine ⟨228991732197469145660627027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152661154798312763773751351 228991732197469145660627027)
  ·
    refine ⟨343487598296203718490940541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228991732197469145660627027 343487598296203718490940541)
    ·
      refine ⟨128807849361076394434102703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343487598296203718490940541 128807849361076394434102703)
      ·
        refine ⟨193211774041614591651154055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128807849361076394434102703 193211774041614591651154055)
        ·
          refine ⟨289817661062421887476731083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193211774041614591651154055 289817661062421887476731083)
          ·
            refine ⟨434726491593632831215096625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289817661062421887476731083 434726491593632831215096625)
            ·
              refine ⟨326044868695224623411322469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434726491593632831215096625 326044868695224623411322469)
              ·
                refine ⟨61133412880354616889622963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326044868695224623411322469 61133412880354616889622963)
                ·
                  refine ⟨91700119320531925334434445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61133412880354616889622963 91700119320531925334434445)
                  ·
                    refine ⟨34387544745199472000412917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91700119320531925334434445 34387544745199472000412917)
                    ·
                      refine ⟨3223832319862450500038711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34387544745199472000412917 3223832319862450500038711)
                      ·
                        rfl

theorem cell23_6278391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_6278391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278391 prefixEnd_6278391 := by exact prefixLift 6278391
  have htrace : WordTrace (prefixWord ++ tailWord_6278391) baseStart_6278391 baseEnd_6278391 := by
    simpa [prefixWord, tailWord_6278391, baseEnd_6278391] using wordTrace_append hprefix tailTrace_6278391
  have hstable : (prefixWord ++ tailWord_6278391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278391).length < 2 ^ (prefixWord ++ tailWord_6278391).sum := by decide
  have hdescent : baseEnd_6278391 < baseStart_6278391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278458 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 4, 5]
def baseStart_6278458 : Nat := 118140960795 + 6278458 * 2 ^ 59
def prefixEnd_6278458 : Nat := 4983230072969 + 3 ^ 40 * 6278458 * 2
def baseEnd_6278458 : Nat := 1074622241022100579300301

theorem tailTrace_6278458 : CollatzResearch.WordTrace tailWord_6278458 prefixEnd_6278458 1074622241022100579300301 := by
  unfold tailWord_6278458
  simp only [CollatzResearch.WordTrace]
  refine ⟨57248543972056604025829007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152662783925484277402210685 57248543972056604025829007)
  ·
    refine ⟨85872815958084906038743511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57248543972056604025829007 85872815958084906038743511)
    ·
      refine ⟨128809223937127359058115267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85872815958084906038743511 128809223937127359058115267)
      ·
        refine ⟨193213835905691038587172901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128809223937127359058115267 193213835905691038587172901)
        ·
          refine ⟨36227594232317069735094919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193213835905691038587172901 36227594232317069735094919)
          ·
            refine ⟨54341391348475604602642379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36227594232317069735094919 54341391348475604602642379)
            ·
              refine ⟨81512087022713406903963569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54341391348475604602642379 81512087022713406903963569)
              ·
                refine ⟨61134065267035055177972677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81512087022713406903963569 61134065267035055177972677)
                ·
                  refine ⟨11462637237569072845869877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61134065267035055177972677 11462637237569072845869877)
                  ·
                    refine ⟨1074622241022100579300301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11462637237569072845869877 1074622241022100579300301)
                    ·
                      rfl

theorem cell23_6278458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_6278458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278458 prefixEnd_6278458 := by exact prefixLift 6278458
  have htrace : WordTrace (prefixWord ++ tailWord_6278458) baseStart_6278458 baseEnd_6278458 := by
    simpa [prefixWord, tailWord_6278458, baseEnd_6278458] using wordTrace_append hprefix tailTrace_6278458
  have hstable : (prefixWord ++ tailWord_6278458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278458).length < 2 ^ (prefixWord ++ tailWord_6278458).sum := by decide
  have hdescent : baseEnd_6278458 < baseStart_6278458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278495 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 2, 4, 2]
def baseStart_6278495 : Nat := 118140960795 + 6278495 * 2 ^ 59
def prefixEnd_6278495 : Nat := 4983230072969 + 3 ^ 40 * 6278495 * 2
def baseEnd_6278495 : Nat := 3223885721850518093138233

theorem tailTrace_6278495 : CollatzResearch.WordTrace tailWord_6278495 prefixEnd_6278495 3223885721850518093138233 := by
  unfold tailWord_6278495
  simp only [CollatzResearch.WordTrace]
  refine ⟨228995525389092371422412939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152663683592728247614941959 228995525389092371422412939)
  ·
    refine ⟨343493288083638557133619409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228995525389092371422412939 343493288083638557133619409)
    ·
      refine ⟨257619966062728917850214557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343493288083638557133619409 257619966062728917850214557)
      ·
        refine ⟨96607487273523344193830459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257619966062728917850214557 96607487273523344193830459)
        ·
          refine ⟨144911230910285016290745689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96607487273523344193830459 144911230910285016290745689)
          ·
            refine ⟨108683423182713762218059267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144911230910285016290745689 108683423182713762218059267)
            ·
              refine ⟨163025134774070643327088901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108683423182713762218059267 163025134774070643327088901)
              ·
                refine ⟨30567212770138245623829169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163025134774070643327088901 30567212770138245623829169)
                ·
                  refine ⟨22925409577603684217871877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30567212770138245623829169 22925409577603684217871877)
                  ·
                    refine ⟨4298514295800690790850977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22925409577603684217871877 4298514295800690790850977)
                    ·
                      refine ⟨3223885721850518093138233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4298514295800690790850977 3223885721850518093138233)
                      ·
                        rfl

theorem cell23_6278495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_6278495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278495 prefixEnd_6278495 := by exact prefixLift 6278495
  have htrace : WordTrace (prefixWord ++ tailWord_6278495) baseStart_6278495 baseEnd_6278495 := by
    simpa [prefixWord, tailWord_6278495, baseEnd_6278495] using wordTrace_append hprefix tailTrace_6278495
  have hstable : (prefixWord ++ tailWord_6278495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278495).length < 2 ^ (prefixWord ++ tailWord_6278495).sum := by decide
  have hdescent : baseEnd_6278495 < baseStart_6278495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278526 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_6278526 : Nat := 118140960795 + 6278526 * 2 ^ 59
def prefixEnd_6278526 : Nat := 4983230072969 + 3 ^ 40 * 6278526 * 2
def baseEnd_6278526 : Nat := 1074633879916935823950197

theorem tailTrace_6278526 : CollatzResearch.WordTrace tailWord_6278526 prefixEnd_6278526 1074633879916935823950197 := by
  unfold tailWord_6278526
  simp only [CollatzResearch.WordTrace]
  refine ⟨28624582006497507964598929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152664437367986709144527621 28624582006497507964598929)
  ·
    refine ⟨21468436504873130973449197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28624582006497507964598929 21468436504873130973449197)
    ·
      refine ⟨8050663689327424115043449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21468436504873130973449197 8050663689327424115043449)
      ·
        refine ⟨6037997766995568086282587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8050663689327424115043449 6037997766995568086282587)
        ·
          refine ⟨9056996650493352129423881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6037997766995568086282587 9056996650493352129423881)
          ·
            refine ⟨6792747487870014097067911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9056996650493352129423881 6792747487870014097067911)
            ·
              refine ⟨10189121231805021145601867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6792747487870014097067911 10189121231805021145601867)
              ·
                refine ⟨15283681847707531718402801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10189121231805021145601867 15283681847707531718402801)
                ·
                  refine ⟨11462761385780648788802101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15283681847707531718402801 11462761385780648788802101)
                  ·
                    refine ⟨1074633879916935823950197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11462761385780648788802101 1074633879916935823950197)
                    ·
                      rfl

theorem cell23_6278526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_6278526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278526 prefixEnd_6278526 := by exact prefixLift 6278526
  have htrace : WordTrace (prefixWord ++ tailWord_6278526) baseStart_6278526 baseEnd_6278526 := by
    simpa [prefixWord, tailWord_6278526, baseEnd_6278526] using wordTrace_append hprefix tailTrace_6278526
  have hstable : (prefixWord ++ tailWord_6278526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278526).length < 2 ^ (prefixWord ++ tailWord_6278526).sum := by decide
  have hdescent : baseEnd_6278526 < baseStart_6278526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278529 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_6278529 : Nat := 118140960795 + 6278529 * 2 ^ 59
def prefixEnd_6278529 : Nat := 4983230072969 + 3 ^ 40 * 6278529 * 2
def baseEnd_6278529 : Nat := 3223903180192770960113077

theorem tailTrace_6278529 : CollatzResearch.WordTrace tailWord_6278529 prefixEnd_6278529 3223903180192770960113077 := by
  unfold tailWord_6278529
  simp only [CollatzResearch.WordTrace]
  refine ⟨228996765470969195229150641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152664510313979463486100427 228996765470969195229150641)
  ·
    refine ⟨171747574103226896421862981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228996765470969195229150641 171747574103226896421862981)
    ·
      refine ⟨32202670144355043079099309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171747574103226896421862981 32202670144355043079099309)
      ·
        refine ⟨12076001304133141154662241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32202670144355043079099309 12076001304133141154662241)
        ·
          refine ⟨9057000978099855865996681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12076001304133141154662241 9057000978099855865996681)
          ·
            refine ⟨6792750733574891899497511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9057000978099855865996681 6792750733574891899497511)
            ·
              refine ⟨10189126100362337849246267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6792750733574891899497511 10189126100362337849246267)
              ·
                refine ⟨15283689150543506773869401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10189126100362337849246267 15283689150543506773869401)
                ·
                  refine ⟨11462766862907630080402051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15283689150543506773869401 11462766862907630080402051)
                  ·
                    refine ⟨17194150294361445120603077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11462766862907630080402051 17194150294361445120603077)
                    ·
                      refine ⟨3223903180192770960113077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17194150294361445120603077 3223903180192770960113077)
                      ·
                        rfl

theorem cell23_6278529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_6278529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278529 prefixEnd_6278529 := by exact prefixLift 6278529
  have htrace : WordTrace (prefixWord ++ tailWord_6278529) baseStart_6278529 baseEnd_6278529 := by
    simpa [prefixWord, tailWord_6278529, baseEnd_6278529] using wordTrace_append hprefix tailTrace_6278529
  have hstable : (prefixWord ++ tailWord_6278529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278529).length < 2 ^ (prefixWord ++ tailWord_6278529).sum := by decide
  have hdescent : baseEnd_6278529 < baseStart_6278529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278532 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_6278532 : Nat := 118140960795 + 6278532 * 2 ^ 59
def prefixEnd_6278532 : Nat := 4983230072969 + 3 ^ 40 * 6278532 * 2
def baseEnd_6278532 : Nat := 3223904720634734448375563

theorem tailTrace_6278532 : CollatzResearch.WordTrace tailWord_6278532 prefixEnd_6278532 3223904720634734448375563 := by
  unfold tailWord_6278532
  simp only [CollatzResearch.WordTrace]
  refine ⟨114498437444979163370754925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152664583259972217827673233 114498437444979163370754925)
  ·
    refine ⟨42936914041867186264033097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114498437444979163370754925 42936914041867186264033097)
    ·
      refine ⟨32202685531400389698024823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42936914041867186264033097 32202685531400389698024823)
      ·
        refine ⟨48304028297100584547037235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32202685531400389698024823 48304028297100584547037235)
        ·
          refine ⟨72456042445650876820555853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48304028297100584547037235 72456042445650876820555853)
          ·
            refine ⟨27171015917119078807708445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72456042445650876820555853 27171015917119078807708445)
            ·
              refine ⟨10189130968919654552890667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27171015917119078807708445 10189130968919654552890667)
              ·
                refine ⟨15283696453379481829336001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10189130968919654552890667 15283696453379481829336001)
                ·
                  refine ⟨11462772340034611372002001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15283696453379481829336001 11462772340034611372002001)
                  ·
                    refine ⟨8597079255025958529001501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11462772340034611372002001 8597079255025958529001501)
                    ·
                      refine ⟨3223904720634734448375563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8597079255025958529001501 3223904720634734448375563)
                      ·
                        rfl

theorem cell23_6278532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_6278532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278532 prefixEnd_6278532 := by exact prefixLift 6278532
  have htrace : WordTrace (prefixWord ++ tailWord_6278532) baseStart_6278532 baseEnd_6278532 := by
    simpa [prefixWord, tailWord_6278532, baseEnd_6278532] using wordTrace_append hprefix tailTrace_6278532
  have hstable : (prefixWord ++ tailWord_6278532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278532).length < 2 ^ (prefixWord ++ tailWord_6278532).sum := by decide
  have hdescent : baseEnd_6278532 < baseStart_6278532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278595 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 4, 4]
def baseStart_6278595 : Nat := 118140960795 + 6278595 * 2 ^ 59
def prefixEnd_6278595 : Nat := 4983230072969 + 3 ^ 40 * 6278595 * 2
def baseEnd_6278595 : Nat := 1074645689971989233962591

theorem tailTrace_6278595 : CollatzResearch.WordTrace tailWord_6278595 prefixEnd_6278595 1074645689971989233962591 := by
  unfold tailWord_6278595
  simp only [CollatzResearch.WordTrace]
  refine ⟨228999172688730088501053239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152666115125820059000702159 228999172688730088501053239)
  ·
    refine ⟨343498759033095132751579859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228999172688730088501053239 343498759033095132751579859)
    ·
      refine ⟨515248138549642699127369789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343498759033095132751579859 515248138549642699127369789)
      ·
        refine ⟨193218051956116012172763671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 515248138549642699127369789 193218051956116012172763671)
        ·
          refine ⟨289827077934174018259145507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193218051956116012172763671 289827077934174018259145507)
          ·
            refine ⟨434740616901261027388718261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289827077934174018259145507 434740616901261027388718261)
            ·
              refine ⟨40756932834493221317692337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 434740616901261027388718261 40756932834493221317692337)
              ·
                refine ⟨30567699625869915988269253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40756932834493221317692337 30567699625869915988269253)
                ·
                  refine ⟨5731443679850609247800485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30567699625869915988269253 5731443679850609247800485)
                  ·
                    refine ⟨1074645689971989233962591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5731443679850609247800485 1074645689971989233962591)
                    ·
                      rfl

theorem cell23_6278595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 4].length) (baseStart_6278595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278595 prefixEnd_6278595 := by exact prefixLift 6278595
  have htrace : WordTrace (prefixWord ++ tailWord_6278595) baseStart_6278595 baseEnd_6278595 := by
    simpa [prefixWord, tailWord_6278595, baseEnd_6278595] using wordTrace_append hprefix tailTrace_6278595
  have hstable : (prefixWord ++ tailWord_6278595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278595).length < 2 ^ (prefixWord ++ tailWord_6278595).sum := by decide
  have hdescent : baseEnd_6278595 < baseStart_6278595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278602 : List Nat := [3, 1, 2, 1, 2, 3, 2, 3, 1, 1, 4]
def baseStart_6278602 : Nat := 118140960795 + 6278602 * 2 ^ 59
def prefixEnd_6278602 : Nat := 4983230072969 + 3 ^ 40 * 6278602 * 2
def baseEnd_6278602 : Nat := 3223940664280549174500241

theorem tailTrace_6278602 : CollatzResearch.WordTrace tailWord_6278602 prefixEnd_6278602 3223940664280549174500241 := by
  unfold tailWord_6278602
  simp only [CollatzResearch.WordTrace]
  refine ⟨57249856999926182174139515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152666285333136485797705373 57249856999926182174139515)
  ·
    refine ⟨85874785499889273261209273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57249856999926182174139515 85874785499889273261209273)
    ·
      refine ⟨64406089124916954945906955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85874785499889273261209273 64406089124916954945906955)
      ·
        refine ⟨96609133687375432418860433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64406089124916954945906955 96609133687375432418860433)
        ·
          refine ⟨72456850265531574314145325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96609133687375432418860433 72456850265531574314145325)
          ·
            refine ⟨27171318849574340367804497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72456850265531574314145325 27171318849574340367804497)
            ·
              refine ⟨20378489137180755275853373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27171318849574340367804497 20378489137180755275853373)
              ·
                refine ⟨7641933426442783228445015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20378489137180755275853373 7641933426442783228445015)
                ·
                  refine ⟨11462900139664174842667523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7641933426442783228445015 11462900139664174842667523)
                  ·
                    refine ⟨17194350209496262264001285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11462900139664174842667523 17194350209496262264001285)
                    ·
                      refine ⟨3223940664280549174500241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17194350209496262264001285 3223940664280549174500241)
                      ·
                        rfl

theorem cell23_6278602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_6278602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278602 prefixEnd_6278602 := by exact prefixLift 6278602
  have htrace : WordTrace (prefixWord ++ tailWord_6278602) baseStart_6278602 baseEnd_6278602 := by
    simpa [prefixWord, tailWord_6278602, baseEnd_6278602] using wordTrace_append hprefix tailTrace_6278602
  have hstable : (prefixWord ++ tailWord_6278602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278602).length < 2 ^ (prefixWord ++ tailWord_6278602).sum := by decide
  have hdescent : baseEnd_6278602 < baseStart_6278602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278625 : List Nat := [1, 2, 3, 1, 2, 4, 2, 8]
def baseStart_6278625 : Nat := 118140960795 + 6278625 * 2 ^ 59
def prefixEnd_6278625 : Nat := 4983230072969 + 3 ^ 40 * 6278625 * 2
def baseEnd_6278625 : Nat := 119405647197614910537505

theorem tailTrace_6278625 : CollatzResearch.WordTrace tailWord_6278625 prefixEnd_6278625 119405647197614910537505 := by
  unfold tailWord_6278625
  simp only [CollatzResearch.WordTrace]
  refine ⟨229000266878621403624645329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152666844585747602416430219 229000266878621403624645329)
  ·
    refine ⟨171750200158966052718483997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229000266878621403624645329 171750200158966052718483997)
    ·
      refine ⟨64406325059612269769431499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171750200158966052718483997 64406325059612269769431499)
      ·
        refine ⟨96609487589418404654147249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64406325059612269769431499 96609487589418404654147249)
        ·
          refine ⟨72457115692063803490610437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96609487589418404654147249 72457115692063803490610437)
          ·
            refine ⟨13585709192261963154489457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72457115692063803490610437 13585709192261963154489457)
            ·
              refine ⟨10189281894196472365867093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13585709192261963154489457 10189281894196472365867093)
              ·
                refine ⟨119405647197614910537505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10189281894196472365867093 119405647197614910537505)
                ·
                  rfl

theorem cell23_6278625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 8].length) (baseStart_6278625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278625 prefixEnd_6278625 := by exact prefixLift 6278625
  have htrace : WordTrace (prefixWord ++ tailWord_6278625) baseStart_6278625 baseEnd_6278625 := by
    simpa [prefixWord, tailWord_6278625, baseEnd_6278625] using wordTrace_append hprefix tailTrace_6278625
  have hstable : (prefixWord ++ tailWord_6278625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278625).length < 2 ^ (prefixWord ++ tailWord_6278625).sum := by decide
  have hdescent : baseEnd_6278625 < baseStart_6278625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278629 : List Nat := [1, 3, 1, 5, 1, 2, 1, 3, 2, 4]
def baseStart_6278629 : Nat := 118140960795 + 6278629 * 2 ^ 59
def prefixEnd_6278629 : Nat := 4983230072969 + 3 ^ 40 * 6278629 * 2
def baseEnd_6278629 : Nat := 1074651509419406856287539

theorem tailTrace_6278629 : CollatzResearch.WordTrace tailWord_6278629 prefixEnd_6278629 1074651509419406856287539 := by
  unfold tailWord_6278629
  simp only [CollatzResearch.WordTrace]
  refine ⟨229000412770606912307790941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152666941847071274871860627 229000412770606912307790941)
  ·
    refine ⟨85875154788977592115421603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229000412770606912307790941 85875154788977592115421603)
    ·
      refine ⟨128812732183466388173132405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85875154788977592115421603 128812732183466388173132405)
      ·
        refine ⟨12076193642199973891231163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128812732183466388173132405 12076193642199973891231163)
        ·
          refine ⟨18114290463299960836846745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12076193642199973891231163 18114290463299960836846745)
          ·
            refine ⟨13585717847474970627635059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18114290463299960836846745 13585717847474970627635059)
            ·
              refine ⟨20378576771212455941452589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13585717847474970627635059 20378576771212455941452589)
              ·
                refine ⟨7641966289204670978044721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20378576771212455941452589 7641966289204670978044721)
                ·
                  refine ⟨5731474716903503233533541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7641966289204670978044721 5731474716903503233533541)
                  ·
                    refine ⟨1074651509419406856287539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5731474716903503233533541 1074651509419406856287539)
                    ·
                      rfl

theorem cell23_6278629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_6278629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278629 prefixEnd_6278629 := by exact prefixLift 6278629
  have htrace : WordTrace (prefixWord ++ tailWord_6278629) baseStart_6278629 baseEnd_6278629 := by
    simpa [prefixWord, tailWord_6278629, baseEnd_6278629] using wordTrace_append hprefix tailTrace_6278629
  have hstable : (prefixWord ++ tailWord_6278629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278629).length < 2 ^ (prefixWord ++ tailWord_6278629).sum := by decide
  have hdescent : baseEnd_6278629 < baseStart_6278629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278652 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 6, 1, 3]
def baseStart_6278652 : Nat := 118140960795 + 6278652 * 2 ^ 59
def prefixEnd_6278652 : Nat := 4983230072969 + 3 ^ 40 * 6278652 * 2
def baseEnd_6278652 : Nat := 3223966338313273978875011

theorem tailTrace_6278652 : CollatzResearch.WordTrace tailWord_6278652 prefixEnd_6278652 3223966338313273978875011 := by
  unfold tailWord_6278652
  simp only [CollatzResearch.WordTrace]
  refine ⟨114500625824761793617939105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152667501099682391490585473 114500625824761793617939105)
  ·
    refine ⟨85875469368571345213454329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114500625824761793617939105 85875469368571345213454329)
    ·
      refine ⟨64406602026428508910090747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85875469368571345213454329 64406602026428508910090747)
      ·
        refine ⟨96609903039642763365136121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64406602026428508910090747 96609903039642763365136121)
        ·
          refine ⟨72457427279732072523852091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96609903039642763365136121 72457427279732072523852091)
          ·
            refine ⟨108686140919598108785778137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72457427279732072523852091 108686140919598108785778137)
            ·
              refine ⟨81514605689698581589333603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108686140919598108785778137 81514605689698581589333603)
              ·
                refine ⟨122271908534547872384000405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81514605689698581589333603 122271908534547872384000405)
                ·
                  refine ⟨5731495712556931518000019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122271908534547872384000405 5731495712556931518000019)
                  ·
                    refine ⟨8597243568835397277000029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5731495712556931518000019 8597243568835397277000029)
                    ·
                      refine ⟨3223966338313273978875011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8597243568835397277000029 3223966338313273978875011)
                      ·
                        rfl

theorem cell23_6278652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_6278652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278652 prefixEnd_6278652 := by exact prefixLift 6278652
  have htrace : WordTrace (prefixWord ++ tailWord_6278652) baseStart_6278652 baseEnd_6278652 := by
    simpa [prefixWord, tailWord_6278652, baseEnd_6278652] using wordTrace_append hprefix tailTrace_6278652
  have hstable : (prefixWord ++ tailWord_6278652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278652).length < 2 ^ (prefixWord ++ tailWord_6278652).sum := by decide
  have hdescent : baseEnd_6278652 < baseStart_6278652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278675 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 4]
def baseStart_6278675 : Nat := 118140960795 + 6278675 * 2 ^ 59
def prefixEnd_6278675 : Nat := 4983230072969 + 3 ^ 40 * 6278675 * 2
def baseEnd_6278675 : Nat := 3223978148368327388887405

theorem tailTrace_6278675 : CollatzResearch.WordTrace tailWord_6278675 prefixEnd_6278675 3223978148368327388887405 := by
  unfold tailWord_6278675
  simp only [CollatzResearch.WordTrace]
  refine ⟨229002090528440262163965479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152668060352293508109310319 229002090528440262163965479)
  ·
    refine ⟨343503135792660393245948219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229002090528440262163965479 343503135792660393245948219)
    ·
      refine ⟨515254703688990589868922329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343503135792660393245948219 515254703688990589868922329)
      ·
        refine ⟨386441027766742942401691747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515254703688990589868922329 386441027766742942401691747)
        ·
          refine ⟨579661541650114413602537621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386441027766742942401691747 579661541650114413602537621)
          ·
            refine ⟨27171634764849113137618951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 579661541650114413602537621 27171634764849113137618951)
            ·
              refine ⟨40757452147273669706428427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27171634764849113137618951 40757452147273669706428427)
              ·
                refine ⟨61136178220910504559642641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40757452147273669706428427 61136178220910504559642641)
                ·
                  refine ⟨45852133665682878419731981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61136178220910504559642641 45852133665682878419731981)
                  ·
                    refine ⟨17194550124631079407399493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45852133665682878419731981 17194550124631079407399493)
                    ·
                      refine ⟨3223978148368327388887405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17194550124631079407399493 3223978148368327388887405)
                      ·
                        rfl

theorem cell23_6278675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_6278675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278675 prefixEnd_6278675 := by exact prefixLift 6278675
  have htrace : WordTrace (prefixWord ++ tailWord_6278675) baseStart_6278675 baseEnd_6278675 := by
    simpa [prefixWord, tailWord_6278675, baseEnd_6278675] using wordTrace_append hprefix tailTrace_6278675
  have hstable : (prefixWord ++ tailWord_6278675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278675).length < 2 ^ (prefixWord ++ tailWord_6278675).sum := by decide
  have hdescent : baseEnd_6278675 < baseStart_6278675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278676 : List Nat := [2, 4, 3, 1, 3, 1, 1, 8]
def baseStart_6278676 : Nat := 118140960795 + 6278676 * 2 ^ 59
def prefixEnd_6278676 : Nat := 4983230072969 + 3 ^ 40 * 6278676 * 2
def baseEnd_6278676 : Nat := 119406617105517847591663

theorem tailTrace_6278676 : CollatzResearch.WordTrace tailWord_6278676 prefixEnd_6278676 119406617105517847591663 := by
  unfold tailWord_6278676
  simp only [CollatzResearch.WordTrace]
  refine ⟨114501063500718319667375941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152668084667624426223167921 114501063500718319667375941)
  ·
    refine ⟨21468949406384684937632989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114501063500718319667375941 21468949406384684937632989)
    ·
      refine ⟨8050856027394256851612371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21468949406384684937632989 8050856027394256851612371)
      ·
        refine ⟨12076284041091385277418557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8050856027394256851612371 12076284041091385277418557)
        ·
          refine ⟨4528606515409269479031959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12076284041091385277418557 4528606515409269479031959)
          ·
            refine ⟨6792909773113904218547939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4528606515409269479031959 6792909773113904218547939)
            ·
              refine ⟨10189364659670856327821909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6792909773113904218547939 10189364659670856327821909)
              ·
                refine ⟨119406617105517847591663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10189364659670856327821909 119406617105517847591663)
                ·
                  rfl

theorem cell23_6278676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 8].length) (baseStart_6278676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278676 prefixEnd_6278676 := by exact prefixLift 6278676
  have htrace : WordTrace (prefixWord ++ tailWord_6278676) baseStart_6278676 baseEnd_6278676 := by
    simpa [prefixWord, tailWord_6278676, baseEnd_6278676] using wordTrace_append hprefix tailTrace_6278676
  have hstable : (prefixWord ++ tailWord_6278676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278676).length < 2 ^ (prefixWord ++ tailWord_6278676).sum := by decide
  have hdescent : baseEnd_6278676 < baseStart_6278676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278705 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 3, 4, 4]
def baseStart_6278705 : Nat := 118140960795 + 6278705 * 2 ^ 59
def prefixEnd_6278705 : Nat := 4983230072969 + 3 ^ 40 * 6278705 * 2
def baseEnd_6278705 : Nat := 3223993552787962271512267

theorem tailTrace_6278705 : CollatzResearch.WordTrace tailWord_6278705 prefixEnd_6278705 3223993552787962271512267 := by
  unfold tailWord_6278705
  simp only [CollatzResearch.WordTrace]
  refine ⟨229003184718331577287557569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152668789812221051525038379 229003184718331577287557569)
  ·
    refine ⟨171752388538748682965668177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229003184718331577287557569 171752388538748682965668177)
    ·
      refine ⟨128814291404061512224251133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171752388538748682965668177 128814291404061512224251133)
      ·
        refine ⟨48305359276523067084094175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128814291404061512224251133 48305359276523067084094175)
        ·
          refine ⟨72458038914784600626141263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48305359276523067084094175 72458038914784600626141263)
          ·
            refine ⟨108687058372176900939211895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72458038914784600626141263 108687058372176900939211895)
            ·
              refine ⟨163030587558265351408817843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108687058372176900939211895 163030587558265351408817843)
              ·
                refine ⟨244545881337398027113226765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163030587558265351408817843 244545881337398027113226765)
                ·
                  refine ⟨91704705501524260167460037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244545881337398027113226765 91704705501524260167460037)
                  ·
                    refine ⟨17194632281535798781398757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91704705501524260167460037 17194632281535798781398757)
                    ·
                      refine ⟨3223993552787962271512267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17194632281535798781398757 3223993552787962271512267)
                      ·
                        rfl

theorem cell23_6278705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_6278705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278705 prefixEnd_6278705 := by exact prefixLift 6278705
  have htrace : WordTrace (prefixWord ++ tailWord_6278705) baseStart_6278705 baseEnd_6278705 := by
    simpa [prefixWord, tailWord_6278705, baseEnd_6278705] using wordTrace_append hprefix tailTrace_6278705
  have hstable : (prefixWord ++ tailWord_6278705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278705).length < 2 ^ (prefixWord ++ tailWord_6278705).sum := by decide
  have hdescent : baseEnd_6278705 < baseStart_6278705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278709 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 1, 4, 2]
def baseStart_6278709 : Nat := 118140960795 + 6278709 * 2 ^ 59
def prefixEnd_6278709 : Nat := 4983230072969 + 3 ^ 40 * 6278709 * 2
def baseEnd_6278709 : Nat := 3223995606710580255862249

theorem tailTrace_6278709 : CollatzResearch.WordTrace tailWord_6278709 prefixEnd_6278709 3223995606710580255862249 := by
  unfold tailWord_6278709
  simp only [CollatzResearch.WordTrace]
  refine ⟨229003330610317085970703181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152668887073544723980468787 229003330610317085970703181)
  ·
    refine ⟨85876248978868907239013693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229003330610317085970703181 85876248978868907239013693)
    ·
      refine ⟨32203593367075840214630135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85876248978868907239013693 32203593367075840214630135)
      ·
        refine ⟨48305390050613760321945203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32203593367075840214630135 48305390050613760321945203)
        ·
          refine ⟨72458085075920640482917805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48305390050613760321945203 72458085075920640482917805)
          ·
            refine ⟨27171781903470240181094177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72458085075920640482917805 27171781903470240181094177)
            ·
              refine ⟨20378836427602680135820633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27171781903470240181094177 20378836427602680135820633)
              ·
                refine ⟨15284127320702010101865475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20378836427602680135820633 15284127320702010101865475)
                ·
                  refine ⟨22926190981053015152798213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15284127320702010101865475 22926190981053015152798213)
                  ·
                    refine ⟨4298660808947440341149665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22926190981053015152798213 4298660808947440341149665)
                    ·
                      refine ⟨3223995606710580255862249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4298660808947440341149665 3223995606710580255862249)
                      ·
                        rfl

theorem cell23_6278709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_6278709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278709 prefixEnd_6278709 := by exact prefixLift 6278709
  have htrace : WordTrace (prefixWord ++ tailWord_6278709) baseStart_6278709 baseEnd_6278709 := by
    simpa [prefixWord, tailWord_6278709, baseEnd_6278709] using wordTrace_append hprefix tailTrace_6278709
  have hstable : (prefixWord ++ tailWord_6278709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278709).length < 2 ^ (prefixWord ++ tailWord_6278709).sum := by decide
  have hdescent : baseEnd_6278709 < baseStart_6278709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278713 : List Nat := [1, 2, 1, 5, 1, 4, 2, 1, 1, 3, 2]
def baseStart_6278713 : Nat := 118140960795 + 6278713 * 2 ^ 59
def prefixEnd_6278713 : Nat := 4983230072969 + 3 ^ 40 * 6278713 * 2
def baseEnd_6278713 : Nat := 3223997660633198240212231

theorem tailTrace_6278713 : CollatzResearch.WordTrace tailWord_6278713 prefixEnd_6278713 3223997660633198240212231 := by
  unfold tailWord_6278713
  simp only [CollatzResearch.WordTrace]
  refine ⟨229003476502302594653848793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152668984334868396435899195 229003476502302594653848793)
  ·
    refine ⟨171752607376726945990386595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229003476502302594653848793 171752607376726945990386595)
    ·
      refine ⟨257628911065090418985579893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171752607376726945990386595 257628911065090418985579893)
      ·
        refine ⟨24152710412352226779898115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 257628911065090418985579893 24152710412352226779898115)
        ·
          refine ⟨36229065618528340169847173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24152710412352226779898115 36229065618528340169847173)
          ·
            refine ⟨6792949803474063781846345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36229065618528340169847173 6792949803474063781846345)
            ·
              refine ⟨5094712352605547836384759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6792949803474063781846345 5094712352605547836384759)
              ·
                refine ⟨7642068528908321754577139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5094712352605547836384759 7642068528908321754577139)
                ·
                  refine ⟨11463102793362482631865709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7642068528908321754577139 11463102793362482631865709)
                  ·
                    refine ⟨4298663547510930986949641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11463102793362482631865709 4298663547510930986949641)
                    ·
                      refine ⟨3223997660633198240212231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4298663547510930986949641 3223997660633198240212231)
                      ·
                        rfl

theorem cell23_6278713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_6278713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278713 prefixEnd_6278713 := by exact prefixLift 6278713
  have htrace : WordTrace (prefixWord ++ tailWord_6278713) baseStart_6278713 baseEnd_6278713 := by
    simpa [prefixWord, tailWord_6278713, baseEnd_6278713] using wordTrace_append hprefix tailTrace_6278713
  have hstable : (prefixWord ++ tailWord_6278713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278713).length < 2 ^ (prefixWord ++ tailWord_6278713).sum := by decide
  have hdescent : baseEnd_6278713 < baseStart_6278713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278732 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 7]
def baseStart_6278732 : Nat := 118140960795 + 6278732 * 2 ^ 59
def prefixEnd_6278732 : Nat := 4983230072969 + 3 ^ 40 * 6278732 * 2
def baseEnd_6278732 : Nat := 358223046307292629541627

theorem tailTrace_6278732 : CollatzResearch.WordTrace tailWord_6278732 prefixEnd_6278732 358223046307292629541627 := by
  unfold tailWord_6278732
  simp only [CollatzResearch.WordTrace]
  refine ⟨114502084744616880449395225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152669446326155840599193633 114502084744616880449395225)
  ·
    refine ⟨85876563558462660337046419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114502084744616880449395225 85876563558462660337046419)
    ·
      refine ⟨128814845337693990505569629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85876563558462660337046419 128814845337693990505569629)
      ·
        refine ⟨48305567001635246439588611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128814845337693990505569629 48305567001635246439588611)
        ·
          refine ⟨72458350502452869659382917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48305567001635246439588611 72458350502452869659382917)
          ·
            refine ⟨13585940719209913061134297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72458350502452869659382917 13585940719209913061134297)
            ·
              refine ⟨10189455539407434795850723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13585940719209913061134297 10189455539407434795850723)
              ·
                refine ⟨15284183309111152193776085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10189455539407434795850723 15284183309111152193776085)
                ·
                  refine ⟨358223046307292629541627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15284183309111152193776085 358223046307292629541627)
                  ·
                    rfl

theorem cell23_6278732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 7].length) (baseStart_6278732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278732 prefixEnd_6278732 := by exact prefixLift 6278732
  have htrace : WordTrace (prefixWord ++ tailWord_6278732) baseStart_6278732 baseEnd_6278732 := by
    simpa [prefixWord, tailWord_6278732, baseEnd_6278732] using wordTrace_append hprefix tailTrace_6278732
  have hstable : (prefixWord ++ tailWord_6278732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278732).length < 2 ^ (prefixWord ++ tailWord_6278732).sum := by decide
  have hdescent : baseEnd_6278732 < baseStart_6278732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278743 : List Nat := [1, 1, 3, 2, 2, 4, 3, 1, 2, 2, 2]
def baseStart_6278743 : Nat := 118140960795 + 6278743 * 2 ^ 59
def prefixEnd_6278743 : Nat := 4983230072969 + 3 ^ 40 * 6278743 * 2
def baseEnd_6278743 : Nat := 3224013065052833122837093

theorem tailTrace_6278743 : CollatzResearch.WordTrace tailWord_6278743 prefixEnd_6278743 3224013065052833122837093 := by
  unfold tailWord_6278743
  simp only [CollatzResearch.WordTrace]
  refine ⟨229004570692193909777440883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152669713794795939851627255 229004570692193909777440883)
  ·
    refine ⟨343506856038290864666161325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229004570692193909777440883 343506856038290864666161325)
    ·
      refine ⟨128815071014359074249810497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343506856038290864666161325 128815071014359074249810497)
      ·
        refine ⟨96611303260769305687357873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128815071014359074249810497 96611303260769305687357873)
        ·
          refine ⟨72458477445576979265518405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96611303260769305687357873 72458477445576979265518405)
          ·
            refine ⟨13585964521045683612284701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72458477445576979265518405 13585964521045683612284701)
            ·
              refine ⟨5094736695392131354606763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13585964521045683612284701 5094736695392131354606763)
              ·
                refine ⟨7642105043088197031910145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5094736695392131354606763 7642105043088197031910145)
                ·
                  refine ⟨5731578782316147773932609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7642105043088197031910145 5731578782316147773932609)
                  ·
                    refine ⟨4298684086737110830449457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5731578782316147773932609 4298684086737110830449457)
                    ·
                      refine ⟨3224013065052833122837093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4298684086737110830449457 3224013065052833122837093)
                      ·
                        rfl

theorem cell23_6278743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_6278743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278743 prefixEnd_6278743 := by exact prefixLift 6278743
  have htrace : WordTrace (prefixWord ++ tailWord_6278743) baseStart_6278743 baseEnd_6278743 := by
    simpa [prefixWord, tailWord_6278743, baseEnd_6278743] using wordTrace_append hprefix tailTrace_6278743
  have hstable : (prefixWord ++ tailWord_6278743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278743).length < 2 ^ (prefixWord ++ tailWord_6278743).sum := by decide
  have hdescent : baseEnd_6278743 < baseStart_6278743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278762 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 1, 7]
def baseStart_6278762 : Nat := 118140960795 + 6278762 * 2 ^ 59
def prefixEnd_6278762 : Nat := 4983230072969 + 3 ^ 40 * 6278762 * 2
def baseEnd_6278762 : Nat := 1074674273728422849499835

theorem tailTrace_6278762 : CollatzResearch.WordTrace tailWord_6278762 prefixEnd_6278762 1074674273728422849499835 := by
  unfold tailWord_6278762
  simp only [CollatzResearch.WordTrace]
  refine ⟨57251315919781269005595635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152670175786083384014921693 57251315919781269005595635)
  ·
    refine ⟨85876973879671903508393453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57251315919781269005595635 85876973879671903508393453)
    ·
      refine ⟨32203865204876963815647545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85876973879671903508393453 32203865204876963815647545)
      ·
        refine ⟨24152898903657722861735659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32203865204876963815647545 24152898903657722861735659)
        ·
          refine ⟨36229348355486584292603489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24152898903657722861735659 36229348355486584292603489)
          ·
            refine ⟨27172011266614938219452617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36229348355486584292603489 27172011266614938219452617)
            ·
              refine ⟨20379008449961203664589463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27172011266614938219452617 20379008449961203664589463)
              ·
                refine ⟨30568512674941805496884195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20379008449961203664589463 30568512674941805496884195)
                ·
                  refine ⟨45852769012412708245326293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30568512674941805496884195 45852769012412708245326293)
                  ·
                    refine ⟨1074674273728422849499835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45852769012412708245326293 1074674273728422849499835)
                    ·
                      rfl

theorem cell23_6278762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_6278762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278762 prefixEnd_6278762 := by exact prefixLift 6278762
  have htrace : WordTrace (prefixWord ++ tailWord_6278762) baseStart_6278762 baseEnd_6278762 := by
    simpa [prefixWord, tailWord_6278762, baseEnd_6278762] using wordTrace_append hprefix tailTrace_6278762
  have hstable : (prefixWord ++ tailWord_6278762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278762).length < 2 ^ (prefixWord ++ tailWord_6278762).sum := by decide
  have hdescent : baseEnd_6278762 < baseStart_6278762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278819 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 3]
def baseStart_6278819 : Nat := 118140960795 + 6278819 * 2 ^ 59
def prefixEnd_6278819 : Nat := 4983230072969 + 3 ^ 40 * 6278819 * 2
def baseEnd_6278819 : Nat := 3224052089582574825486743

theorem tailTrace_6278819 : CollatzResearch.WordTrace tailWord_6278819 prefixEnd_6278819 3224052089582574825486743 := by
  unfold tailWord_6278819
  simp only [CollatzResearch.WordTrace]
  refine ⟨229007342639918574757207511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152671561759945716504805007 229007342639918574757207511)
  ·
    refine ⟨343511013959877862135811267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229007342639918574757207511 343511013959877862135811267)
    ·
      refine ⟨515266520939816793203716901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343511013959877862135811267 515266520939816793203716901)
      ·
        refine ⟨96612472676215648725696919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 515266520939816793203716901 96612472676215648725696919)
        ·
          refine ⟨144918709014323473088545379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96612472676215648725696919 144918709014323473088545379)
          ·
            refine ⟨217378063521485209632818069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144918709014323473088545379 217378063521485209632818069)
            ·
              refine ⟨10189596727569619201538347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 217378063521485209632818069 10189596727569619201538347)
              ·
                refine ⟨15284395091354428802307521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10189596727569619201538347 15284395091354428802307521)
                ·
                  refine ⟨11463296318515821601730641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15284395091354428802307521 11463296318515821601730641)
                  ·
                    refine ⟨8597472238886866201297981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11463296318515821601730641 8597472238886866201297981)
                    ·
                      refine ⟨3224052089582574825486743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8597472238886866201297981 3224052089582574825486743)
                      ·
                        rfl

theorem cell23_6278819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_6278819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278819 prefixEnd_6278819 := by exact prefixLift 6278819
  have htrace : WordTrace (prefixWord ++ tailWord_6278819) baseStart_6278819 baseEnd_6278819 := by
    simpa [prefixWord, tailWord_6278819, baseEnd_6278819] using wordTrace_append hprefix tailTrace_6278819
  have hstable : (prefixWord ++ tailWord_6278819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278819).length < 2 ^ (prefixWord ++ tailWord_6278819).sum := by decide
  have hdescent : baseEnd_6278819 < baseStart_6278819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278839 : List Nat := [1, 1, 3, 1, 5, 2, 2, 2, 6]
def baseStart_6278839 : Nat := 118140960795 + 6278839 * 2 ^ 59
def prefixEnd_6278839 : Nat := 4983230072969 + 3 ^ 40 * 6278839 * 2
def baseEnd_6278839 : Nat := 358229151021740527470739

theorem tailTrace_6278839 : CollatzResearch.WordTrace tailWord_6278839 prefixEnd_6278839 358229151021740527470739 := by
  unfold tailWord_6278839
  simp only [CollatzResearch.WordTrace]
  refine ⟨229008072099846118172935571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152672048066564078781957047 229008072099846118172935571)
  ·
    refine ⟨343512108149769177259403357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229008072099846118172935571 343512108149769177259403357)
    ·
      refine ⟨128817040556163441472276259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343512108149769177259403357 128817040556163441472276259)
      ·
        refine ⟨193225560834245162208414389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128817040556163441472276259 193225560834245162208414389)
        ·
          refine ⟨18114896328210483957038849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193225560834245162208414389 18114896328210483957038849)
          ·
            refine ⟨13586172246157862967779137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18114896328210483957038849 13586172246157862967779137)
            ·
              refine ⟨10189629184618397225834353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13586172246157862967779137 10189629184618397225834353)
              ·
                refine ⟨7642221888463797919375765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10189629184618397225834353 7642221888463797919375765)
                ·
                  refine ⟨358229151021740527470739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7642221888463797919375765 358229151021740527470739)
                  ·
                    rfl

theorem cell23_6278839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 6].length) (baseStart_6278839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278839 prefixEnd_6278839 := by exact prefixLift 6278839
  have htrace : WordTrace (prefixWord ++ tailWord_6278839) baseStart_6278839 baseEnd_6278839 := by
    simpa [prefixWord, tailWord_6278839, baseEnd_6278839] using wordTrace_append hprefix tailTrace_6278839
  have hstable : (prefixWord ++ tailWord_6278839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278839).length < 2 ^ (prefixWord ++ tailWord_6278839).sum := by decide
  have hdescent : baseEnd_6278839 < baseStart_6278839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278859 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 4, 3, 2]
def baseStart_6278859 : Nat := 118140960795 + 6278859 * 2 ^ 59
def prefixEnd_6278859 : Nat := 4983230072969 + 3 ^ 40 * 6278859 * 2
def baseEnd_6278859 : Nat := 3224072628808754668986559

theorem tailTrace_6278859 : CollatzResearch.WordTrace tailWord_6278859 prefixEnd_6278859 3224072628808754668986559 := by
  unfold tailWord_6278859
  simp only [CollatzResearch.WordTrace]
  refine ⟨229008801559773661588663631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152672534373182441059109087 229008801559773661588663631)
  ·
    refine ⟨343513202339660492382995447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229008801559773661588663631 343513202339660492382995447)
    ·
      refine ⟨515269803509490738574493171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343513202339660492382995447 515269803509490738574493171)
      ·
        refine ⟨772904705264236107861739757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515269803509490738574493171 772904705264236107861739757)
        ·
          refine ⟨289839264474088540448152409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 772904705264236107861739757 289839264474088540448152409)
          ·
            refine ⟨217379448355566405336114307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289839264474088540448152409 217379448355566405336114307)
            ·
              refine ⟨326069172533349608004171461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217379448355566405336114307 326069172533349608004171461)
              ·
                refine ⟨61137969850003051500782149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326069172533349608004171461 61137969850003051500782149)
                ·
                  refine ⟨11463369346875572156396653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61137969850003051500782149 11463369346875572156396653)
                  ·
                    refine ⟨4298763505078339558648745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11463369346875572156396653 4298763505078339558648745)
                    ·
                      refine ⟨3224072628808754668986559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4298763505078339558648745 3224072628808754668986559)
                      ·
                        rfl

theorem cell23_6278859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 3, 2].length) (baseStart_6278859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278859 prefixEnd_6278859 := by exact prefixLift 6278859
  have htrace : WordTrace (prefixWord ++ tailWord_6278859) baseStart_6278859 baseEnd_6278859 := by
    simpa [prefixWord, tailWord_6278859, baseEnd_6278859] using wordTrace_append hprefix tailTrace_6278859
  have hstable : (prefixWord ++ tailWord_6278859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278859).length < 2 ^ (prefixWord ++ tailWord_6278859).sum := by decide
  have hdescent : baseEnd_6278859 < baseStart_6278859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278862 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_6278862 : Nat := 118140960795 + 6278862 * 2 ^ 59
def prefixEnd_6278862 : Nat := 4983230072969 + 3 ^ 40 * 6278862 * 2
def baseEnd_6278862 : Nat := 3224074169250718157249045

theorem tailTrace_6278862 : CollatzResearch.WordTrace tailWord_6278862 prefixEnd_6278862 3224074169250718157249045 := by
  unfold tailWord_6278862
  simp only [CollatzResearch.WordTrace]
  refine ⟨28626113872345349137627855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152672607319175195400681893 28626113872345349137627855)
  ·
    refine ⟨42939170808518023706441783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28626113872345349137627855 42939170808518023706441783)
    ·
      refine ⟨64408756212777035559662675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42939170808518023706441783 64408756212777035559662675)
      ·
        refine ⟨96613134319165553339494013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64408756212777035559662675 96613134319165553339494013)
        ·
          refine ⟨36229925369687082502310255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96613134319165553339494013 36229925369687082502310255)
          ·
            refine ⟨54344888054530623753465383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36229925369687082502310255 54344888054530623753465383)
            ·
              refine ⟨81517332081795935630198075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54344888054530623753465383 81517332081795935630198075)
              ·
                refine ⟨122275998122693903445297113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81517332081795935630198075 122275998122693903445297113)
                ·
                  refine ⟨91706998592020427583972835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122275998122693903445297113 91706998592020427583972835)
                  ·
                    refine ⟨137560497888030641375959253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91706998592020427583972835 137560497888030641375959253)
                    ·
                      refine ⟨3224074169250718157249045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137560497888030641375959253 3224074169250718157249045)
                      ·
                        rfl

theorem cell23_6278862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_6278862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278862 prefixEnd_6278862 := by exact prefixLift 6278862
  have htrace : WordTrace (prefixWord ++ tailWord_6278862) baseStart_6278862 baseEnd_6278862 := by
    simpa [prefixWord, tailWord_6278862, baseEnd_6278862] using wordTrace_append hprefix tailTrace_6278862
  have hstable : (prefixWord ++ tailWord_6278862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278862).length < 2 ^ (prefixWord ++ tailWord_6278862).sum := by decide
  have hdescent : baseEnd_6278862 < baseStart_6278862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278866 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_6278866 : Nat := 118140960795 + 6278866 * 2 ^ 59
def prefixEnd_6278866 : Nat := 4983230072969 + 3 ^ 40 * 6278866 * 2
def baseEnd_6278866 : Nat := 3224076223173336141599027

theorem tailTrace_6278866 : CollatzResearch.WordTrace tailWord_6278866 prefixEnd_6278866 3224076223173336141599027 := by
  unfold tailWord_6278866
  simp only [CollatzResearch.WordTrace]
  refine ⟨57252264217687075446042113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152672704580498867856112301 57252264217687075446042113)
  ·
    refine ⟨42939198163265306584531585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57252264217687075446042113 42939198163265306584531585)
    ·
      refine ⟨32204398622448979938398689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42939198163265306584531585 32204398622448979938398689)
      ·
        refine ⟨24153298966836734953799017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32204398622448979938398689 24153298966836734953799017)
        ·
          refine ⟨18114974225127551215349263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24153298966836734953799017 18114974225127551215349263)
          ·
            refine ⟨27172461337691326823023895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18114974225127551215349263 27172461337691326823023895)
            ·
              refine ⟨40758692006536990234535843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27172461337691326823023895 40758692006536990234535843)
              ·
                refine ⟨61138038009805485351803765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40758692006536990234535843 61138038009805485351803765)
                ·
                  refine ⟨5731691063419264251731603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61138038009805485351803765 5731691063419264251731603)
                  ·
                    refine ⟨8597536595128896377597405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5731691063419264251731603 8597536595128896377597405)
                    ·
                      refine ⟨3224076223173336141599027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8597536595128896377597405 3224076223173336141599027)
                      ·
                        rfl

theorem cell23_6278866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_6278866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278866 prefixEnd_6278866 := by exact prefixLift 6278866
  have htrace : WordTrace (prefixWord ++ tailWord_6278866) baseStart_6278866 baseEnd_6278866 := by
    simpa [prefixWord, tailWord_6278866, baseEnd_6278866] using wordTrace_append hprefix tailTrace_6278866
  have hstable : (prefixWord ++ tailWord_6278866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278866).length < 2 ^ (prefixWord ++ tailWord_6278866).sum := by decide
  have hdescent : baseEnd_6278866 < baseStart_6278866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278900 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_6278900 : Nat := 118140960795 + 6278900 * 2 ^ 59
def prefixEnd_6278900 : Nat := 4983230072969 + 3 ^ 40 * 6278900 * 2
def baseEnd_6278900 : Nat := 3224093681515589008573871

theorem tailTrace_6278900 : CollatzResearch.WordTrace tailWord_6278900 prefixEnd_6278900 3224093681515589008573871 := by
  unfold tailWord_6278900
  simp only [CollatzResearch.WordTrace]
  refine ⟨114505148476312562795453077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152673531301750083727270769 114505148476312562795453077)
  ·
    refine ⟨5367428834827151381036863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 114505148476312562795453077 5367428834827151381036863)
    ·
      refine ⟨8051143252240727071555295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5367428834827151381036863 8051143252240727071555295)
      ·
        refine ⟨12076714878361090607332943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8051143252240727071555295 12076714878361090607332943)
        ·
          refine ⟨18115072317541635910999415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12076714878361090607332943 18115072317541635910999415)
          ·
            refine ⟨27172608476312453866499123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18115072317541635910999415 27172608476312453866499123)
            ·
              refine ⟨40758912714468680799748685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27172608476312453866499123 40758912714468680799748685)
              ·
                refine ⟨15284592267925755299905757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40758912714468680799748685 15284592267925755299905757)
                ·
                  refine ⟨5731722100472158237464659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15284592267925755299905757 5731722100472158237464659)
                  ·
                    refine ⟨8597583150708237356196989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5731722100472158237464659 8597583150708237356196989)
                    ·
                      refine ⟨3224093681515589008573871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8597583150708237356196989 3224093681515589008573871)
                      ·
                        rfl

theorem cell23_6278900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_6278900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278900 prefixEnd_6278900 := by exact prefixLift 6278900
  have htrace : WordTrace (prefixWord ++ tailWord_6278900) baseStart_6278900 baseEnd_6278900 := by
    simpa [prefixWord, tailWord_6278900, baseEnd_6278900] using wordTrace_append hprefix tailTrace_6278900
  have hstable : (prefixWord ++ tailWord_6278900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278900).length < 2 ^ (prefixWord ++ tailWord_6278900).sum := by decide
  have hdescent : baseEnd_6278900 < baseStart_6278900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278909 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 3, 2, 3]
def baseStart_6278909 : Nat := 118140960795 + 6278909 * 2 ^ 59
def prefixEnd_6278909 : Nat := 4983230072969 + 3 ^ 40 * 6278909 * 2
def baseEnd_6278909 : Nat := 3224098302841479473361329

theorem tailTrace_6278909 : CollatzResearch.WordTrace tailWord_6278909 prefixEnd_6278909 3224098302841479473361329 := by
  unfold tailWord_6278909
  simp only [CollatzResearch.WordTrace]
  refine ⟨229010625209592520127983781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152673750139728346751989187 229010625209592520127983781)
  ·
    refine ⟨42939492226798597523996959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229010625209592520127983781 42939492226798597523996959)
    ·
      refine ⟨64409238340197896285995439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42939492226798597523996959 64409238340197896285995439)
      ·
        refine ⟨96613857510296844428993159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64409238340197896285995439 96613857510296844428993159)
        ·
          refine ⟨144920786265445266643489739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96613857510296844428993159 144920786265445266643489739)
          ·
            refine ⟨217381179398167899965234609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144920786265445266643489739 217381179398167899965234609)
            ·
              refine ⟨163035884548625924973925957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217381179398167899965234609 163035884548625924973925957)
              ·
                refine ⟨30569228352867360932611117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163035884548625924973925957 30569228352867360932611117)
                ·
                  refine ⟨11463460632325260349729169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30569228352867360932611117 11463460632325260349729169)
                  ·
                    refine ⟨8597595474243945262296877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11463460632325260349729169 8597595474243945262296877)
                    ·
                      refine ⟨3224098302841479473361329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8597595474243945262296877 3224098302841479473361329)
                      ·
                        rfl

theorem cell23_6278909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_6278909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278909 prefixEnd_6278909 := by exact prefixLift 6278909
  have htrace : WordTrace (prefixWord ++ tailWord_6278909) baseStart_6278909 baseEnd_6278909 := by
    simpa [prefixWord, tailWord_6278909, baseEnd_6278909] using wordTrace_append hprefix tailTrace_6278909
  have hstable : (prefixWord ++ tailWord_6278909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278909).length < 2 ^ (prefixWord ++ tailWord_6278909).sum := by decide
  have hdescent : baseEnd_6278909 < baseStart_6278909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278916 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 1, 6]
def baseStart_6278916 : Nat := 118140960795 + 6278916 * 2 ^ 59
def prefixEnd_6278916 : Nat := 4983230072969 + 3 ^ 40 * 6278916 * 2
def baseEnd_6278916 : Nat := 1074700632402020315324599

theorem tailTrace_6278916 : CollatzResearch.WordTrace tailWord_6278916 prefixEnd_6278916 1074700632402020315324599 := by
  unfold tailWord_6278916
  simp only [CollatzResearch.WordTrace]
  refine ⟨114505440260283580161744301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152673920347044773548992401 114505440260283580161744301)
  ·
    refine ⟨42939540097606342560654113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114505440260283580161744301 42939540097606342560654113)
    ·
      refine ⟨32204655073204756920490585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42939540097606342560654113 32204655073204756920490585)
      ·
        refine ⟨24153491304903567690367939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32204655073204756920490585 24153491304903567690367939)
        ·
          refine ⟨36230236957355351535551909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24153491304903567690367939 36230236957355351535551909)
          ·
            refine ⟨6793169429504128412915983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36230236957355351535551909 6793169429504128412915983)
            ·
              refine ⟨10189754144256192619373975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6793169429504128412915983 10189754144256192619373975)
              ·
                refine ⟨15284631216384288929060963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10189754144256192619373975 15284631216384288929060963)
                ·
                  refine ⟨22926946824576433393591445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15284631216384288929060963 22926946824576433393591445)
                  ·
                    refine ⟨1074700632402020315324599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22926946824576433393591445 1074700632402020315324599)
                    ·
                      rfl

theorem cell23_6278916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_6278916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278916 prefixEnd_6278916 := by exact prefixLift 6278916
  have htrace : WordTrace (prefixWord ++ tailWord_6278916) baseStart_6278916 baseEnd_6278916 := by
    simpa [prefixWord, tailWord_6278916, baseEnd_6278916] using wordTrace_append hprefix tailTrace_6278916
  have hstable : (prefixWord ++ tailWord_6278916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278916).length < 2 ^ (prefixWord ++ tailWord_6278916).sum := by decide
  have hdescent : baseEnd_6278916 < baseStart_6278916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278926 : List Nat := [4, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3]
def baseStart_6278926 : Nat := 118140960795 + 6278926 * 2 ^ 59
def prefixEnd_6278926 : Nat := 4983230072969 + 3 ^ 40 * 6278926 * 2
def baseEnd_6278926 : Nat := 3224107032012605906848751

theorem tailTrace_6278926 : CollatzResearch.WordTrace tailWord_6278926 prefixEnd_6278926 3224107032012605906848751 := by
  unfold tailWord_6278926
  simp only [CollatzResearch.WordTrace]
  refine ⟨28626405656316366503919079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152674163500353954687568421 28626405656316366503919079)
  ·
    refine ⟨42939608484474549755878619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28626405656316366503919079 42939608484474549755878619)
    ·
      refine ⟨64409412726711824633817929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42939608484474549755878619 64409412726711824633817929)
      ·
        refine ⟨48307059545033868475363447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64409412726711824633817929 48307059545033868475363447)
        ·
          refine ⟨72460589317550802713045171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48307059545033868475363447 72460589317550802713045171)
          ·
            refine ⟨108690883976326204069567757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72460589317550802713045171 108690883976326204069567757)
            ·
              refine ⟨40759081491122326526087909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108690883976326204069567757 40759081491122326526087909)
              ·
                refine ⟨7642327779585436223641483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40759081491122326526087909 7642327779585436223641483)
                ·
                  refine ⟨11463491669378154335462225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7642327779585436223641483 11463491669378154335462225)
                  ·
                    refine ⟨8597618752033615751596669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11463491669378154335462225 8597618752033615751596669)
                    ·
                      refine ⟨3224107032012605906848751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8597618752033615751596669 3224107032012605906848751)
                      ·
                        rfl

theorem cell23_6278926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_6278926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278926 prefixEnd_6278926 := by exact prefixLift 6278926
  have htrace : WordTrace (prefixWord ++ tailWord_6278926) baseStart_6278926 baseEnd_6278926 := by
    simpa [prefixWord, tailWord_6278926, baseEnd_6278926] using wordTrace_append hprefix tailTrace_6278926
  have hstable : (prefixWord ++ tailWord_6278926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278926).length < 2 ^ (prefixWord ++ tailWord_6278926).sum := by decide
  have hdescent : baseEnd_6278926 < baseStart_6278926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278956 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 3]
def baseStart_6278956 : Nat := 118140960795 + 6278956 * 2 ^ 59
def prefixEnd_6278956 : Nat := 4983230072969 + 3 ^ 40 * 6278956 * 2
def baseEnd_6278956 : Nat := 3224122436432240789473613

theorem tailTrace_6278956 : CollatzResearch.WordTrace tailWord_6278956 prefixEnd_6278956 3224122436432240789473613 := by
  unfold tailWord_6278956
  simp only [CollatzResearch.WordTrace]
  refine ⟨114506169720211123577472361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152674892960281498103296481 114506169720211123577472361)
  ·
    refine ⟨85879627290158342683104271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114506169720211123577472361 85879627290158342683104271)
    ·
      refine ⟨128819440935237514024656407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85879627290158342683104271 128819440935237514024656407)
      ·
        refine ⟨193229161402856271036984611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128819440935237514024656407 193229161402856271036984611)
        ·
          refine ⟨289843742104284406555476917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193229161402856271036984611 289843742104284406555476917)
          ·
            refine ⟨27172850822276663114575961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 289843742104284406555476917 27172850822276663114575961)
            ·
              refine ⟨20379638116707497335931971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27172850822276663114575961 20379638116707497335931971)
              ·
                refine ⟨30569457175061246003897957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20379638116707497335931971 30569457175061246003897957)
                ·
                  refine ⟨5731773220323983625730867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30569457175061246003897957 5731773220323983625730867)
                  ·
                    refine ⟨8597659830485975438596301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5731773220323983625730867 8597659830485975438596301)
                    ·
                      refine ⟨3224122436432240789473613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8597659830485975438596301 3224122436432240789473613)
                      ·
                        rfl

theorem cell23_6278956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 3].length) (baseStart_6278956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278956 prefixEnd_6278956 := by exact prefixLift 6278956
  have htrace : WordTrace (prefixWord ++ tailWord_6278956) baseStart_6278956 baseEnd_6278956 := by
    simpa [prefixWord, tailWord_6278956, baseEnd_6278956] using wordTrace_append hprefix tailTrace_6278956
  have hstable : (prefixWord ++ tailWord_6278956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278956).length < 2 ^ (prefixWord ++ tailWord_6278956).sum := by decide
  have hdescent : baseEnd_6278956 < baseStart_6278956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6278983 : List Nat := [1, 1, 4, 1, 2, 1, 5, 2, 1, 3, 2]
def baseStart_6278983 : Nat := 118140960795 + 6278983 * 2 ^ 59
def prefixEnd_6278983 : Nat := 4983230072969 + 3 ^ 40 * 6278983 * 2
def baseEnd_6278983 : Nat := 3224136300409912183835989

theorem tailTrace_6278983 : CollatzResearch.WordTrace tailWord_6278983 prefixEnd_6278983 3224136300409912183835989 := by
  unfold tailWord_6278983
  simp only [CollatzResearch.WordTrace]
  refine ⟨229013324211324430766177603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152675549474216287177451735 229013324211324430766177603)
  ·
    refine ⟨343519986316986646149266405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229013324211324430766177603 343519986316986646149266405)
    ·
      refine ⟨64409997434434996152987451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 343519986316986646149266405 64409997434434996152987451)
      ·
        refine ⟨96614996151652494229481177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64409997434434996152987451 96614996151652494229481177)
        ·
          refine ⟨72461247113739370672110883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96614996151652494229481177 72461247113739370672110883)
          ·
            refine ⟨108691870670609056008166325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72461247113739370672110883 108691870670609056008166325)
            ·
              refine ⟨10189862875369599000765593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108691870670609056008166325 10189862875369599000765593)
              ·
                refine ⟨7642397156527199250574195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10189862875369599000765593 7642397156527199250574195)
                ·
                  refine ⟨11463595734790798875861293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7642397156527199250574195 11463595734790798875861293)
                  ·
                    refine ⟨4298848400546549578447985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11463595734790798875861293 4298848400546549578447985)
                    ·
                      refine ⟨3224136300409912183835989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4298848400546549578447985 3224136300409912183835989)
                      ·
                        rfl

theorem cell23_6278983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_6278983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6278983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6278983 prefixEnd_6278983 := by exact prefixLift 6278983
  have htrace : WordTrace (prefixWord ++ tailWord_6278983) baseStart_6278983 baseEnd_6278983 := by
    simpa [prefixWord, tailWord_6278983, baseEnd_6278983] using wordTrace_append hprefix tailTrace_6278983
  have hstable : (prefixWord ++ tailWord_6278983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6278983).length < 2 ^ (prefixWord ++ tailWord_6278983).sum := by decide
  have hdescent : baseEnd_6278983 < baseStart_6278983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6278983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279009 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_6279009 : Nat := 118140960795 + 6279009 * 2 ^ 59
def prefixEnd_6279009 : Nat := 4983230072969 + 3 ^ 40 * 6279009 * 2
def baseEnd_6279009 : Nat := 3224149650906929082110869

theorem tailTrace_6279009 : CollatzResearch.WordTrace tailWord_6279009 prefixEnd_6279009 3224149650906929082110869 := by
  unfold tailWord_6279009
  simp only [CollatzResearch.WordTrace]
  refine ⟨229014272509230237206624081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152676181672820158137749387 229014272509230237206624081)
  ·
    refine ⟨171760704381922677904968061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229014272509230237206624081 171760704381922677904968061)
    ·
      refine ⟨64410264143221004214363023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171760704381922677904968061 64410264143221004214363023)
      ·
        refine ⟨96615396214831506321544535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64410264143221004214363023 96615396214831506321544535)
        ·
          refine ⟨144923094322247259482316803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96615396214831506321544535 144923094322247259482316803)
          ·
            refine ⟨217384641483370889223475205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144923094322247259482316803 217384641483370889223475205)
            ·
              refine ⟨40759620278132041729401601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217384641483370889223475205 40759620278132041729401601)
              ·
                refine ⟨30569715208599031297051201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40759620278132041729401601 30569715208599031297051201)
                ·
                  refine ⟨22927286406449273472788401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30569715208599031297051201 22927286406449273472788401)
                  ·
                    refine ⟨17195464804836955104591301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22927286406449273472788401 17195464804836955104591301)
                    ·
                      refine ⟨3224149650906929082110869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17195464804836955104591301 3224149650906929082110869)
                      ·
                        rfl

theorem cell23_6279009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_6279009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279009 prefixEnd_6279009 := by exact prefixLift 6279009
  have htrace : WordTrace (prefixWord ++ tailWord_6279009) baseStart_6279009 baseEnd_6279009 := by
    simpa [prefixWord, tailWord_6279009, baseEnd_6279009] using wordTrace_append hprefix tailTrace_6279009
  have hstable : (prefixWord ++ tailWord_6279009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279009).length < 2 ^ (prefixWord ++ tailWord_6279009).sum := by decide
  have hdescent : baseEnd_6279009 < baseStart_6279009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279049 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 1, 7]
def baseStart_6279049 : Nat := 118140960795 + 6279049 * 2 ^ 59
def prefixEnd_6279049 : Nat := 4983230072969 + 3 ^ 40 * 6279049 * 2
def baseEnd_6279049 : Nat := 1074723396711036308536895

theorem tailTrace_6279049 : CollatzResearch.WordTrace tailWord_6279049 prefixEnd_6279049 1074723396711036308536895 := by
  unfold tailWord_6279049
  simp only [CollatzResearch.WordTrace]
  refine ⟨229015731429085324038080201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152677154286056882692053467 229015731429085324038080201)
  ·
    refine ⟨171761798571813993028560151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229015731429085324038080201 171761798571813993028560151)
    ·
      refine ⟨257642697857720989542840227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171761798571813993028560151 257642697857720989542840227)
      ·
        refine ⟨386464046786581484314260341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257642697857720989542840227 386464046786581484314260341)
        ·
          refine ⟨36231004386242014154461907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 386464046786581484314260341 36231004386242014154461907)
          ·
            refine ⟨54346506579363021231692861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36231004386242014154461907 54346506579363021231692861)
            ·
              refine ⟨20379939967261132961884823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54346506579363021231692861 20379939967261132961884823)
              ·
                refine ⟨30569909950891699442827235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20379939967261132961884823 30569909950891699442827235)
                ·
                  refine ⟨45854864926337549164240853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30569909950891699442827235 45854864926337549164240853)
                  ·
                    refine ⟨1074723396711036308536895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45854864926337549164240853 1074723396711036308536895)
                    ·
                      rfl

theorem cell23_6279049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 7].length) (baseStart_6279049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279049 prefixEnd_6279049 := by exact prefixLift 6279049
  have htrace : WordTrace (prefixWord ++ tailWord_6279049) baseStart_6279049 baseEnd_6279049 := by
    simpa [prefixWord, tailWord_6279049, baseEnd_6279049] using wordTrace_append hprefix tailTrace_6279049
  have hstable : (prefixWord ++ tailWord_6279049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279049).length < 2 ^ (prefixWord ++ tailWord_6279049).sum := by decide
  have hdescent : baseEnd_6279049 < baseStart_6279049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279064 : List Nat := [2, 1, 2, 6, 1, 2, 1, 2, 2, 2, 2]
def baseStart_6279064 : Nat := 118140960795 + 6279064 * 2 ^ 59
def prefixEnd_6279064 : Nat := 4983230072969 + 3 ^ 40 * 6279064 * 2
def baseEnd_6279064 : Nat := 3224177892342926366923117

theorem tailTrace_6279064 : CollatzResearch.WordTrace tailWord_6279064 prefixEnd_6279064 3224177892342926366923117 := by
  unfold tailWord_6279064
  simp only [CollatzResearch.WordTrace]
  refine ⟨114508139262015490799938123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152677519016020654399917497 114508139262015490799938123)
  ·
    refine ⟨171762208893023236199907185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114508139262015490799938123 171762208893023236199907185)
    ·
      refine ⟨128821656669767427149930389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171762208893023236199907185 128821656669767427149930389)
      ·
        refine ⟨6038515156395348147652987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 128821656669767427149930389 6038515156395348147652987)
        ·
          refine ⟨9057772734593022221479481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6038515156395348147652987 9057772734593022221479481)
          ·
            refine ⟨6793329550944766666109611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9057772734593022221479481 6793329550944766666109611)
            ·
              refine ⟨10189994326417149999164417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6793329550944766666109611 10189994326417149999164417)
              ·
                refine ⟨7642495744812862499373313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10189994326417149999164417 7642495744812862499373313)
                ·
                  refine ⟨5731871808609646874529985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7642495744812862499373313 5731871808609646874529985)
                  ·
                    refine ⟨4298903856457235155897489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5731871808609646874529985 4298903856457235155897489)
                    ·
                      refine ⟨3224177892342926366923117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4298903856457235155897489 3224177892342926366923117)
                      ·
                        rfl

theorem cell23_6279064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_6279064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279064 prefixEnd_6279064 := by exact prefixLift 6279064
  have htrace : WordTrace (prefixWord ++ tailWord_6279064) baseStart_6279064 baseEnd_6279064 := by
    simpa [prefixWord, tailWord_6279064, baseEnd_6279064] using wordTrace_append hprefix tailTrace_6279064
  have hstable : (prefixWord ++ tailWord_6279064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279064).length < 2 ^ (prefixWord ++ tailWord_6279064).sum := by decide
  have hdescent : baseEnd_6279064 < baseStart_6279064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279070 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 7]
def baseStart_6279070 : Nat := 118140960795 + 6279070 * 2 ^ 59
def prefixEnd_6279070 : Nat := 4983230072969 + 3 ^ 40 * 6279070 * 2
def baseEnd_6279070 : Nat := 358242330358539260383121

theorem tailTrace_6279070 : CollatzResearch.WordTrace tailWord_6279070 prefixEnd_6279070 358242330358539260383121 := by
  unfold tailWord_6279070
  simp only [CollatzResearch.WordTrace]
  refine ⟨28627062170251155578074333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152677664908006163083063109 28627062170251155578074333)
  ·
    refine ⟨10735148313844183341777875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28627062170251155578074333 10735148313844183341777875)
    ·
      refine ⟨16102722470766275012666813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10735148313844183341777875 16102722470766275012666813)
      ·
        refine ⟨6038520926537353129750055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16102722470766275012666813 6038520926537353129750055)
        ·
          refine ⟨9057781389806029694625083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6038520926537353129750055 9057781389806029694625083)
          ·
            refine ⟨13586672084709044541937625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9057781389806029694625083 13586672084709044541937625)
            ·
              refine ⟨10190004063531783406453219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13586672084709044541937625 10190004063531783406453219)
              ·
                refine ⟨15285006095297675109679829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10190004063531783406453219 15285006095297675109679829)
                ·
                  refine ⟨358242330358539260383121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15285006095297675109679829 358242330358539260383121)
                  ·
                    rfl

theorem cell23_6279070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_6279070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279070 prefixEnd_6279070 := by exact prefixLift 6279070
  have htrace : WordTrace (prefixWord ++ tailWord_6279070) baseStart_6279070 baseEnd_6279070 := by
    simpa [prefixWord, tailWord_6279070, baseEnd_6279070] using wordTrace_append hprefix tailTrace_6279070
  have hstable : (prefixWord ++ tailWord_6279070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279070).length < 2 ^ (prefixWord ++ tailWord_6279070).sum := by decide
  have hdescent : baseEnd_6279070 < baseStart_6279070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279096 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 3, 4]
def baseStart_6279096 : Nat := 118140960795 + 6279096 * 2 ^ 59
def prefixEnd_6279096 : Nat := 4983230072969 + 3 ^ 40 * 6279096 * 2
def baseEnd_6279096 : Nat := 1074731441241290080574323

theorem tailTrace_6279096 : CollatzResearch.WordTrace tailWord_6279096 prefixEnd_6279096 1074731441241290080574323 := by
  unfold tailWord_6279096
  simp only [CollatzResearch.WordTrace]
  refine ⟨114508722829957525532520571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152678297106610034043360761 114508722829957525532520571)
  ·
    refine ⟨171763084244936288298780857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114508722829957525532520571 171763084244936288298780857)
    ·
      refine ⟨128822313183702216224085643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171763084244936288298780857 128822313183702216224085643)
      ·
        refine ⟨193233469775553324336128465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128822313183702216224085643 193233469775553324336128465)
        ·
          refine ⟨144925102331664993252096349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193233469775553324336128465 144925102331664993252096349)
          ·
            refine ⟨54346913374374372469536131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144925102331664993252096349 54346913374374372469536131)
            ·
              refine ⟨81520370061561558704304197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54346913374374372469536131 81520370061561558704304197)
              ·
                refine ⟨15285069386542792257057037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81520370061561558704304197 15285069386542792257057037)
                ·
                  refine ⟨5731901019953547096396389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15285069386542792257057037 5731901019953547096396389)
                  ·
                    refine ⟨1074731441241290080574323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5731901019953547096396389 1074731441241290080574323)
                    ·
                      rfl

theorem cell23_6279096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_6279096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279096 prefixEnd_6279096 := by exact prefixLift 6279096
  have htrace : WordTrace (prefixWord ++ tailWord_6279096) baseStart_6279096 baseEnd_6279096 := by
    simpa [prefixWord, tailWord_6279096, baseEnd_6279096] using wordTrace_append hprefix tailTrace_6279096
  have hstable : (prefixWord ++ tailWord_6279096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279096).length < 2 ^ (prefixWord ++ tailWord_6279096).sum := by decide
  have hdescent : baseEnd_6279096 < baseStart_6279096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279130 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 3, 4]
def baseStart_6279130 : Nat := 118140960795 + 6279130 * 2 ^ 59
def prefixEnd_6279130 : Nat := 4983230072969 + 3 ^ 40 * 6279130 * 2
def baseEnd_6279130 : Nat := 1074737260688707702899271

theorem tailTrace_6279130 : CollatzResearch.WordTrace tailWord_6279130 prefixEnd_6279130 1074737260688707702899271 := by
  unfold tailWord_6279130
  simp only [CollatzResearch.WordTrace]
  refine ⟨57254671435447968717944711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152679123827861249914519229 57254671435447968717944711)
  ·
    refine ⟨85882007153171953076917067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57254671435447968717944711 85882007153171953076917067)
    ·
      refine ⟨128823010729757929615375601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85882007153171953076917067 128823010729757929615375601)
      ·
        refine ⟨96617258047318447211531701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128823010729757929615375601 96617258047318447211531701)
        ·
          refine ⟨9057867941936104426081097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96617258047318447211531701 9057867941936104426081097)
          ·
            refine ⟨6793400956452078319560823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9057867941936104426081097 6793400956452078319560823)
            ·
              refine ⟨10190101434678117479341235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6793400956452078319560823 10190101434678117479341235)
              ·
                refine ⟨15285152152017176219011853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10190101434678117479341235 15285152152017176219011853)
                ·
                  refine ⟨5731932057006441082129445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15285152152017176219011853 5731932057006441082129445)
                  ·
                    refine ⟨1074737260688707702899271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5731932057006441082129445 1074737260688707702899271)
                    ·
                      rfl

theorem cell23_6279130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_6279130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279130 prefixEnd_6279130 := by exact prefixLift 6279130
  have htrace : WordTrace (prefixWord ++ tailWord_6279130) baseStart_6279130 baseEnd_6279130 := by
    simpa [prefixWord, tailWord_6279130, baseEnd_6279130] using wordTrace_append hprefix tailTrace_6279130
  have hstable : (prefixWord ++ tailWord_6279130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279130).length < 2 ^ (prefixWord ++ tailWord_6279130).sum := by decide
  have hdescent : baseEnd_6279130 < baseStart_6279130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279143 : List Nat := [1, 1, 5, 2, 3, 1, 1, 3, 6]
def baseStart_6279143 : Nat := 118140960795 + 6279143 * 2 ^ 59
def prefixEnd_6279143 : Nat := 4983230072969 + 3 ^ 40 * 6279143 * 2
def baseEnd_6279143 : Nat := 358246495257181284203917

theorem tailTrace_6279143 : CollatzResearch.WordTrace tailWord_6279143 prefixEnd_6279143 358246495257181284203917 := by
  unfold tailWord_6279143
  simp only [CollatzResearch.WordTrace]
  refine ⟨229019159890744778092002083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152679439927163185394668055 229019159890744778092002083)
  ·
    refine ⟨343528739836117167138003125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229019159890744778092002083 343528739836117167138003125)
    ·
      refine ⟨32205819359635984419187793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 343528739836117167138003125 32205819359635984419187793)
      ·
        refine ⟨24154364519726988314390845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32205819359635984419187793 24154364519726988314390845)
        ·
          refine ⟨9057886694897620617896567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24154364519726988314390845 9057886694897620617896567)
          ·
            refine ⟨13586830042346430926844851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9057886694897620617896567 13586830042346430926844851)
            ·
              refine ⟨20380245063519646390267277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13586830042346430926844851 20380245063519646390267277)
              ·
                refine ⟨7642591898819867396350229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20380245063519646390267277 7642591898819867396350229)
                ·
                  refine ⟨358246495257181284203917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7642591898819867396350229 358246495257181284203917)
                  ·
                    rfl

theorem cell23_6279143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 6].length) (baseStart_6279143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279143 prefixEnd_6279143 := by exact prefixLift 6279143
  have htrace : WordTrace (prefixWord ++ tailWord_6279143) baseStart_6279143 baseEnd_6279143 := by
    simpa [prefixWord, tailWord_6279143, baseEnd_6279143] using wordTrace_append hprefix tailTrace_6279143
  have hstable : (prefixWord ++ tailWord_6279143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279143).length < 2 ^ (prefixWord ++ tailWord_6279143).sum := by decide
  have hdescent : baseEnd_6279143 < baseStart_6279143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279163 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 2, 3, 2]
def baseStart_6279163 : Nat := 118140960795 + 6279163 * 2 ^ 59
def prefixEnd_6279163 : Nat := 4983230072969 + 3 ^ 40 * 6279163 * 2
def baseEnd_6279163 : Nat := 3224228726927721479585161

theorem tailTrace_6279163 : CollatzResearch.WordTrace tailWord_6279163 prefixEnd_6279163 3224228726927721479585161 := by
  unfold tailWord_6279163
  simp only [CollatzResearch.WordTrace]
  refine ⟨229019889350672321507730143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152679926233781547671820095 229019889350672321507730143)
  ·
    refine ⟨343529834026008482261595215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229019889350672321507730143 343529834026008482261595215)
    ·
      refine ⟨515294751039012723392392823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343529834026008482261595215 515294751039012723392392823)
      ·
        refine ⟨772942126558519085088589235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515294751039012723392392823 772942126558519085088589235)
        ·
          refine ⟨1159413189837778627632883853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 772942126558519085088589235 1159413189837778627632883853)
          ·
            refine ⟨434779946189166985362331445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1159413189837778627632883853 434779946189166985362331445)
            ·
              refine ⟨40760619955234404877718573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 434779946189166985362331445 40760619955234404877718573)
              ·
                refine ⟨15285232483212901829144465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40760619955234404877718573 15285232483212901829144465)
                ·
                  refine ⟨11463924362409676371858349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15285232483212901829144465 11463924362409676371858349)
                  ·
                    refine ⟨4298971635903628639446881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11463924362409676371858349 4298971635903628639446881)
                    ·
                      refine ⟨3224228726927721479585161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4298971635903628639446881 3224228726927721479585161)
                      ·
                        rfl

theorem cell23_6279163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 3, 2].length) (baseStart_6279163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279163 prefixEnd_6279163 := by exact prefixLift 6279163
  have htrace : WordTrace (prefixWord ++ tailWord_6279163) baseStart_6279163 baseEnd_6279163 := by
    simpa [prefixWord, tailWord_6279163, baseEnd_6279163] using wordTrace_append hprefix tailTrace_6279163
  have hstable : (prefixWord ++ tailWord_6279163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279163).length < 2 ^ (prefixWord ++ tailWord_6279163).sum := by decide
  have hdescent : baseEnd_6279163 < baseStart_6279163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279181 : List Nat := [1, 7, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_6279181 : Nat := 118140960795 + 6279181 * 2 ^ 59
def prefixEnd_6279181 : Nat := 4983230072969 + 3 ^ 40 * 6279181 * 2
def baseEnd_6279181 : Nat := 1074745989859834136386693

theorem tailTrace_6279181 : CollatzResearch.WordTrace tailWord_6279181 prefixEnd_6279181 1074745989859834136386693 := by
  unfold tailWord_6279181
  simp only [CollatzResearch.WordTrace]
  refine ⟨229020545864607110581885397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152680363909738073721256931 229020545864607110581885397)
  ·
    refine ⟨5367669043701729154262939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 229020545864607110581885397 5367669043701729154262939)
    ·
      refine ⟨8051503565552593731394409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5367669043701729154262939 8051503565552593731394409)
      ·
        refine ⟨6038627674164445298545807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8051503565552593731394409 6038627674164445298545807)
        ·
          refine ⟨9057941511246667947818711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6038627674164445298545807 9057941511246667947818711)
          ·
            refine ⟨13586912266870001921728067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9057941511246667947818711 13586912266870001921728067)
            ·
              refine ⟨20380368400305002882592101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13586912266870001921728067 20380368400305002882592101)
              ·
                refine ⟨3821319075057188040486019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20380368400305002882592101 3821319075057188040486019)
                ·
                  refine ⟨5731978612585782060729029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3821319075057188040486019 5731978612585782060729029)
                  ·
                    refine ⟨1074745989859834136386693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5731978612585782060729029 1074745989859834136386693)
                    ·
                      rfl

theorem cell23_6279181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_6279181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279181 prefixEnd_6279181 := by exact prefixLift 6279181
  have htrace : WordTrace (prefixWord ++ tailWord_6279181) baseStart_6279181 baseEnd_6279181 := by
    simpa [prefixWord, tailWord_6279181, baseEnd_6279181] using wordTrace_append hprefix tailTrace_6279181
  have hstable : (prefixWord ++ tailWord_6279181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279181).length < 2 ^ (prefixWord ++ tailWord_6279181).sum := by decide
  have hdescent : baseEnd_6279181 < baseStart_6279181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279187 : List Nat := [1, 1, 1, 2, 1, 4, 6, 2, 1, 1, 3]
def baseStart_6279187 : Nat := 118140960795 + 6279187 * 2 ^ 59
def prefixEnd_6279187 : Nat := 4983230072969 + 3 ^ 40 * 6279187 * 2
def baseEnd_6279187 : Nat := 3224241050463429385685051

theorem tailTrace_6279187 : CollatzResearch.WordTrace tailWord_6279187 prefixEnd_6279187 3224241050463429385685051 := by
  unfold tailWord_6279187
  simp only [CollatzResearch.WordTrace]
  refine ⟨229020764702585373606603815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152680509801723582404402543 229020764702585373606603815)
  ·
    refine ⟨343531147053878060409905723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229020764702585373606603815 343531147053878060409905723)
    ·
      refine ⟨515296720580817090614858585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343531147053878060409905723 515296720580817090614858585)
      ·
        refine ⟨386472540435612817961143939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515296720580817090614858585 386472540435612817961143939)
        ·
          refine ⟨579708810653419226941715909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386472540435612817961143939 579708810653419226941715909)
          ·
            refine ⟨108695401997516105051571733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 579708810653419226941715909 108695401997516105051571733)
            ·
              refine ⟨5095096968633567424292425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108695401997516105051571733 5095096968633567424292425)
              ·
                refine ⟨3821322726475175568219319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5095096968633567424292425 3821322726475175568219319)
                ·
                  refine ⟨5731984089712763352328979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3821322726475175568219319 5731984089712763352328979)
                  ·
                    refine ⟨8597976134569145028493469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5731984089712763352328979 8597976134569145028493469)
                    ·
                      refine ⟨3224241050463429385685051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8597976134569145028493469 3224241050463429385685051)
                      ·
                        rfl

theorem cell23_6279187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 1, 1, 3].length) (baseStart_6279187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279187 prefixEnd_6279187 := by exact prefixLift 6279187
  have htrace : WordTrace (prefixWord ++ tailWord_6279187) baseStart_6279187 baseEnd_6279187 := by
    simpa [prefixWord, tailWord_6279187, baseEnd_6279187] using wordTrace_append hprefix tailTrace_6279187
  have hstable : (prefixWord ++ tailWord_6279187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279187).length < 2 ^ (prefixWord ++ tailWord_6279187).sum := by decide
  have hdescent : baseEnd_6279187 < baseStart_6279187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279203 : List Nat := [1, 1, 1, 4, 3, 1, 1, 5, 2, 4]
def baseStart_6279203 : Nat := 118140960795 + 6279203 * 2 ^ 59
def prefixEnd_6279203 : Nat := 4983230072969 + 3 ^ 40 * 6279203 * 2
def baseEnd_6279203 : Nat := 1074749755384633774361659

theorem tailTrace_6279203 : CollatzResearch.WordTrace tailWord_6279203 prefixEnd_6279203 1074749755384633774361659 := by
  unfold tailWord_6279203
  simp only [CollatzResearch.WordTrace]
  refine ⟨229021348270527408339186263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152680898847018272226124175 229021348270527408339186263)
  ·
    refine ⟨343532022405791112508779395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229021348270527408339186263 343532022405791112508779395)
    ·
      refine ⟨515298033608686668763169093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343532022405791112508779395 515298033608686668763169093)
      ·
        refine ⟨96618381301628750393094205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 515298033608686668763169093 96618381301628750393094205)
        ·
          refine ⟨36231892988110781397410327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96618381301628750393094205 36231892988110781397410327)
          ·
            refine ⟨54347839482166172096115491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36231892988110781397410327 54347839482166172096115491)
            ·
              refine ⟨81521759223249258144173237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54347839482166172096115491 81521759223249258144173237)
              ·
                refine ⟨7642664927179617951016241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81521759223249258144173237 7642664927179617951016241)
                ·
                  refine ⟨5731998695384713463262181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7642664927179617951016241 5731998695384713463262181)
                  ·
                    refine ⟨1074749755384633774361659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5731998695384713463262181 1074749755384633774361659)
                    ·
                      rfl

theorem cell23_6279203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 4].length) (baseStart_6279203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279203 prefixEnd_6279203 := by exact prefixLift 6279203
  have htrace : WordTrace (prefixWord ++ tailWord_6279203) baseStart_6279203 baseEnd_6279203 := by
    simpa [prefixWord, tailWord_6279203, baseEnd_6279203] using wordTrace_append hprefix tailTrace_6279203
  have hstable : (prefixWord ++ tailWord_6279203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279203).length < 2 ^ (prefixWord ++ tailWord_6279203).sum := by decide
  have hdescent : baseEnd_6279203 < baseStart_6279203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279243 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 4, 1, 3]
def baseStart_6279243 : Nat := 118140960795 + 6279243 * 2 ^ 59
def prefixEnd_6279243 : Nat := 4983230072969 + 3 ^ 40 * 6279243 * 2
def baseEnd_6279243 : Nat := 3224269805380081166584793

theorem tailTrace_6279243 : CollatzResearch.WordTrace tailWord_6279243 prefixEnd_6279243 3224269805380081166584793 := by
  unfold tailWord_6279243
  simp only [CollatzResearch.WordTrace]
  refine ⟨229022807190382495170642383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152681871460254996780428255 229022807190382495170642383)
  ·
    refine ⟨343534210785573742755963575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229022807190382495170642383 343534210785573742755963575)
    ·
      refine ⟨515301316178360614133945363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343534210785573742755963575 515301316178360614133945363)
      ·
        refine ⟨772951974267540921200918045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515301316178360614133945363 772951974267540921200918045)
        ·
          refine ⟨289856990350327845450344267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 772951974267540921200918045 289856990350327845450344267)
          ·
            refine ⟨434785485525491768175516401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289856990350327845450344267 434785485525491768175516401)
            ·
              refine ⟨326089114144118826131637301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434785485525491768175516401 326089114144118826131637301)
              ·
                refine ⟨30570854451011139949840997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 326089114144118826131637301 30570854451011139949840997)
                ·
                  refine ⟨5732035209564588740595187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30570854451011139949840997 5732035209564588740595187)
                  ·
                    refine ⟨8598052814346883110892781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5732035209564588740595187 8598052814346883110892781)
                    ·
                      refine ⟨3224269805380081166584793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8598052814346883110892781 3224269805380081166584793)
                      ·
                        rfl

theorem cell23_6279243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 1, 3].length) (baseStart_6279243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279243 prefixEnd_6279243 := by exact prefixLift 6279243
  have htrace : WordTrace (prefixWord ++ tailWord_6279243) baseStart_6279243 baseEnd_6279243 := by
    simpa [prefixWord, tailWord_6279243, baseEnd_6279243] using wordTrace_append hprefix tailTrace_6279243
  have hstable : (prefixWord ++ tailWord_6279243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279243).length < 2 ^ (prefixWord ++ tailWord_6279243).sum := by decide
  have hdescent : baseEnd_6279243 < baseStart_6279243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279260 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_6279260 : Nat := 118140960795 + 6279260 * 2 ^ 59
def prefixEnd_6279260 : Nat := 4983230072969 + 3 ^ 40 * 6279260 * 2
def baseEnd_6279260 : Nat := 3224278534551207600072215

theorem tailTrace_6279260 : CollatzResearch.WordTrace tailWord_6279260 prefixEnd_6279260 3224278534551207600072215 := by
  unfold tailWord_6279260
  simp only [CollatzResearch.WordTrace]
  refine ⟨114511713615660453537005617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152682284820880604716007489 114511713615660453537005617)
  ·
    refine ⟨85883785211745340152754213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114511713615660453537005617 85883785211745340152754213)
    ·
      refine ⟨16103209727202251278641415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85883785211745340152754213 16103209727202251278641415)
      ·
        refine ⟨24154814590803376917962123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16103209727202251278641415 24154814590803376917962123)
        ·
          refine ⟨36232221886205065376943185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24154814590803376917962123 36232221886205065376943185)
          ·
            refine ⟨27174166414653799032707389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36232221886205065376943185 27174166414653799032707389)
            ·
              refine ⟨10190312405495174637265271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27174166414653799032707389 10190312405495174637265271)
              ·
                refine ⟨15285468608242761955897907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10190312405495174637265271 15285468608242761955897907)
                ·
                  refine ⟨22928202912364142933846861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15285468608242761955897907 22928202912364142933846861)
                  ·
                    refine ⟨8598076092136553600192573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22928202912364142933846861 8598076092136553600192573)
                    ·
                      refine ⟨3224278534551207600072215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8598076092136553600192573 3224278534551207600072215)
                      ·
                        rfl

theorem cell23_6279260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_6279260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279260 prefixEnd_6279260 := by exact prefixLift 6279260
  have htrace : WordTrace (prefixWord ++ tailWord_6279260) baseStart_6279260 baseEnd_6279260 := by
    simpa [prefixWord, tailWord_6279260, baseEnd_6279260] using wordTrace_append hprefix tailTrace_6279260
  have hstable : (prefixWord ++ tailWord_6279260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279260).length < 2 ^ (prefixWord ++ tailWord_6279260).sum := by decide
  have hdescent : baseEnd_6279260 < baseStart_6279260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279317 : List Nat := [1, 3, 2, 1, 1, 1, 5, 3, 2, 2, 2]
def baseStart_6279317 : Nat := 118140960795 + 6279317 * 2 ^ 59
def prefixEnd_6279317 : Nat := 4983230072969 + 3 ^ 40 * 6279317 * 2
def baseEnd_6279317 : Nat := 3224307802948513877059453

theorem tailTrace_6279317 : CollatzResearch.WordTrace tailWord_6279317 prefixEnd_6279317 3224307802948513877059453 := by
  unfold tailWord_6279317
  simp only [CollatzResearch.WordTrace]
  refine ⟨229025506192114405808836205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152683670794742937205890803 229025506192114405808836205)
  ·
    refine ⟨85884564822042902178313577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229025506192114405808836205 85884564822042902178313577)
    ·
      refine ⟨64413423616532176633735183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85884564822042902178313577 64413423616532176633735183)
      ·
        refine ⟨96620135424798264950602775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64413423616532176633735183 96620135424798264950602775)
        ·
          refine ⟨144930203137197397425904163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96620135424798264950602775 144930203137197397425904163)
          ·
            refine ⟨217395304705796096138856245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144930203137197397425904163 217395304705796096138856245)
            ·
              refine ⟨20380809816168384013017773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 217395304705796096138856245 20380809816168384013017773)
              ·
                refine ⟨7642803681063144004881665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20380809816168384013017773 7642803681063144004881665)
                ·
                  refine ⟨5732102760797358003661249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7642803681063144004881665 5732102760797358003661249)
                  ·
                    refine ⟨4299077070598018502745937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5732102760797358003661249 4299077070598018502745937)
                    ·
                      refine ⟨3224307802948513877059453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4299077070598018502745937 3224307802948513877059453)
                      ·
                        rfl

theorem cell23_6279317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_6279317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279317 prefixEnd_6279317 := by exact prefixLift 6279317
  have htrace : WordTrace (prefixWord ++ tailWord_6279317) baseStart_6279317 baseEnd_6279317 := by
    simpa [prefixWord, tailWord_6279317, baseEnd_6279317] using wordTrace_append hprefix tailTrace_6279317
  have hstable : (prefixWord ++ tailWord_6279317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279317).length < 2 ^ (prefixWord ++ tailWord_6279317).sum := by decide
  have hdescent : baseEnd_6279317 < baseStart_6279317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279353 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 2, 5]
def baseStart_6279353 : Nat := 118140960795 + 6279353 * 2 ^ 59
def prefixEnd_6279353 : Nat := 4983230072969 + 3 ^ 40 * 6279353 * 2
def baseEnd_6279353 : Nat := 1074775429417358578736429

theorem tailTrace_6279353 : CollatzResearch.WordTrace tailWord_6279353 prefixEnd_6279353 1074775429417358578736429 := by
  unfold tailWord_6279353
  simp only [CollatzResearch.WordTrace]
  refine ⟨229026819219983983957146713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152684546146655989304764475 229026819219983983957146713)
  ·
    refine ⟨171770114414987987967860035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229026819219983983957146713 171770114414987987967860035)
    ·
      refine ⟨257655171622481981951790053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171770114414987987967860035 257655171622481981951790053)
      ·
        refine ⟨48310344679215371615960635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257655171622481981951790053 48310344679215371615960635)
        ·
          refine ⟨72465517018823057423940953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48310344679215371615960635 72465517018823057423940953)
          ·
            refine ⟨54349137764117293067955715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72465517018823057423940953 54349137764117293067955715)
            ·
              refine ⟨81523706646175939601933573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54349137764117293067955715 81523706646175939601933573)
              ·
                refine ⟨15285694996157988675362545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81523706646175939601933573 15285694996157988675362545)
                ·
                  refine ⟨11464271247118491506521909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15285694996157988675362545 11464271247118491506521909)
                  ·
                    refine ⟨1074775429417358578736429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11464271247118491506521909 1074775429417358578736429)
                    ·
                      rfl

theorem cell23_6279353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 5].length) (baseStart_6279353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279353 prefixEnd_6279353 := by exact prefixLift 6279353
  have htrace : WordTrace (prefixWord ++ tailWord_6279353) baseStart_6279353 baseEnd_6279353 := by
    simpa [prefixWord, tailWord_6279353, baseEnd_6279353] using wordTrace_append hprefix tailTrace_6279353
  have hstable : (prefixWord ++ tailWord_6279353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279353).length < 2 ^ (prefixWord ++ tailWord_6279353).sum := by decide
  have hdescent : baseEnd_6279353 < baseStart_6279353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279360 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 2, 5, 2]
def baseStart_6279360 : Nat := 118140960795 + 6279360 * 2 ^ 59
def prefixEnd_6279360 : Nat := 4983230072969 + 3 ^ 40 * 6279360 * 2
def baseEnd_6279360 : Nat := 3224329882616657208821755

theorem tailTrace_6279360 : CollatzResearch.WordTrace tailWord_6279360 prefixEnd_6279360 3224329882616657208821755 := by
  unfold tailWord_6279360
  simp only [CollatzResearch.WordTrace]
  refine ⟨114513537265479312076325767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152684716353972416101767689 114513537265479312076325767)
  ·
    refine ⟨171770305898218968114488651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114513537265479312076325767 171770305898218968114488651)
    ·
      refine ⟨257655458847328452171732977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171770305898218968114488651 257655458847328452171732977)
      ·
        refine ⟨193241594135496339128799733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257655458847328452171732977 193241594135496339128799733)
        ·
          refine ⟨18116399450202781793324975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193241594135496339128799733 18116399450202781793324975)
          ·
            refine ⟨27174599175304172689987463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18116399450202781793324975 27174599175304172689987463)
            ·
              refine ⟨40761898762956259034981195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27174599175304172689987463 40761898762956259034981195)
              ·
                refine ⟨61142848144434388552471793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40761898762956259034981195 61142848144434388552471793)
                ·
                  refine ⟨45857136108325791414353845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61142848144434388552471793 45857136108325791414353845)
                  ·
                    refine ⟨4299106510155542945095673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45857136108325791414353845 4299106510155542945095673)
                    ·
                      refine ⟨3224329882616657208821755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4299106510155542945095673 3224329882616657208821755)
                      ·
                        rfl

theorem cell23_6279360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 2, 5, 2].length) (baseStart_6279360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279360 prefixEnd_6279360 := by exact prefixLift 6279360
  have htrace : WordTrace (prefixWord ++ tailWord_6279360) baseStart_6279360 baseEnd_6279360 := by
    simpa [prefixWord, tailWord_6279360, baseEnd_6279360] using wordTrace_append hprefix tailTrace_6279360
  have hstable : (prefixWord ++ tailWord_6279360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279360).length < 2 ^ (prefixWord ++ tailWord_6279360).sum := by decide
  have hdescent : baseEnd_6279360 < baseStart_6279360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279443 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 3, 5]
def baseStart_6279443 : Nat := 118140960795 + 6279443 * 2 ^ 59
def prefixEnd_6279443 : Nat := 4983230072969 + 3 ^ 40 * 6279443 * 2
def baseEnd_6279443 : Nat := 1074790833836993461361291

theorem tailTrace_6279443 : CollatzResearch.WordTrace tailWord_6279443 prefixEnd_6279443 1074790833836993461361291 := by
  unfold tailWord_6279443
  simp only [CollatzResearch.WordTrace]
  refine ⟨229030101789657929327922983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152686734526438619551948655 229030101789657929327922983)
  ·
    refine ⟨343545152684486893991884475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229030101789657929327922983 343545152684486893991884475)
    ·
      refine ⟨515317729026730340987826713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343545152684486893991884475 515317729026730340987826713)
      ·
        refine ⟨386488296770047755740870035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515317729026730340987826713 386488296770047755740870035)
        ·
          refine ⟨579732445155071633611305053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386488296770047755740870035 579732445155071633611305053)
          ·
            refine ⟨217399666933151862604239395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 579732445155071633611305053 217399666933151862604239395)
            ·
              refine ⟨326099500399727793906359093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217399666933151862604239395 326099500399727793906359093)
              ·
                refine ⟨30571828162474480678721165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 326099500399727793906359093 30571828162474480678721165)
                ·
                  refine ⟨11464435560927930254520437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30571828162474480678721165 11464435560927930254520437)
                  ·
                    refine ⟨1074790833836993461361291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11464435560927930254520437 1074790833836993461361291)
                    ·
                      rfl

theorem cell23_6279443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 5].length) (baseStart_6279443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279443 prefixEnd_6279443 := by exact prefixLift 6279443
  have htrace : WordTrace (prefixWord ++ tailWord_6279443) baseStart_6279443 baseEnd_6279443 := by
    simpa [prefixWord, tailWord_6279443, baseEnd_6279443] using wordTrace_append hprefix tailTrace_6279443
  have hstable : (prefixWord ++ tailWord_6279443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279443).length < 2 ^ (prefixWord ++ tailWord_6279443).sum := by decide
  have hdescent : baseEnd_6279443 < baseStart_6279443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279497 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 5, 2, 2]
def baseStart_6279497 : Nat := 118140960795 + 6279497 * 2 ^ 59
def prefixEnd_6279497 : Nat := 4983230072969 + 3 ^ 40 * 6279497 * 2
def baseEnd_6279497 : Nat := 3224400229466323172808625

theorem tailTrace_6279497 : CollatzResearch.WordTrace tailWord_6279497 prefixEnd_6279497 3224400229466323172808625 := by
  unfold tailWord_6279497
  simp only [CollatzResearch.WordTrace]
  refine ⟨229032071331462296550388745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152688047554308197700259163 229032071331462296550388745)
  ·
    refine ⟨171774053498596722412791559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229032071331462296550388745 171774053498596722412791559)
    ·
      refine ⟨257661080247895083619187339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171774053498596722412791559 257661080247895083619187339)
      ·
        refine ⟨386491620371842625428781009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257661080247895083619187339 386491620371842625428781009)
        ·
          refine ⟨289868715278881969071585757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386491620371842625428781009 289868715278881969071585757)
          ·
            refine ⟨108700768229580738401844659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289868715278881969071585757 108700768229580738401844659)
            ·
              refine ⟨163051152344371107602766989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108700768229580738401844659 163051152344371107602766989)
              ·
                refine ⟨61144182129139165351037621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163051152344371107602766989 61144182129139165351037621)
                ·
                  refine ⟨5732267074606796751659777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61144182129139165351037621 5732267074606796751659777)
                  ·
                    refine ⟨4299200305955097563744833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5732267074606796751659777 4299200305955097563744833)
                    ·
                      refine ⟨3224400229466323172808625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4299200305955097563744833 3224400229466323172808625)
                      ·
                        rfl

theorem cell23_6279497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 2, 2].length) (baseStart_6279497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279497 prefixEnd_6279497 := by exact prefixLift 6279497
  have htrace : WordTrace (prefixWord ++ tailWord_6279497) baseStart_6279497 baseEnd_6279497 := by
    simpa [prefixWord, tailWord_6279497, baseEnd_6279497] using wordTrace_append hprefix tailTrace_6279497
  have hstable : (prefixWord ++ tailWord_6279497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279497).length < 2 ^ (prefixWord ++ tailWord_6279497).sum := by decide
  have hdescent : baseEnd_6279497 < baseStart_6279497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279520 : List Nat := [2, 1, 1, 3, 6, 10]
def baseStart_6279520 : Nat := 118140960795 + 6279520 * 2 ^ 59
def prefixEnd_6279520 : Nat := 4983230072969 + 3 ^ 40 * 6279520 * 2
def baseEnd_6279520 : Nat := 13269185347824594991033

theorem tailTrace_6279520 : CollatzResearch.WordTrace tailWord_6279520 prefixEnd_6279520 13269185347824594991033 := by
  unfold tailWord_6279520
  simp only [CollatzResearch.WordTrace]
  refine ⟨114516455105189485739238007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152688606806919314318984009 114516455105189485739238007)
  ·
    refine ⟨171774682657784228608857011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114516455105189485739238007 171774682657784228608857011)
    ·
      refine ⟨257662023986676342913285517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171774682657784228608857011 257662023986676342913285517)
      ·
        refine ⟨96623258995003628592482069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257662023986676342913285517 96623258995003628592482069)
        ·
          refine ⟨4529215265390795090272597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96623258995003628592482069 4529215265390795090272597)
          ·
            refine ⟨13269185347824594991033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4529215265390795090272597 13269185347824594991033)
            ·
              rfl

theorem cell23_6279520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 10].length) (baseStart_6279520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279520 prefixEnd_6279520 := by exact prefixLift 6279520
  have htrace : WordTrace (prefixWord ++ tailWord_6279520) baseStart_6279520 baseEnd_6279520 := by
    simpa [prefixWord, tailWord_6279520, baseEnd_6279520] using wordTrace_append hprefix tailTrace_6279520
  have hstable : (prefixWord ++ tailWord_6279520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279520).length < 2 ^ (prefixWord ++ tailWord_6279520).sum := by decide
  have hdescent : baseEnd_6279520 < baseStart_6279520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279547 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 3]
def baseStart_6279547 : Nat := 118140960795 + 6279547 * 2 ^ 59
def prefixEnd_6279547 : Nat := 4983230072969 + 3 ^ 40 * 6279547 * 2
def baseEnd_6279547 : Nat := 3224425903499047977183395

theorem tailTrace_6279547 : CollatzResearch.WordTrace tailWord_6279547 prefixEnd_6279547 3224425903499047977183395 := by
  unfold tailWord_6279547
  simp only [CollatzResearch.WordTrace]
  refine ⟨229033894981281155089708895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152689263320854103393139263 229033894981281155089708895)
  ·
    refine ⟨343550842471921732634563343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229033894981281155089708895 343550842471921732634563343)
    ·
      refine ⟨515326263707882598951845015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343550842471921732634563343 515326263707882598951845015)
      ·
        refine ⟨772989395561823898427767523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515326263707882598951845015 772989395561823898427767523)
        ·
          refine ⟨1159484093342735847641651285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 772989395561823898427767523 1159484093342735847641651285)
          ·
            refine ⟨13587704218860185714550601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1159484093342735847641651285 13587704218860185714550601)
            ·
              refine ⟨10190778164145139285912951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13587704218860185714550601 10190778164145139285912951)
              ·
                refine ⟨15286167246217708928869427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10190778164145139285912951 15286167246217708928869427)
                ·
                  refine ⟨22929250869326563393304141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15286167246217708928869427 22929250869326563393304141)
                  ·
                    refine ⟨8598469075997461272489053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22929250869326563393304141 8598469075997461272489053)
                    ·
                      refine ⟨3224425903499047977183395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8598469075997461272489053 3224425903499047977183395)
                      ·
                        rfl

theorem cell23_6279547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 3].length) (baseStart_6279547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279547 prefixEnd_6279547 := by exact prefixLift 6279547
  have htrace : WordTrace (prefixWord ++ tailWord_6279547) baseStart_6279547 baseEnd_6279547 := by
    simpa [prefixWord, tailWord_6279547, baseEnd_6279547] using wordTrace_append hprefix tailTrace_6279547
  have hstable : (prefixWord ++ tailWord_6279547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279547).length < 2 ^ (prefixWord ++ tailWord_6279547).sum := by decide
  have hdescent : baseEnd_6279547 < baseStart_6279547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279560 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_6279560 : Nat := 118140960795 + 6279560 * 2 ^ 59
def prefixEnd_6279560 : Nat := 4983230072969 + 3 ^ 40 * 6279560 * 2
def baseEnd_6279560 : Nat := 3224432578747556426320835

theorem tailTrace_6279560 : CollatzResearch.WordTrace tailWord_6279560 prefixEnd_6279560 3224432578747556426320835 := by
  unfold tailWord_6279560
  simp only [CollatzResearch.WordTrace]
  refine ⟨114517184565117029154966067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152689579420156038873288089 114517184565117029154966067)
  ·
    refine ⟨171775776847675543732449101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114517184565117029154966067 171775776847675543732449101)
    ·
      refine ⟨64415916317878328899668413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171775776847675543732449101 64415916317878328899668413)
      ·
        refine ⟨24155968619204373337375655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64415916317878328899668413 24155968619204373337375655)
        ·
          refine ⟨36233952928806560006063483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24155968619204373337375655 36233952928806560006063483)
          ·
            refine ⟨54350929393209840009095225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36233952928806560006063483 54350929393209840009095225)
            ·
              refine ⟨40763197044907380006821419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54350929393209840009095225 40763197044907380006821419)
              ·
                refine ⟨61144795567361070010232129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40763197044907380006821419 61144795567361070010232129)
                ·
                  refine ⟨45858596675520802507674097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61144795567361070010232129 45858596675520802507674097)
                  ·
                    refine ⟨34393947506640601880755573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45858596675520802507674097 34393947506640601880755573)
                    ·
                      refine ⟨3224432578747556426320835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34393947506640601880755573 3224432578747556426320835)
                      ·
                        rfl

theorem cell23_6279560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_6279560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279560 prefixEnd_6279560 := by exact prefixLift 6279560
  have htrace : WordTrace (prefixWord ++ tailWord_6279560) baseStart_6279560 baseEnd_6279560 := by
    simpa [prefixWord, tailWord_6279560, baseEnd_6279560] using wordTrace_append hprefix tailTrace_6279560
  have hstable : (prefixWord ++ tailWord_6279560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279560).length < 2 ^ (prefixWord ++ tailWord_6279560).sum := by decide
  have hdescent : baseEnd_6279560 < baseStart_6279560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279638 : List Nat := [5, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_6279638 : Nat := 118140960795 + 6279638 * 2 ^ 59
def prefixEnd_6279638 : Nat := 4983230072969 + 3 ^ 40 * 6279638 * 2
def baseEnd_6279638 : Nat := 3224472630238607121145477

theorem tailTrace_6279638 : CollatzResearch.WordTrace tailWord_6279638 prefixEnd_6279638 3224472630238607121145477 := by
  unfold tailWord_6279638
  simp only [CollatzResearch.WordTrace]
  refine ⟨14314825876496967351954473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152691476015967651754181045 14314825876496967351954473)
  ·
    refine ⟨10736119407372725513965855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14314825876496967351954473 10736119407372725513965855)
    ·
      refine ⟨16104179111059088270948783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10736119407372725513965855 16104179111059088270948783)
      ·
        refine ⟨24156268666588632406423175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16104179111059088270948783 24156268666588632406423175)
        ·
          refine ⟨36234402999882948609634763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24156268666588632406423175 36234402999882948609634763)
          ·
            refine ⟨54351604499824422914452145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36234402999882948609634763 54351604499824422914452145)
            ·
              refine ⟨40763703374868317185839109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54351604499824422914452145 40763703374868317185839109)
              ·
                refine ⟨7643194382787809472344833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40763703374868317185839109 7643194382787809472344833)
                ·
                  refine ⟨5732395787090857104258625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7643194382787809472344833 5732395787090857104258625)
                  ·
                    refine ⟨4299296840318142828193969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5732395787090857104258625 4299296840318142828193969)
                    ·
                      refine ⟨3224472630238607121145477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4299296840318142828193969 3224472630238607121145477)
                      ·
                        rfl

theorem cell23_6279638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_6279638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279638 prefixEnd_6279638 := by exact prefixLift 6279638
  have htrace : WordTrace (prefixWord ++ tailWord_6279638) baseStart_6279638 baseEnd_6279638 := by
    simpa [prefixWord, tailWord_6279638, baseEnd_6279638] using wordTrace_append hprefix tailTrace_6279638
  have hstable : (prefixWord ++ tailWord_6279638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279638).length < 2 ^ (prefixWord ++ tailWord_6279638).sum := by decide
  have hdescent : baseEnd_6279638 < baseStart_6279638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279694 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_6279694 : Nat := 118140960795 + 6279694 * 2 ^ 59
def prefixEnd_6279694 : Nat := 4983230072969 + 3 ^ 40 * 6279694 * 2
def baseEnd_6279694 : Nat := 3224501385155258902045219

theorem tailTrace_6279694 : CollatzResearch.WordTrace tailWord_6279694 prefixEnd_6279694 3224501385155258902045219 := by
  unfold tailWord_6279694
  simp only [CollatzResearch.WordTrace]
  refine ⟨28629907063968574899413767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152692837674499066130206757 28629907063968574899413767)
  ·
    refine ⟨42944860595952862349120651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28629907063968574899413767 42944860595952862349120651)
    ·
      refine ⟨64417290893929293523680977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42944860595952862349120651 64417290893929293523680977)
      ·
        refine ⟨48312968170446970142760733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64417290893929293523680977 48312968170446970142760733)
        ·
          refine ⟨18117363063917613803535275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48312968170446970142760733 18117363063917613803535275)
          ·
            refine ⟨27176044595876420705302913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18117363063917613803535275 27176044595876420705302913)
            ·
              refine ⟨20382033446907315528977185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27176044595876420705302913 20382033446907315528977185)
              ·
                refine ⟨15286525085180486646732889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20382033446907315528977185 15286525085180486646732889)
                ·
                  refine ⟨11464893813885364985049667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15286525085180486646732889 11464893813885364985049667)
                  ·
                    refine ⟨17197340720828047477574501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11464893813885364985049667 17197340720828047477574501)
                    ·
                      refine ⟨3224501385155258902045219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17197340720828047477574501 3224501385155258902045219)
                      ·
                        rfl

theorem cell23_6279694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_6279694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279694 prefixEnd_6279694 := by exact prefixLift 6279694
  have htrace : WordTrace (prefixWord ++ tailWord_6279694) baseStart_6279694 baseEnd_6279694 := by
    simpa [prefixWord, tailWord_6279694, baseEnd_6279694] using wordTrace_append hprefix tailTrace_6279694
  have hstable : (prefixWord ++ tailWord_6279694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279694).length < 2 ^ (prefixWord ++ tailWord_6279694).sum := by decide
  have hdescent : baseEnd_6279694 < baseStart_6279694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279697 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 3]
def baseStart_6279697 : Nat := 118140960795 + 6279697 * 2 ^ 59
def prefixEnd_6279697 : Nat := 4983230072969 + 3 ^ 40 * 6279697 * 2
def baseEnd_6279697 : Nat := 3224502925597222390307705

theorem tailTrace_6279697 : CollatzResearch.WordTrace tailWord_6279697 prefixEnd_6279697 3224502925597222390307705 := by
  unfold tailWord_6279697
  simp only [CollatzResearch.WordTrace]
  refine ⟨229039365930737730707669345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152692910620491820471779563 229039365930737730707669345)
  ·
    refine ⟨171779524448053298030752009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229039365930737730707669345 171779524448053298030752009)
    ·
      refine ⟨128834643336039973523064007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171779524448053298030752009 128834643336039973523064007)
      ·
        refine ⟨193251965004059960284596011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128834643336039973523064007 193251965004059960284596011)
        ·
          refine ⟨289877947506089940426894017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193251965004059960284596011 289877947506089940426894017)
          ·
            refine ⟨217408460629567455320170513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289877947506089940426894017 217408460629567455320170513)
            ·
              refine ⟨163056345472175591490127885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217408460629567455320170513 163056345472175591490127885)
              ·
                refine ⟨61146129552065846808797957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163056345472175591490127885 61146129552065846808797957)
                ·
                  refine ⟨11464899291012346276649617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61146129552065846808797957 11464899291012346276649617)
                  ·
                    refine ⟨8598674468259259707487213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11464899291012346276649617 8598674468259259707487213)
                    ·
                      refine ⟨3224502925597222390307705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8598674468259259707487213 3224502925597222390307705)
                      ·
                        rfl

theorem cell23_6279697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_6279697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279697 prefixEnd_6279697 := by exact prefixLift 6279697
  have htrace : WordTrace (prefixWord ++ tailWord_6279697) baseStart_6279697 baseEnd_6279697 := by
    simpa [prefixWord, tailWord_6279697, baseEnd_6279697] using wordTrace_append hprefix tailTrace_6279697
  have hstable : (prefixWord ++ tailWord_6279697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279697).length < 2 ^ (prefixWord ++ tailWord_6279697).sum := by decide
  have hdescent : baseEnd_6279697 < baseStart_6279697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279717 : List Nat := [1, 3, 1, 2, 2, 1, 4, 3, 6]
def baseStart_6279717 : Nat := 118140960795 + 6279717 * 2 ^ 59
def prefixEnd_6279717 : Nat := 4983230072969 + 3 ^ 40 * 6279717 * 2
def baseEnd_6279717 : Nat := 358279243912256923561957

theorem tailTrace_6279717 : CollatzResearch.WordTrace tailWord_6279717 prefixEnd_6279717 358279243912256923561957 := by
  unfold tailWord_6279717
  simp only [CollatzResearch.WordTrace]
  refine ⟨229040095390665274123397405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152693396927110182748931603 229040095390665274123397405)
  ·
    refine ⟨85890035771499477796274027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229040095390665274123397405 85890035771499477796274027)
    ·
      refine ⟨128835053657249216694411041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85890035771499477796274027 128835053657249216694411041)
      ·
        refine ⟨96626290242936912520808281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128835053657249216694411041 96626290242936912520808281)
        ·
          refine ⟨72469717682202684390606211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96626290242936912520808281 72469717682202684390606211)
          ·
            refine ⟨108704576523304026585909317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72469717682202684390606211 108704576523304026585909317)
            ·
              refine ⟨20382108098119504984857997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108704576523304026585909317 20382108098119504984857997)
              ·
                refine ⟨7643290536794814369321749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20382108098119504984857997 7643290536794814369321749)
                ·
                  refine ⟨358279243912256923561957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7643290536794814369321749 358279243912256923561957)
                  ·
                    rfl

theorem cell23_6279717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 6].length) (baseStart_6279717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279717 prefixEnd_6279717 := by exact prefixLift 6279717
  have htrace : WordTrace (prefixWord ++ tailWord_6279717) baseStart_6279717 baseEnd_6279717 := by
    simpa [prefixWord, tailWord_6279717, baseEnd_6279717] using wordTrace_append hprefix tailTrace_6279717
  have hstable : (prefixWord ++ tailWord_6279717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279717).length < 2 ^ (prefixWord ++ tailWord_6279717).sum := by decide
  have hdescent : baseEnd_6279717 < baseStart_6279717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279725 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_6279725 : Nat := 118140960795 + 6279725 * 2 ^ 59
def prefixEnd_6279725 : Nat := 4983230072969 + 3 ^ 40 * 6279725 * 2
def baseEnd_6279725 : Nat := 1074839101018516093585859

theorem tailTrace_6279725 : CollatzResearch.WordTrace tailWord_6279725 prefixEnd_6279725 1074839101018516093585859 := by
  unfold tailWord_6279725
  simp only [CollatzResearch.WordTrace]
  refine ⟨229040387174636291489688629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152693591449757527659792419 229040387174636291489688629)
  ·
    refine ⟨21472536297622152327158309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229040387174636291489688629 21472536297622152327158309)
    ·
      refine ⟨4026100555804153561342183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21472536297622152327158309 4026100555804153561342183)
      ·
        refine ⟨6039150833706230342013275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4026100555804153561342183 6039150833706230342013275)
        ·
          refine ⟨9058726250559345513019913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6039150833706230342013275 9058726250559345513019913)
          ·
            refine ⟨6794044687919509134764935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9058726250559345513019913 6794044687919509134764935)
            ·
              refine ⟨10191067031879263702147403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6794044687919509134764935 10191067031879263702147403)
              ·
                refine ⟨15286600547818895553221105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10191067031879263702147403 15286600547818895553221105)
                ·
                  refine ⟨11464950410864171664915829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15286600547818895553221105 11464950410864171664915829)
                  ·
                    refine ⟨1074839101018516093585859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11464950410864171664915829 1074839101018516093585859)
                    ·
                      rfl

theorem cell23_6279725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_6279725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279725 prefixEnd_6279725 := by exact prefixLift 6279725
  have htrace : WordTrace (prefixWord ++ tailWord_6279725) baseStart_6279725 baseEnd_6279725 := by
    simpa [prefixWord, tailWord_6279725, baseEnd_6279725] using wordTrace_append hprefix tailTrace_6279725
  have hstable : (prefixWord ++ tailWord_6279725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279725).length < 2 ^ (prefixWord ++ tailWord_6279725).sum := by decide
  have hdescent : baseEnd_6279725 < baseStart_6279725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279761 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 3, 1, 3]
def baseStart_6279761 : Nat := 118140960795 + 6279761 * 2 ^ 59
def prefixEnd_6279761 : Nat := 4983230072969 + 3 ^ 40 * 6279761 * 2
def baseEnd_6279761 : Nat := 3224535788359110139907411

theorem tailTrace_6279761 : CollatzResearch.WordTrace tailWord_6279761 prefixEnd_6279761 3224535788359110139907411 := by
  unfold tailWord_6279761
  simp only [CollatzResearch.WordTrace]
  refine ⟨229041700202505869637999137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152694466801670579758666091 229041700202505869637999137)
  ·
    refine ⟨171781275151879402228499353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229041700202505869637999137 171781275151879402228499353)
    ·
      refine ⟨128835956363909551671374515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171781275151879402228499353 128835956363909551671374515)
      ·
        refine ⟨193253934545864327507061773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128835956363909551671374515 193253934545864327507061773)
        ·
          refine ⟨72470225454699122815148165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193253934545864327507061773 72470225454699122815148165)
          ·
            refine ⟨13588167272756085527840281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72470225454699122815148165 13588167272756085527840281)
            ·
              refine ⟨10191125454567064145880211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13588167272756085527840281 10191125454567064145880211)
              ·
                refine ⟨15286688181850596218820317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10191125454567064145880211 15286688181850596218820317)
                ·
                  refine ⟨5732508068193973582057619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15286688181850596218820317 5732508068193973582057619)
                  ·
                    refine ⟨8598762102290960373086429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5732508068193973582057619 8598762102290960373086429)
                    ·
                      refine ⟨3224535788359110139907411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8598762102290960373086429 3224535788359110139907411)
                      ·
                        rfl

theorem cell23_6279761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 1, 3].length) (baseStart_6279761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279761 prefixEnd_6279761 := by exact prefixLift 6279761
  have htrace : WordTrace (prefixWord ++ tailWord_6279761) baseStart_6279761 baseEnd_6279761 := by
    simpa [prefixWord, tailWord_6279761, baseEnd_6279761] using wordTrace_append hprefix tailTrace_6279761
  have hstable : (prefixWord ++ tailWord_6279761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279761).length < 2 ^ (prefixWord ++ tailWord_6279761).sum := by decide
  have hdescent : baseEnd_6279761 < baseStart_6279761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279781 : List Nat := [1, 3, 1, 3, 4, 1, 2, 2, 1, 5]
def baseStart_6279781 : Nat := 118140960795 + 6279781 * 2 ^ 59
def prefixEnd_6279781 : Nat := 4983230072969 + 3 ^ 40 * 6279781 * 2
def baseEnd_6279781 : Nat := 1074848685990733353885773

theorem tailTrace_6279781 : CollatzResearch.WordTrace tailWord_6279781 prefixEnd_6279781 1074848685990733353885773 := by
  unfold tailWord_6279781
  simp only [CollatzResearch.WordTrace]
  refine ⟨229042429662433413053727197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152694953108288942035818131 229042429662433413053727197)
  ·
    refine ⟨85890911123412529895147699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229042429662433413053727197 85890911123412529895147699)
    ·
      refine ⟨128836366685118794842721549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85890911123412529895147699 128836366685118794842721549)
      ·
        refine ⟨48313637506919548066020581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128836366685118794842721549 48313637506919548066020581)
        ·
          refine ⟨9058807032547415262378859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48313637506919548066020581 9058807032547415262378859)
          ·
            refine ⟨13588210548821122893568289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9058807032547415262378859 13588210548821122893568289)
            ·
              refine ⟨10191157911615842170176217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13588210548821122893568289 10191157911615842170176217)
              ·
                refine ⟨7643368433711881627632163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10191157911615842170176217 7643368433711881627632163)
                ·
                  refine ⟨11465052650567822441448245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7643368433711881627632163 11465052650567822441448245)
                  ·
                    refine ⟨1074848685990733353885773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11465052650567822441448245 1074848685990733353885773)
                    ·
                      rfl

theorem cell23_6279781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_6279781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279781 prefixEnd_6279781 := by exact prefixLift 6279781
  have htrace : WordTrace (prefixWord ++ tailWord_6279781) baseStart_6279781 baseEnd_6279781 := by
    simpa [prefixWord, tailWord_6279781, baseEnd_6279781] using wordTrace_append hprefix tailTrace_6279781
  have hstable : (prefixWord ++ tailWord_6279781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279781).length < 2 ^ (prefixWord ++ tailWord_6279781).sum := by decide
  have hdescent : baseEnd_6279781 < baseStart_6279781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279828 : List Nat := [2, 4, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_6279828 : Nat := 118140960795 + 6279828 * 2 ^ 59
def prefixEnd_6279828 : Nat := 4983230072969 + 3 ^ 40 * 6279828 * 2
def baseEnd_6279828 : Nat := 1074856730520987125923201

theorem tailTrace_6279828 : CollatzResearch.WordTrace tailWord_6279828 prefixEnd_6279828 1074856730520987125923201 := by
  unfold tailWord_6279828
  simp only [CollatzResearch.WordTrace]
  refine ⟨114522071946631570040344069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152696095928842093387125425 114522071946631570040344069)
  ·
    refine ⟨21472888489993419382564513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114522071946631570040344069 21472888489993419382564513)
    ·
      refine ⟨16104666367495064536923385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21472888489993419382564513 16104666367495064536923385)
      ·
        refine ⟨12078499775621298402692539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16104666367495064536923385 12078499775621298402692539)
        ·
          refine ⟨18117749663431947604038809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12078499775621298402692539 18117749663431947604038809)
          ·
            refine ⟨13588312247573960703029107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18117749663431947604038809 13588312247573960703029107)
            ·
              refine ⟨20382468371360941054543661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13588312247573960703029107 20382468371360941054543661)
              ·
                refine ⟨7643425639260352895453873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20382468371360941054543661 7643425639260352895453873)
                ·
                  refine ⟨5732569229445264671590405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7643425639260352895453873 5732569229445264671590405)
                  ·
                    refine ⟨1074856730520987125923201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5732569229445264671590405 1074856730520987125923201)
                    ·
                      rfl

theorem cell23_6279828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_6279828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279828 prefixEnd_6279828 := by exact prefixLift 6279828
  have htrace : WordTrace (prefixWord ++ tailWord_6279828) baseStart_6279828 baseEnd_6279828 := by
    simpa [prefixWord, tailWord_6279828, baseEnd_6279828] using wordTrace_append hprefix tailTrace_6279828
  have hstable : (prefixWord ++ tailWord_6279828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279828).length < 2 ^ (prefixWord ++ tailWord_6279828).sum := by decide
  have hdescent : baseEnd_6279828 < baseStart_6279828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279868 : List Nat := [2, 2, 2, 3, 1, 1, 4, 2, 2, 1, 3]
def baseStart_6279868 : Nat := 118140960795 + 6279868 * 2 ^ 59
def prefixEnd_6279868 : Nat := 4983230072969 + 3 ^ 40 * 6279868 * 2
def baseEnd_6279868 : Nat := 3224590730789141221269419

theorem tailTrace_6279868 : CollatzResearch.WordTrace tailWord_6279868 prefixEnd_6279868 3224590730789141221269419 := by
  unfold tailWord_6279868
  simp only [CollatzResearch.WordTrace]
  refine ⟨114522801406559113456072129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152697068542078817941429505 114522801406559113456072129)
  ·
    refine ⟨85892101054919335092054097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114522801406559113456072129 85892101054919335092054097)
    ·
      refine ⟨64419075791189501319040573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85892101054919335092054097 64419075791189501319040573)
      ·
        refine ⟨24157153421696062994640215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64419075791189501319040573 24157153421696062994640215)
        ·
          refine ⟨36235730132544094491960323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24157153421696062994640215 36235730132544094491960323)
          ·
            refine ⟨54353595198816141737940485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36235730132544094491960323 54353595198816141737940485)
            ·
              refine ⟨10191299099778026575863841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54353595198816141737940485 10191299099778026575863841)
              ·
                refine ⟨7643474324833519931897881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10191299099778026575863841 7643474324833519931897881)
                ·
                  refine ⟨5732605743625139948923411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7643474324833519931897881 5732605743625139948923411)
                  ·
                    refine ⟨8598908615437709923385117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5732605743625139948923411 8598908615437709923385117)
                    ·
                      refine ⟨3224590730789141221269419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8598908615437709923385117 3224590730789141221269419)
                      ·
                        rfl

theorem cell23_6279868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_6279868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279868 prefixEnd_6279868 := by exact prefixLift 6279868
  have htrace : WordTrace (prefixWord ++ tailWord_6279868) baseStart_6279868 baseEnd_6279868 := by
    simpa [prefixWord, tailWord_6279868, baseEnd_6279868] using wordTrace_append hprefix tailTrace_6279868
  have hstable : (prefixWord ++ tailWord_6279868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279868).length < 2 ^ (prefixWord ++ tailWord_6279868).sum := by decide
  have hdescent : baseEnd_6279868 < baseStart_6279868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279884 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 1, 8]
def baseStart_6279884 : Nat := 118140960795 + 6279884 * 2 ^ 59
def prefixEnd_6279884 : Nat := 4983230072969 + 3 ^ 40 * 6279884 * 2
def baseEnd_6279884 : Nat := 1074866315493204386223115

theorem tailTrace_6279884 : CollatzResearch.WordTrace tailWord_6279884 prefixEnd_6279884 1074866315493204386223115 := by
  unfold tailWord_6279884
  simp only [CollatzResearch.WordTrace]
  refine ⟨114523093190530130822363353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152697457587373507763151137 114523093190530130822363353)
  ·
    refine ⟨85892319892897598116772515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114523093190530130822363353 85892319892897598116772515)
    ·
      refine ⟨128838479839346397175158773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85892319892897598116772515 128838479839346397175158773)
      ·
        refine ⟨12078607484938724735171135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128838479839346397175158773 12078607484938724735171135)
        ·
          refine ⟨18117911227408087102756703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12078607484938724735171135 18117911227408087102756703)
          ·
            refine ⟨27176866841112130654135055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18117911227408087102756703 27176866841112130654135055)
            ·
              refine ⟨40765300261668195981202583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27176866841112130654135055 40765300261668195981202583)
              ·
                refine ⟨61147950392502293971803875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40765300261668195981202583 61147950392502293971803875)
                ·
                  refine ⟨91721925588753440957705813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61147950392502293971803875 91721925588753440957705813)
                  ·
                    refine ⟨1074866315493204386223115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91721925588753440957705813 1074866315493204386223115)
                    ·
                      rfl

theorem cell23_6279884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_6279884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279884 prefixEnd_6279884 := by exact prefixLift 6279884
  have htrace : WordTrace (prefixWord ++ tailWord_6279884) baseStart_6279884 baseEnd_6279884 := by
    simpa [prefixWord, tailWord_6279884, baseEnd_6279884] using wordTrace_append hprefix tailTrace_6279884
  have hstable : (prefixWord ++ tailWord_6279884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279884).length < 2 ^ (prefixWord ++ tailWord_6279884).sum := by decide
  have hdescent : baseEnd_6279884 < baseStart_6279884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279885 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_6279885 : Nat := 118140960795 + 6279885 * 2 ^ 59
def prefixEnd_6279885 : Nat := 4983230072969 + 3 ^ 40 * 6279885 * 2
def baseEnd_6279885 : Nat := 3224599459960267654756841

theorem tailTrace_6279885 : CollatzResearch.WordTrace tailWord_6279885 prefixEnd_6279885 3224599459960267654756841 := by
  unfold tailWord_6279885
  simp only [CollatzResearch.WordTrace]
  refine ⟨229046222854056638815513109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152697481902704425877008739 229046222854056638815513109)
  ·
    refine ⟨10736541696283904944477177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 229046222854056638815513109 10736541696283904944477177)
    ·
      refine ⟨8052406272212928708357883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10736541696283904944477177 8052406272212928708357883)
      ·
        refine ⟨12078609408319393062536825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8052406272212928708357883 12078609408319393062536825)
        ·
          refine ⟨9058957056239544796902619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12078609408319393062536825 9058957056239544796902619)
          ·
            refine ⟨13588435584359317195353929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9058957056239544796902619 13588435584359317195353929)
            ·
              refine ⟨10191326688269487896515447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13588435584359317195353929 10191326688269487896515447)
              ·
                refine ⟨15286990032404231844773171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10191326688269487896515447 15286990032404231844773171)
                ·
                  refine ⟨22930485048606347767159757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15286990032404231844773171 22930485048606347767159757)
                  ·
                    refine ⟨8598931893227380412684909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22930485048606347767159757 8598931893227380412684909)
                    ·
                      refine ⟨3224599459960267654756841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8598931893227380412684909 3224599459960267654756841)
                      ·
                        rfl

theorem cell23_6279885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_6279885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279885 prefixEnd_6279885 := by exact prefixLift 6279885
  have htrace : WordTrace (prefixWord ++ tailWord_6279885) baseStart_6279885 baseEnd_6279885 := by
    simpa [prefixWord, tailWord_6279885, baseEnd_6279885] using wordTrace_append hprefix tailTrace_6279885
  have hstable : (prefixWord ++ tailWord_6279885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279885).length < 2 ^ (prefixWord ++ tailWord_6279885).sum := by decide
  have hdescent : baseEnd_6279885 < baseStart_6279885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279912 : List Nat := [2, 1, 4, 1, 4, 2, 2, 1, 1, 3, 2]
def baseStart_6279912 : Nat := 118140960795 + 6279912 * 2 ^ 59
def prefixEnd_6279912 : Nat := 4983230072969 + 3 ^ 40 * 6279912 * 2
def baseEnd_6279912 : Nat := 3224613323937939049119217

theorem tailTrace_6279912 : CollatzResearch.WordTrace tailWord_6279912 prefixEnd_6279912 3224613323937939049119217 := by
  unfold tailWord_6279912
  simp only [CollatzResearch.WordTrace]
  refine ⟨114523603812479411213372995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152698138416639214951163993 114523603812479411213372995)
  ·
    refine ⟨171785405718719116820059493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114523603812479411213372995 171785405718719116820059493)
    ·
      refine ⟨32209763572259834403761155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171785405718719116820059493 32209763572259834403761155)
      ·
        refine ⟨48314645358389751605641733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32209763572259834403761155 48314645358389751605641733)
        ·
          refine ⟨9058996004698078426057825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48314645358389751605641733 9058996004698078426057825)
          ·
            refine ⟨6794247003523558819543369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9058996004698078426057825 6794247003523558819543369)
            ·
              refine ⟨5095685252642669114657527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6794247003523558819543369 5095685252642669114657527)
              ·
                refine ⟨7643527878964003671986291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5095685252642669114657527 7643527878964003671986291)
                ·
                  refine ⟨11465291818446005507979437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7643527878964003671986291 11465291818446005507979437)
                  ·
                    refine ⟨4299484431917252065492289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11465291818446005507979437 4299484431917252065492289)
                    ·
                      refine ⟨3224613323937939049119217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4299484431917252065492289 3224613323937939049119217)
                      ·
                        rfl

theorem cell23_6279912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_6279912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279912 prefixEnd_6279912 := by exact prefixLift 6279912
  have htrace : WordTrace (prefixWord ++ tailWord_6279912) baseStart_6279912 baseEnd_6279912 := by
    simpa [prefixWord, tailWord_6279912, baseEnd_6279912] using wordTrace_append hprefix tailTrace_6279912
  have hstable : (prefixWord ++ tailWord_6279912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279912).length < 2 ^ (prefixWord ++ tailWord_6279912).sum := by decide
  have hdescent : baseEnd_6279912 < baseStart_6279912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279944 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 1, 7]
def baseStart_6279944 : Nat := 118140960795 + 6279944 * 2 ^ 59
def prefixEnd_6279944 : Nat := 4983230072969 + 3 ^ 40 * 6279944 * 2
def baseEnd_6279944 : Nat := 1074876585106294307973023

theorem tailTrace_6279944 : CollatzResearch.WordTrace tailWord_6279944 prefixEnd_6279944 1074876585106294307973023 := by
  unfold tailWord_6279944
  simp only [CollatzResearch.WordTrace]
  refine ⟨114524187380421445945955443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152698916507228594594607257 114524187380421445945955443)
  ·
    refine ⟨171786281070632168918933165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114524187380421445945955443 171786281070632168918933165)
    ·
      refine ⟨64419855401487063344599937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171786281070632168918933165 64419855401487063344599937)
      ·
        refine ⟨48314891551115297508449953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64419855401487063344599937 48314891551115297508449953)
        ·
          refine ⟨36236168663336473131337465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48314891551115297508449953 36236168663336473131337465)
          ·
            refine ⟨27177126497502354848503099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36236168663336473131337465 27177126497502354848503099)
            ·
              refine ⟨40765689746253532272754649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27177126497502354848503099 40765689746253532272754649)
              ·
                refine ⟨30574267309690149204565987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40765689746253532272754649 30574267309690149204565987)
                ·
                  refine ⟨45861400964535223806848981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30574267309690149204565987 45861400964535223806848981)
                  ·
                    refine ⟨1074876585106294307973023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45861400964535223806848981 1074876585106294307973023)
                    ·
                      rfl

theorem cell23_6279944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_6279944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279944 prefixEnd_6279944 := by exact prefixLift 6279944
  have htrace : WordTrace (prefixWord ++ tailWord_6279944) baseStart_6279944 baseEnd_6279944 := by
    simpa [prefixWord, tailWord_6279944, baseEnd_6279944] using wordTrace_append hprefix tailTrace_6279944
  have hstable : (prefixWord ++ tailWord_6279944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279944).length < 2 ^ (prefixWord ++ tailWord_6279944).sum := by decide
  have hdescent : baseEnd_6279944 < baseStart_6279944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6279988 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_6279988 : Nat := 118140960795 + 6279988 * 2 ^ 59
def prefixEnd_6279988 : Nat := 4983230072969 + 3 ^ 40 * 6279988 * 2
def baseEnd_6279988 : Nat := 3224652348467680751768867

theorem tailTrace_6279988 : CollatzResearch.WordTrace tailWord_6279988 prefixEnd_6279988 3224652348467680751768867 := by
  unfold tailWord_6279988
  simp only [CollatzResearch.WordTrace]
  refine ⟨114524989786341743703256309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152699986381788991604341745 114524989786341743703256309)
  ·
    refine ⟨10736717792469538472180279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114524989786341743703256309 10736717792469538472180279)
    ·
      refine ⟨16105076688704307708270419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10736717792469538472180279 16105076688704307708270419)
      ·
        refine ⟨24157615033056461562405629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16105076688704307708270419 24157615033056461562405629)
        ·
          refine ⟨9059105637396173085902111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24157615033056461562405629 9059105637396173085902111)
          ·
            refine ⟨13588658456094259628853167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9059105637396173085902111 13588658456094259628853167)
            ·
              refine ⟨20382987684141389443279751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13588658456094259628853167 20382987684141389443279751)
              ·
                refine ⟨30574481526212084164919627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20382987684141389443279751 30574481526212084164919627)
                ·
                  refine ⟨45861722289318126247379441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30574481526212084164919627 45861722289318126247379441)
                  ·
                    refine ⟨34396291716988594685534581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45861722289318126247379441 34396291716988594685534581)
                    ·
                      refine ⟨3224652348467680751768867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34396291716988594685534581 3224652348467680751768867)
                      ·
                        rfl

theorem cell23_6279988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_6279988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6279988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6279988 prefixEnd_6279988 := by exact prefixLift 6279988
  have htrace : WordTrace (prefixWord ++ tailWord_6279988) baseStart_6279988 baseEnd_6279988 := by
    simpa [prefixWord, tailWord_6279988, baseEnd_6279988] using wordTrace_append hprefix tailTrace_6279988
  have hstable : (prefixWord ++ tailWord_6279988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6279988).length < 2 ^ (prefixWord ++ tailWord_6279988).sum := by decide
  have hdescent : baseEnd_6279988 < baseStart_6279988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6279988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280018 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_6280018 : Nat := 118140960795 + 6280018 * 2 ^ 59
def prefixEnd_6280018 : Nat := 4983230072969 + 3 ^ 40 * 6280018 * 2
def baseEnd_6280018 : Nat := 3224667752887315634393729

theorem tailTrace_6280018 : CollatzResearch.WordTrace tailWord_6280018 prefixEnd_6280018 3224667752887315634393729 := by
  unfold tailWord_6280018
  simp only [CollatzResearch.WordTrace]
  refine ⟨57262768440643700632526177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152700715841716535020069805 57262768440643700632526177)
  ·
    refine ⟨42947076330482775474394633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57262768440643700632526177 42947076330482775474394633)
    ·
      refine ⟨32210307247862081605795975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42947076330482775474394633 32210307247862081605795975)
      ·
        refine ⟨48315460871793122408693963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32210307247862081605795975 48315460871793122408693963)
        ·
          refine ⟨72473191307689683613040945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48315460871793122408693963 72473191307689683613040945)
          ·
            refine ⟨54354893480767262709780709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72473191307689683613040945 54354893480767262709780709)
            ·
              refine ⟨10191542527643861758083883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54354893480767262709780709 10191542527643861758083883)
              ·
                refine ⟨15287313791465792637125825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10191542527643861758083883 15287313791465792637125825)
                ·
                  refine ⟨11465485343599344477844369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15287313791465792637125825 11465485343599344477844369)
                  ·
                    refine ⟨8599114007699508358383277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11465485343599344477844369 8599114007699508358383277)
                    ·
                      refine ⟨3224667752887315634393729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8599114007699508358383277 3224667752887315634393729)
                      ·
                        rfl

theorem cell23_6280018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_6280018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280018 prefixEnd_6280018 := by exact prefixLift 6280018
  have htrace : WordTrace (prefixWord ++ tailWord_6280018) baseStart_6280018 baseEnd_6280018 := by
    simpa [prefixWord, tailWord_6280018, baseEnd_6280018] using wordTrace_append hprefix tailTrace_6280018
  have hstable : (prefixWord ++ tailWord_6280018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280018).length < 2 ^ (prefixWord ++ tailWord_6280018).sum := by decide
  have hdescent : baseEnd_6280018 < baseStart_6280018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280041 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 5, 5, 2]
def baseStart_6280041 : Nat := 118140960795 + 6280041 * 2 ^ 59
def prefixEnd_6280041 : Nat := 4983230072969 + 3 ^ 40 * 6280041 * 2
def baseEnd_6280041 : Nat := 3224679562942369044406123

theorem tailTrace_6280041 : CollatzResearch.WordTrace tailWord_6280041 prefixEnd_6280041 3224679562942369044406123 := by
  unfold tailWord_6280041
  simp only [CollatzResearch.WordTrace]
  refine ⟨229051912641491477458191977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152701275094327651638794651 229051912641491477458191977)
  ·
    refine ⟨171788934481118608093643983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229051912641491477458191977 171788934481118608093643983)
    ·
      refine ⟨257683401721677912140465975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171788934481118608093643983 257683401721677912140465975)
      ·
        refine ⟨386525102582516868210698963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257683401721677912140465975 386525102582516868210698963)
        ·
          refine ⟨579787653873775302316048445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386525102582516868210698963 579787653873775302316048445)
          ·
            refine ⟨217420370202665738368518167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 579787653873775302316048445 217420370202665738368518167)
            ·
              refine ⟨326130555303998607552777251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217420370202665738368518167 326130555303998607552777251)
              ·
                refine ⟨489195832955997911329165877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326130555303998607552777251 489195832955997911329165877)
                ·
                  refine ⟨45862109339624804187109301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 489195832955997911329165877 45862109339624804187109301)
                  ·
                    refine ⟨4299572750589825392541497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45862109339624804187109301 4299572750589825392541497)
                    ·
                      refine ⟨3224679562942369044406123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4299572750589825392541497 3224679562942369044406123)
                      ·
                        rfl

theorem cell23_6280041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 5, 2].length) (baseStart_6280041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280041 prefixEnd_6280041 := by exact prefixLift 6280041
  have htrace : WordTrace (prefixWord ++ tailWord_6280041) baseStart_6280041 baseEnd_6280041 := by
    simpa [prefixWord, tailWord_6280041, baseEnd_6280041] using wordTrace_append hprefix tailTrace_6280041
  have hstable : (prefixWord ++ tailWord_6280041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280041).length < 2 ^ (prefixWord ++ tailWord_6280041).sum := by decide
  have hdescent : baseEnd_6280041 < baseStart_6280041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280081 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 4, 4]
def baseStart_6280081 : Nat := 118140960795 + 6280081 * 2 ^ 59
def prefixEnd_6280081 : Nat := 4983230072969 + 3 ^ 40 * 6280081 * 2
def baseEnd_6280081 : Nat := 1074900034056182962635313

theorem tailTrace_6280081 : CollatzResearch.WordTrace tailWord_6280081 prefixEnd_6280081 1074900034056182962635313 := by
  unfold tailWord_6280081
  simp only [CollatzResearch.WordTrace]
  refine ⟨229053371561346564289648097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152702247707564376193098731 229053371561346564289648097)
  ·
    refine ⟨171790028671009923217236073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229053371561346564289648097 171790028671009923217236073)
    ·
      refine ⟨128842521503257442412927055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171790028671009923217236073 128842521503257442412927055)
      ·
        refine ⟨193263782254886163619390583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128842521503257442412927055 193263782254886163619390583)
        ·
          refine ⟨289895673382329245429085875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193263782254886163619390583 289895673382329245429085875)
          ·
            refine ⟨434843510073493868143628813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289895673382329245429085875 434843510073493868143628813)
            ·
              refine ⟨163066316277560200553860805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 434843510073493868143628813 163066316277560200553860805)
              ·
                refine ⟨30574934302042537603848901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163066316277560200553860805 30574934302042537603848901)
                ·
                  refine ⟨5732800181632975800721669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30574934302042537603848901 5732800181632975800721669)
                  ·
                    refine ⟨1074900034056182962635313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5732800181632975800721669 1074900034056182962635313)
                    ·
                      rfl

theorem cell23_6280081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_6280081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280081 prefixEnd_6280081 := by exact prefixLift 6280081
  have htrace : WordTrace (prefixWord ++ tailWord_6280081) baseStart_6280081 baseEnd_6280081 := by
    simpa [prefixWord, tailWord_6280081, baseEnd_6280081] using wordTrace_append hprefix tailTrace_6280081
  have hstable : (prefixWord ++ tailWord_6280081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280081).length < 2 ^ (prefixWord ++ tailWord_6280081).sum := by decide
  have hdescent : baseEnd_6280081 < baseStart_6280081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280085 : List Nat := [1, 3, 2, 1, 1, 6, 2, 1, 1, 5]
def baseStart_6280085 : Nat := 118140960795 + 6280085 * 2 ^ 59
def prefixEnd_6280085 : Nat := 4983230072969 + 3 ^ 40 * 6280085 * 2
def baseEnd_6280085 : Nat := 1074900718697055624085307

theorem tailTrace_6280085 : CollatzResearch.WordTrace tailWord_6280085 prefixEnd_6280085 1074900718697055624085307 := by
  unfold tailWord_6280085
  simp only [CollatzResearch.WordTrace]
  refine ⟨229053517453332072972793709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152702344968888048648529139 229053517453332072972793709)
  ·
    refine ⟨85895069044999527364797641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229053517453332072972793709 85895069044999527364797641)
    ·
      refine ⟨64421301783749645523598231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85895069044999527364797641 64421301783749645523598231)
      ·
        refine ⟨96631952675624468285397347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64421301783749645523598231 96631952675624468285397347)
        ·
          refine ⟨144947929013436702428096021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96631952675624468285397347 144947929013436702428096021)
          ·
            refine ⟨6794434172504845426317001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 144947929013436702428096021 6794434172504845426317001)
            ·
              refine ⟨5095825629378634069737751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6794434172504845426317001 5095825629378634069737751)
              ·
                refine ⟨7643738444067951104606627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5095825629378634069737751 7643738444067951104606627)
                ·
                  refine ⟨11465607666101926656909941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7643738444067951104606627 11465607666101926656909941)
                  ·
                    refine ⟨1074900718697055624085307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11465607666101926656909941 1074900718697055624085307)
                    ·
                      rfl

theorem cell23_6280085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_6280085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280085 prefixEnd_6280085 := by exact prefixLift 6280085
  have htrace : WordTrace (prefixWord ++ tailWord_6280085) baseStart_6280085 baseEnd_6280085 := by
    simpa [prefixWord, tailWord_6280085, baseEnd_6280085] using wordTrace_append hprefix tailTrace_6280085
  have hstable : (prefixWord ++ tailWord_6280085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280085).length < 2 ^ (prefixWord ++ tailWord_6280085).sum := by decide
  have hdescent : baseEnd_6280085 < baseStart_6280085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280105 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 3, 2, 2]
def baseStart_6280105 : Nat := 118140960795 + 6280105 * 2 ^ 59
def prefixEnd_6280105 : Nat := 4983230072969 + 3 ^ 40 * 6280105 * 2
def baseEnd_6280105 : Nat := 3224712425704256794005829

theorem tailTrace_6280105 : CollatzResearch.WordTrace tailWord_6280105 prefixEnd_6280105 3224712425704256794005829 := by
  unfold tailWord_6280105
  simp only [CollatzResearch.WordTrace]
  refine ⟨229054246913259616388521769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152702831275506410925681179 229054246913259616388521769)
  ·
    refine ⟨171790685184944712291391327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229054246913259616388521769 171790685184944712291391327)
    ·
      refine ⟨257686027777417068437086991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171790685184944712291391327 257686027777417068437086991)
      ·
        refine ⟨386529041666125602655630487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257686027777417068437086991 386529041666125602655630487)
        ·
          refine ⟨579793562499188403983445731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386529041666125602655630487 579793562499188403983445731)
          ·
            refine ⟨869690343748782605975168597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579793562499188403983445731 869690343748782605975168597)
            ·
              refine ⟨10191683715806046163771507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 869690343748782605975168597 10191683715806046163771507)
              ·
                refine ⟨15287525573709069245657261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10191683715806046163771507 15287525573709069245657261)
                ·
                  refine ⟨5732822090140900967121473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15287525573709069245657261 5732822090140900967121473)
                  ·
                    refine ⟨4299616567605675725341105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5732822090140900967121473 4299616567605675725341105)
                    ·
                      refine ⟨3224712425704256794005829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4299616567605675725341105 3224712425704256794005829)
                      ·
                        rfl

theorem cell23_6280105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 2, 2].length) (baseStart_6280105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280105 prefixEnd_6280105 := by exact prefixLift 6280105
  have htrace : WordTrace (prefixWord ++ tailWord_6280105) baseStart_6280105 baseEnd_6280105 := by
    simpa [prefixWord, tailWord_6280105, baseEnd_6280105] using wordTrace_append hprefix tailTrace_6280105
  have hstable : (prefixWord ++ tailWord_6280105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280105).length < 2 ^ (prefixWord ++ tailWord_6280105).sum := by decide
  have hdescent : baseEnd_6280105 < baseStart_6280105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280128 : List Nat := [2, 1, 1, 2, 3, 5, 2, 7]
def baseStart_6280128 : Nat := 118140960795 + 6280128 * 2 ^ 59
def prefixEnd_6280128 : Nat := 4983230072969 + 3 ^ 40 * 6280128 * 2
def baseEnd_6280128 : Nat := 119434230954048526074749

theorem tailTrace_6280128 : CollatzResearch.WordTrace tailWord_6280128 prefixEnd_6280128 119434230954048526074749 := by
  unfold tailWord_6280128
  simp only [CollatzResearch.WordTrace]
  refine ⟨114527542896088145658304519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152703390528117527544406025 114527542896088145658304519)
  ·
    refine ⟨171791314344132218487456779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114527542896088145658304519 171791314344132218487456779)
    ·
      refine ⟨257686971516198327731185169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171791314344132218487456779 257686971516198327731185169)
      ·
        refine ⟨193265228637148745798388877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257686971516198327731185169 193265228637148745798388877)
        ·
          refine ⟨72474460738930779674395829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193265228637148745798388877 72474460738930779674395829)
          ·
            refine ⟨6794480694274760594474609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72474460738930779674395829 6794480694274760594474609)
            ·
              refine ⟨5095860520706070445855957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6794480694274760594474609 5095860520706070445855957)
              ·
                refine ⟨119434230954048526074749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5095860520706070445855957 119434230954048526074749)
                ·
                  rfl

theorem cell23_6280128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 7].length) (baseStart_6280128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280128 prefixEnd_6280128 := by exact prefixLift 6280128
  have htrace : WordTrace (prefixWord ++ tailWord_6280128) baseStart_6280128 baseEnd_6280128 := by
    simpa [prefixWord, tailWord_6280128, baseEnd_6280128] using wordTrace_append hprefix tailTrace_6280128
  have hstable : (prefixWord ++ tailWord_6280128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280128).length < 2 ^ (prefixWord ++ tailWord_6280128).sum := by decide
  have hdescent : baseEnd_6280128 < baseStart_6280128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280139 : List Nat := [1, 1, 1, 1, 3, 7, 1, 3, 1, 2, 2]
def baseStart_6280139 : Nat := 118140960795 + 6280139 * 2 ^ 59
def prefixEnd_6280139 : Nat := 4983230072969 + 3 ^ 40 * 6280139 * 2
def baseEnd_6280139 : Nat := 3224729884046509660980673

theorem tailTrace_6280139 : CollatzResearch.WordTrace tailWord_6280139 prefixEnd_6280139 3224729884046509660980673 := by
  unfold tailWord_6280139
  simp only [CollatzResearch.WordTrace]
  refine ⟨229055486995136440195259471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152703657996757626796839647 229055486995136440195259471)
  ·
    refine ⟨343583230492704660292889207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229055486995136440195259471 343583230492704660292889207)
    ·
      refine ⟨515374845739056990439333811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343583230492704660292889207 515374845739056990439333811)
      ·
        refine ⟨773062268608585485659000717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515374845739056990439333811 773062268608585485659000717)
        ·
          refine ⟨289898350728219557122125269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 773062268608585485659000717 289898350728219557122125269)
          ·
            refine ⟨6794492595192645870049811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 289898350728219557122125269 6794492595192645870049811)
            ·
              refine ⟨10191738892788968805074717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6794492595192645870049811 10191738892788968805074717)
              ·
                refine ⟨3821902084795863301903019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10191738892788968805074717 3821902084795863301903019)
                ·
                  refine ⟨5732853127193794952854529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3821902084795863301903019 5732853127193794952854529)
                  ·
                    refine ⟨4299639845395346214640897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5732853127193794952854529 4299639845395346214640897)
                    ·
                      refine ⟨3224729884046509660980673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4299639845395346214640897 3224729884046509660980673)
                      ·
                        rfl

theorem cell23_6280139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 1, 2, 2].length) (baseStart_6280139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280139 prefixEnd_6280139 := by exact prefixLift 6280139
  have htrace : WordTrace (prefixWord ++ tailWord_6280139) baseStart_6280139 baseEnd_6280139 := by
    simpa [prefixWord, tailWord_6280139, baseEnd_6280139] using wordTrace_append hprefix tailTrace_6280139
  have hstable : (prefixWord ++ tailWord_6280139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280139).length < 2 ^ (prefixWord ++ tailWord_6280139).sum := by decide
  have hdescent : baseEnd_6280139 < baseStart_6280139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280161 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_6280161 : Nat := 118140960795 + 6280161 * 2 ^ 59
def prefixEnd_6280161 : Nat := 4983230072969 + 3 ^ 40 * 6280161 * 2
def baseEnd_6280161 : Nat := 3224741180620908574905571

theorem tailTrace_6280161 : CollatzResearch.WordTrace tailWord_6280161 prefixEnd_6280161 3224741180620908574905571 := by
  unfold tailWord_6280161
  simp only [CollatzResearch.WordTrace]
  refine ⟨229056289401056737952560337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152704192934037825301706891 229056289401056737952560337)
  ·
    refine ⟨171792217050792553464420253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229056289401056737952560337 171792217050792553464420253)
    ·
      refine ⟨64422081394047207549157595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171792217050792553464420253 64422081394047207549157595)
      ·
        refine ⟨96633122091070811323736393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64422081394047207549157595 96633122091070811323736393)
        ·
          refine ⟨72474841568303108492802295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96633122091070811323736393 72474841568303108492802295)
          ·
            refine ⟨108712262352454662739203443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72474841568303108492802295 108712262352454662739203443)
            ·
              refine ⟨163068393528681994108805165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108712262352454662739203443 163068393528681994108805165)
              ·
                refine ⟨61150647573255747790801937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163068393528681994108805165 61150647573255747790801937)
                ·
                  refine ⟨45862985679941810843101453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61150647573255747790801937 45862985679941810843101453)
                  ·
                    refine ⟨17198619629978179066163045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45862985679941810843101453 17198619629978179066163045)
                    ·
                      refine ⟨3224741180620908574905571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17198619629978179066163045 3224741180620908574905571)
                      ·
                        rfl

theorem cell23_6280161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_6280161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280161 prefixEnd_6280161 := by exact prefixLift 6280161
  have htrace : WordTrace (prefixWord ++ tailWord_6280161) baseStart_6280161 baseEnd_6280161 := by
    simpa [prefixWord, tailWord_6280161, baseEnd_6280161] using wordTrace_append hprefix tailTrace_6280161
  have hstable : (prefixWord ++ tailWord_6280161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280161).length < 2 ^ (prefixWord ++ tailWord_6280161).sum := by decide
  have hdescent : baseEnd_6280161 < baseStart_6280161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280182 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2]
def baseStart_6280182 : Nat := 118140960795 + 6280182 * 2 ^ 59
def prefixEnd_6280182 : Nat := 4983230072969 + 3 ^ 40 * 6280182 * 2
def baseEnd_6280182 : Nat := 3224751963714652992742975

theorem tailTrace_6280182 : CollatzResearch.WordTrace tailWord_6280182 prefixEnd_6280182 3224751963714652992742975 := by
  unfold tailWord_6280182
  simp only [CollatzResearch.WordTrace]
  refine ⟨14316065958373791158692175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152704703555987105692716533 14316065958373791158692175)
  ·
    refine ⟨21474098937560686738038263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14316065958373791158692175 21474098937560686738038263)
    ·
      refine ⟨32211148406341030107057395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21474098937560686738038263 32211148406341030107057395)
      ·
        refine ⟨48316722609511545160586093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32211148406341030107057395 48316722609511545160586093)
        ·
          refine ⟨18118770978566829435219785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48316722609511545160586093 18118770978566829435219785)
          ·
            refine ⟨13589078233925122076414839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18118770978566829435219785 13589078233925122076414839)
            ·
              refine ⟨20383617350887683114622259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13589078233925122076414839 20383617350887683114622259)
              ·
                refine ⟨30575426026331524671933389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20383617350887683114622259 30575426026331524671933389)
                ·
                  refine ⟨11465784759874321751975021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30575426026331524671933389 11465784759874321751975021)
                  ·
                    refine ⟨4299669284952870656990633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11465784759874321751975021 4299669284952870656990633)
                    ·
                      refine ⟨3224751963714652992742975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4299669284952870656990633 3224751963714652992742975)
                      ·
                        rfl

theorem cell23_6280182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_6280182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280182 prefixEnd_6280182 := by exact prefixLift 6280182
  have htrace : WordTrace (prefixWord ++ tailWord_6280182) baseStart_6280182 baseEnd_6280182 := by
    simpa [prefixWord, tailWord_6280182, baseEnd_6280182] using wordTrace_append hprefix tailTrace_6280182
  have hstable : (prefixWord ++ tailWord_6280182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280182).length < 2 ^ (prefixWord ++ tailWord_6280182).sum := by decide
  have hdescent : baseEnd_6280182 < baseStart_6280182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280191 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 4]
def baseStart_6280191 : Nat := 118140960795 + 6280191 * 2 ^ 59
def prefixEnd_6280191 : Nat := 4983230072969 + 3 ^ 40 * 6280191 * 2
def baseEnd_6280191 : Nat := 3224756585040543457530433

theorem tailTrace_6280191 : CollatzResearch.WordTrace tailWord_6280191 prefixEnd_6280191 3224756585040543457530433 := by
  unfold tailWord_6280191
  simp only [CollatzResearch.WordTrace]
  refine ⟨229057383590948053076152427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152704922393965368717434951 229057383590948053076152427)
  ·
    refine ⟨343586075386422079614228641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229057383590948053076152427 343586075386422079614228641)
    ·
      refine ⟨257689556539816559710671481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343586075386422079614228641 257689556539816559710671481)
      ·
        refine ⟨193267167404862419783003611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257689556539816559710671481 193267167404862419783003611)
        ·
          refine ⟨289900751107293629674505417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193267167404862419783003611 289900751107293629674505417)
          ·
            refine ⟨217425563330470222255879063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289900751107293629674505417 217425563330470222255879063)
            ·
              refine ⟨326138344995705333383818595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217425563330470222255879063 326138344995705333383818595)
              ·
                refine ⟨489207517493558000075727893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326138344995705333383818595 489207517493558000075727893)
                ·
                  refine ⟨22931602382510531253549745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 489207517493558000075727893 22931602382510531253549745)
                  ·
                    refine ⟨17198701786882898440162309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22931602382510531253549745 17198701786882898440162309)
                    ·
                      refine ⟨3224756585040543457530433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17198701786882898440162309 3224756585040543457530433)
                      ·
                        rfl

theorem cell23_6280191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_6280191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280191 prefixEnd_6280191 := by exact prefixLift 6280191
  have htrace : WordTrace (prefixWord ++ tailWord_6280191) baseStart_6280191 baseEnd_6280191 := by
    simpa [prefixWord, tailWord_6280191, baseEnd_6280191] using wordTrace_append hprefix tailTrace_6280191
  have hstable : (prefixWord ++ tailWord_6280191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280191).length < 2 ^ (prefixWord ++ tailWord_6280191).sum := by decide
  have hdescent : baseEnd_6280191 < baseStart_6280191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280248 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 1, 7]
def baseStart_6280248 : Nat := 118140960795 + 6280248 * 2 ^ 59
def prefixEnd_6280248 : Nat := 4983230072969 + 3 ^ 40 * 6280248 * 2
def baseEnd_6280248 : Nat := 1074928617812616578172557

theorem tailTrace_6280248 : CollatzResearch.WordTrace tailWord_6280248 prefixEnd_6280248 1074928617812616578172557 := by
  unfold tailWord_6280248
  simp only [CollatzResearch.WordTrace]
  refine ⟨114529731275870775905488699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152706308367827701207318265 114529731275870775905488699)
  ·
    refine ⟨171794596913806163858233049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114529731275870775905488699 171794596913806163858233049)
    ·
      refine ⟨128845947685354622893674787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171794596913806163858233049 128845947685354622893674787)
      ·
        refine ⟨193268921528031934340512181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128845947685354622893674787 193268921528031934340512181)
        ·
          refine ⟨18118961393252993844423017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193268921528031934340512181 18118961393252993844423017)
          ·
            refine ⟨13589221044939745383317263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18118961393252993844423017 13589221044939745383317263)
            ·
              refine ⟨20383831567409618074975895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13589221044939745383317263 20383831567409618074975895)
              ·
                refine ⟨30575747351114427112463843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20383831567409618074975895 30575747351114427112463843)
                ·
                  refine ⟨45863621026671640668695765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30575747351114427112463843 45863621026671640668695765)
                  ·
                    refine ⟨1074928617812616578172557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45863621026671640668695765 1074928617812616578172557)
                    ·
                      rfl

theorem cell23_6280248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_6280248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280248 prefixEnd_6280248 := by exact prefixLift 6280248
  have htrace : WordTrace (prefixWord ++ tailWord_6280248) baseStart_6280248 baseEnd_6280248 := by
    simpa [prefixWord, tailWord_6280248, baseEnd_6280248] using wordTrace_append hprefix tailTrace_6280248
  have hstable : (prefixWord ++ tailWord_6280248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280248).length < 2 ^ (prefixWord ++ tailWord_6280248).sum := by decide
  have hdescent : baseEnd_6280248 < baseStart_6280248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280262 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_6280262 : Nat := 118140960795 + 6280262 * 2 ^ 59
def prefixEnd_6280262 : Nat := 4983230072969 + 3 ^ 40 * 6280262 * 2
def baseEnd_6280262 : Nat := 3224793042167012679742607

theorem tailTrace_6280262 : CollatzResearch.WordTrace tailWord_6280262 prefixEnd_6280262 3224793042167012679742607 := by
  unfold tailWord_6280262
  simp only [CollatzResearch.WordTrace]
  refine ⟨7158124161677838506312095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 152706648782460554801324693 7158124161677838506312095)
  ·
    refine ⟨10737186242516757759468143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7158124161677838506312095 10737186242516757759468143)
    ·
      refine ⟨16105779363775136639202215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10737186242516757759468143 16105779363775136639202215)
      ·
        refine ⟨24158669045662704958803323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16105779363775136639202215 24158669045662704958803323)
        ·
          refine ⟨36238003568494057438204985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24158669045662704958803323 36238003568494057438204985)
          ·
            refine ⟨27178502676370543078653739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36238003568494057438204985 27178502676370543078653739)
            ·
              refine ⟨40767754014555814617980609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27178502676370543078653739 40767754014555814617980609)
              ·
                refine ⟨30575815510916860963485457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40767754014555814617980609 30575815510916860963485457)
                ·
                  refine ⟨22931861633187645722614093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30575815510916860963485457 22931861633187645722614093)
                  ·
                    refine ⟨8599448112445367145980285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22931861633187645722614093 8599448112445367145980285)
                    ·
                      refine ⟨3224793042167012679742607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8599448112445367145980285 3224793042167012679742607)
                      ·
                        rfl

theorem cell23_6280262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_6280262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280262 prefixEnd_6280262 := by exact prefixLift 6280262
  have htrace : WordTrace (prefixWord ++ tailWord_6280262) baseStart_6280262 baseEnd_6280262 := by
    simpa [prefixWord, tailWord_6280262, baseEnd_6280262] using wordTrace_append hprefix tailTrace_6280262
  have hstable : (prefixWord ++ tailWord_6280262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280262).length < 2 ^ (prefixWord ++ tailWord_6280262).sum := by decide
  have hdescent : baseEnd_6280262 < baseStart_6280262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280268 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 4, 1, 4]
def baseStart_6280268 : Nat := 118140960795 + 6280268 * 2 ^ 59
def prefixEnd_6280268 : Nat := 4983230072969 + 3 ^ 40 * 6280268 * 2
def baseEnd_6280268 : Nat := 3224796123050939656267579

theorem tailTrace_6280268 : CollatzResearch.WordTrace tailWord_6280268 prefixEnd_6280268 3224796123050939656267579 := by
  unfold tailWord_6280268
  simp only [CollatzResearch.WordTrace]
  refine ⟨114530096005834547613352729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152706794674446063484470305 114530096005834547613352729)
  ·
    refine ⟨85897572004375910710014547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114530096005834547613352729 85897572004375910710014547)
    ·
      refine ⟨128846358006563866065021821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85897572004375910710014547 128846358006563866065021821)
      ·
        refine ⟨48317384252461449774383183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128846358006563866065021821 48317384252461449774383183)
        ·
          refine ⟨72476076378692174661574775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48317384252461449774383183 72476076378692174661574775)
          ·
            refine ⟨108714114568038261992362163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72476076378692174661574775 108714114568038261992362163)
            ·
              refine ⟨163071171852057392988543245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108714114568038261992362163 163071171852057392988543245)
              ·
                refine ⟨61151689444521522370703717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163071171852057392988543245 61151689444521522370703717)
                ·
                  refine ⟨11465941770847785444506947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61151689444521522370703717 11465941770847785444506947)
                  ·
                    refine ⟨17198912656271678166760421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11465941770847785444506947 17198912656271678166760421)
                    ·
                      refine ⟨3224796123050939656267579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17198912656271678166760421 3224796123050939656267579)
                      ·
                        rfl

theorem cell23_6280268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_6280268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280268 prefixEnd_6280268 := by exact prefixLift 6280268
  have htrace : WordTrace (prefixWord ++ tailWord_6280268) baseStart_6280268 baseEnd_6280268 := by
    simpa [prefixWord, tailWord_6280268, baseEnd_6280268] using wordTrace_append hprefix tailTrace_6280268
  have hstable : (prefixWord ++ tailWord_6280268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280268).length < 2 ^ (prefixWord ++ tailWord_6280268).sum := by decide
  have hdescent : baseEnd_6280268 < baseStart_6280268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280288 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 3]
def baseStart_6280288 : Nat := 118140960795 + 6280288 * 2 ^ 59
def prefixEnd_6280288 : Nat := 4983230072969 + 3 ^ 40 * 6280288 * 2
def baseEnd_6280288 : Nat := 3224806392664029578017487

theorem tailTrace_6280288 : CollatzResearch.WordTrace tailWord_6280288 prefixEnd_6280288 3224806392664029578017487 := by
  unfold tailWord_6280288
  simp only [CollatzResearch.WordTrace]
  refine ⟨114530460735798319321216759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152707280981064425761622345 114530460735798319321216759)
  ·
    refine ⟨171795691103697478981825139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114530460735798319321216759 171795691103697478981825139)
    ·
      refine ⟨257693536655546218472737709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171795691103697478981825139 257693536655546218472737709)
      ·
        refine ⟨96635076245829831927276641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257693536655546218472737709 96635076245829831927276641)
        ·
          refine ⟨72476307184372373945457481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96635076245829831927276641 72476307184372373945457481)
          ·
            refine ⟨54357230388279280459093111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72476307184372373945457481 54357230388279280459093111)
            ·
              refine ⟨81535845582418920688639667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54357230388279280459093111 81535845582418920688639667)
              ·
                refine ⟨122303768373628381032959501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81535845582418920688639667 122303768373628381032959501)
                ·
                  refine ⟨45863913140110642887359813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122303768373628381032959501 45863913140110642887359813)
                  ·
                    refine ⟨8599483713770745541379965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45863913140110642887359813 8599483713770745541379965)
                    ·
                      refine ⟨3224806392664029578017487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8599483713770745541379965 3224806392664029578017487)
                      ·
                        rfl

theorem cell23_6280288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_6280288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280288 prefixEnd_6280288 := by exact prefixLift 6280288
  have htrace : WordTrace (prefixWord ++ tailWord_6280288) baseStart_6280288 baseEnd_6280288 := by
    simpa [prefixWord, tailWord_6280288, baseEnd_6280288] using wordTrace_append hprefix tailTrace_6280288
  have hstable : (prefixWord ++ tailWord_6280288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280288).length < 2 ^ (prefixWord ++ tailWord_6280288).sum := by decide
  have hdescent : baseEnd_6280288 < baseStart_6280288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280295 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 3, 4]
def baseStart_6280295 : Nat := 118140960795 + 6280295 * 2 ^ 59
def prefixEnd_6280295 : Nat := 4983230072969 + 3 ^ 40 * 6280295 * 2
def baseEnd_6280295 : Nat := 1074936662342870350209985

theorem tailTrace_6280295 : CollatzResearch.WordTrace tailWord_6280295 prefixEnd_6280295 1074936662342870350209985 := by
  unfold tailWord_6280295
  simp only [CollatzResearch.WordTrace]
  refine ⟨229061176782571278837938339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152707451188380852558625559 229061176782571278837938339)
  ·
    refine ⟨343591765173856918256907509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229061176782571278837938339 343591765173856918256907509)
    ·
      refine ⟨32211727985049086086585079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 343591765173856918256907509 32211727985049086086585079)
      ·
        refine ⟨48317591977573629129877619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32211727985049086086585079 48317591977573629129877619)
        ·
          refine ⟨72476387966360443694816429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48317591977573629129877619 72476387966360443694816429)
          ·
            refine ⟨27178645487385166385556161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72476387966360443694816429 27178645487385166385556161)
            ·
              refine ⟨20383984115538874789167121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27178645487385166385556161 20383984115538874789167121)
              ·
                refine ⟨15287988086654156091875341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20383984115538874789167121 15287988086654156091875341)
                ·
                  refine ⟨5732995532495308534453253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15287988086654156091875341 5732995532495308534453253)
                  ·
                    refine ⟨1074936662342870350209985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5732995532495308534453253 1074936662342870350209985)
                    ·
                      rfl

theorem cell23_6280295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_6280295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280295 prefixEnd_6280295 := by exact prefixLift 6280295
  have htrace : WordTrace (prefixWord ++ tailWord_6280295) baseStart_6280295 baseEnd_6280295 := by
    simpa [prefixWord, tailWord_6280295, baseEnd_6280295] using wordTrace_append hprefix tailTrace_6280295
  have hstable : (prefixWord ++ tailWord_6280295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280295).length < 2 ^ (prefixWord ++ tailWord_6280295).sum := by decide
  have hdescent : baseEnd_6280295 < baseStart_6280295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280312 : List Nat := [2, 1, 2, 1, 1, 1, 7, 3, 1, 4]
def baseStart_6280312 : Nat := 118140960795 + 6280312 * 2 ^ 59
def prefixEnd_6280312 : Nat := 4983230072969 + 3 ^ 40 * 6280312 * 2
def baseEnd_6280312 : Nat := 1074939572066579161372459

theorem tailTrace_6280312 : CollatzResearch.WordTrace tailWord_6280312 prefixEnd_6280312 1074939572066579161372459 := by
  unfold tailWord_6280312
  simp only [CollatzResearch.WordTrace]
  refine ⟨114530898411754845370653595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152707864549006460494204793 114530898411754845370653595)
  ·
    refine ⟨171796347617632268055980393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114530898411754845370653595 171796347617632268055980393)
    ·
      refine ⟨128847260713224201041985295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171796347617632268055980393 128847260713224201041985295)
      ·
        refine ⟨193270891069836301562977943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128847260713224201041985295 193270891069836301562977943)
        ·
          refine ⟨289906336604754452344466915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193270891069836301562977943 289906336604754452344466915)
          ·
            refine ⟨434859504907131678516700373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289906336604754452344466915 434859504907131678516700373)
            ·
              refine ⟨10192019646260898715235165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 434859504907131678516700373 10192019646260898715235165)
              ·
                refine ⟨3822007367347837018213187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10192019646260898715235165 3822007367347837018213187)
                ·
                  refine ⟨5733011051021755527319781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3822007367347837018213187 5733011051021755527319781)
                  ·
                    refine ⟨1074939572066579161372459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5733011051021755527319781 1074939572066579161372459)
                    ·
                      rfl

theorem cell23_6280312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 1, 4].length) (baseStart_6280312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280312 prefixEnd_6280312 := by exact prefixLift 6280312
  have htrace : WordTrace (prefixWord ++ tailWord_6280312) baseStart_6280312 baseEnd_6280312 := by
    simpa [prefixWord, tailWord_6280312, baseEnd_6280312] using wordTrace_append hprefix tailTrace_6280312
  have hstable : (prefixWord ++ tailWord_6280312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280312).length < 2 ^ (prefixWord ++ tailWord_6280312).sum := by decide
  have hdescent : baseEnd_6280312 < baseStart_6280312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280329 : List Nat := [1, 2, 1, 1, 4, 4, 3, 2, 1, 4]
def baseStart_6280329 : Nat := 118140960795 + 6280329 * 2 ^ 59
def prefixEnd_6280329 : Nat := 4983230072969 + 3 ^ 40 * 6280329 * 2
def baseEnd_6280329 : Nat := 1074942481790287972534933

theorem tailTrace_6280329 : CollatzResearch.WordTrace tailWord_6280329 prefixEnd_6280329 1074942481790287972534933 := by
  unfold tailWord_6280329
  simp only [CollatzResearch.WordTrace]
  refine ⟨229062416864448102644676041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152708277909632068429784027 229062416864448102644676041)
  ·
    refine ⟨171796812648336076983507031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229062416864448102644676041 171796812648336076983507031)
    ·
      refine ⟨257695218972504115475260547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171796812648336076983507031 257695218972504115475260547)
      ·
        refine ⟨386542828458756173212890821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257695218972504115475260547 386542828458756173212890821)
        ·
          refine ⟨72476780336016782477417029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 386542828458756173212890821 72476780336016782477417029)
          ·
            refine ⟨13589396313003146714515693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72476780336016782477417029 13589396313003146714515693)
            ·
              refine ⟨5096023617376180017943385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13589396313003146714515693 5096023617376180017943385)
              ·
                refine ⟨3822017713032135013457539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5096023617376180017943385 3822017713032135013457539)
                ·
                  refine ⟨5733026569548202520186309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3822017713032135013457539 5733026569548202520186309)
                  ·
                    refine ⟨1074942481790287972534933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5733026569548202520186309 1074942481790287972534933)
                    ·
                      rfl

theorem cell23_6280329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 1, 4].length) (baseStart_6280329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280329 prefixEnd_6280329 := by exact prefixLift 6280329
  have htrace : WordTrace (prefixWord ++ tailWord_6280329) baseStart_6280329 baseEnd_6280329 := by
    simpa [prefixWord, tailWord_6280329, baseEnd_6280329] using wordTrace_append hprefix tailTrace_6280329
  have hstable : (prefixWord ++ tailWord_6280329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280329).length < 2 ^ (prefixWord ++ tailWord_6280329).sum := by decide
  have hdescent : baseEnd_6280329 < baseStart_6280329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280368 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 1, 6]
def baseStart_6280368 : Nat := 118140960795 + 6280368 * 2 ^ 59
def prefixEnd_6280368 : Nat := 4983230072969 + 3 ^ 40 * 6280368 * 2
def baseEnd_6280368 : Nat := 1074949157038796421672373

theorem tailTrace_6280368 : CollatzResearch.WordTrace tailWord_6280368 prefixEnd_6280368 1074949157038796421672373 := by
  unfold tailWord_6280368
  simp only [CollatzResearch.WordTrace]
  refine ⟨114531919655653406152672879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152709226207537874870230505 114531919655653406152672879)
  ·
    refine ⟨171797879483480109229009319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114531919655653406152672879 171797879483480109229009319)
    ·
      refine ⟨257696819225220163843513979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171797879483480109229009319 257696819225220163843513979)
      ·
        refine ⟨386545228837830245765270969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257696819225220163843513979 386545228837830245765270969)
        ·
          refine ⟨289908921628372684323953227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386545228837830245765270969 289908921628372684323953227)
          ·
            refine ⟨434863382442559026485929841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289908921628372684323953227 434863382442559026485929841)
            ·
              refine ⟨326147536831919269864447381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434863382442559026485929841 326147536831919269864447381)
              ·
                refine ⟨15288165788996215774895971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 326147536831919269864447381 15288165788996215774895971)
                ·
                  refine ⟨22932248683494323662343957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15288165788996215774895971 22932248683494323662343957)
                  ·
                    refine ⟨1074949157038796421672373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22932248683494323662343957 1074949157038796421672373)
                    ·
                      rfl

theorem cell23_6280368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 1, 6].length) (baseStart_6280368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280368 prefixEnd_6280368 := by exact prefixLift 6280368
  have htrace : WordTrace (prefixWord ++ tailWord_6280368) baseStart_6280368 baseEnd_6280368 := by
    simpa [prefixWord, tailWord_6280368, baseEnd_6280368] using wordTrace_append hprefix tailTrace_6280368
  have hstable : (prefixWord ++ tailWord_6280368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280368).length < 2 ^ (prefixWord ++ tailWord_6280368).sum := by decide
  have hdescent : baseEnd_6280368 < baseStart_6280368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280402 : List Nat := [3, 2, 2, 2, 1, 1, 1, 5, 2, 4]
def baseStart_6280402 : Nat := 118140960795 + 6280402 * 2 ^ 59
def prefixEnd_6280402 : Nat := 4983230072969 + 3 ^ 40 * 6280402 * 2
def baseEnd_6280402 : Nat := 1074954976486214043997321

theorem tailTrace_6280402 : CollatzResearch.WordTrace tailWord_6280402 prefixEnd_6280402 1074954976486214043997321 := by
  unfold tailWord_6280402
  simp only [CollatzResearch.WordTrace]
  refine ⟨57266269848295909028020865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152710052928789090741388973 57266269848295909028020865)
  ·
    refine ⟨42949702386221931771015649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57266269848295909028020865 42949702386221931771015649)
    ·
      refine ⟨32212276789666448828261737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42949702386221931771015649 32212276789666448828261737)
      ·
        refine ⟨24159207592249836621196303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32212276789666448828261737 24159207592249836621196303)
        ·
          refine ⟨36238811388374754931794455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24159207592249836621196303 36238811388374754931794455)
          ·
            refine ⟨54358217082562132397691683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36238811388374754931794455 54358217082562132397691683)
            ·
              refine ⟨81537325623843198596537525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54358217082562132397691683 81537325623843198596537525)
              ·
                refine ⟨7644124277235299868425393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81537325623843198596537525 7644124277235299868425393)
                ·
                  refine ⟨5733093207926474901319045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7644124277235299868425393 5733093207926474901319045)
                  ·
                    refine ⟨1074954976486214043997321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5733093207926474901319045 1074954976486214043997321)
                    ·
                      rfl

theorem cell23_6280402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_6280402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280402 prefixEnd_6280402 := by exact prefixLift 6280402
  have htrace : WordTrace (prefixWord ++ tailWord_6280402) baseStart_6280402 baseEnd_6280402 := by
    simpa [prefixWord, tailWord_6280402, baseEnd_6280402] using wordTrace_append hprefix tailTrace_6280402
  have hstable : (prefixWord ++ tailWord_6280402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280402).length < 2 ^ (prefixWord ++ tailWord_6280402).sum := by decide
  have hdescent : baseEnd_6280402 < baseStart_6280402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280413 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_6280413 : Nat := 118140960795 + 6280413 * 2 ^ 59
def prefixEnd_6280413 : Nat := 4983230072969 + 3 ^ 40 * 6280413 * 2
def baseEnd_6280413 : Nat := 3224870577745841588954413

theorem tailTrace_6280413 : CollatzResearch.WordTrace tailWord_6280413 prefixEnd_6280413 3224870577745841588954413 := by
  unfold tailWord_6280413
  simp only [CollatzResearch.WordTrace]
  refine ⟨229065480596143784990733893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152710320397429189993822595 229065480596143784990733893)
  ·
    refine ⟨42949777611776959685762605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229065480596143784990733893 42949777611776959685762605)
    ·
      refine ⟨16106166604416359882160977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42949777611776959685762605 16106166604416359882160977)
      ·
        refine ⟨12079624953312269911620733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16106166604416359882160977 12079624953312269911620733)
        ·
          refine ⟨4529859357492101216857775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12079624953312269911620733 4529859357492101216857775)
          ·
            refine ⟨6794789036238151825286663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4529859357492101216857775 6794789036238151825286663)
            ·
              refine ⟨10192183554357227737929995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6794789036238151825286663 10192183554357227737929995)
              ·
                refine ⟨15288275331535841606894993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10192183554357227737929995 15288275331535841606894993)
                ·
                  refine ⟨11466206498651881205171245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15288275331535841606894993 11466206498651881205171245)
                  ·
                    refine ⟨4299827436994455451939217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11466206498651881205171245 4299827436994455451939217)
                    ·
                      refine ⟨3224870577745841588954413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4299827436994455451939217 3224870577745841588954413)
                      ·
                        rfl

theorem cell23_6280413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_6280413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280413 prefixEnd_6280413 := by exact prefixLift 6280413
  have htrace : WordTrace (prefixWord ++ tailWord_6280413) baseStart_6280413 baseEnd_6280413 := by
    simpa [prefixWord, tailWord_6280413, baseEnd_6280413] using wordTrace_append hprefix tailTrace_6280413
  have hstable : (prefixWord ++ tailWord_6280413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280413).length < 2 ^ (prefixWord ++ tailWord_6280413).sum := by decide
  have hdescent : baseEnd_6280413 < baseStart_6280413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280426 : List Nat := [3, 1, 3, 1, 1, 3, 1, 5, 1, 2, 2]
def baseStart_6280426 : Nat := 118140960795 + 6280426 * 2 ^ 59
def prefixEnd_6280426 : Nat := 4983230072969 + 3 ^ 40 * 6280426 * 2
def baseEnd_6280426 : Nat := 3224877252994350038091853

theorem tailTrace_6280426 : CollatzResearch.WordTrace tailWord_6280426 prefixEnd_6280426 3224877252994350038091853 := by
  unfold tailWord_6280426
  simp only [CollatzResearch.WordTrace]
  refine ⟨57266488686274172052739283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152710636496731125473971421 57266488686274172052739283)
  ·
    refine ⟨85899733029411258079108925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57266488686274172052739283 85899733029411258079108925)
    ·
      refine ⟨32212399886029221779665847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85899733029411258079108925 32212399886029221779665847)
      ·
        refine ⟨48318599829043832669498771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32212399886029221779665847 48318599829043832669498771)
        ·
          refine ⟨72477899743565749004248157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48318599829043832669498771 72477899743565749004248157)
          ·
            refine ⟨27179212403837155876593059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72477899743565749004248157 27179212403837155876593059)
            ·
              refine ⟨40768818605755733814889589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27179212403837155876593059 40768818605755733814889589)
              ·
                refine ⟨3822076744289600045145899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40768818605755733814889589 3822076744289600045145899)
                ·
                  refine ⟨5733115116434400067718849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3822076744289600045145899 5733115116434400067718849)
                  ·
                    refine ⟨4299836337325800050789137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5733115116434400067718849 4299836337325800050789137)
                    ·
                      refine ⟨3224877252994350038091853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4299836337325800050789137 3224877252994350038091853)
                      ·
                        rfl

theorem cell23_6280426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_6280426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280426 prefixEnd_6280426 := by exact prefixLift 6280426
  have htrace : WordTrace (prefixWord ++ tailWord_6280426) baseStart_6280426 baseEnd_6280426 := by
    simpa [prefixWord, tailWord_6280426, baseEnd_6280426] using wordTrace_append hprefix tailTrace_6280426
  have hstable : (prefixWord ++ tailWord_6280426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280426).length < 2 ^ (prefixWord ++ tailWord_6280426).sum := by decide
  have hdescent : baseEnd_6280426 < baseStart_6280426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280429 : List Nat := [1, 5, 1, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_6280429 : Nat := 118140960795 + 6280429 * 2 ^ 59
def prefixEnd_6280429 : Nat := 4983230072969 + 3 ^ 40 * 6280429 * 2
def baseEnd_6280429 : Nat := 3224878793436313526354339

theorem tailTrace_6280429 : CollatzResearch.WordTrace tailWord_6280429 prefixEnd_6280429 3224878793436313526354339 := by
  unfold tailWord_6280429
  simp only [CollatzResearch.WordTrace]
  refine ⟨229066064164085819723316341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152710709442723879815544227 229066064164085819723316341)
  ·
    refine ⟨21474943515383045599060907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229066064164085819723316341 21474943515383045599060907)
    ·
      refine ⟨32212415273074568398591361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21474943515383045599060907 32212415273074568398591361)
      ·
        refine ⟨24159311454805926298943521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32212415273074568398591361 24159311454805926298943521)
        ·
          refine ⟨18119483591104444724207641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24159311454805926298943521 18119483591104444724207641)
          ·
            refine ⟨13589612693328333543155731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18119483591104444724207641 13589612693328333543155731)
            ·
              refine ⟨20384419039992500314733597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13589612693328333543155731 20384419039992500314733597)
              ·
                refine ⟨7644157139997187618025099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20384419039992500314733597 7644157139997187618025099)
                ·
                  refine ⟨11466235709995781427037649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7644157139997187618025099 11466235709995781427037649)
                  ·
                    refine ⟨8599676782496836070278237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11466235709995781427037649 8599676782496836070278237)
                    ·
                      refine ⟨3224878793436313526354339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8599676782496836070278237 3224878793436313526354339)
                      ·
                        rfl

theorem cell23_6280429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_6280429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280429 prefixEnd_6280429 := by exact prefixLift 6280429
  have htrace : WordTrace (prefixWord ++ tailWord_6280429) baseStart_6280429 baseEnd_6280429 := by
    simpa [prefixWord, tailWord_6280429, baseEnd_6280429] using wordTrace_append hprefix tailTrace_6280429
  have hstable : (prefixWord ++ tailWord_6280429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280429).length < 2 ^ (prefixWord ++ tailWord_6280429).sum := by decide
  have hdescent : baseEnd_6280429 < baseStart_6280429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280442 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3]
def baseStart_6280442 : Nat := 118140960795 + 6280442 * 2 ^ 59
def prefixEnd_6280442 : Nat := 4983230072969 + 3 ^ 40 * 6280442 * 2
def baseEnd_6280442 : Nat := 3224885468684821975491779

theorem tailTrace_6280442 : CollatzResearch.WordTrace tailWord_6280442 prefixEnd_6280442 3224885468684821975491779 := by
  unfold tailWord_6280442
  simp only [CollatzResearch.WordTrace]
  refine ⟨57266634578259680735884895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152711025542025815295693053 57266634578259680735884895)
  ·
    refine ⟨85899951867389521103827343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57266634578259680735884895 85899951867389521103827343)
    ·
      refine ⟨128849927801084281655741015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85899951867389521103827343 128849927801084281655741015)
      ·
        refine ⟨193274891701626422483611523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128849927801084281655741015 193274891701626422483611523)
        ·
          refine ⟨289912337552439633725417285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193274891701626422483611523 289912337552439633725417285)
          ·
            refine ⟨54358563291082431323515741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 289912337552439633725417285 54358563291082431323515741)
            ·
              refine ⟨20384461234155911746318403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54358563291082431323515741 20384461234155911746318403)
              ·
                refine ⟨30576691851233867619477605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20384461234155911746318403 30576691851233867619477605)
                ·
                  refine ⟨5733129722106350178652051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30576691851233867619477605 5733129722106350178652051)
                  ·
                    refine ⟨8599694583159525267978077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5733129722106350178652051 8599694583159525267978077)
                    ·
                      refine ⟨3224885468684821975491779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8599694583159525267978077 3224885468684821975491779)
                      ·
                        rfl

theorem cell23_6280442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3].length) (baseStart_6280442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280442 prefixEnd_6280442 := by exact prefixLift 6280442
  have htrace : WordTrace (prefixWord ++ tailWord_6280442) baseStart_6280442 baseEnd_6280442 := by
    simpa [prefixWord, tailWord_6280442, baseEnd_6280442] using wordTrace_append hprefix tailTrace_6280442
  have hstable : (prefixWord ++ tailWord_6280442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280442).length < 2 ^ (prefixWord ++ tailWord_6280442).sum := by decide
  have hdescent : baseEnd_6280442 < baseStart_6280442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280466 : List Nat := [3, 2, 4, 2, 1, 2, 2, 7]
def baseStart_6280466 : Nat := 118140960795 + 6280466 * 2 ^ 59
def prefixEnd_6280466 : Nat := 4983230072969 + 3 ^ 40 * 6280466 * 2
def baseEnd_6280466 : Nat := 119440658971130736355247

theorem tailTrace_6280466 : CollatzResearch.WordTrace tailWord_6280466 prefixEnd_6280466 119440658971130736355247 := by
  unfold tailWord_6280466
  simp only [CollatzResearch.WordTrace]
  refine ⟨57266853416237943760603313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152711609109967850028275501 57266853416237943760603313)
  ·
    refine ⟨42950140062178457820452485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57266853416237943760603313 42950140062178457820452485)
    ·
      refine ⟨8053151261658460841334841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42950140062178457820452485 8053151261658460841334841)
      ·
        refine ⟨6039863446243845631001131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8053151261658460841334841 6039863446243845631001131)
        ·
          refine ⟨9059795169365768446501697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6039863446243845631001131 9059795169365768446501697)
          ·
            refine ⟨6794846377024326334876273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9059795169365768446501697 6794846377024326334876273)
            ·
              refine ⟨5096134782768244751157205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6794846377024326334876273 5096134782768244751157205)
              ·
                refine ⟨119440658971130736355247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5096134782768244751157205 119440658971130736355247)
                ·
                  rfl

theorem cell23_6280466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 7].length) (baseStart_6280466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280466 prefixEnd_6280466 := by exact prefixLift 6280466
  have htrace : WordTrace (prefixWord ++ tailWord_6280466) baseStart_6280466 baseEnd_6280466 := by
    simpa [prefixWord, tailWord_6280466, baseEnd_6280466] using wordTrace_append hprefix tailTrace_6280466
  have hstable : (prefixWord ++ tailWord_6280466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280466).length < 2 ^ (prefixWord ++ tailWord_6280466).sum := by decide
  have hdescent : baseEnd_6280466 < baseStart_6280466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280485 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 1, 3, 5]
def baseStart_6280485 : Nat := 118140960795 + 6280485 * 2 ^ 59
def prefixEnd_6280485 : Nat := 4983230072969 + 3 ^ 40 * 6280485 * 2
def baseEnd_6280485 : Nat := 3224907548352965307254081

theorem tailTrace_6280485 : CollatzResearch.WordTrace tailWord_6280485 prefixEnd_6280485 3224907548352965307254081 := by
  unfold tailWord_6280485
  simp only [CollatzResearch.WordTrace]
  refine ⟨229068106651882941287354909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152712071101255294191569939 229068106651882941287354909)
  ·
    refine ⟨85900539994456102982758091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229068106651882941287354909 85900539994456102982758091)
    ·
      refine ⟨128850809991684154474137137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85900539994456102982758091 128850809991684154474137137)
      ·
        refine ⟨96638107493763115855602853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128850809991684154474137137 96638107493763115855602853)
        ·
          refine ⟨18119645155080584222925535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96638107493763115855602853 18119645155080584222925535)
          ·
            refine ⟨27179467732620876334388303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18119645155080584222925535 27179467732620876334388303)
            ·
              refine ⟨40769201598931314501582455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27179467732620876334388303 40769201598931314501582455)
              ·
                refine ⟨61153802398396971752373683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40769201598931314501582455 61153802398396971752373683)
                ·
                  refine ⟨91730703597595457628560525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61153802398396971752373683 91730703597595457628560525)
                  ·
                    refine ⟨34399013849098296610710197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91730703597595457628560525 34399013849098296610710197)
                    ·
                      refine ⟨3224907548352965307254081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34399013849098296610710197 3224907548352965307254081)
                      ·
                        rfl

theorem cell23_6280485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_6280485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280485 prefixEnd_6280485 := by exact prefixLift 6280485
  have htrace : WordTrace (prefixWord ++ tailWord_6280485) baseStart_6280485 baseEnd_6280485 := by
    simpa [prefixWord, tailWord_6280485, baseEnd_6280485] using wordTrace_append hprefix tailTrace_6280485
  have hstable : (prefixWord ++ tailWord_6280485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280485).length < 2 ^ (prefixWord ++ tailWord_6280485).sum := by decide
  have hdescent : baseEnd_6280485 < baseStart_6280485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280499 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 4, 2, 2]
def baseStart_6280499 : Nat := 118140960795 + 6280499 * 2 ^ 59
def prefixEnd_6280499 : Nat := 4983230072969 + 3 ^ 40 * 6280499 * 2
def baseEnd_6280499 : Nat := 3224914737082128252479017

theorem tailTrace_6280499 : CollatzResearch.WordTrace tailWord_6280499 prefixEnd_6280499 3224914737082128252479017 := by
  unfold tailWord_6280499
  simp only [CollatzResearch.WordTrace]
  refine ⟨229068617273832221678364551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152712411515888147785576367 229068617273832221678364551)
  ·
    refine ⟨343602925910748332517546827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229068617273832221678364551 343602925910748332517546827)
    ·
      refine ⟨515404388866122498776320241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343602925910748332517546827 515404388866122498776320241)
      ·
        refine ⟨386553291649591874082240181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515404388866122498776320241 386553291649591874082240181)
        ·
          refine ⟨36239371092149238195210017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 386553291649591874082240181 36239371092149238195210017)
          ·
            refine ⟨27179528319111928646407513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36239371092149238195210017 27179528319111928646407513)
            ·
              refine ⟨20384646239333946484805635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27179528319111928646407513 20384646239333946484805635)
              ·
                refine ⟨30576969359000919727208453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20384646239333946484805635 30576969359000919727208453)
                ·
                  refine ⟨5733181754812672448851585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30576969359000919727208453 5733181754812672448851585)
                  ·
                    refine ⟨4299886316109504336638689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5733181754812672448851585 4299886316109504336638689)
                    ·
                      refine ⟨3224914737082128252479017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4299886316109504336638689 3224914737082128252479017)
                      ·
                        rfl

theorem cell23_6280499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 2, 2].length) (baseStart_6280499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280499 prefixEnd_6280499 := by exact prefixLift 6280499
  have htrace : WordTrace (prefixWord ++ tailWord_6280499) baseStart_6280499 baseEnd_6280499 := by
    simpa [prefixWord, tailWord_6280499, baseEnd_6280499] using wordTrace_append hprefix tailTrace_6280499
  have hstable : (prefixWord ++ tailWord_6280499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280499).length < 2 ^ (prefixWord ++ tailWord_6280499).sum := by decide
  have hdescent : baseEnd_6280499 < baseStart_6280499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280515 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 3]
def baseStart_6280515 : Nat := 118140960795 + 6280515 * 2 ^ 59
def prefixEnd_6280515 : Nat := 4983230072969 + 3 ^ 40 * 6280515 * 2
def baseEnd_6280515 : Nat := 3224922952772600189878943

theorem tailTrace_6280515 : CollatzResearch.WordTrace tailWord_6280515 prefixEnd_6280515 3224922952772600189878943 := by
  unfold tailWord_6280515
  simp only [CollatzResearch.WordTrace]
  refine ⟨229069200841774256410946999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152712800561182837607297999 229069200841774256410946999)
  ·
    refine ⟨343603801262661384616420499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229069200841774256410946999 343603801262661384616420499)
    ·
      refine ⟨515405701893992076924630749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343603801262661384616420499 515405701893992076924630749)
      ·
        refine ⟨193277138210247028846736531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 515405701893992076924630749 193277138210247028846736531)
        ·
          refine ⟨289915707315370543270104797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193277138210247028846736531 289915707315370543270104797)
          ·
            refine ⟨108718390243263953726289299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289915707315370543270104797 108718390243263953726289299)
            ·
              refine ⟨163077585364895930589433949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108718390243263953726289299 163077585364895930589433949)
              ·
                refine ⟨61154094511835973971037731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163077585364895930589433949 61154094511835973971037731)
                ·
                  refine ⟨91731141767753960956556597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61154094511835973971037731 91731141767753960956556597)
                  ·
                    refine ⟨8599794540726933839677181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91731141767753960956556597 8599794540726933839677181)
                    ·
                      refine ⟨3224922952772600189878943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8599794540726933839677181 3224922952772600189878943)
                      ·
                        rfl

theorem cell23_6280515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_6280515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280515 prefixEnd_6280515 := by exact prefixLift 6280515
  have htrace : WordTrace (prefixWord ++ tailWord_6280515) baseStart_6280515 baseEnd_6280515 := by
    simpa [prefixWord, tailWord_6280515, baseEnd_6280515] using wordTrace_append hprefix tailTrace_6280515
  have hstable : (prefixWord ++ tailWord_6280515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280515).length < 2 ^ (prefixWord ++ tailWord_6280515).sum := by decide
  have hdescent : baseEnd_6280515 < baseStart_6280515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280556 : List Nat := [2, 2, 1, 1, 5, 3, 2, 2, 5]
def baseStart_6280556 : Nat := 118140960795 + 6280556 * 2 ^ 59
def prefixEnd_6280556 : Nat := 4983230072969 + 3 ^ 40 * 6280556 * 2
def baseEnd_6280556 : Nat := 358327111719937169940695

theorem tailTrace_6280556 : CollatzResearch.WordTrace tailWord_6280556 prefixEnd_6280556 358327111719937169940695 := by
  unfold tailWord_6280556
  simp only [CollatzResearch.WordTrace]
  refine ⟨114535348117312860206594761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152713797489750480275459681 114535348117312860206594761)
  ·
    refine ⟨85901511087984645154946071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114535348117312860206594761 85901511087984645154946071)
    ·
      refine ⟨128852266631976967732419107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85901511087984645154946071 128852266631976967732419107)
      ·
        refine ⟨193278399947965451598628661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128852266631976967732419107 193278399947965451598628661)
        ·
          refine ⟨18119849995121761087371437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193278399947965451598628661 18119849995121761087371437)
          ·
            refine ⟨6794943748170660407764289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18119849995121761087371437 6794943748170660407764289)
            ·
              refine ⟨5096207811127995305823217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6794943748170660407764289 5096207811127995305823217)
              ·
                refine ⟨3822155858345996479367413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5096207811127995305823217 3822155858345996479367413)
                ·
                  refine ⟨358327111719937169940695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3822155858345996479367413 358327111719937169940695)
                  ·
                    rfl

theorem cell23_6280556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 5].length) (baseStart_6280556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280556 prefixEnd_6280556 := by exact prefixLift 6280556
  have htrace : WordTrace (prefixWord ++ tailWord_6280556) baseStart_6280556 baseEnd_6280556 := by
    simpa [prefixWord, tailWord_6280556, baseEnd_6280556] using wordTrace_append hprefix tailTrace_6280556
  have hstable : (prefixWord ++ tailWord_6280556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280556).length < 2 ^ (prefixWord ++ tailWord_6280556).sum := by decide
  have hdescent : baseEnd_6280556 < baseStart_6280556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280649 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 2, 3, 2]
def baseStart_6280649 : Nat := 118140960795 + 6280649 * 2 ^ 59
def prefixEnd_6280649 : Nat := 4983230072969 + 3 ^ 40 * 6280649 * 2
def baseEnd_6280649 : Nat := 3224991759180302665603327

theorem tailTrace_6280649 : CollatzResearch.WordTrace tailWord_6280649 prefixEnd_6280649 3224991759180302665603327 := by
  unfold tailWord_6280649
  simp only [CollatzResearch.WordTrace]
  refine ⟨229074088223288797296325001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152716058815525864864216667 229074088223288797296325001)
  ·
    refine ⟨171805566167466597972243751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229074088223288797296325001 171805566167466597972243751)
    ·
      refine ⟨257708349251199896958365627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171805566167466597972243751 257708349251199896958365627)
      ·
        refine ⟨386562523876799845437548441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257708349251199896958365627 386562523876799845437548441)
        ·
          refine ⟨289921892907599884078161331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386562523876799845437548441 289921892907599884078161331)
          ·
            refine ⟨434882839361399826117241997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289921892907599884078161331 434882839361399826117241997)
            ·
              refine ⟨163081064760524934793965749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 434882839361399826117241997 163081064760524934793965749)
              ·
                refine ⟨15288849821299212636934289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163081064760524934793965749 15288849821299212636934289)
                ·
                  refine ⟨11466637365974409477700717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15288849821299212636934289 11466637365974409477700717)
                  ·
                    refine ⟨4299989012240403554137769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11466637365974409477700717 4299989012240403554137769)
                    ·
                      refine ⟨3224991759180302665603327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4299989012240403554137769 3224991759180302665603327)
                      ·
                        rfl

theorem cell23_6280649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 3, 2].length) (baseStart_6280649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280649 prefixEnd_6280649 := by exact prefixLift 6280649
  have htrace : WordTrace (prefixWord ++ tailWord_6280649) baseStart_6280649 baseEnd_6280649 := by
    simpa [prefixWord, tailWord_6280649, baseEnd_6280649] using wordTrace_append hprefix tailTrace_6280649
  have hstable : (prefixWord ++ tailWord_6280649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280649).length < 2 ^ (prefixWord ++ tailWord_6280649).sum := by decide
  have hdescent : baseEnd_6280649 < baseStart_6280649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280666 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2]
def baseStart_6280666 : Nat := 118140960795 + 6280666 * 2 ^ 59
def prefixEnd_6280666 : Nat := 4983230072969 + 3 ^ 40 * 6280666 * 2
def baseEnd_6280666 : Nat := 3225000488351429099090749

theorem tailTrace_6280666 : CollatzResearch.WordTrace tailWord_6280666 prefixEnd_6280666 3225000488351429099090749 := by
  unfold tailWord_6280666
  simp only [CollatzResearch.WordTrace]
  refine ⟨57268677066056802299923463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152716472176151472799795901 57268677066056802299923463)
  ·
    refine ⟨85903015599085203449885195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57268677066056802299923463 85903015599085203449885195)
    ·
      refine ⟨128854523398627805174827793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85903015599085203449885195 128854523398627805174827793)
      ·
        refine ⟨96640892548970853881120845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128854523398627805174827793 96640892548970853881120845)
        ·
          refine ⟨36240334705864070205420317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96640892548970853881120845 36240334705864070205420317)
          ·
            refine ⟨13590125514699026327032619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36240334705864070205420317 13590125514699026327032619)
            ·
              refine ⟨20385188272048539490548929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13590125514699026327032619 20385188272048539490548929)
              ·
                refine ⟨15288891204036404617911697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20385188272048539490548929 15288891204036404617911697)
                ·
                  refine ⟨11466668403027303463433773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15288891204036404617911697 11466668403027303463433773)
                  ·
                    refine ⟨4300000651135238798787665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11466668403027303463433773 4300000651135238798787665)
                    ·
                      refine ⟨3225000488351429099090749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4300000651135238798787665 3225000488351429099090749)
                      ·
                        rfl

theorem cell23_6280666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_6280666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280666 prefixEnd_6280666 := by exact prefixLift 6280666
  have htrace : WordTrace (prefixWord ++ tailWord_6280666) baseStart_6280666 baseEnd_6280666 := by
    simpa [prefixWord, tailWord_6280666, baseEnd_6280666] using wordTrace_append hprefix tailTrace_6280666
  have hstable : (prefixWord ++ tailWord_6280666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280666).length < 2 ^ (prefixWord ++ tailWord_6280666).sum := by decide
  have hdescent : baseEnd_6280666 < baseStart_6280666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280693 : List Nat := [1, 3, 5, 1, 1, 3, 1, 2, 1, 5]
def baseStart_6280693 : Nat := 118140960795 + 6280693 * 2 ^ 59
def prefixEnd_6280693 : Nat := 4983230072969 + 3 ^ 40 * 6280693 * 2
def baseEnd_6280693 : Nat := 1075004784109700164484375

theorem tailTrace_6280693 : CollatzResearch.WordTrace tailWord_6280693 prefixEnd_6280693 1075004784109700164484375 := by
  unfold tailWord_6280693
  simp only [CollatzResearch.WordTrace]
  refine ⟨229075693035129392810926733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152717128690086261873951155 229075693035129392810926733)
  ·
    refine ⟨85903384888173522304097525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229075693035129392810926733 85903384888173522304097525)
    ·
      refine ⟨8053442333266267716009143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85903384888173522304097525 8053442333266267716009143)
      ·
        refine ⟨12080163499899401574013715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8053442333266267716009143 12080163499899401574013715)
        ·
          refine ⟨18120245249849102361020573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12080163499899401574013715 18120245249849102361020573)
          ·
            refine ⟨6795091968693413385382715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18120245249849102361020573 6795091968693413385382715)
            ·
              refine ⟨10192637953040120078074073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6795091968693413385382715 10192637953040120078074073)
              ·
                refine ⟨7644478464780090058555555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10192637953040120078074073 7644478464780090058555555)
                ·
                  refine ⟨11466717697170135087833333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7644478464780090058555555 11466717697170135087833333)
                  ·
                    refine ⟨1075004784109700164484375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11466717697170135087833333 1075004784109700164484375)
                    ·
                      rfl

theorem cell23_6280693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_6280693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280693 prefixEnd_6280693 := by exact prefixLift 6280693
  have htrace : WordTrace (prefixWord ++ tailWord_6280693) baseStart_6280693 baseEnd_6280693 := by
    simpa [prefixWord, tailWord_6280693, baseEnd_6280693] using wordTrace_append hprefix tailTrace_6280693
  have hstable : (prefixWord ++ tailWord_6280693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280693).length < 2 ^ (prefixWord ++ tailWord_6280693).sum := by decide
  have hdescent : baseEnd_6280693 < baseStart_6280693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280696 : List Nat := [2, 1, 2, 1, 1, 7, 1, 2, 1, 1, 4]
def baseStart_6280696 : Nat := 118140960795 + 6280696 * 2 ^ 59
def prefixEnd_6280696 : Nat := 4983230072969 + 3 ^ 40 * 6280696 * 2
def baseEnd_6280696 : Nat := 3225015892771063981715611

theorem tailTrace_6280696 : CollatzResearch.WordTrace tailWord_6280696 prefixEnd_6280696 3225015892771063981715611 := by
  unfold tailWord_6280696
  simp only [CollatzResearch.WordTrace]
  refine ⟨114537901227059262161642971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152717201636079016215523961 114537901227059262161642971)
  ·
    refine ⟨171806851840588893242464457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114537901227059262161642971 171806851840588893242464457)
    ·
      refine ⟨128855138880441669931848343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171806851840588893242464457 128855138880441669931848343)
      ·
        refine ⟨193282708320662504897772515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128855138880441669931848343 193282708320662504897772515)
        ·
          refine ⟨289924062480993757346658773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193282708320662504897772515 289924062480993757346658773)
          ·
            refine ⟨6795095214398291187812315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 289924062480993757346658773 6795095214398291187812315)
            ·
              refine ⟨10192642821597436781718473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6795095214398291187812315 10192642821597436781718473)
              ·
                refine ⟨7644482116198077586288855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10192642821597436781718473 7644482116198077586288855)
                ·
                  refine ⟨11466723174297116379433283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7644482116198077586288855 11466723174297116379433283)
                  ·
                    refine ⟨17200084761445674569149925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11466723174297116379433283 17200084761445674569149925)
                    ·
                      refine ⟨3225015892771063981715611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17200084761445674569149925 3225015892771063981715611)
                      ·
                        rfl

theorem cell23_6280696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_6280696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280696 prefixEnd_6280696 := by exact prefixLift 6280696
  have htrace : WordTrace (prefixWord ++ tailWord_6280696) baseStart_6280696 baseEnd_6280696 := by
    simpa [prefixWord, tailWord_6280696, baseEnd_6280696] using wordTrace_append hprefix tailTrace_6280696
  have hstable : (prefixWord ++ tailWord_6280696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280696).length < 2 ^ (prefixWord ++ tailWord_6280696).sum := by decide
  have hdescent : baseEnd_6280696 < baseStart_6280696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280706 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_6280706 : Nat := 118140960795 + 6280706 * 2 ^ 59
def prefixEnd_6280706 : Nat := 4983230072969 + 3 ^ 40 * 6280706 * 2
def baseEnd_6280706 : Nat := 1075007009192536314196855

theorem tailTrace_6280706 : CollatzResearch.WordTrace tailWord_6280706 prefixEnd_6280706 1075007009192536314196855 := by
  unfold tailWord_6280706
  simp only [CollatzResearch.WordTrace]
  refine ⟨57269041796020574007787493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152717444789388197354099981 57269041796020574007787493)
  ·
    refine ⟨10737945336753857626460155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57269041796020574007787493 10737945336753857626460155)
    ·
      refine ⟨16106918005130786439690233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10737945336753857626460155 16106918005130786439690233)
      ·
        refine ⟨12080188503848089829767675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16106918005130786439690233 12080188503848089829767675)
        ·
          refine ⟨18120282755772134744651513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12080188503848089829767675 18120282755772134744651513)
          ·
            refine ⟨13590212066829101058488635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18120282755772134744651513 13590212066829101058488635)
            ·
              refine ⟨20385318100243651587732953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13590212066829101058488635 20385318100243651587732953)
              ·
                refine ⟨15288988575182738690799715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20385318100243651587732953 15288988575182738690799715)
                ·
                  refine ⟨22933482862774108036199573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15288988575182738690799715 22933482862774108036199573)
                  ·
                    refine ⟨1075007009192536314196855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22933482862774108036199573 1075007009192536314196855)
                    ·
                      rfl

theorem cell23_6280706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_6280706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280706 prefixEnd_6280706 := by exact prefixLift 6280706
  have htrace : WordTrace (prefixWord ++ tailWord_6280706) baseStart_6280706 baseEnd_6280706 := by
    simpa [prefixWord, tailWord_6280706, baseEnd_6280706] using wordTrace_append hprefix tailTrace_6280706
  have hstable : (prefixWord ++ tailWord_6280706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280706).length < 2 ^ (prefixWord ++ tailWord_6280706).sum := by decide
  have hdescent : baseEnd_6280706 < baseStart_6280706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280713 : List Nat := [1, 2, 1, 1, 3, 1, 4, 5, 1, 2, 2]
def baseStart_6280713 : Nat := 118140960795 + 6280713 * 2 ^ 59
def prefixEnd_6280713 : Nat := 4983230072969 + 3 ^ 40 * 6280713 * 2
def baseEnd_6280713 : Nat := 3225024621942190415203033

theorem tailTrace_6280713 : CollatzResearch.WordTrace tailWord_6280713 prefixEnd_6280713 3225024621942190415203033 := by
  unfold tailWord_6280713
  simp only [CollatzResearch.WordTrace]
  refine ⟨229076422495056936226654793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152717614996704624151103195 229076422495056936226654793)
  ·
    refine ⟨171807316871292702169991095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229076422495056936226654793 171807316871292702169991095)
    ·
      refine ⟨257710975306939053254986643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171807316871292702169991095 257710975306939053254986643)
      ·
        refine ⟨386566462960408579882479965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257710975306939053254986643 386566462960408579882479965)
        ·
          refine ⟨144962423610153217455929987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386566462960408579882479965 144962423610153217455929987)
          ·
            refine ⟨217443635415229826183894981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144962423610153217455929987 217443635415229826183894981)
            ·
              refine ⟨40770681640355592409480309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217443635415229826183894981 40770681640355592409480309)
              ·
                refine ⟨3822251403783336788388779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40770681640355592409480309 3822251403783336788388779)
                ·
                  refine ⟨5733377105675005182583169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3822251403783336788388779 5733377105675005182583169)
                  ·
                    refine ⟨4300032829256253886937377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5733377105675005182583169 4300032829256253886937377)
                    ·
                      refine ⟨3225024621942190415203033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4300032829256253886937377 3225024621942190415203033)
                      ·
                        rfl

theorem cell23_6280713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 1, 2, 2].length) (baseStart_6280713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280713 prefixEnd_6280713 := by exact prefixLift 6280713
  have htrace : WordTrace (prefixWord ++ tailWord_6280713) baseStart_6280713 baseEnd_6280713 := by
    simpa [prefixWord, tailWord_6280713, baseEnd_6280713] using wordTrace_append hprefix tailTrace_6280713
  have hstable : (prefixWord ++ tailWord_6280713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280713).length < 2 ^ (prefixWord ++ tailWord_6280713).sum := by decide
  have hdescent : baseEnd_6280713 < baseStart_6280713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280716 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 1, 1, 5]
def baseStart_6280716 : Nat := 118140960795 + 6280716 * 2 ^ 59
def prefixEnd_6280716 : Nat := 4983230072969 + 3 ^ 40 * 6280716 * 2
def baseEnd_6280716 : Nat := 3225026162384153903465519

theorem tailTrace_6280716 : CollatzResearch.WordTrace tailWord_6280716 prefixEnd_6280716 3225026162384153903465519 := by
  unfold tailWord_6280716
  simp only [CollatzResearch.WordTrace]
  refine ⟨114538265957023033869507001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152717687942697378492676001 114538265957023033869507001)
  ·
    refine ⟨85903699467767275402130251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114538265957023033869507001 85903699467767275402130251)
    ·
      refine ⟨128855549201650913103195377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85903699467767275402130251 128855549201650913103195377)
      ·
        refine ⟨96641661901238184827396533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128855549201650913103195377 96641661901238184827396533)
        ·
          refine ⟨9060155803241079827568425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96641661901238184827396533 9060155803241079827568425)
          ·
            refine ⟨6795116852430809870676319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9060155803241079827568425 6795116852430809870676319)
            ·
              refine ⟨10192675278646214806014479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6795116852430809870676319 10192675278646214806014479)
              ·
                refine ⟨15289012917969322209021719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10192675278646214806014479 15289012917969322209021719)
                ·
                  refine ⟨22933519376953983313532579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15289012917969322209021719 22933519376953983313532579)
                  ·
                    refine ⟨34400279065430974970298869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22933519376953983313532579 34400279065430974970298869)
                    ·
                      refine ⟨3225026162384153903465519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34400279065430974970298869 3225026162384153903465519)
                      ·
                        rfl

theorem cell23_6280716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_6280716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280716 prefixEnd_6280716 := by exact prefixLift 6280716
  have htrace : WordTrace (prefixWord ++ tailWord_6280716) baseStart_6280716 baseEnd_6280716 := by
    simpa [prefixWord, tailWord_6280716, baseEnd_6280716] using wordTrace_append hprefix tailTrace_6280716
  have hstable : (prefixWord ++ tailWord_6280716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280716).length < 2 ^ (prefixWord ++ tailWord_6280716).sum := by decide
  have hdescent : baseEnd_6280716 < baseStart_6280716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280724 : List Nat := [2, 4, 3, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_6280724 : Nat := 118140960795 + 6280724 * 2 ^ 59
def prefixEnd_6280724 : Nat := 4983230072969 + 3 ^ 40 * 6280724 * 2
def baseEnd_6280724 : Nat := 3225030270229389872165483

theorem tailTrace_6280724 : CollatzResearch.WordTrace tailWord_6280724 prefixEnd_6280724 3225030270229389872165483 := by
  unfold tailWord_6280724
  simp only [CollatzResearch.WordTrace]
  refine ⟨114538411849008542552652613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152717882465344723403536817 114538411849008542552652613)
  ·
    refine ⟨21475952221689101728622365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114538411849008542552652613 21475952221689101728622365)
    ·
      refine ⟨8053482083133413148233387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21475952221689101728622365 8053482083133413148233387)
      ·
        refine ⟨12080223124700119722350081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8053482083133413148233387 12080223124700119722350081)
        ·
          refine ⟨9060167343525089791762561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12080223124700119722350081 9060167343525089791762561)
          ·
            refine ⟨6795125507643817343821921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9060167343525089791762561 6795125507643817343821921)
            ·
              refine ⟨5096344130732863007866441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6795125507643817343821921 5096344130732863007866441)
              ·
                refine ⟨3822258098049647255899831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5096344130732863007866441 3822258098049647255899831)
                ·
                  refine ⟨5733387147074470883849747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3822258098049647255899831 5733387147074470883849747)
                  ·
                    refine ⟨8600080720611706325774621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5733387147074470883849747 8600080720611706325774621)
                    ·
                      refine ⟨3225030270229389872165483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8600080720611706325774621 3225030270229389872165483)
                      ·
                        rfl

theorem cell23_6280724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_6280724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280724 prefixEnd_6280724 := by exact prefixLift 6280724
  have htrace : WordTrace (prefixWord ++ tailWord_6280724) baseStart_6280724 baseEnd_6280724 := by
    simpa [prefixWord, tailWord_6280724, baseEnd_6280724] using wordTrace_append hprefix tailTrace_6280724
  have hstable : (prefixWord ++ tailWord_6280724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280724).length < 2 ^ (prefixWord ++ tailWord_6280724).sum := by decide
  have hdescent : baseEnd_6280724 < baseStart_6280724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6280732 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 1, 9]
def baseStart_6280732 : Nat := 118140960795 + 6280732 * 2 ^ 59
def prefixEnd_6280732 : Nat := 4983230072969 + 3 ^ 40 * 6280732 * 2
def baseEnd_6280732 : Nat := 1075011459358208613621815

theorem tailTrace_6280732 : CollatzResearch.WordTrace tailWord_6280732 prefixEnd_6280732 1075011459358208613621815 := by
  unfold tailWord_6280732
  simp only [CollatzResearch.WordTrace]
  refine ⟨114538557740994051235798225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152718076987992068314397633 114538557740994051235798225)
  ·
    refine ⟨85903918305745538426848669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114538557740994051235798225 85903918305745538426848669)
    ·
      refine ⟨32213969364654576910068251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85903918305745538426848669 32213969364654576910068251)
      ·
        refine ⟨48320954046981865365102377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32213969364654576910068251 48320954046981865365102377)
        ·
          refine ⟨36240715535236399023826783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48320954046981865365102377 36240715535236399023826783)
          ·
            refine ⟨54361073302854598535740175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36240715535236399023826783 54361073302854598535740175)
            ·
              refine ⟨81541609954281897803610263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54361073302854598535740175 81541609954281897803610263)
              ·
                refine ⟨122312414931422846705415395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81541609954281897803610263 122312414931422846705415395)
                ·
                  refine ⟨183468622397134270058123093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122312414931422846705415395 183468622397134270058123093)
                  ·
                    refine ⟨1075011459358208613621815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 183468622397134270058123093 1075011459358208613621815)
                    ·
                      rfl

theorem cell23_6280732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_6280732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6280732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6280732 prefixEnd_6280732 := by exact prefixLift 6280732
  have htrace : WordTrace (prefixWord ++ tailWord_6280732) baseStart_6280732 baseEnd_6280732 := by
    simpa [prefixWord, tailWord_6280732, baseEnd_6280732] using wordTrace_append hprefix tailTrace_6280732
  have hstable : (prefixWord ++ tailWord_6280732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6280732).length < 2 ^ (prefixWord ++ tailWord_6280732).sum := by decide
  have hdescent : baseEnd_6280732 < baseStart_6280732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6280732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
