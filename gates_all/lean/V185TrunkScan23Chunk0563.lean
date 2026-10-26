import V185TrunkScan23Chunk0562

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3328133 : List Nat := [1, 3, 1, 1, 5, 2, 2, 2, 1, 5]
def baseStart_3328133 : Nat := 118140960795 + 3328133 * 2 ^ 59
def prefixEnd_3328133 : Nat := 4983230072969 + 3 ^ 40 * 3328133 * 2
def baseEnd_3328133 : Nat := 569643970363377466010567

theorem tailTrace_3328133 : CollatzResearch.WordTrace tailWord_3328133 prefixEnd_3328133 569643970363377466010567 := by
  unfold tailWord_3328133
  simp only [CollatzResearch.WordTrace]
  refine ⟨121386982851750015708885053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80924655234500010472590035 121386982851750015708885053)
  ·
    refine ⟨45520118569406255890831895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121386982851750015708885053 45520118569406255890831895)
    ·
      refine ⟨68280177854109383836247843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45520118569406255890831895 68280177854109383836247843)
      ·
        refine ⟨102420266781164075754371765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68280177854109383836247843 102420266781164075754371765)
        ·
          refine ⟨9601900010734132101972353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102420266781164075754371765 9601900010734132101972353)
          ·
            refine ⟨7201425008050599076479265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9601900010734132101972353 7201425008050599076479265)
            ·
              refine ⟨5401068756037949307359449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7201425008050599076479265 5401068756037949307359449)
              ·
                refine ⟨4050801567028461980519587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5401068756037949307359449 4050801567028461980519587)
                ·
                  refine ⟨6076202350542692970779381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4050801567028461980519587 6076202350542692970779381)
                  ·
                    refine ⟨569643970363377466010567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6076202350542692970779381 569643970363377466010567)
                    ·
                      rfl

theorem cell23_3328133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_3328133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328133 prefixEnd_3328133 := by exact prefixLift 3328133
  have htrace : WordTrace (prefixWord ++ tailWord_3328133) baseStart_3328133 baseEnd_3328133 := by
    simpa [prefixWord, tailWord_3328133, baseEnd_3328133] using wordTrace_append hprefix tailTrace_3328133
  have hstable : (prefixWord ++ tailWord_3328133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328133).length < 2 ^ (prefixWord ++ tailWord_3328133).sum := by decide
  have hdescent : baseEnd_3328133 < baseStart_3328133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328146 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3328146 : Nat := 118140960795 + 3328146 * 2 ^ 59
def prefixEnd_3328146 : Nat := 4983230072969 + 3 ^ 40 * 3328146 * 2
def baseEnd_3328146 : Nat := 569646195446213615723047

theorem tailTrace_3328146 : CollatzResearch.WordTrace tailWord_3328146 prefixEnd_3328146 569646195446213615723047 := by
  unfold tailWord_3328146
  simp only [CollatzResearch.WordTrace]
  refine ⟨30346864250175729732277073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80924971333801945952738861 30346864250175729732277073)
  ·
    refine ⟨22760148187631797299207805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30346864250175729732277073 22760148187631797299207805)
    ·
      refine ⟨8535055570361923987202927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22760148187631797299207805 8535055570361923987202927)
      ·
        refine ⟨12802583355542885980804391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8535055570361923987202927 12802583355542885980804391)
        ·
          refine ⟨19203875033314328971206587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12802583355542885980804391 19203875033314328971206587)
          ·
            refine ⟨28805812549971493456809881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19203875033314328971206587 28805812549971493456809881)
            ·
              refine ⟨21604359412478620092607411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28805812549971493456809881 21604359412478620092607411)
              ·
                refine ⟨32406539118717930138911117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21604359412478620092607411 32406539118717930138911117)
                ·
                  refine ⟨12152452169519223802091669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32406539118717930138911117 12152452169519223802091669)
                  ·
                    refine ⟨569646195446213615723047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12152452169519223802091669 569646195446213615723047)
                    ·
                      rfl

theorem cell23_3328146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3328146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328146 prefixEnd_3328146 := by exact prefixLift 3328146
  have htrace : WordTrace (prefixWord ++ tailWord_3328146) baseStart_3328146 baseEnd_3328146 := by
    simpa [prefixWord, tailWord_3328146, baseEnd_3328146] using wordTrace_append hprefix tailTrace_3328146
  have hstable : (prefixWord ++ tailWord_3328146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328146).length < 2 ^ (prefixWord ++ tailWord_3328146).sum := by decide
  have hdescent : baseEnd_3328146 < baseStart_3328146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328153 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 5, 2, 2]
def baseStart_3328153 : Nat := 118140960795 + 3328153 * 2 ^ 59
def prefixEnd_3328153 : Nat := 4983230072969 + 3 ^ 40 * 3328153 * 2
def baseEnd_3328153 : Nat := 1708942180703222319781609

theorem tailTrace_3328153 : CollatzResearch.WordTrace tailWord_3328153 prefixEnd_3328153 1708942180703222319781609 := by
  unfold tailWord_3328153
  simp only [CollatzResearch.WordTrace]
  refine ⟨121387712311677559124613113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80925141541118372749742075 121387712311677559124613113)
  ·
    refine ⟨91040784233758169343459835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121387712311677559124613113 91040784233758169343459835)
    ·
      refine ⟨136561176350637254015189753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91040784233758169343459835 136561176350637254015189753)
      ·
        refine ⟨102420882262977940511392315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136561176350637254015189753 102420882262977940511392315)
        ·
          refine ⟨153631323394466910767088473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102420882262977940511392315 153631323394466910767088473)
          ·
            refine ⟨115223492545850183075316355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153631323394466910767088473 115223492545850183075316355)
            ·
              refine ⟨172835238818775274612974533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115223492545850183075316355 172835238818775274612974533)
              ·
                refine ⟨32406607278520363989932725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172835238818775274612974533 32406607278520363989932725)
                ·
                  refine ⟨3038119432361284124056193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32406607278520363989932725 3038119432361284124056193)
                  ·
                    refine ⟨2278589574270963093042145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3038119432361284124056193 2278589574270963093042145)
                    ·
                      refine ⟨1708942180703222319781609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2278589574270963093042145 1708942180703222319781609)
                      ·
                        rfl

theorem cell23_3328153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 2, 2].length) (baseStart_3328153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328153 prefixEnd_3328153 := by exact prefixLift 3328153
  have htrace : WordTrace (prefixWord ++ tailWord_3328153) baseStart_3328153 baseEnd_3328153 := by
    simpa [prefixWord, tailWord_3328153, baseEnd_3328153] using wordTrace_append hprefix tailTrace_3328153
  have hstable : (prefixWord ++ tailWord_3328153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328153).length < 2 ^ (prefixWord ++ tailWord_3328153).sum := by decide
  have hdescent : baseEnd_3328153 < baseStart_3328153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328164 : List Nat := [2, 3, 1, 2, 4, 1, 3, 2, 1, 1, 3]
def baseStart_3328164 : Nat := 118140960795 + 3328164 * 2 ^ 59
def prefixEnd_3328164 : Nat := 4983230072969 + 3 ^ 40 * 3328164 * 2
def baseEnd_3328164 : Nat := 1708947828990421776744059

theorem tailTrace_3328164 : CollatzResearch.WordTrace tailWord_3328164 prefixEnd_3328164 1708947828990421776744059 := by
  unfold tailWord_3328164
  simp only [CollatzResearch.WordTrace]
  refine ⟨60694056757318854001631773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80925409009758472002175697 60694056757318854001631773)
  ·
    refine ⟨22760271283994570250611915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60694056757318854001631773 22760271283994570250611915)
    ·
      refine ⟨34140406925991855375917873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22760271283994570250611915 34140406925991855375917873)
      ·
        refine ⟨25605305194493891531938405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34140406925991855375917873 25605305194493891531938405)
        ·
          refine ⟨4800994723967604662238451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25605305194493891531938405 4800994723967604662238451)
          ·
            refine ⟨7201492085951406993357677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4800994723967604662238451 7201492085951406993357677)
            ·
              refine ⟨2700559532231777622509129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7201492085951406993357677 2700559532231777622509129)
              ·
                refine ⟨2025419649173833216881847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2700559532231777622509129 2025419649173833216881847)
                ·
                  refine ⟨3038129473760749825322771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025419649173833216881847 3038129473760749825322771)
                  ·
                    refine ⟨4557194210641124737984157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3038129473760749825322771 4557194210641124737984157)
                    ·
                      refine ⟨1708947828990421776744059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4557194210641124737984157 1708947828990421776744059)
                      ·
                        rfl

theorem cell23_3328164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_3328164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328164 prefixEnd_3328164 := by exact prefixLift 3328164
  have htrace : WordTrace (prefixWord ++ tailWord_3328164) baseStart_3328164 baseEnd_3328164 := by
    simpa [prefixWord, tailWord_3328164, baseEnd_3328164] using wordTrace_append hprefix tailTrace_3328164
  have hstable : (prefixWord ++ tailWord_3328164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328164).length < 2 ^ (prefixWord ++ tailWord_3328164).sum := by decide
  have hdescent : baseEnd_3328164 < baseStart_3328164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328173 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_3328173 : Nat := 118140960795 + 3328173 * 2 ^ 59
def prefixEnd_3328173 : Nat := 4983230072969 + 3 ^ 40 * 3328173 * 2
def baseEnd_3328173 : Nat := 1708952450316312241531517

theorem tailTrace_3328173 : CollatzResearch.WordTrace tailWord_3328173 prefixEnd_3328173 1708952450316312241531517 := by
  unfold tailWord_3328173
  simp only [CollatzResearch.WordTrace]
  refine ⟨121388441771605102540341173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80925627847736735026894115 121388441771605102540341173)
  ·
    refine ⟨11380166416087978363156985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121388441771605102540341173 11380166416087978363156985)
    ·
      refine ⟨8535124812065983772367739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11380166416087978363156985 8535124812065983772367739)
      ·
        refine ⟨12802687218098975658551609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8535124812065983772367739 12802687218098975658551609)
        ·
          refine ⟨9602015413574231743913707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12802687218098975658551609 9602015413574231743913707)
          ·
            refine ⟨14403023120361347615870561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9602015413574231743913707 14403023120361347615870561)
            ·
              refine ⟨10802267340271010711902921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14403023120361347615870561 10802267340271010711902921)
              ·
                refine ⟨8101700505203258033927191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10802267340271010711902921 8101700505203258033927191)
                ·
                  refine ⟨12152550757804887050890787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8101700505203258033927191 12152550757804887050890787)
                  ·
                    refine ⟨18228826136707330576336181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12152550757804887050890787 18228826136707330576336181)
                    ·
                      refine ⟨1708952450316312241531517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18228826136707330576336181 1708952450316312241531517)
                      ·
                        rfl

theorem cell23_3328173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_3328173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328173 prefixEnd_3328173 := by exact prefixLift 3328173
  have htrace : WordTrace (prefixWord ++ tailWord_3328173) baseStart_3328173 baseEnd_3328173 := by
    simpa [prefixWord, tailWord_3328173, baseEnd_3328173] using wordTrace_append hprefix tailTrace_3328173
  have hstable : (prefixWord ++ tailWord_3328173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328173).length < 2 ^ (prefixWord ++ tailWord_3328173).sum := by decide
  have hdescent : baseEnd_3328173 < baseStart_3328173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328179 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 6]
def baseStart_3328179 : Nat := 118140960795 + 3328179 * 2 ^ 59
def prefixEnd_3328179 : Nat := 4983230072969 + 3 ^ 40 * 3328179 * 2
def baseEnd_3328179 : Nat := 1708955531200239218056489

theorem tailTrace_3328179 : CollatzResearch.WordTrace tailWord_3328179 prefixEnd_3328179 1708955531200239218056489 := by
  unfold tailWord_3328179
  simp only [CollatzResearch.WordTrace]
  refine ⟨121388660609583365565059591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80925773739722243710039727 121388660609583365565059591)
  ·
    refine ⟨182082990914375048347589387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121388660609583365565059591 182082990914375048347589387)
    ·
      refine ⟨273124486371562572521384081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182082990914375048347589387 273124486371562572521384081)
      ·
        refine ⟨204843364778671929391038061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273124486371562572521384081 204843364778671929391038061)
        ·
          refine ⟨76816261792001973521639273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204843364778671929391038061 76816261792001973521639273)
          ·
            refine ⟨57612196344001480141229455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76816261792001973521639273 57612196344001480141229455)
            ·
              refine ⟨86418294516002220211844183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57612196344001480141229455 86418294516002220211844183)
              ·
                refine ⟨129627441774003330317766275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86418294516002220211844183 129627441774003330317766275)
                ·
                  refine ⟨194441162661004995476649413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129627441774003330317766275 194441162661004995476649413)
                  ·
                    refine ⟨36457717998938436651871765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 194441162661004995476649413 36457717998938436651871765)
                    ·
                      refine ⟨1708955531200239218056489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36457717998938436651871765 1708955531200239218056489)
                      ·
                        rfl

theorem cell23_3328179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_3328179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328179 prefixEnd_3328179 := by exact prefixLift 3328179
  have htrace : WordTrace (prefixWord ++ tailWord_3328179) baseStart_3328179 baseEnd_3328179 := by
    simpa [prefixWord, tailWord_3328179, baseEnd_3328179] using wordTrace_append hprefix tailTrace_3328179
  have hstable : (prefixWord ++ tailWord_3328179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328179).length < 2 ^ (prefixWord ++ tailWord_3328179).sum := by decide
  have hdescent : baseEnd_3328179 < baseStart_3328179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328190 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_3328190 : Nat := 118140960795 + 3328190 * 2 ^ 59
def prefixEnd_3328190 : Nat := 4983230072969 + 3 ^ 40 * 3328190 * 2
def baseEnd_3328190 : Nat := 1708961179487438675018939

theorem tailTrace_3328190 : CollatzResearch.WordTrace tailWord_3328190 prefixEnd_3328190 1708961179487438675018939 := by
  unfold tailWord_3328190
  simp only [CollatzResearch.WordTrace]
  refine ⟨15173632726567939305463753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80926041208362342962473349 15173632726567939305463753)
  ·
    refine ⟨11380224544925954479097815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15173632726567939305463753 11380224544925954479097815)
    ·
      refine ⟨17070336817388931718646723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11380224544925954479097815 17070336817388931718646723)
      ·
        refine ⟨25605505226083397577970085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17070336817388931718646723 25605505226083397577970085)
        ·
          refine ⟨4801032229890637045869391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25605505226083397577970085 4801032229890637045869391)
          ·
            refine ⟨7201548344835955568804087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4801032229890637045869391 7201548344835955568804087)
            ·
              refine ⟨10802322517253933353206131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7201548344835955568804087 10802322517253933353206131)
              ·
                refine ⟨16203483775880900029809197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10802322517253933353206131 16203483775880900029809197)
                ·
                  refine ⟨6076306415955337511178449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16203483775880900029809197 6076306415955337511178449)
                  ·
                    refine ⟨4557229811966503133383837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6076306415955337511178449 4557229811966503133383837)
                    ·
                      refine ⟨1708961179487438675018939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4557229811966503133383837 1708961179487438675018939)
                      ·
                        rfl

theorem cell23_3328190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_3328190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328190 prefixEnd_3328190 := by exact prefixLift 3328190
  have htrace : WordTrace (prefixWord ++ tailWord_3328190) baseStart_3328190 baseEnd_3328190 := by
    simpa [prefixWord, tailWord_3328190, baseEnd_3328190] using wordTrace_append hprefix tailTrace_3328190
  have hstable : (prefixWord ++ tailWord_3328190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328190).length < 2 ^ (prefixWord ++ tailWord_3328190).sum := by decide
  have hdescent : baseEnd_3328190 < baseStart_3328190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328221 : List Nat := [1, 4, 3, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_3328221 : Nat := 118140960795 + 3328221 * 2 ^ 59
def prefixEnd_3328221 : Nat := 4983230072969 + 3 ^ 40 * 3328221 * 2
def baseEnd_3328221 : Nat := 1708977097387728053731297

theorem tailTrace_3328221 : CollatzResearch.WordTrace tailWord_3328221 prefixEnd_3328221 1708977097387728053731297 := by
  unfold tailWord_3328221
  simp only [CollatzResearch.WordTrace]
  refine ⟨121390192475431206738088517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80926794983620804492059011 121390192475431206738088517)
  ·
    refine ⟨22760661089143351263391597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121390192475431206738088517 22760661089143351263391597)
    ·
      refine ⟨8535247908428756723771849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22760661089143351263391597 8535247908428756723771849)
      ·
        refine ⟨6401435931321567542828887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8535247908428756723771849 6401435931321567542828887)
        ·
          refine ⟨9602153896982351314243331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6401435931321567542828887 9602153896982351314243331)
          ·
            refine ⟨14403230845473526971364997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9602153896982351314243331 14403230845473526971364997)
            ·
              refine ⟨2700605783526286307130937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14403230845473526971364997 2700605783526286307130937)
              ·
                refine ⟨2025454337644714730348203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2700605783526286307130937 2025454337644714730348203)
                ·
                  refine ⟨3038181506467072095522305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025454337644714730348203 3038181506467072095522305)
                  ·
                    refine ⟨2278636129850304071641729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3038181506467072095522305 2278636129850304071641729)
                    ·
                      refine ⟨1708977097387728053731297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2278636129850304071641729 1708977097387728053731297)
                      ·
                        rfl

theorem cell23_3328221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_3328221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328221 prefixEnd_3328221 := by exact prefixLift 3328221
  have htrace : WordTrace (prefixWord ++ tailWord_3328221) baseStart_3328221 baseEnd_3328221 := by
    simpa [prefixWord, tailWord_3328221, baseEnd_3328221] using wordTrace_append hprefix tailTrace_3328221
  have hstable : (prefixWord ++ tailWord_3328221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328221).length < 2 ^ (prefixWord ++ tailWord_3328221).sum := by decide
  have hdescent : baseEnd_3328221 < baseStart_3328221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328236 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 2, 6]
def baseStart_3328236 : Nat := 118140960795 + 3328236 * 2 ^ 59
def prefixEnd_3328236 : Nat := 4983230072969 + 3 ^ 40 * 3328236 * 2
def baseEnd_3328236 : Nat := 569661599865848498347909

theorem tailTrace_3328236 : CollatzResearch.WordTrace tailWord_3328236 prefixEnd_3328236 569661599865848498347909 := by
  unfold tailWord_3328236
  simp only [CollatzResearch.WordTrace]
  refine ⟨60695369785188432149942281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80927159713584576199923041 60695369785188432149942281)
  ·
    refine ⟨45521527338891324112456711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60695369785188432149942281 45521527338891324112456711)
    ·
      refine ⟨68282291008336986168685067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45521527338891324112456711 68282291008336986168685067)
      ·
        refine ⟨102423436512505479253027601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68282291008336986168685067 102423436512505479253027601)
        ·
          refine ⟨76817577384379109439770701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102423436512505479253027601 76817577384379109439770701)
          ·
            refine ⟨28806591519142166039914013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76817577384379109439770701 28806591519142166039914013)
            ·
              refine ⟨10802471819678312264967755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28806591519142166039914013 10802471819678312264967755)
              ·
                refine ⟨16203707729517468397451633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10802471819678312264967755 16203707729517468397451633)
                ·
                  refine ⟨12152780797138101298088725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16203707729517468397451633 12152780797138101298088725)
                  ·
                    refine ⟨569661599865848498347909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12152780797138101298088725 569661599865848498347909)
                    ·
                      rfl

theorem cell23_3328236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_3328236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328236 prefixEnd_3328236 := by exact prefixLift 3328236
  have htrace : WordTrace (prefixWord ++ tailWord_3328236) baseStart_3328236 baseEnd_3328236 := by
    simpa [prefixWord, tailWord_3328236, baseEnd_3328236] using wordTrace_append hprefix tailTrace_3328236
  have hstable : (prefixWord ++ tailWord_3328236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328236).length < 2 ^ (prefixWord ++ tailWord_3328236).sum := by decide
  have hdescent : baseEnd_3328236 < baseStart_3328236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328264 : List Nat := [2, 1, 3, 2, 3, 3, 2, 1, 1, 3, 2]
def baseStart_3328264 : Nat := 118140960795 + 3328264 * 2 ^ 59
def prefixEnd_3328264 : Nat := 4983230072969 + 3 ^ 40 * 3328264 * 2
def baseEnd_3328264 : Nat := 1708999177055871385493599

theorem tailTrace_3328264 : CollatzResearch.WordTrace tailWord_3328264 prefixEnd_3328264 1708999177055871385493599 := by
  unfold tailWord_3328264
  simp only [CollatzResearch.WordTrace]
  refine ⟨60695880407137712540951923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80927840542850283387935897 60695880407137712540951923)
  ·
    refine ⟨91043820610706568811427885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60695880407137712540951923 91043820610706568811427885)
    ·
      refine ⟨34141432729014963304285457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91043820610706568811427885 34141432729014963304285457)
      ·
        refine ⟨25606074546761222478214093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34141432729014963304285457 25606074546761222478214093)
        ·
          refine ⟨9602277955035458429330285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25606074546761222478214093 9602277955035458429330285)
          ·
            refine ⟨3600854233138296910998857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9602277955035458429330285 3600854233138296910998857)
            ·
              refine ⟨2700640674853722683249143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3600854233138296910998857 2700640674853722683249143)
              ·
                refine ⟨4050961012280584024873715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2700640674853722683249143 4050961012280584024873715)
                ·
                  refine ⟨6076441518420876037310573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4050961012280584024873715 6076441518420876037310573)
                  ·
                    refine ⟨2278665569407828513991465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6076441518420876037310573 2278665569407828513991465)
                    ·
                      refine ⟨1708999177055871385493599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2278665569407828513991465 1708999177055871385493599)
                      ·
                        rfl

theorem cell23_3328264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_3328264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328264 prefixEnd_3328264 := by exact prefixLift 3328264
  have htrace : WordTrace (prefixWord ++ tailWord_3328264) baseStart_3328264 baseEnd_3328264 := by
    simpa [prefixWord, tailWord_3328264, baseEnd_3328264] using wordTrace_append hprefix tailTrace_3328264
  have hstable : (prefixWord ++ tailWord_3328264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328264).length < 2 ^ (prefixWord ++ tailWord_3328264).sum := by decide
  have hdescent : baseEnd_3328264 < baseStart_3328264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328277 : List Nat := [1, 3, 2, 1, 2, 1, 5, 2, 2, 2, 2]
def baseStart_3328277 : Nat := 118140960795 + 3328277 * 2 ^ 59
def prefixEnd_3328277 : Nat := 4983230072969 + 3 ^ 40 * 3328277 * 2
def baseEnd_3328277 : Nat := 1709005852304379834631039

theorem tailTrace_3328277 : CollatzResearch.WordTrace tailWord_3328277 prefixEnd_3328277 1709005852304379834631039 := by
  unfold tailWord_3328277
  simp only [CollatzResearch.WordTrace]
  refine ⟨121392234963228328302127085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80928156642152218868084723 121392234963228328302127085)
  ·
    refine ⟨45522088111210623113297657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121392234963228328302127085 45522088111210623113297657)
    ·
      refine ⟨34141566083407967334973243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45522088111210623113297657 34141566083407967334973243)
      ·
        refine ⟨51212349125111951002459865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34141566083407967334973243 51212349125111951002459865)
        ·
          refine ⟨38409261843833963251844899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51212349125111951002459865 38409261843833963251844899)
          ·
            refine ⟨57613892765750944877767349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38409261843833963251844899 57613892765750944877767349)
            ·
              refine ⟨5401302446789151082290689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57613892765750944877767349 5401302446789151082290689)
              ·
                refine ⟨4050976835091863311718017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5401302446789151082290689 4050976835091863311718017)
                ·
                  refine ⟨3038232626318897483788513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4050976835091863311718017 3038232626318897483788513)
                  ·
                    refine ⟨2278674469739173112841385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3038232626318897483788513 2278674469739173112841385)
                    ·
                      refine ⟨1709005852304379834631039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2278674469739173112841385 1709005852304379834631039)
                      ·
                        rfl

theorem cell23_3328277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_3328277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328277 prefixEnd_3328277 := by exact prefixLift 3328277
  have htrace : WordTrace (prefixWord ++ tailWord_3328277) baseStart_3328277 baseEnd_3328277 := by
    simpa [prefixWord, tailWord_3328277, baseEnd_3328277] using wordTrace_append hprefix tailTrace_3328277
  have hstable : (prefixWord ++ tailWord_3328277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328277).length < 2 ^ (prefixWord ++ tailWord_3328277).sum := by decide
  have hdescent : baseEnd_3328277 < baseStart_3328277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328283 : List Nat := [1, 1, 1, 1, 1, 1, 8, 4, 5]
def baseStart_3328283 : Nat := 118140960795 + 3328283 * 2 ^ 59
def prefixEnd_3328283 : Nat := 4983230072969 + 3 ^ 40 * 3328283 * 2
def baseEnd_3328283 : Nat := 189889881465367423461779

theorem tailTrace_3328283 : CollatzResearch.WordTrace tailWord_3328283 prefixEnd_3328283 189889881465367423461779 := by
  unfold tailWord_3328283
  simp only [CollatzResearch.WordTrace]
  refine ⟨121392453801206591326845503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80928302534137727551230335 121392453801206591326845503)
  ·
    refine ⟨182088680701809886990268255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121392453801206591326845503 182088680701809886990268255)
    ·
      refine ⟨273133021052714830485402383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182088680701809886990268255 273133021052714830485402383)
      ·
        refine ⟨409699531579072245728103575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273133021052714830485402383 409699531579072245728103575)
        ·
          refine ⟨614549297368608368592155363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409699531579072245728103575 614549297368608368592155363)
          ·
            refine ⟨921823946052912552888233045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614549297368608368592155363 921823946052912552888233045)
            ·
              refine ⟨10802624367807568979158981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 921823946052912552888233045 10802624367807568979158981)
              ·
                refine ⟨2025492068963919183592309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10802624367807568979158981 2025492068963919183592309)
                ·
                  refine ⟨189889881465367423461779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2025492068963919183592309 189889881465367423461779)
                  ·
                    rfl

theorem cell23_3328283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 5].length) (baseStart_3328283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328283 prefixEnd_3328283 := by exact prefixLift 3328283
  have htrace : WordTrace (prefixWord ++ tailWord_3328283) baseStart_3328283 baseEnd_3328283 := by
    simpa [prefixWord, tailWord_3328283, baseEnd_3328283] using wordTrace_append hprefix tailTrace_3328283
  have hstable : (prefixWord ++ tailWord_3328283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328283).length < 2 ^ (prefixWord ++ tailWord_3328283).sum := by decide
  have hdescent : baseEnd_3328283 < baseStart_3328283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328303 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 2, 5, 2]
def baseStart_3328303 : Nat := 118140960795 + 3328303 * 2 ^ 59
def prefixEnd_3328303 : Nat := 4983230072969 + 3 ^ 40 * 3328303 * 2
def baseEnd_3328303 : Nat := 1709019202801396732905919

theorem tailTrace_3328303 : CollatzResearch.WordTrace tailWord_3328303 prefixEnd_3328303 1709019202801396732905919 := by
  unfold tailWord_3328303
  simp only [CollatzResearch.WordTrace]
  refine ⟨121393183261134134742573563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80928788840756089828382375 121393183261134134742573563)
  ·
    refine ⟨182089774891701202113860345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121393183261134134742573563 182089774891701202113860345)
    ·
      refine ⟨136567331168775901585395259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182089774891701202113860345 136567331168775901585395259)
      ·
        refine ⟨204850996753163852378092889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136567331168775901585395259 204850996753163852378092889)
        ·
          refine ⟨153638247564872889283569667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204850996753163852378092889 153638247564872889283569667)
          ·
            refine ⟨230457371347309333925354501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153638247564872889283569667 230457371347309333925354501)
            ·
              refine ⟨43210757127620500111003969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 230457371347309333925354501 43210757127620500111003969)
              ·
                refine ⟨32408067845715375083252977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43210757127620500111003969 32408067845715375083252977)
                ·
                  refine ⟨24306050884286531312439733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32408067845715375083252977 24306050884286531312439733)
                  ·
                    refine ⟨2278692270401862310541225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24306050884286531312439733 2278692270401862310541225)
                    ·
                      refine ⟨1709019202801396732905919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2278692270401862310541225 1709019202801396732905919)
                      ·
                        rfl

theorem cell23_3328303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 5, 2].length) (baseStart_3328303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328303 prefixEnd_3328303 := by exact prefixLift 3328303
  have htrace : WordTrace (prefixWord ++ tailWord_3328303) baseStart_3328303 baseEnd_3328303 := by
    simpa [prefixWord, tailWord_3328303, baseEnd_3328303] using wordTrace_append hprefix tailTrace_3328303
  have hstable : (prefixWord ++ tailWord_3328303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328303).length < 2 ^ (prefixWord ++ tailWord_3328303).sum := by decide
  have hdescent : baseEnd_3328303 < baseStart_3328303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328313 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 1, 7]
def baseStart_3328313 : Nat := 118140960795 + 3328313 * 2 ^ 59
def prefixEnd_3328313 : Nat := 4983230072969 + 3 ^ 40 * 3328313 * 2
def baseEnd_3328313 : Nat := 569674779202647231260291

theorem tailTrace_3328313 : CollatzResearch.WordTrace tailWord_3328313 prefixEnd_3328313 569674779202647231260291 := by
  unfold tailWord_3328313
  simp only [CollatzResearch.WordTrace]
  refine ⟨121393547991097906450437593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80929031994065270966958395 121393547991097906450437593)
  ·
    refine ⟨91045160993323429837828195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121393547991097906450437593 91045160993323429837828195)
    ·
      refine ⟨136567741489985144756742293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91045160993323429837828195 136567741489985144756742293)
      ·
        refine ⟨6401612882343053660472295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 136567741489985144756742293 6401612882343053660472295)
        ·
          refine ⟨9602419323514580490708443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6401612882343053660472295 9602419323514580490708443)
          ·
            refine ⟨14403628985271870736062665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9602419323514580490708443 14403628985271870736062665)
            ·
              refine ⟨10802721738953903052046999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14403628985271870736062665 10802721738953903052046999)
              ·
                refine ⟨16204082608430854578070499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10802721738953903052046999 16204082608430854578070499)
                ·
                  refine ⟨24306123912646281867105749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16204082608430854578070499 24306123912646281867105749)
                  ·
                    refine ⟨569674779202647231260291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24306123912646281867105749 569674779202647231260291)
                    ·
                      rfl

theorem cell23_3328313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 7].length) (baseStart_3328313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328313 prefixEnd_3328313 := by exact prefixLift 3328313
  have htrace : WordTrace (prefixWord ++ tailWord_3328313) baseStart_3328313 baseEnd_3328313 := by
    simpa [prefixWord, tailWord_3328313, baseEnd_3328313] using wordTrace_append hprefix tailTrace_3328313
  have hstable : (prefixWord ++ tailWord_3328313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328313).length < 2 ^ (prefixWord ++ tailWord_3328313).sum := by decide
  have hdescent : baseEnd_3328313 < baseStart_3328313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328370 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 2, 2, 3]
def baseStart_3328370 : Nat := 118140960795 + 3328370 * 2 ^ 59
def prefixEnd_3328370 : Nat := 4983230072969 + 3 ^ 40 * 3328370 * 2
def baseEnd_3328370 : Nat := 1709053606005247970768111

theorem tailTrace_3328370 : CollatzResearch.WordTrace tailWord_3328370 prefixEnd_3328370 1709053606005247970768111 := by
  unfold tailWord_3328370
  simp only [CollatzResearch.WordTrace]
  refine ⟨30348906737972851296315641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80930417967927603456841709 30348906737972851296315641)
  ·
    refine ⟨22761680053479638472236731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30348906737972851296315641 22761680053479638472236731)
    ·
      refine ⟨34142520080219457708355097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22761680053479638472236731 34142520080219457708355097)
      ·
        refine ⟨25606890060164593281266323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34142520080219457708355097 25606890060164593281266323)
        ·
          refine ⟨38410335090246889921899485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25606890060164593281266323 38410335090246889921899485)
          ·
            refine ⟨14403875658842583720712307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38410335090246889921899485 14403875658842583720712307)
            ·
              refine ⟨21605813488263875581068461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14403875658842583720712307 21605813488263875581068461)
              ·
                refine ⟨8102180058098953342900673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21605813488263875581068461 8102180058098953342900673)
                ·
                  refine ⟨6076635043574215007175505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8102180058098953342900673 6076635043574215007175505)
                  ·
                    refine ⟨4557476282680661255381629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6076635043574215007175505 4557476282680661255381629)
                    ·
                      refine ⟨1709053606005247970768111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4557476282680661255381629 1709053606005247970768111)
                      ·
                        rfl

theorem cell23_3328370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_3328370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328370 prefixEnd_3328370 := by exact prefixLift 3328370
  have htrace : WordTrace (prefixWord ++ tailWord_3328370) baseStart_3328370 baseEnd_3328370 := by
    simpa [prefixWord, tailWord_3328370, baseEnd_3328370] using wordTrace_append hprefix tailTrace_3328370
  have hstable : (prefixWord ++ tailWord_3328370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328370).length < 2 ^ (prefixWord ++ tailWord_3328370).sum := by decide
  have hdescent : baseEnd_3328370 < baseStart_3328370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328434 : List Nat := [3, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3]
def baseStart_3328434 : Nat := 118140960795 + 3328434 * 2 ^ 59
def prefixEnd_3328434 : Nat := 4983230072969 + 3 ^ 40 * 3328434 * 2
def baseEnd_3328434 : Nat := 1709086468767135720367817

theorem tailTrace_3328434 : CollatzResearch.WordTrace tailWord_3328434 prefixEnd_3328434 1709086468767135720367817 := by
  unfold tailWord_3328434
  simp only [CollatzResearch.WordTrace]
  refine ⟨30349490305914886028898089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80931974149106362743728237 30349490305914886028898089)
  ·
    refine ⟨22762117729436164521673567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30349490305914886028898089 22762117729436164521673567)
    ·
      refine ⟨34143176594154246782510351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22762117729436164521673567 34143176594154246782510351)
      ·
        refine ⟨51214764891231370173765527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34143176594154246782510351 51214764891231370173765527)
        ·
          refine ⟨76822147336847055260648291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51214764891231370173765527 76822147336847055260648291)
          ·
            refine ⟨115233221005270582890972437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76822147336847055260648291 115233221005270582890972437)
            ·
              refine ⟨5401557234622058573014333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115233221005270582890972437 5401557234622058573014333)
              ·
                refine ⟨2025583962983271964880375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5401557234622058573014333 2025583962983271964880375)
                ·
                  refine ⟨3038375944474907947320563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025583962983271964880375 3038375944474907947320563)
                  ·
                    refine ⟨4557563916712361920980845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3038375944474907947320563 4557563916712361920980845)
                    ·
                      refine ⟨1709086468767135720367817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4557563916712361920980845 1709086468767135720367817)
                      ·
                        rfl

theorem cell23_3328434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_3328434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328434 prefixEnd_3328434 := by exact prefixLift 3328434
  have htrace : WordTrace (prefixWord ++ tailWord_3328434) baseStart_3328434 baseEnd_3328434 := by
    simpa [prefixWord, tailWord_3328434, baseEnd_3328434] using wordTrace_append hprefix tailTrace_3328434
  have hstable : (prefixWord ++ tailWord_3328434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328434).length < 2 ^ (prefixWord ++ tailWord_3328434).sum := by decide
  have hdescent : baseEnd_3328434 < baseStart_3328434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328437 : List Nat := [1, 3, 3, 2, 3, 1, 1, 3, 1, 5]
def baseStart_3328437 : Nat := 118140960795 + 3328437 * 2 ^ 59
def prefixEnd_3328437 : Nat := 4983230072969 + 3 ^ 40 * 3328437 * 2
def baseEnd_3328437 : Nat := 569696003069699736210101

theorem tailTrace_3328437 : CollatzResearch.WordTrace tailWord_3328437 prefixEnd_3328437 569696003069699736210101 := by
  unfold tailWord_3328437
  simp only [CollatzResearch.WordTrace]
  refine ⟨121398070642648675627951565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80932047095099117085301043 121398070642648675627951565)
  ·
    refine ⟨45524276490993253360481837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121398070642648675627951565 45524276490993253360481837)
    ·
      refine ⟨17071603684122470010180689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45524276490993253360481837 17071603684122470010180689)
      ·
        refine ⟨12803702763091852507635517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17071603684122470010180689 12803702763091852507635517)
        ·
          refine ⟨4801388536159444690363319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12803702763091852507635517 4801388536159444690363319)
          ·
            refine ⟨7202082804239167035544979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4801388536159444690363319 7202082804239167035544979)
            ·
              refine ⟨10803124206358750553317469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7202082804239167035544979 10803124206358750553317469)
              ·
                refine ⟨4051171577384531457494051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10803124206358750553317469 4051171577384531457494051)
                ·
                  refine ⟨6076757366076797186241077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4051171577384531457494051 6076757366076797186241077)
                  ·
                    refine ⟨569696003069699736210101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6076757366076797186241077 569696003069699736210101)
                    ·
                      rfl

theorem cell23_3328437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_3328437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328437 prefixEnd_3328437 := by exact prefixLift 3328437
  have htrace : WordTrace (prefixWord ++ tailWord_3328437) baseStart_3328437 baseEnd_3328437 := by
    simpa [prefixWord, tailWord_3328437, baseEnd_3328437] using wordTrace_append hprefix tailTrace_3328437
  have hstable : (prefixWord ++ tailWord_3328437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328437).length < 2 ^ (prefixWord ++ tailWord_3328437).sum := by decide
  have hdescent : baseEnd_3328437 < baseStart_3328437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328457 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 3, 2, 2]
def baseStart_3328457 : Nat := 118140960795 + 3328457 * 2 ^ 59
def prefixEnd_3328457 : Nat := 4983230072969 + 3 ^ 40 * 3328457 * 2
def baseEnd_3328457 : Nat := 1709098278822189130380211

theorem tailTrace_3328457 : CollatzResearch.WordTrace tailWord_3328457 prefixEnd_3328457 1709098278822189130380211 := by
  unfold tailWord_3328457
  simp only [CollatzResearch.WordTrace]
  refine ⟨121398800102576219043679625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80932533401717479362453083 121398800102576219043679625)
  ·
    refine ⟨91049100076932164282759719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121398800102576219043679625 91049100076932164282759719)
    ·
      refine ⟨136573650115398246424139579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91049100076932164282759719 136573650115398246424139579)
      ·
        refine ⟨204860475173097369636209369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136573650115398246424139579 204860475173097369636209369)
        ·
          refine ⟨153645356379823027227157027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204860475173097369636209369 153645356379823027227157027)
          ·
            refine ⟨230468034569734540840735541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153645356379823027227157027 230468034569734540840735541)
            ·
              refine ⟨21606378240912613203818957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 230468034569734540840735541 21606378240912613203818957)
              ·
                refine ⟨8102391840342229951432109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21606378240912613203818957 8102391840342229951432109)
                ·
                  refine ⟨3038396940128336231787041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8102391840342229951432109 3038396940128336231787041)
                  ·
                    refine ⟨2278797705096252173840281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3038396940128336231787041 2278797705096252173840281)
                    ·
                      refine ⟨1709098278822189130380211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2278797705096252173840281 1709098278822189130380211)
                      ·
                        rfl

theorem cell23_3328457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 2, 2].length) (baseStart_3328457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328457 prefixEnd_3328457 := by exact prefixLift 3328457
  have htrace : WordTrace (prefixWord ++ tailWord_3328457) baseStart_3328457 baseEnd_3328457 := by
    simpa [prefixWord, tailWord_3328457, baseEnd_3328457] using wordTrace_append hprefix tailTrace_3328457
  have hstable : (prefixWord ++ tailWord_3328457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328457).length < 2 ^ (prefixWord ++ tailWord_3328457).sum := by decide
  have hdescent : baseEnd_3328457 < baseStart_3328457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328518 : List Nat := [6, 2, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_3328518 : Nat := 118140960795 + 3328518 * 2 ^ 59
def prefixEnd_3328518 : Nat := 4983230072969 + 3 ^ 40 * 3328518 * 2
def baseEnd_3328518 : Nat := 569709867047371130572477

theorem tailTrace_3328518 : CollatzResearch.WordTrace tailWord_3328518 prefixEnd_3328518 569709867047371130572477 := by
  unfold tailWord_3328518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3793782029854850826926569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80934016636903484307766805 3793782029854850826926569)
  ·
    refine ⟨2845336522391138120194927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3793782029854850826926569 2845336522391138120194927)
    ·
      refine ⟨4268004783586707180292391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2845336522391138120194927 4268004783586707180292391)
      ·
        refine ⟨6402007175380060770438587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4268004783586707180292391 6402007175380060770438587)
        ·
          refine ⟨9603010763070091155657881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6402007175380060770438587 9603010763070091155657881)
          ·
            refine ⟨7202258072302568366743411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9603010763070091155657881 7202258072302568366743411)
            ·
              refine ⟨10803387108453852550115117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7202258072302568366743411 10803387108453852550115117)
              ·
                refine ⟨4051270165670194706293169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10803387108453852550115117 4051270165670194706293169)
                ·
                  refine ⟨3038452624252646029719877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4051270165670194706293169 3038452624252646029719877)
                  ·
                    refine ⟨569709867047371130572477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3038452624252646029719877 569709867047371130572477)
                    ·
                      rfl

theorem cell23_3328518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_3328518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328518 prefixEnd_3328518 := by exact prefixLift 3328518
  have htrace : WordTrace (prefixWord ++ tailWord_3328518) baseStart_3328518 baseEnd_3328518 := by
    simpa [prefixWord, tailWord_3328518, baseEnd_3328518] using wordTrace_append hprefix tailTrace_3328518
  have hstable : (prefixWord ++ tailWord_3328518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328518).length < 2 ^ (prefixWord ++ tailWord_3328518).sum := by decide
  have hdescent : baseEnd_3328518 < baseStart_3328518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328524 : List Nat := [2, 2, 1, 2, 4, 2, 1, 3, 2, 1, 3]
def baseStart_3328524 : Nat := 118140960795 + 3328524 * 2 ^ 59
def prefixEnd_3328524 : Nat := 4983230072969 + 3 ^ 40 * 3328524 * 2
def baseEnd_3328524 : Nat := 1709132682026040368242403

theorem tailTrace_3328524 : CollatzResearch.WordTrace tailWord_3328524 prefixEnd_3328524 1709132682026040368242403 := by
  unfold tailWord_3328524
  simp only [CollatzResearch.WordTrace]
  refine ⟨60700621896666744743184313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80934162528888992990912417 60700621896666744743184313)
  ·
    refine ⟨45525466422500058557388235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60700621896666744743184313 45525466422500058557388235)
    ·
      refine ⟨68288199633750087836082353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45525466422500058557388235 68288199633750087836082353)
      ·
        refine ⟨51216149725312565877061765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68288199633750087836082353 51216149725312565877061765)
        ·
          refine ⟨9603028073496106101949081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51216149725312565877061765 9603028073496106101949081)
          ·
            refine ⟨7202271055122079576461811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9603028073496106101949081 7202271055122079576461811)
            ·
              refine ⟨10803406582683119364692717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7202271055122079576461811 10803406582683119364692717)
              ·
                refine ⟨4051277468506169761759769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10803406582683119364692717 4051277468506169761759769)
                ·
                  refine ⟨3038458101379627321319827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4051277468506169761759769 3038458101379627321319827)
                  ·
                    refine ⟨4557687152069440981979741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3038458101379627321319827 4557687152069440981979741)
                    ·
                      refine ⟨1709132682026040368242403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4557687152069440981979741 1709132682026040368242403)
                      ·
                        rfl

theorem cell23_3328524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_3328524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328524 prefixEnd_3328524 := by exact prefixLift 3328524
  have htrace : WordTrace (prefixWord ++ tailWord_3328524) baseStart_3328524 baseEnd_3328524 := by
    simpa [prefixWord, tailWord_3328524, baseEnd_3328524] using wordTrace_append hprefix tailTrace_3328524
  have hstable : (prefixWord ++ tailWord_3328524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328524).length < 2 ^ (prefixWord ++ tailWord_3328524).sum := by decide
  have hdescent : baseEnd_3328524 < baseStart_3328524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328547 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 3, 4, 2]
def baseStart_3328547 : Nat := 118140960795 + 3328547 * 2 ^ 59
def prefixEnd_3328547 : Nat := 4983230072969 + 3 ^ 40 * 3328547 * 2
def baseEnd_3328547 : Nat := 1709144492081093778254797

theorem tailTrace_3328547 : CollatzResearch.WordTrace tailWord_3328547 prefixEnd_3328547 1709144492081093778254797 := by
  unfold tailWord_3328547
  simp only [CollatzResearch.WordTrace]
  refine ⟨121402082672250164414455895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80934721781500109609637263 121402082672250164414455895)
  ·
    refine ⟨182103124008375246621683843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121402082672250164414455895 182103124008375246621683843)
    ·
      refine ⟨273154686012562869932525765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182103124008375246621683843 273154686012562869932525765)
      ·
        refine ⟨51216503627355538112348581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273154686012562869932525765 51216503627355538112348581)
        ·
          refine ⟨9603094430129163396065359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51216503627355538112348581 9603094430129163396065359)
          ·
            refine ⟨14404641645193745094098039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9603094430129163396065359 14404641645193745094098039)
            ·
              refine ⟨21606962467790617641147059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14404641645193745094098039 21606962467790617641147059)
              ·
                refine ⟨32410443701685926461720589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21606962467790617641147059 32410443701685926461720589)
                ·
                  refine ⟨12153916388132222423145221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32410443701685926461720589 12153916388132222423145221)
                  ·
                    refine ⟨2278859322774791704339729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12153916388132222423145221 2278859322774791704339729)
                    ·
                      refine ⟨1709144492081093778254797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2278859322774791704339729 1709144492081093778254797)
                      ·
                        rfl

theorem cell23_3328547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_3328547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328547 prefixEnd_3328547 := by exact prefixLift 3328547
  have htrace : WordTrace (prefixWord ++ tailWord_3328547) baseStart_3328547 baseEnd_3328547 := by
    simpa [prefixWord, tailWord_3328547, baseEnd_3328547] using wordTrace_append hprefix tailTrace_3328547
  have hstable : (prefixWord ++ tailWord_3328547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328547).length < 2 ^ (prefixWord ++ tailWord_3328547).sum := by decide
  have hdescent : baseEnd_3328547 < baseStart_3328547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328574 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_3328574 : Nat := 118140960795 + 3328574 * 2 ^ 59
def prefixEnd_3328574 : Nat := 4983230072969 + 3 ^ 40 * 3328574 * 2
def baseEnd_3328574 : Nat := 569719452019588390872391

theorem tailTrace_3328574 : CollatzResearch.WordTrace tailWord_3328574 prefixEnd_3328574 569719452019588390872391 := by
  unfold tailWord_3328574
  simp only [CollatzResearch.WordTrace]
  refine ⟨15175383430394043503211097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80935378295434898683792517 15175383430394043503211097)
  ·
    refine ⟨11381537572795532627408323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15175383430394043503211097 11381537572795532627408323)
    ·
      refine ⟨17072306359193298941112485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11381537572795532627408323 17072306359193298941112485)
      ·
        refine ⟨3201057442348743551458591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17072306359193298941112485 3201057442348743551458591)
        ·
          refine ⟨4801586163523115327187887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201057442348743551458591 4801586163523115327187887)
          ·
            refine ⟨7202379245284672990781831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4801586163523115327187887 7202379245284672990781831)
            ·
              refine ⟨10803568867927009486172747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7202379245284672990781831 10803568867927009486172747)
              ·
                refine ⟨16205353301890514229259121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10803568867927009486172747 16205353301890514229259121)
                ·
                  refine ⟨12154014976417885671944341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16205353301890514229259121 12154014976417885671944341)
                  ·
                    refine ⟨569719452019588390872391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12154014976417885671944341 569719452019588390872391)
                    ·
                      rfl

theorem cell23_3328574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_3328574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328574 prefixEnd_3328574 := by exact prefixLift 3328574
  have htrace : WordTrace (prefixWord ++ tailWord_3328574) baseStart_3328574 baseEnd_3328574 := by
    simpa [prefixWord, tailWord_3328574, baseEnd_3328574] using wordTrace_append hprefix tailTrace_3328574
  have hstable : (prefixWord ++ tailWord_3328574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328574).length < 2 ^ (prefixWord ++ tailWord_3328574).sum := by decide
  have hdescent : baseEnd_3328574 < baseStart_3328574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328577 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_3328577 : Nat := 118140960795 + 3328577 * 2 ^ 59
def prefixEnd_3328577 : Nat := 4983230072969 + 3 ^ 40 * 3328577 * 2
def baseEnd_3328577 : Nat := 1709159896500728660879659

theorem tailTrace_3328577 : CollatzResearch.WordTrace tailWord_3328577 prefixEnd_3328577 1709159896500728660879659 := by
  unfold tailWord_3328577
  simp only [CollatzResearch.WordTrace]
  refine ⟨121403176862141479538047985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80935451241427653025365323 121403176862141479538047985)
  ·
    refine ⟨91052382646606109653535989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121403176862141479538047985 91052382646606109653535989)
    ·
      refine ⟨8536160873119322780018999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91052382646606109653535989 8536160873119322780018999)
      ·
        refine ⟨12804241309678984170028499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8536160873119322780018999 12804241309678984170028499)
        ·
          refine ⟨19206361964518476255042749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12804241309678984170028499 19206361964518476255042749)
          ·
            refine ⟨7202385736694428595641031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19206361964518476255042749 7202385736694428595641031)
            ·
              refine ⟨10803578605041642893461547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7202385736694428595641031 10803578605041642893461547)
              ·
                refine ⟨16205367907562464340192321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10803578605041642893461547 16205367907562464340192321)
                ·
                  refine ⟨12154025930671848255144241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16205367907562464340192321 12154025930671848255144241)
                  ·
                    refine ⟨9115519448003886191358181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12154025930671848255144241 9115519448003886191358181)
                    ·
                      refine ⟨1709159896500728660879659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9115519448003886191358181 1709159896500728660879659)
                      ·
                        rfl

theorem cell23_3328577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_3328577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328577 prefixEnd_3328577 := by exact prefixLift 3328577
  have htrace : WordTrace (prefixWord ++ tailWord_3328577) baseStart_3328577 baseEnd_3328577 := by
    simpa [prefixWord, tailWord_3328577, baseEnd_3328577] using wordTrace_append hprefix tailTrace_3328577
  have hstable : (prefixWord ++ tailWord_3328577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328577).length < 2 ^ (prefixWord ++ tailWord_3328577).sum := by decide
  have hdescent : baseEnd_3328577 < baseStart_3328577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328647 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 3, 4]
def baseStart_3328647 : Nat := 118140960795 + 3328647 * 2 ^ 59
def prefixEnd_3328647 : Nat := 4983230072969 + 3 ^ 40 * 3328647 * 2
def baseEnd_3328647 : Nat := 569731946715514462334779

theorem tailTrace_3328647 : CollatzResearch.WordTrace tailWord_3328647 prefixEnd_3328647 569731946715514462334779 := by
  unfold tailWord_3328647
  simp only [CollatzResearch.WordTrace]
  refine ⟨121405729971887881493096195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80937153314591920995397463 121405729971887881493096195)
  ·
    refine ⟨182108594957831822239644293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121405729971887881493096195 182108594957831822239644293)
    ·
      refine ⟨34145361554593466669933305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182108594957831822239644293 34145361554593466669933305)
      ·
        refine ⟨25609021165945100002449979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34145361554593466669933305 25609021165945100002449979)
        ·
          refine ⟨38413531748917650003674969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25609021165945100002449979 38413531748917650003674969)
          ·
            refine ⟨28810148811688237502756227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38413531748917650003674969 28810148811688237502756227)
            ·
              refine ⟨43215223217532356254134341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28810148811688237502756227 43215223217532356254134341)
              ·
                refine ⟨8102854353287316797650189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43215223217532356254134341 8102854353287316797650189)
                ·
                  refine ⟨3038570382482743799118821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8102854353287316797650189 3038570382482743799118821)
                  ·
                    refine ⟨569731946715514462334779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3038570382482743799118821 569731946715514462334779)
                    ·
                      rfl

theorem cell23_3328647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_3328647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328647 prefixEnd_3328647 := by exact prefixLift 3328647
  have htrace : WordTrace (prefixWord ++ tailWord_3328647) baseStart_3328647 baseEnd_3328647 := by
    simpa [prefixWord, tailWord_3328647, baseEnd_3328647] using wordTrace_append hprefix tailTrace_3328647
  have hstable : (prefixWord ++ tailWord_3328647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328647).length < 2 ^ (prefixWord ++ tailWord_3328647).sum := by decide
  have hdescent : baseEnd_3328647 < baseStart_3328647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328690 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 2, 9]
def baseStart_3328690 : Nat := 118140960795 + 3328690 * 2 ^ 59
def prefixEnd_3328690 : Nat := 4983230072969 + 3 ^ 40 * 3328690 * 2
def baseEnd_3328690 : Nat := 569739306604895572922213

theorem tailTrace_3328690 : CollatzResearch.WordTrace tailWord_3328690 prefixEnd_3328690 569739306604895572922213 := by
  unfold tailWord_3328690
  simp only [CollatzResearch.WordTrace]
  refine ⟨30351824577683024959227881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80938198873821399891274349 30351824577683024959227881)
  ·
    refine ⟨22763868433262268719420911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30351824577683024959227881 22763868433262268719420911)
    ·
      refine ⟨34145802649893403079131367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22763868433262268719420911 34145802649893403079131367)
      ·
        refine ⟨51218703974840104618697051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34145802649893403079131367 51218703974840104618697051)
        ·
          refine ⟨76828055962260156928045577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51218703974840104618697051 76828055962260156928045577)
          ·
            refine ⟨57621041971695117696034183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76828055962260156928045577 57621041971695117696034183)
            ·
              refine ⟨86431562957542676544051275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57621041971695117696034183 86431562957542676544051275)
              ·
                refine ⟨129647344436314014816076913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86431562957542676544051275 129647344436314014816076913)
                ·
                  refine ⟨97235508327235511112057685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129647344436314014816076913 97235508327235511112057685)
                  ·
                    refine ⟨569739306604895572922213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 97235508327235511112057685 569739306604895572922213)
                    ·
                      rfl

theorem cell23_3328690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_3328690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328690 prefixEnd_3328690 := by exact prefixLift 3328690
  have htrace : WordTrace (prefixWord ++ tailWord_3328690) baseStart_3328690 baseEnd_3328690 := by
    simpa [prefixWord, tailWord_3328690, baseEnd_3328690] using wordTrace_append hprefix tailTrace_3328690
  have hstable : (prefixWord ++ tailWord_3328690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328690).length < 2 ^ (prefixWord ++ tailWord_3328690).sum := by decide
  have hdescent : baseEnd_3328690 < baseStart_3328690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328721 : List Nat := [1, 2, 2, 1, 2, 3, 2, 5, 1, 1, 3]
def baseStart_3328721 : Nat := 118140960795 + 3328721 * 2 ^ 59
def prefixEnd_3328721 : Nat := 4983230072969 + 3 ^ 40 * 3328721 * 2
def baseEnd_3328721 : Nat := 1709233837714976097478997

theorem tailTrace_3328721 : CollatzResearch.WordTrace tailWord_3328721 prefixEnd_3328721 1709233837714976097478997 := by
  unfold tailWord_3328721
  simp only [CollatzResearch.WordTrace]
  refine ⟨121408428973619792131290017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80938952649079861420860011 121408428973619792131290017)
  ·
    refine ⟨91056321730214844098467513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121408428973619792131290017 91056321730214844098467513)
    ·
      refine ⟨68292241297661133073850635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91056321730214844098467513 68292241297661133073850635)
      ·
        refine ⟨102438361946491699610775953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68292241297661133073850635 102438361946491699610775953)
        ·
          refine ⟨76828771459868774708081965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102438361946491699610775953 76828771459868774708081965)
          ·
            refine ⟨28810789297450790515530737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76828771459868774708081965 28810789297450790515530737)
            ·
              refine ⟨21608091973088092886648053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28810789297450790515530737 21608091973088092886648053)
              ·
                refine ⟨2025758622477008708123255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21608091973088092886648053 2025758622477008708123255)
                ·
                  refine ⟨3038637933715513062184883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025758622477008708123255 3038637933715513062184883)
                  ·
                    refine ⟨4557956900573269593277325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3038637933715513062184883 4557956900573269593277325)
                    ·
                      refine ⟨1709233837714976097478997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4557956900573269593277325 1709233837714976097478997)
                      ·
                        rfl

theorem cell23_3328721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 1, 1, 3].length) (baseStart_3328721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328721 prefixEnd_3328721 := by exact prefixLift 3328721
  have htrace : WordTrace (prefixWord ++ tailWord_3328721) baseStart_3328721 baseEnd_3328721 := by
    simpa [prefixWord, tailWord_3328721, baseEnd_3328721] using wordTrace_append hprefix tailTrace_3328721
  have hstable : (prefixWord ++ tailWord_3328721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328721).length < 2 ^ (prefixWord ++ tailWord_3328721).sum := by decide
  have hdescent : baseEnd_3328721 < baseStart_3328721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328754 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 1, 6]
def baseStart_3328754 : Nat := 118140960795 + 3328754 * 2 ^ 59
def prefixEnd_3328754 : Nat := 4983230072969 + 3 ^ 40 * 3328754 * 2
def baseEnd_3328754 : Nat := 569750260858858156122115

theorem tailTrace_3328754 : CollatzResearch.WordTrace tailWord_3328754 prefixEnd_3328754 569750260858858156122115 := by
  unfold tailWord_3328754
  simp only [CollatzResearch.WordTrace]
  refine ⟨30352408145625059691810329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80939755055000159178160877 30352408145625059691810329)
  ·
    refine ⟨22764306109218794768857747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30352408145625059691810329 22764306109218794768857747)
    ·
      refine ⟨34146459163828192153286621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22764306109218794768857747 34146459163828192153286621)
      ·
        refine ⟨12804922186435572057482483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34146459163828192153286621 12804922186435572057482483)
        ·
          refine ⟨19207383279653358086223725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12804922186435572057482483 19207383279653358086223725)
          ·
            refine ⟨7202768729870009282333897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19207383279653358086223725 7202768729870009282333897)
            ·
              refine ⟨5402076547402506961750423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7202768729870009282333897 5402076547402506961750423)
              ·
                refine ⟨8103114821103760442625635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5402076547402506961750423 8103114821103760442625635)
                ·
                  refine ⟨12154672231655640663938453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8103114821103760442625635 12154672231655640663938453)
                  ·
                    refine ⟨569750260858858156122115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12154672231655640663938453 569750260858858156122115)
                    ·
                      rfl

theorem cell23_3328754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_3328754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328754 prefixEnd_3328754 := by exact prefixLift 3328754
  have htrace : WordTrace (prefixWord ++ tailWord_3328754) baseStart_3328754 baseEnd_3328754 := by
    simpa [prefixWord, tailWord_3328754, baseEnd_3328754] using wordTrace_append hprefix tailTrace_3328754
  have hstable : (prefixWord ++ tailWord_3328754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328754).length < 2 ^ (prefixWord ++ tailWord_3328754).sum := by decide
  have hdescent : baseEnd_3328754 < baseStart_3328754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328764 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 3, 2, 3]
def baseStart_3328764 : Nat := 118140960795 + 3328764 * 2 ^ 59
def prefixEnd_3328764 : Nat := 4983230072969 + 3 ^ 40 * 3328764 * 2
def baseEnd_3328764 : Nat := 1709255917383119429241299

theorem tailTrace_3328764 : CollatzResearch.WordTrace tailWord_3328764 prefixEnd_3328764 1709255917383119429241299 := by
  unfold tailWord_3328764
  simp only [CollatzResearch.WordTrace]
  refine ⟨60704998656232005237552673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80939998208309340316736897 60704998656232005237552673)
  ·
    refine ⟨45528748992174003928164505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60704998656232005237552673 45528748992174003928164505)
    ·
      refine ⟨34146561744130502946123379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45528748992174003928164505 34146561744130502946123379)
      ·
        refine ⟨51219842616195754419185069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34146561744130502946123379 51219842616195754419185069)
        ·
          refine ⟨19207440981073407907194401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51219842616195754419185069 19207440981073407907194401)
          ·
            refine ⟨14405580735805055930395801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19207440981073407907194401 14405580735805055930395801)
            ·
              refine ⟨10804185551853791947796851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14405580735805055930395801 10804185551853791947796851)
              ·
                refine ⟨16206278327780687921695277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10804185551853791947796851 16206278327780687921695277)
                ·
                  refine ⟨6077354372917757970635729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16206278327780687921695277 6077354372917757970635729)
                  ·
                    refine ⟨4558015779688318477976797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6077354372917757970635729 4558015779688318477976797)
                    ·
                      refine ⟨1709255917383119429241299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4558015779688318477976797 1709255917383119429241299)
                      ·
                        rfl

theorem cell23_3328764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_3328764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328764 prefixEnd_3328764 := by exact prefixLift 3328764
  have htrace : WordTrace (prefixWord ++ tailWord_3328764) baseStart_3328764 baseEnd_3328764 := by
    simpa [prefixWord, tailWord_3328764, baseEnd_3328764] using wordTrace_append hprefix tailTrace_3328764
  have hstable : (prefixWord ++ tailWord_3328764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328764).length < 2 ^ (prefixWord ++ tailWord_3328764).sum := by decide
  have hdescent : baseEnd_3328764 < baseStart_3328764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328829 : List Nat := [1, 4, 1, 4, 3, 1, 1, 3, 1, 2, 2]
def baseStart_3328829 : Nat := 118140960795 + 3328829 * 2 ^ 59
def prefixEnd_3328829 : Nat := 4983230072969 + 3 ^ 40 * 3328829 * 2
def baseEnd_3328829 : Nat := 1709289293625661674928501

theorem tailTrace_3328829 : CollatzResearch.WordTrace tailWord_3328829 prefixEnd_3328829 1709289293625661674928501 := by
  unfold tailWord_3328829
  simp only [CollatzResearch.WordTrace]
  refine ⟨121412368057228526576221541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80941578704819017717481027 121412368057228526576221541)
  ·
    refine ⟨22764819010730348733041539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121412368057228526576221541 22764819010730348733041539)
    ·
      refine ⟨34147228516095523099562309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22764819010730348733041539 34147228516095523099562309)
      ·
        refine ⟨6402605346767910581167933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34147228516095523099562309 6402605346767910581167933)
        ·
          refine ⟨2400977005037966467937975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6402605346767910581167933 2400977005037966467937975)
          ·
            refine ⟨3601465507556949701906963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2400977005037966467937975 3601465507556949701906963)
            ·
              refine ⟨5402198261335424552860445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3601465507556949701906963 5402198261335424552860445)
              ·
                refine ⟨2025824348000784207322667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5402198261335424552860445 2025824348000784207322667)
                ·
                  refine ⟨3038736522001176310984001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025824348000784207322667 3038736522001176310984001)
                  ·
                    refine ⟨2279052391500882233238001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3038736522001176310984001 2279052391500882233238001)
                    ·
                      refine ⟨1709289293625661674928501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2279052391500882233238001 1709289293625661674928501)
                      ·
                        rfl

theorem cell23_3328829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_3328829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328829 prefixEnd_3328829 := by exact prefixLift 3328829
  have htrace : WordTrace (prefixWord ++ tailWord_3328829) baseStart_3328829 baseEnd_3328829 := by
    simpa [prefixWord, tailWord_3328829, baseEnd_3328829] using wordTrace_append hprefix tailTrace_3328829
  have hstable : (prefixWord ++ tailWord_3328829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328829).length < 2 ^ (prefixWord ++ tailWord_3328829).sum := by decide
  have hdescent : baseEnd_3328829 < baseStart_3328829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328887 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 1, 7]
def baseStart_3328887 : Nat := 118140960795 + 3328887 * 2 ^ 59
def prefixEnd_3328887 : Nat := 4983230072969 + 3 ^ 40 * 3328887 * 2
def baseEnd_3328887 : Nat := 569773025167874149334411

theorem tailTrace_3328887 : CollatzResearch.WordTrace tailWord_3328887 prefixEnd_3328887 569773025167874149334411 := by
  unfold tailWord_3328887
  simp only [CollatzResearch.WordTrace]
  refine ⟨121414483491018402481832915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80942988994012268321221943 121414483491018402481832915)
  ·
    refine ⟨182121725236527603722749373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121414483491018402481832915 182121725236527603722749373)
    ·
      refine ⟨68295646963697851396031015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182121725236527603722749373 68295646963697851396031015)
      ·
        refine ⟨102443470445546777094046523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68295646963697851396031015 102443470445546777094046523)
        ·
          refine ⟨153665205668320165641069785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102443470445546777094046523 153665205668320165641069785)
          ·
            refine ⟨115248904251240124230802339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153665205668320165641069785 115248904251240124230802339)
            ·
              refine ⟨172873356376860186346203509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115248904251240124230802339 172873356376860186346203509)
              ·
                refine ⟨16206877160330642469956579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172873356376860186346203509 16206877160330642469956579)
                ·
                  refine ⟨24310315740495963704934869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16206877160330642469956579 24310315740495963704934869)
                  ·
                    refine ⟨569773025167874149334411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24310315740495963704934869 569773025167874149334411)
                    ·
                      rfl

theorem cell23_3328887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_3328887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328887 prefixEnd_3328887 := by exact prefixLift 3328887
  have htrace : WordTrace (prefixWord ++ tailWord_3328887) baseStart_3328887 baseEnd_3328887 := by
    simpa [prefixWord, tailWord_3328887, baseEnd_3328887] using wordTrace_append hprefix tailTrace_3328887
  have hstable : (prefixWord ++ tailWord_3328887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328887).length < 2 ^ (prefixWord ++ tailWord_3328887).sum := by decide
  have hdescent : baseEnd_3328887 < baseStart_3328887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328968 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 3, 4]
def baseStart_3328968 : Nat := 118140960795 + 3328968 * 2 ^ 59
def prefixEnd_3328968 : Nat := 4983230072969 + 3 ^ 40 * 3328968 * 2
def baseEnd_3328968 : Nat := 569786889145545543696787

theorem tailTrace_3328968 : CollatzResearch.WordTrace tailWord_3328968 prefixEnd_3328968 569786889145545543696787 := by
  unfold tailWord_3328968
  simp only [CollatzResearch.WordTrace]
  refine ⟨60708718901862476657765779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80944958535816635543687705 60708718901862476657765779)
  ·
    refine ⟨91063078352793714986648669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60708718901862476657765779 91063078352793714986648669)
    ·
      refine ⟨34148654382297643119993251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91063078352793714986648669 34148654382297643119993251)
      ·
        refine ⟨51222981573446464679989877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34148654382297643119993251 51222981573446464679989877)
        ·
          refine ⟨4802154522510606063749051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51222981573446464679989877 4802154522510606063749051)
          ·
            refine ⟨7203231783765909095623577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4802154522510606063749051 7203231783765909095623577)
            ·
              refine ⟨5402423837824431821717683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7203231783765909095623577 5402423837824431821717683)
              ·
                refine ⟨8103635756736647732576525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5402423837824431821717683 8103635756736647732576525)
                ·
                  refine ⟨3038863408776242899716197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8103635756736647732576525 3038863408776242899716197)
                  ·
                    refine ⟨569786889145545543696787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3038863408776242899716197 569786889145545543696787)
                    ·
                      rfl

theorem cell23_3328968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_3328968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328968 prefixEnd_3328968 := by exact prefixLift 3328968
  have htrace : WordTrace (prefixWord ++ tailWord_3328968) baseStart_3328968 baseEnd_3328968 := by
    simpa [prefixWord, tailWord_3328968, baseEnd_3328968] using wordTrace_append hprefix tailTrace_3328968
  have hstable : (prefixWord ++ tailWord_3328968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328968).length < 2 ^ (prefixWord ++ tailWord_3328968).sum := by decide
  have hdescent : baseEnd_3328968 < baseStart_3328968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329001 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 8, 3, 2]
def baseStart_3329001 : Nat := 118140960795 + 3329001 * 2 ^ 59
def prefixEnd_3329001 : Nat := 4983230072969 + 3 ^ 40 * 3329001 * 2
def baseEnd_3329001 : Nat := 1709377612298235001977709

theorem tailTrace_3329001 : CollatzResearch.WordTrace tailWord_3329001 prefixEnd_3329001 1709377612298235001977709 := by
  unfold tailWord_3329001
  simp only [CollatzResearch.WordTrace]
  refine ⟨121418641412605399951482857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80945760941736933300988571 121418641412605399951482857)
  ·
    refine ⟨91063981059454049963612143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121418641412605399951482857 91063981059454049963612143)
    ·
      refine ⟨136595971589181074945418215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91063981059454049963612143 136595971589181074945418215)
      ·
        refine ⟨204893957383771612418127323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136595971589181074945418215 204893957383771612418127323)
        ·
          refine ⟨307340936075657418627190985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204893957383771612418127323 307340936075657418627190985)
          ·
            refine ⟨230505702056743063970393239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307340936075657418627190985 230505702056743063970393239)
            ·
              refine ⟨345758553085114595955589859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230505702056743063970393239 345758553085114595955589859)
              ·
                refine ⟨518637829627671893933384789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345758553085114595955589859 518637829627671893933384789)
                ·
                  refine ⟨6077787065949280007031853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 518637829627671893933384789 6077787065949280007031853)
                  ·
                    refine ⟨2279170149730980002636945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6077787065949280007031853 2279170149730980002636945)
                    ·
                      refine ⟨1709377612298235001977709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2279170149730980002636945 1709377612298235001977709)
                      ·
                        rfl

theorem cell23_3329001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 3, 2].length) (baseStart_3329001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329001 prefixEnd_3329001 := by exact prefixLift 3329001
  have htrace : WordTrace (prefixWord ++ tailWord_3329001) baseStart_3329001 baseEnd_3329001 := by
    simpa [prefixWord, tailWord_3329001, baseEnd_3329001] using wordTrace_append hprefix tailTrace_3329001
  have hstable : (prefixWord ++ tailWord_3329001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329001).length < 2 ^ (prefixWord ++ tailWord_3329001).sum := by decide
  have hdescent : baseEnd_3329001 < baseStart_3329001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329025 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_3329025 : Nat := 118140960795 + 3329025 * 2 ^ 59
def prefixEnd_3329025 : Nat := 4983230072969 + 3 ^ 40 * 3329025 * 2
def baseEnd_3329025 : Nat := 1709389935833942908077599

theorem tailTrace_3329025 : CollatzResearch.WordTrace tailWord_3329025 prefixEnd_3329025 1709389935833942908077599 := by
  unfold tailWord_3329025
  simp only [CollatzResearch.WordTrace]
  refine ⟨121419516764518452050356529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80946344509678968033571019 121419516764518452050356529)
  ·
    refine ⟨91064637573388839037767397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121419516764518452050356529 91064637573388839037767397)
    ·
      refine ⟨17074619545010407319581387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91064637573388839037767397 17074619545010407319581387)
      ·
        refine ⟨25611929317515610979372081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17074619545010407319581387 25611929317515610979372081)
        ·
          refine ⟨19208946988136708234529061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25611929317515610979372081 19208946988136708234529061)
          ·
            refine ⟨3601677560275632793974199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19208946988136708234529061 3601677560275632793974199)
            ·
              refine ⟨5402516340413449190961299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3601677560275632793974199 5402516340413449190961299)
              ·
                refine ⟨8103774510620173786441949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5402516340413449190961299 8103774510620173786441949)
                ·
                  refine ⟨3038915441482565169915731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8103774510620173786441949 3038915441482565169915731)
                  ·
                    refine ⟨4558373162223847754873597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3038915441482565169915731 4558373162223847754873597)
                    ·
                      refine ⟨1709389935833942908077599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4558373162223847754873597 1709389935833942908077599)
                      ·
                        rfl

theorem cell23_3329025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_3329025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329025 prefixEnd_3329025 := by exact prefixLift 3329025
  have htrace : WordTrace (prefixWord ++ tailWord_3329025) baseStart_3329025 baseEnd_3329025 := by
    simpa [prefixWord, tailWord_3329025, baseEnd_3329025] using wordTrace_append hprefix tailTrace_3329025
  have hstable : (prefixWord ++ tailWord_3329025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329025).length < 2 ^ (prefixWord ++ tailWord_3329025).sum := by decide
  have hdescent : baseEnd_3329025 < baseStart_3329025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329031 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_3329031 : Nat := 118140960795 + 3329031 * 2 ^ 59
def prefixEnd_3329031 : Nat := 4983230072969 + 3 ^ 40 * 3329031 * 2
def baseEnd_3329031 : Nat := 1709393016717869884602571

theorem tailTrace_3329031 : CollatzResearch.WordTrace tailWord_3329031 prefixEnd_3329031 1709393016717869884602571 := by
  unfold tailWord_3329031
  simp only [CollatzResearch.WordTrace]
  refine ⟨121419735602496715075074947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80946490401664476716716631 121419735602496715075074947)
  ·
    refine ⟨182129603403745072612612421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121419735602496715075074947 182129603403745072612612421)
    ·
      refine ⟨34149300638202201114864829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182129603403745072612612421 34149300638202201114864829)
      ·
        refine ⟨12805987739325825418074311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34149300638202201114864829 12805987739325825418074311)
        ·
          refine ⟨19208981608988738127111467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12805987739325825418074311 19208981608988738127111467)
          ·
            refine ⟨28813472413483107190667201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19208981608988738127111467 28813472413483107190667201)
            ·
              refine ⟨21610104310112330393000401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28813472413483107190667201 21610104310112330393000401)
              ·
                refine ⟨16207578232584247794750301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21610104310112330393000401 16207578232584247794750301)
                ·
                  refine ⟨6077841837219092923031363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16207578232584247794750301 6077841837219092923031363)
                  ·
                    refine ⟨9116762755828639384547045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6077841837219092923031363 9116762755828639384547045)
                    ·
                      refine ⟨1709393016717869884602571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9116762755828639384547045 1709393016717869884602571)
                      ·
                        rfl

theorem cell23_3329031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_3329031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329031 prefixEnd_3329031 := by exact prefixLift 3329031
  have htrace : WordTrace (prefixWord ++ tailWord_3329031) baseStart_3329031 baseEnd_3329031 := by
    simpa [prefixWord, tailWord_3329031, baseEnd_3329031] using wordTrace_append hprefix tailTrace_3329031
  have hstable : (prefixWord ++ tailWord_3329031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329031).length < 2 ^ (prefixWord ++ tailWord_3329031).sum := by decide
  have hdescent : baseEnd_3329031 < baseStart_3329031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329048 : List Nat := [2, 1, 2, 3, 2, 2, 3, 2, 1, 1, 4]
def baseStart_3329048 : Nat := 118140960795 + 3329048 * 2 ^ 59
def prefixEnd_3329048 : Nat := 4983230072969 + 3 ^ 40 * 3329048 * 2
def baseEnd_3329048 : Nat := 1709401745888996318089993

theorem tailTrace_3329048 : CollatzResearch.WordTrace tailWord_3329048 prefixEnd_3329048 1709401745888996318089993 := by
  unfold tailWord_3329048
  simp only [CollatzResearch.WordTrace]
  refine ⟨60710177821717563489221899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80946903762290084652295865 60710177821717563489221899)
  ·
    refine ⟨91065266732576345233832849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60710177821717563489221899 91065266732576345233832849)
    ·
      refine ⟨68298950049432258925374637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91065266732576345233832849 68298950049432258925374637)
      ·
        refine ⟨25612106268537097097015489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68298950049432258925374637 25612106268537097097015489)
        ·
          refine ⟨19209079701402822822761617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25612106268537097097015489 19209079701402822822761617)
          ·
            refine ⟨14406809776052117117071213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19209079701402822822761617 14406809776052117117071213)
            ·
              refine ⟨5402553666019543918901705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14406809776052117117071213 5402553666019543918901705)
              ·
                refine ⟨4051915249514657939176279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5402553666019543918901705 4051915249514657939176279)
                ·
                  refine ⟨6077872874271986908764419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4051915249514657939176279 6077872874271986908764419)
                  ·
                    refine ⟨9116809311407980363146629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6077872874271986908764419 9116809311407980363146629)
                    ·
                      refine ⟨1709401745888996318089993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9116809311407980363146629 1709401745888996318089993)
                      ·
                        rfl

theorem cell23_3329048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_3329048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329048 prefixEnd_3329048 := by exact prefixLift 3329048
  have htrace : WordTrace (prefixWord ++ tailWord_3329048) baseStart_3329048 baseEnd_3329048 := by
    simpa [prefixWord, tailWord_3329048, baseEnd_3329048] using wordTrace_append hprefix tailTrace_3329048
  have hstable : (prefixWord ++ tailWord_3329048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329048).length < 2 ^ (prefixWord ++ tailWord_3329048).sum := by decide
  have hdescent : baseEnd_3329048 < baseStart_3329048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329061 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 1, 2, 4]
def baseStart_3329061 : Nat := 118140960795 + 3329061 * 2 ^ 59
def prefixEnd_3329061 : Nat := 4983230072969 + 3 ^ 40 * 3329061 * 2
def baseEnd_3329061 : Nat := 1709408421137504767227433

theorem tailTrace_3329061 : CollatzResearch.WordTrace tailWord_3329061 prefixEnd_3329061 1709408421137504767227433 := by
  unfold tailWord_3329061
  simp only [CollatzResearch.WordTrace]
  refine ⟨121420829792388030198667037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80947219861592020132444691 121420829792388030198667037)
  ·
    refine ⟨45532811172145511324500139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121420829792388030198667037 45532811172145511324500139)
    ·
      refine ⟨68299216758218266986750209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45532811172145511324500139 68299216758218266986750209)
      ·
        refine ⟨51224412568663700240062657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68299216758218266986750209 51224412568663700240062657)
        ·
          refine ⟨38418309426497775180046993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51224412568663700240062657 38418309426497775180046993)
          ·
            refine ⟨28813732069873331385035245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38418309426497775180046993 28813732069873331385035245)
            ·
              refine ⟨10805149526202499269388217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28813732069873331385035245 10805149526202499269388217)
              ·
                refine ⟨8103862144651874452041163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10805149526202499269388217 8103862144651874452041163)
                ·
                  refine ⟨12155793216977811678061745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8103862144651874452041163 12155793216977811678061745)
                  ·
                    refine ⟨9116844912733358758546309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12155793216977811678061745 9116844912733358758546309)
                    ·
                      refine ⟨1709408421137504767227433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9116844912733358758546309 1709408421137504767227433)
                      ·
                        rfl

theorem cell23_3329061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_3329061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329061 prefixEnd_3329061 := by exact prefixLift 3329061
  have htrace : WordTrace (prefixWord ++ tailWord_3329061) baseStart_3329061 baseEnd_3329061 := by
    simpa [prefixWord, tailWord_3329061, baseEnd_3329061] using wordTrace_append hprefix tailTrace_3329061
  have hstable : (prefixWord ++ tailWord_3329061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329061).length < 2 ^ (prefixWord ++ tailWord_3329061).sum := by decide
  have hdescent : baseEnd_3329061 < baseStart_3329061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329076 : List Nat := [2, 5, 1, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_3329076 : Nat := 118140960795 + 3329076 * 2 ^ 59
def prefixEnd_3329076 : Nat := 4983230072969 + 3 ^ 40 * 3329076 * 2
def baseEnd_3329076 : Nat := 1709416123347322208539865

theorem tailTrace_3329076 : CollatzResearch.WordTrace tailWord_3329076 prefixEnd_3329076 1709416123347322208539865 := by
  unfold tailWord_3329076
  simp only [CollatzResearch.WordTrace]
  refine ⟨60710688443666843880231541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80947584591555791840308721 60710688443666843880231541)
  ·
    refine ⟨5691627041593766613771707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60710688443666843880231541 5691627041593766613771707)
    ·
      refine ⟨8537440562390649920657561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5691627041593766613771707 8537440562390649920657561)
      ·
        refine ⟨6403080421792987440493171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8537440562390649920657561 6403080421792987440493171)
        ·
          refine ⟨9604620632689481160739757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6403080421792987440493171 9604620632689481160739757)
          ·
            refine ⟨3601732737258555435277409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9604620632689481160739757 3601732737258555435277409)
            ·
              refine ⟨2701299552943916576458057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3601732737258555435277409 2701299552943916576458057)
              ·
                refine ⟨2025974664707937432343543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2701299552943916576458057 2025974664707937432343543)
                ·
                  refine ⟨3038961997061906148515315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025974664707937432343543 3038961997061906148515315)
                  ·
                    refine ⟨4558442995592859222772973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3038961997061906148515315 4558442995592859222772973)
                    ·
                      refine ⟨1709416123347322208539865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4558442995592859222772973 1709416123347322208539865)
                      ·
                        rfl

theorem cell23_3329076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_3329076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329076 prefixEnd_3329076 := by exact prefixLift 3329076
  have htrace : WordTrace (prefixWord ++ tailWord_3329076) baseStart_3329076 baseEnd_3329076 := by
    simpa [prefixWord, tailWord_3329076, baseEnd_3329076] using wordTrace_append hprefix tailTrace_3329076
  have hstable : (prefixWord ++ tailWord_3329076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329076).length < 2 ^ (prefixWord ++ tailWord_3329076).sum := by decide
  have hdescent : baseEnd_3329076 < baseStart_3329076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329125 : List Nat := [1, 3, 1, 3, 2, 1, 3, 3, 1, 3, 2]
def baseStart_3329125 : Nat := 118140960795 + 3329125 * 2 ^ 59
def prefixEnd_3329125 : Nat := 4983230072969 + 3 ^ 40 * 3329125 * 2
def baseEnd_3329125 : Nat := 1709441283899392516827139

theorem tailTrace_3329125 : CollatzResearch.WordTrace tailWord_3329125 prefixEnd_3329125 1709441283899392516827139 := by
  unfold tailWord_3329125
  simp only [CollatzResearch.WordTrace]
  refine ⟨121423164064156169128996829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80948776042770779419331219 121423164064156169128996829)
  ·
    refine ⟨45533686524058563423373811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121423164064156169128996829 45533686524058563423373811)
    ·
      refine ⟨68300529786087845135060717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45533686524058563423373811 68300529786087845135060717)
      ·
        refine ⟨25612698669782941925647769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68300529786087845135060717 25612698669782941925647769)
        ·
          refine ⟨19209524002337206444235827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25612698669782941925647769 19209524002337206444235827)
          ·
            refine ⟨28814286003505809666353741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19209524002337206444235827 28814286003505809666353741)
            ·
              refine ⟨10805357251314678624882653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28814286003505809666353741 10805357251314678624882653)
              ·
                refine ⟨4052008969243004484330995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10805357251314678624882653 4052008969243004484330995)
                ·
                  refine ⟨6078013453864506726496493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052008969243004484330995 6078013453864506726496493)
                  ·
                    refine ⟨2279255045199190022436185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6078013453864506726496493 2279255045199190022436185)
                    ·
                      refine ⟨1709441283899392516827139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2279255045199190022436185 1709441283899392516827139)
                      ·
                        rfl

theorem cell23_3329125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_3329125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329125 prefixEnd_3329125 := by exact prefixLift 3329125
  have htrace : WordTrace (prefixWord ++ tailWord_3329125) baseStart_3329125 baseEnd_3329125 := by
    simpa [prefixWord, tailWord_3329125, baseEnd_3329125] using wordTrace_append hprefix tailTrace_3329125
  have hstable : (prefixWord ++ tailWord_3329125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329125).length < 2 ^ (prefixWord ++ tailWord_3329125).sum := by decide
  have hdescent : baseEnd_3329125 < baseStart_3329125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329161 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 7]
def baseStart_3329161 : Nat := 118140960795 + 3329161 * 2 ^ 59
def prefixEnd_3329161 : Nat := 4983230072969 + 3 ^ 40 * 3329161 * 2
def baseEnd_3329161 : Nat := 189939974355883819552997

theorem tailTrace_3329161 : CollatzResearch.WordTrace tailWord_3329161 prefixEnd_3329161 189939974355883819552997 := by
  unfold tailWord_3329161
  simp only [CollatzResearch.WordTrace]
  refine ⟨121424477092025747277307337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80949651394683831518204891 121424477092025747277307337)
  ·
    refine ⟨91068357819019310457980503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121424477092025747277307337 91068357819019310457980503)
    ·
      refine ⟨136602536728528965686970755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91068357819019310457980503 136602536728528965686970755)
      ·
        refine ⟨204903805092793448530456133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136602536728528965686970755 204903805092793448530456133)
        ·
          refine ⟨38419463454898771599460525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204903805092793448530456133 38419463454898771599460525)
          ·
            refine ⟨14407298795587039349797697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38419463454898771599460525 14407298795587039349797697)
            ·
              refine ⟨10805474096690279512348273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14407298795587039349797697 10805474096690279512348273)
              ·
                refine ⟨8104105572517709634261205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10805474096690279512348273 8104105572517709634261205)
                ·
                  refine ⟨189939974355883819552997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8104105572517709634261205 189939974355883819552997)
                  ·
                    rfl

theorem cell23_3329161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 7].length) (baseStart_3329161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329161 prefixEnd_3329161 := by exact prefixLift 3329161
  have htrace : WordTrace (prefixWord ++ tailWord_3329161) baseStart_3329161 baseEnd_3329161 := by
    simpa [prefixWord, tailWord_3329161, baseEnd_3329161] using wordTrace_append hprefix tailTrace_3329161
  have hstable : (prefixWord ++ tailWord_3329161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329161).length < 2 ^ (prefixWord ++ tailWord_3329161).sum := by decide
  have hdescent : baseEnd_3329161 < baseStart_3329161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329171 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 3]
def baseStart_3329171 : Nat := 118140960795 + 3329171 * 2 ^ 59
def prefixEnd_3329171 : Nat := 4983230072969 + 3 ^ 40 * 3329171 * 2
def baseEnd_3329171 : Nat := 1709464904009499336851927

theorem tailTrace_3329171 : CollatzResearch.WordTrace tailWord_3329171 prefixEnd_3329171 1709464904009499336851927 := by
  unfold tailWord_3329171
  simp only [CollatzResearch.WordTrace]
  refine ⟨121424841821989518985171367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80949894547993012656780911 121424841821989518985171367)
  ·
    refine ⟨182137262732984278477757051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121424841821989518985171367 182137262732984278477757051)
    ·
      refine ⟨273205894099476417716635577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182137262732984278477757051 273205894099476417716635577)
      ·
        refine ⟨204904420574607313287476683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273205894099476417716635577 204904420574607313287476683)
        ·
          refine ⟨307356630861910969931215025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204904420574607313287476683 307356630861910969931215025)
          ·
            refine ⟨230517473146433227448411269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307356630861910969931215025 230517473146433227448411269)
            ·
              refine ⟨43222026214956230146577113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 230517473146433227448411269 43222026214956230146577113)
              ·
                refine ⟨32416519661217172609932835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43222026214956230146577113 32416519661217172609932835)
                ·
                  refine ⟨48624779491825758914899253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32416519661217172609932835 48624779491825758914899253)
                  ·
                    refine ⟨4558573077358664898271805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48624779491825758914899253 4558573077358664898271805)
                    ·
                      refine ⟨1709464904009499336851927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4558573077358664898271805 1709464904009499336851927)
                      ·
                        rfl

theorem cell23_3329171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 3].length) (baseStart_3329171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329171 prefixEnd_3329171 := by exact prefixLift 3329171
  have htrace : WordTrace (prefixWord ++ tailWord_3329171) baseStart_3329171 baseEnd_3329171 := by
    simpa [prefixWord, tailWord_3329171, baseEnd_3329171] using wordTrace_append hprefix tailTrace_3329171
  have hstable : (prefixWord ++ tailWord_3329171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329171).length < 2 ^ (prefixWord ++ tailWord_3329171).sum := by decide
  have hdescent : baseEnd_3329171 < baseStart_3329171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329211 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 4]
def baseStart_3329211 : Nat := 118140960795 + 3329211 * 2 ^ 59
def prefixEnd_3329211 : Nat := 4983230072969 + 3 ^ 40 * 3329211 * 2
def baseEnd_3329211 : Nat := 1709485443235679180351743

theorem tailTrace_3329211 : CollatzResearch.WordTrace tailWord_3329211 prefixEnd_3329211 1709485443235679180351743 := by
  unfold tailWord_3329211
  simp only [CollatzResearch.WordTrace]
  refine ⟨121426300741844605816627487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80950867161229737211084991 121426300741844605816627487)
  ·
    refine ⟨182139451112766908724941231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121426300741844605816627487 182139451112766908724941231)
    ·
      refine ⟨273209176669150363087411847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182139451112766908724941231 273209176669150363087411847)
      ·
        refine ⟨409813765003725544631117771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273209176669150363087411847 409813765003725544631117771)
        ·
          refine ⟨614720647505588316946676657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409813765003725544631117771 614720647505588316946676657)
          ·
            refine ⟨461040485629191237710007493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614720647505588316946676657 461040485629191237710007493)
            ·
              refine ⟨86445091055473357070626405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 461040485629191237710007493 86445091055473357070626405)
              ·
                refine ⟨16208454572901254450742451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86445091055473357070626405 16208454572901254450742451)
                ·
                  refine ⟨24312681859351881676113677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16208454572901254450742451 24312681859351881676113677)
                  ·
                    refine ⟨9117255697256955628542629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24312681859351881676113677 9117255697256955628542629)
                    ·
                      refine ⟨1709485443235679180351743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9117255697256955628542629 1709485443235679180351743)
                      ·
                        rfl

theorem cell23_3329211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 4].length) (baseStart_3329211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329211 prefixEnd_3329211 := by exact prefixLift 3329211
  have htrace : WordTrace (prefixWord ++ tailWord_3329211) baseStart_3329211 baseEnd_3329211 := by
    simpa [prefixWord, tailWord_3329211, baseEnd_3329211] using wordTrace_append hprefix tailTrace_3329211
  have hstable : (prefixWord ++ tailWord_3329211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329211).length < 2 ^ (prefixWord ++ tailWord_3329211).sum := by decide
  have hdescent : baseEnd_3329211 < baseStart_3329211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329241 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 2, 1, 6]
def baseStart_3329241 : Nat := 118140960795 + 3329241 * 2 ^ 59
def prefixEnd_3329241 : Nat := 4983230072969 + 3 ^ 40 * 3329241 * 2
def baseEnd_3329241 : Nat := 1709500847655314062976605

theorem tailTrace_3329241 : CollatzResearch.WordTrace tailWord_3329241 prefixEnd_3329241 1709500847655314062976605 := by
  unfold tailWord_3329241
  simp only [CollatzResearch.WordTrace]
  refine ⟨121427394931735920940219577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80951596621157280626813051 121427394931735920940219577)
  ·
    refine ⟨91070546198801940705164683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121427394931735920940219577 91070546198801940705164683)
    ·
      refine ⟨136605819298202911057747025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91070546198801940705164683 136605819298202911057747025)
      ·
        refine ⟨102454364473652183293310269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136605819298202911057747025 102454364473652183293310269)
        ·
          refine ⟨38420386677619568734991351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102454364473652183293310269 38420386677619568734991351)
          ·
            refine ⟨57630580016429353102487027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38420386677619568734991351 57630580016429353102487027)
            ·
              refine ⟨86445870024644029653730541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57630580016429353102487027 86445870024644029653730541)
              ·
                refine ⟨32417201259241511120148953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86445870024644029653730541 32417201259241511120148953)
                ·
                  refine ⟨24312900944431133340111715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32417201259241511120148953 24312900944431133340111715)
                  ·
                    refine ⟨36469351416646700010167573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24312900944431133340111715 36469351416646700010167573)
                    ·
                      refine ⟨1709500847655314062976605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36469351416646700010167573 1709500847655314062976605)
                      ·
                        rfl

theorem cell23_3329241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_3329241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329241 prefixEnd_3329241 := by exact prefixLift 3329241
  have htrace : WordTrace (prefixWord ++ tailWord_3329241) baseStart_3329241 baseEnd_3329241 := by
    simpa [prefixWord, tailWord_3329241, baseEnd_3329241] using wordTrace_append hprefix tailTrace_3329241
  have hstable : (prefixWord ++ tailWord_3329241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329241).length < 2 ^ (prefixWord ++ tailWord_3329241).sum := by decide
  have hdescent : baseEnd_3329241 < baseStart_3329241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329271 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 6]
def baseStart_3329271 : Nat := 118140960795 + 3329271 * 2 ^ 59
def prefixEnd_3329271 : Nat := 4983230072969 + 3 ^ 40 * 3329271 * 2
def baseEnd_3329271 : Nat := 1709516252074948945601467

theorem tailTrace_3329271 : CollatzResearch.WordTrace tailWord_3329271 prefixEnd_3329271 1709516252074948945601467 := by
  unfold tailWord_3329271
  simp only [CollatzResearch.WordTrace]
  refine ⟨121428489121627236063811667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80952326081084824042541111 121428489121627236063811667)
  ·
    refine ⟨182142733682440854095717501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121428489121627236063811667 182142733682440854095717501)
    ·
      refine ⟨68303525130915320285894063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182142733682440854095717501 68303525130915320285894063)
      ·
        refine ⟨102455287696372980428841095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68303525130915320285894063 102455287696372980428841095)
        ·
          refine ⟨153682931544559470643261643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102455287696372980428841095 153682931544559470643261643)
          ·
            refine ⟨230524397316839205964892465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153682931544559470643261643 230524397316839205964892465)
            ·
              refine ⟨172893297987629404473669349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230524397316839205964892465 172893297987629404473669349)
              ·
                refine ⟨32417493372680513338813003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172893297987629404473669349 32417493372680513338813003)
                ·
                  refine ⟨48626240059020770008219505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32417493372680513338813003 48626240059020770008219505)
                  ·
                    refine ⟨36469680044265577506164629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48626240059020770008219505 36469680044265577506164629)
                    ·
                      refine ⟨1709516252074948945601467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36469680044265577506164629 1709516252074948945601467)
                      ·
                        rfl

theorem cell23_3329271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_3329271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329271 prefixEnd_3329271 := by exact prefixLift 3329271
  have htrace : WordTrace (prefixWord ++ tailWord_3329271) baseStart_3329271 baseEnd_3329271 := by
    simpa [prefixWord, tailWord_3329271, baseEnd_3329271] using wordTrace_append hprefix tailTrace_3329271
  have hstable : (prefixWord ++ tailWord_3329271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329271).length < 2 ^ (prefixWord ++ tailWord_3329271).sum := by decide
  have hdescent : baseEnd_3329271 < baseStart_3329271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329282 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_3329282 : Nat := 118140960795 + 3329282 * 2 ^ 59
def prefixEnd_3329282 : Nat := 4983230072969 + 3 ^ 40 * 3329282 * 2
def baseEnd_3329282 : Nat := 1709521900362148402563917

theorem tailTrace_3329282 : CollatzResearch.WordTrace tailWord_3329282 prefixEnd_3329282 1709521900362148402563917 := by
  unfold tailWord_3329282
  simp only [CollatzResearch.WordTrace]
  refine ⟨30357222581146846235615525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80952593549724923294974733 30357222581146846235615525)
  ·
    refine ⟨5691979233965033669177911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30357222581146846235615525 5691979233965033669177911)
    ·
      refine ⟨8537968850947550503766867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5691979233965033669177911 8537968850947550503766867)
      ·
        refine ⟨12806953276421325755650301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8537968850947550503766867 12806953276421325755650301)
        ·
          refine ⟨4802607478657997158368863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12806953276421325755650301 4802607478657997158368863)
          ·
            refine ⟨7203911217986995737553295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4802607478657997158368863 7203911217986995737553295)
            ·
              refine ⟨10805866826980493606329943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7203911217986995737553295 10805866826980493606329943)
              ·
                refine ⟨16208800240470740409494915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10805866826980493606329943 16208800240470740409494915)
                ·
                  refine ⟨24313200360706110614242373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16208800240470740409494915 24313200360706110614242373)
                  ·
                    refine ⟨4558725067632395740170445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24313200360706110614242373 4558725067632395740170445)
                    ·
                      refine ⟨1709521900362148402563917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4558725067632395740170445 1709521900362148402563917)
                      ·
                        rfl

theorem cell23_3329282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_3329282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329282 prefixEnd_3329282 := by exact prefixLift 3329282
  have htrace : WordTrace (prefixWord ++ tailWord_3329282) baseStart_3329282 baseEnd_3329282 := by
    simpa [prefixWord, tailWord_3329282, baseEnd_3329282] using wordTrace_append hprefix tailTrace_3329282
  have hstable : (prefixWord ++ tailWord_3329282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329282).length < 2 ^ (prefixWord ++ tailWord_3329282).sum := by decide
  have hdescent : baseEnd_3329282 < baseStart_3329282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329322 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_3329322 : Nat := 118140960795 + 3329322 * 2 ^ 59
def prefixEnd_3329322 : Nat := 4983230072969 + 3 ^ 40 * 3329322 * 2
def baseEnd_3329322 : Nat := 1709542439588328246063733

theorem tailTrace_3329322 : CollatzResearch.WordTrace tailWord_3329322 prefixEnd_3329322 1709542439588328246063733 := by
  unfold tailWord_3329322
  simp only [CollatzResearch.WordTrace]
  refine ⟨30357587311110617943479555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80953566162961647849278813 30357587311110617943479555)
  ·
    refine ⟨45536380966665926915219333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30357587311110617943479555 45536380966665926915219333)
    ·
      refine ⟨8538071431249861296603625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45536380966665926915219333 8538071431249861296603625)
      ·
        refine ⟨6403553573437395972452719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8538071431249861296603625 6403553573437395972452719)
        ·
          refine ⟨9605330360156093958679079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6403553573437395972452719 9605330360156093958679079)
          ·
            refine ⟨14407995540234140938018619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9605330360156093958679079 14407995540234140938018619)
            ·
              refine ⟨21611993310351211407027929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14407995540234140938018619 21611993310351211407027929)
              ·
                refine ⟨16208994982763408555270947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21611993310351211407027929 16208994982763408555270947)
                ·
                  refine ⟨24313492474145112832906421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16208994982763408555270947 24313492474145112832906421)
                  ·
                    refine ⟨2279389919451104328084977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24313492474145112832906421 2279389919451104328084977)
                    ·
                      refine ⟨1709542439588328246063733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2279389919451104328084977 1709542439588328246063733)
                      ·
                        rfl

theorem cell23_3329322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_3329322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329322 prefixEnd_3329322 := by exact prefixLift 3329322
  have htrace : WordTrace (prefixWord ++ tailWord_3329322) baseStart_3329322 baseEnd_3329322 := by
    simpa [prefixWord, tailWord_3329322, baseEnd_3329322] using wordTrace_append hprefix tailTrace_3329322
  have hstable : (prefixWord ++ tailWord_3329322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329322).length < 2 ^ (prefixWord ++ tailWord_3329322).sum := by decide
  have hdescent : baseEnd_3329322 < baseStart_3329322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329332 : List Nat := [2, 5, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_3329332 : Nat := 118140960795 + 3329332 * 2 ^ 59
def prefixEnd_3329332 : Nat := 4983230072969 + 3 ^ 40 * 3329332 * 2
def baseEnd_3329332 : Nat := 569849191464957735646229

theorem tailTrace_3329332 : CollatzResearch.WordTrace tailWord_3329332 prefixEnd_3329332 569849191464957735646229 := by
  unfold tailWord_3329332
  simp only [CollatzResearch.WordTrace]
  refine ⟨60715356987203121740891125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80953809316270828987854833 60715356987203121740891125)
  ·
    refine ⟨5692064717550292663208543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60715356987203121740891125 5692064717550292663208543)
    ·
      refine ⟨8538097076325438994812815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5692064717550292663208543 8538097076325438994812815)
      ·
        refine ⟨12807145614488158492219223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8538097076325438994812815 12807145614488158492219223)
        ·
          refine ⟨19210718421732237738328835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12807145614488158492219223 19210718421732237738328835)
          ·
            refine ⟨28816077632598356607493253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19210718421732237738328835 28816077632598356607493253)
            ·
              refine ⟨5403014556112191863904985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28816077632598356607493253 5403014556112191863904985)
              ·
                refine ⟨4052260917084143897928739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5403014556112191863904985 4052260917084143897928739)
                ·
                  refine ⟨6078391375626215846893109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052260917084143897928739 6078391375626215846893109)
                  ·
                    refine ⟨569849191464957735646229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6078391375626215846893109 569849191464957735646229)
                    ·
                      rfl

theorem cell23_3329332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_3329332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329332 prefixEnd_3329332 := by exact prefixLift 3329332
  have htrace : WordTrace (prefixWord ++ tailWord_3329332) baseStart_3329332 baseEnd_3329332 := by
    simpa [prefixWord, tailWord_3329332, baseEnd_3329332] using wordTrace_append hprefix tailTrace_3329332
  have hstable : (prefixWord ++ tailWord_3329332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329332).length < 2 ^ (prefixWord ++ tailWord_3329332).sum := by decide
  have hdescent : baseEnd_3329332 < baseStart_3329332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329338 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5]
def baseStart_3329338 : Nat := 118140960795 + 3329338 * 2 ^ 59
def prefixEnd_3329338 : Nat := 4983230072969 + 3 ^ 40 * 3329338 * 2
def baseEnd_3329338 : Nat := 1709550655278800183463659

theorem tailTrace_3329338 : CollatzResearch.WordTrace tailWord_3329338 prefixEnd_3329338 1709550655278800183463659 := by
  unfold tailWord_3329338
  simp only [CollatzResearch.WordTrace]
  refine ⟨30357733203096126626625167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80953955208256337671000445 30357733203096126626625167)
  ·
    refine ⟨45536599804644189939937751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30357733203096126626625167 45536599804644189939937751)
    ·
      refine ⟨68304899706966284909906627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45536599804644189939937751 68304899706966284909906627)
      ·
        refine ⟨102457349560449427364859941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68304899706966284909906627 102457349560449427364859941)
        ·
          refine ⟨19210753042584267630911239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102457349560449427364859941 19210753042584267630911239)
          ·
            refine ⟨28816129563876401446366859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19210753042584267630911239 28816129563876401446366859)
            ·
              refine ⟨43224194345814602169550289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28816129563876401446366859 43224194345814602169550289)
              ·
                refine ⟨32418145759360951627162717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43224194345814602169550289 32418145759360951627162717)
                ·
                  refine ⟨12156804659760356860186019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32418145759360951627162717 12156804659760356860186019)
                  ·
                    refine ⟨18235206989640535290279029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12156804659760356860186019 18235206989640535290279029)
                    ·
                      refine ⟨1709550655278800183463659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18235206989640535290279029 1709550655278800183463659)
                      ·
                        rfl

theorem cell23_3329338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_3329338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329338 prefixEnd_3329338 := by exact prefixLift 3329338
  have htrace : WordTrace (prefixWord ++ tailWord_3329338) baseStart_3329338 baseEnd_3329338 := by
    simpa [prefixWord, tailWord_3329338, baseEnd_3329338] using wordTrace_append hprefix tailTrace_3329338
  have hstable : (prefixWord ++ tailWord_3329338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329338).length < 2 ^ (prefixWord ++ tailWord_3329338).sum := by decide
  have hdescent : baseEnd_3329338 < baseStart_3329338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329369 : List Nat := [1, 2, 1, 2, 2, 2, 2, 6, 1, 2, 2]
def baseStart_3329369 : Nat := 118140960795 + 3329369 * 2 ^ 59
def prefixEnd_3329369 : Nat := 4983230072969 + 3 ^ 40 * 3329369 * 2
def baseEnd_3329369 : Nat := 1709566573179089562176017

theorem tailTrace_3329369 : CollatzResearch.WordTrace tailWord_3329369 prefixEnd_3329369 1709566573179089562176017 := by
  unfold tailWord_3329369
  simp only [CollatzResearch.WordTrace]
  refine ⟨121432063475272198800879161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80954708983514799200586107 121432063475272198800879161)
  ·
    refine ⟨91074047606454149100659371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121432063475272198800879161 91074047606454149100659371)
    ·
      refine ⟨136611071409681223650989057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91074047606454149100659371 136611071409681223650989057)
      ·
        refine ⟨102458303557260917738241793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136611071409681223650989057 102458303557260917738241793)
        ·
          refine ⟨76843727667945688303681345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102458303557260917738241793 76843727667945688303681345)
          ·
            refine ⟨57632795750959266227761009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76843727667945688303681345 57632795750959266227761009)
            ·
              refine ⟨43224596813219449670820757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57632795750959266227761009 43224596813219449670820757)
              ·
                refine ⟨2026152975619661703319723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43224596813219449670820757 2026152975619661703319723)
                ·
                  refine ⟨3039229463429492554979585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026152975619661703319723 3039229463429492554979585)
                  ·
                    refine ⟨2279422097572119416234689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3039229463429492554979585 2279422097572119416234689)
                    ·
                      refine ⟨1709566573179089562176017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2279422097572119416234689 1709566573179089562176017)
                      ·
                        rfl

theorem cell23_3329369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 1, 2, 2].length) (baseStart_3329369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329369 prefixEnd_3329369 := by exact prefixLift 3329369
  have htrace : WordTrace (prefixWord ++ tailWord_3329369) baseStart_3329369 baseEnd_3329369 := by
    simpa [prefixWord, tailWord_3329369, baseEnd_3329369] using wordTrace_append hprefix tailTrace_3329369
  have hstable : (prefixWord ++ tailWord_3329369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329369).length < 2 ^ (prefixWord ++ tailWord_3329369).sum := by decide
  have hdescent : baseEnd_3329369 < baseStart_3329369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329379 : List Nat := [1, 1, 1, 5, 2, 4, 2, 1, 2, 4]
def baseStart_3329379 : Nat := 118140960795 + 3329379 * 2 ^ 59
def prefixEnd_3329379 : Nat := 4983230072969 + 3 ^ 40 * 3329379 * 2
def baseEnd_3329379 : Nat := 569857235995211507683657

theorem tailTrace_3329379 : CollatzResearch.WordTrace tailWord_3329379 prefixEnd_3329379 569857235995211507683657 := by
  unfold tailWord_3329379
  simp only [CollatzResearch.WordTrace]
  refine ⟨121432428205235970508743191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80954952136823980339162127 121432428205235970508743191)
  ·
    refine ⟨182148642307853955763114787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121432428205235970508743191 182148642307853955763114787)
    ·
      refine ⟨273222963461780933644672181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182148642307853955763114787 273222963461780933644672181)
      ·
        refine ⟨25614652824541962529188017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 273222963461780933644672181 25614652824541962529188017)
        ·
          refine ⟨19210989618406471896891013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25614652824541962529188017 19210989618406471896891013)
          ·
            refine ⟨3602060553451213480667065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19210989618406471896891013 3602060553451213480667065)
            ·
              refine ⟨2701545415088410110500299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3602060553451213480667065 2701545415088410110500299)
              ·
                refine ⟨4052318122632615165750449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2701545415088410110500299 4052318122632615165750449)
                ·
                  refine ⟨3039238591974461374312837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4052318122632615165750449 3039238591974461374312837)
                  ·
                    refine ⟨569857235995211507683657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3039238591974461374312837 569857235995211507683657)
                    ·
                      rfl

theorem cell23_3329379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 2, 4].length) (baseStart_3329379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329379 prefixEnd_3329379 := by exact prefixLift 3329379
  have htrace : WordTrace (prefixWord ++ tailWord_3329379) baseStart_3329379 baseEnd_3329379 := by
    simpa [prefixWord, tailWord_3329379, baseEnd_3329379] using wordTrace_append hprefix tailTrace_3329379
  have hstable : (prefixWord ++ tailWord_3329379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329379).length < 2 ^ (prefixWord ++ tailWord_3329379).sum := by decide
  have hdescent : baseEnd_3329379 < baseStart_3329379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329385 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 6, 1, 3]
def baseStart_3329385 : Nat := 118140960795 + 3329385 * 2 ^ 59
def prefixEnd_3329385 : Nat := 4983230072969 + 3 ^ 40 * 3329385 * 2
def baseEnd_3329385 : Nat := 1709574788869561499575943

theorem tailTrace_3329385 : CollatzResearch.WordTrace tailWord_3329385 prefixEnd_3329385 1709574788869561499575943 := by
  unfold tailWord_3329385
  simp only [CollatzResearch.WordTrace]
  refine ⟨121432647043214233533461609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80955098028809489022307739 121432647043214233533461609)
  ·
    refine ⟨91074485282410675150096207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121432647043214233533461609 91074485282410675150096207)
    ·
      refine ⟨136611727923616012725144311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91074485282410675150096207 136611727923616012725144311)
      ·
        refine ⟨204917591885424019087716467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136611727923616012725144311 204917591885424019087716467)
        ·
          refine ⟨307376387828136028631574701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204917591885424019087716467 307376387828136028631574701)
          ·
            refine ⟨115266145435551010736840513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307376387828136028631574701 115266145435551010736840513)
            ·
              refine ⟨86449609076663258052630385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115266145435551010736840513 86449609076663258052630385)
              ·
                refine ⟨64837206807497443539472789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86449609076663258052630385 64837206807497443539472789)
                ·
                  refine ⟨3039244069101442665912787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64837206807497443539472789 3039244069101442665912787)
                  ·
                    refine ⟨4558866103652163998869181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3039244069101442665912787 4558866103652163998869181)
                    ·
                      refine ⟨1709574788869561499575943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4558866103652163998869181 1709574788869561499575943)
                      ·
                        rfl

theorem cell23_3329385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 1, 3].length) (baseStart_3329385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329385 prefixEnd_3329385 := by exact prefixLift 3329385
  have htrace : WordTrace (prefixWord ++ tailWord_3329385) baseStart_3329385 baseEnd_3329385 := by
    simpa [prefixWord, tailWord_3329385, baseEnd_3329385] using wordTrace_append hprefix tailTrace_3329385
  have hstable : (prefixWord ++ tailWord_3329385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329385).length < 2 ^ (prefixWord ++ tailWord_3329385).sum := by decide
  have hdescent : baseEnd_3329385 < baseStart_3329385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329386 : List Nat := [3, 1, 3, 3, 3, 1, 1, 2, 1, 1, 4]
def baseStart_3329386 : Nat := 118140960795 + 3329386 * 2 ^ 59
def prefixEnd_3329386 : Nat := 4983230072969 + 3 ^ 40 * 3329386 * 2
def baseEnd_3329386 : Nat := 1709575302350215995663439

theorem tailTrace_3329386 : CollatzResearch.WordTrace tailWord_3329386 prefixEnd_3329386 1709575302350215995663439 := by
  unfold tailWord_3329386
  simp only [CollatzResearch.WordTrace]
  refine ⟨30358170879052652676062003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80955122344140407136165341 30358170879052652676062003)
  ·
    refine ⟨45537256318578979014093005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30358170879052652676062003 45537256318578979014093005)
    ·
      refine ⟨17076471119467117130284877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45537256318578979014093005 17076471119467117130284877)
      ·
        refine ⟨6403676669800168923856829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17076471119467117130284877 6403676669800168923856829)
        ·
          refine ⟨2401378751175063346446311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6403676669800168923856829 2401378751175063346446311)
          ·
            refine ⟨3602068126762595019669467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401378751175063346446311 3602068126762595019669467)
            ·
              refine ⟨5403102190143892529504201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3602068126762595019669467 5403102190143892529504201)
              ·
                refine ⟨4052326642607919397128151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5403102190143892529504201 4052326642607919397128151)
                ·
                  refine ⟨6078489963911879095692227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052326642607919397128151 6078489963911879095692227)
                  ·
                    refine ⟨9117734945867818643538341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6078489963911879095692227 9117734945867818643538341)
                    ·
                      refine ⟨1709575302350215995663439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9117734945867818643538341 1709575302350215995663439)
                      ·
                        rfl

theorem cell23_3329386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_3329386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329386 prefixEnd_3329386 := by exact prefixLift 3329386
  have htrace : WordTrace (prefixWord ++ tailWord_3329386) baseStart_3329386 baseEnd_3329386 := by
    simpa [prefixWord, tailWord_3329386, baseEnd_3329386] using wordTrace_append hprefix tailTrace_3329386
  have hstable : (prefixWord ++ tailWord_3329386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329386).length < 2 ^ (prefixWord ++ tailWord_3329386).sum := by decide
  have hdescent : baseEnd_3329386 < baseStart_3329386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329389 : List Nat := [1, 5, 1, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_3329389 : Nat := 118140960795 + 3329389 * 2 ^ 59
def prefixEnd_3329389 : Nat := 4983230072969 + 3 ^ 40 * 3329389 * 2
def baseEnd_3329389 : Nat := 1709576842792179483925925

theorem tailTrace_3329389 : CollatzResearch.WordTrace tailWord_3329389 prefixEnd_3329389 1709576842792179483925925 := by
  unfold tailWord_3329389
  simp only [CollatzResearch.WordTrace]
  refine ⟨121432792935199742216607221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80955195290133161477738147 121432792935199742216607221)
  ·
    refine ⟨11384324337674975832806927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121432792935199742216607221 11384324337674975832806927)
    ·
      refine ⟨17076486506512463749210391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11384324337674975832806927 17076486506512463749210391)
      ·
        refine ⟨25614729759768695623815587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17076486506512463749210391 25614729759768695623815587)
        ·
          refine ⟨38422094639653043435723381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25614729759768695623815587 38422094639653043435723381)
          ·
            refine ⟨3602071372467472822099067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38422094639653043435723381 3602071372467472822099067)
            ·
              refine ⟨5403107058701209233148601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3602071372467472822099067 5403107058701209233148601)
              ·
                refine ⟨4052330294025906924861451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5403107058701209233148601 4052330294025906924861451)
                ·
                  refine ⟨6078495441038860387292177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052330294025906924861451 6078495441038860387292177)
                  ·
                    refine ⟨4558871580779145290469133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6078495441038860387292177 4558871580779145290469133)
                    ·
                      refine ⟨1709576842792179483925925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4558871580779145290469133 1709576842792179483925925)
                      ·
                        rfl

theorem cell23_3329389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_3329389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329389 prefixEnd_3329389 := by exact prefixLift 3329389
  have htrace : WordTrace (prefixWord ++ tailWord_3329389) baseStart_3329389 baseEnd_3329389 := by
    simpa [prefixWord, tailWord_3329389, baseEnd_3329389] using wordTrace_append hprefix tailTrace_3329389
  have hstable : (prefixWord ++ tailWord_3329389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329389).length < 2 ^ (prefixWord ++ tailWord_3329389).sum := by decide
  have hdescent : baseEnd_3329389 < baseStart_3329389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329406 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3329406 : Nat := 118140960795 + 3329406 * 2 ^ 59
def prefixEnd_3329406 : Nat := 4983230072969 + 3 ^ 40 * 3329406 * 2
def baseEnd_3329406 : Nat := 1709585571963305917413347

theorem tailTrace_3329406 : CollatzResearch.WordTrace tailWord_3329406 prefixEnd_3329406 1709585571963305917413347 := by
  unfold tailWord_3329406
  simp only [CollatzResearch.WordTrace]
  refine ⟨15179176622017269264997009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80955608650758769413317381 15179176622017269264997009)
  ·
    refine ⟨11384382466512951948747757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15179176622017269264997009 11384382466512951948747757)
    ·
      refine ⟨4269143424942356980780409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11384382466512951948747757 4269143424942356980780409)
      ·
        refine ⟨3201857568706767735585307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4269143424942356980780409 3201857568706767735585307)
        ·
          refine ⟨4802786353060151603377961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201857568706767735585307 4802786353060151603377961)
          ·
            refine ⟨3602089764795113702533471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4802786353060151603377961 3602089764795113702533471)
            ·
              refine ⟨5403134647192670553800207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3602089764795113702533471 5403134647192670553800207)
              ·
                refine ⟨8104701970789005830700311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5403134647192670553800207 8104701970789005830700311)
                ·
                  refine ⟨12157052956183508746050467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8104701970789005830700311 12157052956183508746050467)
                  ·
                    refine ⟨18235579434275263119075701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12157052956183508746050467 18235579434275263119075701)
                    ·
                      refine ⟨1709585571963305917413347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18235579434275263119075701 1709585571963305917413347)
                      ·
                        rfl

theorem cell23_3329406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3329406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329406 prefixEnd_3329406 := by exact prefixLift 3329406
  have htrace : WordTrace (prefixWord ++ tailWord_3329406) baseStart_3329406 baseEnd_3329406 := by
    simpa [prefixWord, tailWord_3329406, baseEnd_3329406] using wordTrace_append hprefix tailTrace_3329406
  have hstable : (prefixWord ++ tailWord_3329406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329406).length < 2 ^ (prefixWord ++ tailWord_3329406).sum := by decide
  have hdescent : baseEnd_3329406 < baseStart_3329406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329408 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 4]
def baseStart_3329408 : Nat := 118140960795 + 3329408 * 2 ^ 59
def prefixEnd_3329408 : Nat := 4983230072969 + 3 ^ 40 * 3329408 * 2
def baseEnd_3329408 : Nat := 1709586598924614909588337

theorem tailTrace_3329408 : CollatzResearch.WordTrace tailWord_3329408 prefixEnd_3329408 1709586598924614909588337 := by
  unfold tailWord_3329408
  simp only [CollatzResearch.WordTrace]
  refine ⟨60716742961065454230774439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80955657281420605641032585 60716742961065454230774439)
  ·
    refine ⟨91075114441598181346161659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60716742961065454230774439 91075114441598181346161659)
    ·
      refine ⟨136612671662397272019242489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91075114441598181346161659 136612671662397272019242489)
      ·
        refine ⟨102459503746797954014431867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136612671662397272019242489 102459503746797954014431867)
        ·
          refine ⟨153689255620196931021647801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102459503746797954014431867 153689255620196931021647801)
          ·
            refine ⟨115266941715147698266235851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153689255620196931021647801 115266941715147698266235851)
            ·
              refine ⟨172900412572721547399353777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115266941715147698266235851 172900412572721547399353777)
              ·
                refine ⟨129675309429541160549515333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172900412572721547399353777 129675309429541160549515333)
                ·
                  refine ⟨24314120518038967603034125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129675309429541160549515333 24314120518038967603034125)
                  ·
                    refine ⟨9117795194264612851137797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24314120518038967603034125 9117795194264612851137797)
                    ·
                      refine ⟨1709586598924614909588337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9117795194264612851137797 1709586598924614909588337)
                      ·
                        rfl

theorem cell23_3329408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_3329408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329408 prefixEnd_3329408 := by exact prefixLift 3329408
  have htrace : WordTrace (prefixWord ++ tailWord_3329408) baseStart_3329408 baseEnd_3329408 := by
    simpa [prefixWord, tailWord_3329408, baseEnd_3329408] using wordTrace_append hprefix tailTrace_3329408
  have hstable : (prefixWord ++ tailWord_3329408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329408).length < 2 ^ (prefixWord ++ tailWord_3329408).sum := by decide
  have hdescent : baseEnd_3329408 < baseStart_3329408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329475 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 3]
def baseStart_3329475 : Nat := 118140960795 + 3329475 * 2 ^ 59
def prefixEnd_3329475 : Nat := 4983230072969 + 3 ^ 40 * 3329475 * 2
def baseEnd_3329475 : Nat := 1709621002128466147450529

theorem tailTrace_3329475 : CollatzResearch.WordTrace tailWord_3329475 prefixEnd_3329475 1709621002128466147450529 := by
  unfold tailWord_3329475
  simp only [CollatzResearch.WordTrace]
  refine ⟨121435929612888178904237879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80957286408592119269491919 121435929612888178904237879)
  ·
    refine ⟨182153894419332268356356819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121435929612888178904237879 182153894419332268356356819)
    ·
      refine ⟨273230841628998402534535229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182153894419332268356356819 273230841628998402534535229)
      ·
        refine ⟨102461565610874400950450711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273230841628998402534535229 102461565610874400950450711)
        ·
          refine ⟨153692348416311601425676067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102461565610874400950450711 153692348416311601425676067)
          ·
            refine ⟨230538522624467402138514101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153692348416311601425676067 230538522624467402138514101)
            ·
              refine ⟨21612986496043818950485697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 230538522624467402138514101 21612986496043818950485697)
              ·
                refine ⟨16209739872032864212864273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21612986496043818950485697 16209739872032864212864273)
                ·
                  refine ⟨12157304904024648159648205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16209739872032864212864273 12157304904024648159648205)
                  ·
                    refine ⟨4558989339009243059868077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12157304904024648159648205 4558989339009243059868077)
                    ·
                      refine ⟨1709621002128466147450529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4558989339009243059868077 1709621002128466147450529)
                      ·
                        rfl

theorem cell23_3329475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_3329475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329475 prefixEnd_3329475 := by exact prefixLift 3329475
  have htrace : WordTrace (prefixWord ++ tailWord_3329475) baseStart_3329475 baseEnd_3329475 := by
    simpa [prefixWord, tailWord_3329475, baseEnd_3329475] using wordTrace_append hprefix tailTrace_3329475
  have hstable : (prefixWord ++ tailWord_3329475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329475).length < 2 ^ (prefixWord ++ tailWord_3329475).sum := by decide
  have hdescent : baseEnd_3329475 < baseStart_3329475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329476 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_3329476 : Nat := 118140960795 + 3329476 * 2 ^ 59
def prefixEnd_3329476 : Nat := 4983230072969 + 3 ^ 40 * 3329476 * 2
def baseEnd_3329476 : Nat := 1709621515609120643538025

theorem tailTrace_3329476 : CollatzResearch.WordTrace tailWord_3329476 prefixEnd_3329476 1709621515609120643538025 := by
  unfold tailWord_3329476
  simp only [CollatzResearch.WordTrace]
  refine ⟨60717983042942278037512141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80957310723923037383349521 60717983042942278037512141)
  ·
    refine ⟨22769243641103354264067053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60717983042942278037512141 22769243641103354264067053)
    ·
      refine ⟨8538466365413757849025145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22769243641103354264067053 8538466365413757849025145)
      ·
        refine ⟨6403849774060318386768859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8538466365413757849025145 6403849774060318386768859)
        ·
          refine ⟨9605774661090477580153289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6403849774060318386768859 9605774661090477580153289)
          ·
            refine ⟨7204330995817858185114967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9605774661090477580153289 7204330995817858185114967)
            ·
              refine ⟨10806496493726787277672451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7204330995817858185114967 10806496493726787277672451)
              ·
                refine ⟨16209744740590180916508677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10806496493726787277672451 16209744740590180916508677)
                ·
                  refine ⟨3039327138860658921845377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16209744740590180916508677 3039327138860658921845377)
                  ·
                    refine ⟨2279495354145494191384033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3039327138860658921845377 2279495354145494191384033)
                    ·
                      refine ⟨1709621515609120643538025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2279495354145494191384033 1709621515609120643538025)
                      ·
                        rfl

theorem cell23_3329476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_3329476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329476 prefixEnd_3329476 := by exact prefixLift 3329476
  have htrace : WordTrace (prefixWord ++ tailWord_3329476) baseStart_3329476 baseEnd_3329476 := by
    simpa [prefixWord, tailWord_3329476, baseEnd_3329476] using wordTrace_append hprefix tailTrace_3329476
  have hstable : (prefixWord ++ tailWord_3329476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329476).length < 2 ^ (prefixWord ++ tailWord_3329476).sum := by decide
  have hdescent : baseEnd_3329476 < baseStart_3329476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329482 : List Nat := [3, 1, 2, 1, 2, 3, 2, 4, 5]
def baseStart_3329482 : Nat := 118140960795 + 3329482 * 2 ^ 59
def prefixEnd_3329482 : Nat := 4983230072969 + 3 ^ 40 * 3329482 * 2
def baseEnd_3329482 : Nat := 189958288499227513340333

theorem tailTrace_3329482 : CollatzResearch.WordTrace tailWord_3329482 prefixEnd_3329482 189958288499227513340333 := by
  unfold tailWord_3329482
  simp only [CollatzResearch.WordTrace]
  refine ⟨30359046230965704774935675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80957456615908546066495133 30359046230965704774935675)
  ·
    refine ⟨45538569346448557162403513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30359046230965704774935675 45538569346448557162403513)
    ·
      refine ⟨34153927009836417871802635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45538569346448557162403513 34153927009836417871802635)
      ·
        refine ⟨51230890514754626807703953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34153927009836417871802635 51230890514754626807703953)
        ·
          refine ⟨38423167886065970105777965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51230890514754626807703953 38423167886065970105777965)
          ·
            refine ⟨14408687957274738789666737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38423167886065970105777965 14408687957274738789666737)
            ·
              refine ⟨10806515967956054092250053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14408687957274738789666737 10806515967956054092250053)
              ·
                refine ⟨2026221743991760142296885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10806515967956054092250053 2026221743991760142296885)
                ·
                  refine ⟨189958288499227513340333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2026221743991760142296885 189958288499227513340333)
                  ·
                    rfl

theorem cell23_3329482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 5].length) (baseStart_3329482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329482 prefixEnd_3329482 := by exact prefixLift 3329482
  have htrace : WordTrace (prefixWord ++ tailWord_3329482) baseStart_3329482 baseEnd_3329482 := by
    simpa [prefixWord, tailWord_3329482, baseEnd_3329482] using wordTrace_append hprefix tailTrace_3329482
  have hstable : (prefixWord ++ tailWord_3329482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329482).length < 2 ^ (prefixWord ++ tailWord_3329482).sum := by decide
  have hdescent : baseEnd_3329482 < baseStart_3329482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329532 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 4, 4, 2]
def baseStart_3329532 : Nat := 118140960795 + 3329532 * 2 ^ 59
def prefixEnd_3329532 : Nat := 4983230072969 + 3 ^ 40 * 3329532 * 2
def baseEnd_3329532 : Nat := 1709650270525772424437767

theorem tailTrace_3329532 : CollatzResearch.WordTrace tailWord_3329532 prefixEnd_3329532 1709650270525772424437767 := by
  unfold tailWord_3329532
  simp only [CollatzResearch.WordTrace]
  refine ⟨60719004286840838819531425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80958672382454451759375233 60719004286840838819531425)
  ·
    refine ⟨45539253215130629114648569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60719004286840838819531425 45539253215130629114648569)
    ·
      refine ⟨34154439911347971835986427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45539253215130629114648569 34154439911347971835986427)
      ·
        refine ⟨51231659867021957753979641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34154439911347971835986427 51231659867021957753979641)
        ·
          refine ⟨38423744900266468315484731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51231659867021957753979641 38423744900266468315484731)
          ·
            refine ⟨57635617350399702473227097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38423744900266468315484731 57635617350399702473227097)
            ·
              refine ⟨43226713012799776854920323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57635617350399702473227097 43226713012799776854920323)
              ·
                refine ⟨64840069519199665282380485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43226713012799776854920323 64840069519199665282380485)
                ·
                  refine ⟨12157513034849937240446341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64840069519199665282380485 12157513034849937240446341)
                  ·
                    refine ⟨2279533694034363232583689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12157513034849937240446341 2279533694034363232583689)
                    ·
                      refine ⟨1709650270525772424437767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2279533694034363232583689 1709650270525772424437767)
                      ·
                        rfl

theorem cell23_3329532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_3329532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329532 prefixEnd_3329532 := by exact prefixLift 3329532
  have htrace : WordTrace (prefixWord ++ tailWord_3329532) baseStart_3329532 baseEnd_3329532 := by
    simpa [prefixWord, tailWord_3329532, baseEnd_3329532] using wordTrace_append hprefix tailTrace_3329532
  have hstable : (prefixWord ++ tailWord_3329532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329532).length < 2 ^ (prefixWord ++ tailWord_3329532).sum := by decide
  have hdescent : baseEnd_3329532 < baseStart_3329532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329535 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 3]
def baseStart_3329535 : Nat := 118140960795 + 3329535 * 2 ^ 59
def prefixEnd_3329535 : Nat := 4983230072969 + 3 ^ 40 * 3329535 * 2
def baseEnd_3329535 : Nat := 1709651810967735912700253

theorem tailTrace_3329535 : CollatzResearch.WordTrace tailWord_3329535 prefixEnd_3329535 1709651810967735912700253 := by
  unfold tailWord_3329535
  simp only [CollatzResearch.WordTrace]
  refine ⟨121438117992670809151422059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80958745328447206100948039 121438117992670809151422059)
  ·
    refine ⟨182157176989006213727133089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121438117992670809151422059 182157176989006213727133089)
    ·
      refine ⟨136617882741754660295349817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182157176989006213727133089 136617882741754660295349817)
      ·
        refine ⟨102463412056315995221512363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136617882741754660295349817 102463412056315995221512363)
        ·
          refine ⟨153695118084473992832268545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102463412056315995221512363 153695118084473992832268545)
          ·
            refine ⟨115271338563355494624201409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153695118084473992832268545 115271338563355494624201409)
            ·
              refine ⟨86453503922516620968151057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115271338563355494624201409 86453503922516620968151057)
              ·
                refine ⟨64840127941887465726113293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86453503922516620968151057 64840127941887465726113293)
                ·
                  refine ⟨24315047978207799647292485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64840127941887465726113293 24315047978207799647292485)
                  ·
                    refine ⟨4559071495913962433867341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24315047978207799647292485 4559071495913962433867341)
                    ·
                      refine ⟨1709651810967735912700253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4559071495913962433867341 1709651810967735912700253)
                      ·
                        rfl

theorem cell23_3329535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_3329535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329535 prefixEnd_3329535 := by exact prefixLift 3329535
  have htrace : WordTrace (prefixWord ++ tailWord_3329535) baseStart_3329535 baseEnd_3329535 := by
    simpa [prefixWord, tailWord_3329535, baseEnd_3329535] using wordTrace_append hprefix tailTrace_3329535
  have hstable : (prefixWord ++ tailWord_3329535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329535).length < 2 ^ (prefixWord ++ tailWord_3329535).sum := by decide
  have hdescent : baseEnd_3329535 < baseStart_3329535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329569 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 2, 2, 3]
def baseStart_3329569 : Nat := 118140960795 + 3329569 * 2 ^ 59
def prefixEnd_3329569 : Nat := 4983230072969 + 3 ^ 40 * 3329569 * 2
def baseEnd_3329569 : Nat := 1709669269309988779675097

theorem tailTrace_3329569 : CollatzResearch.WordTrace tailWord_3329569 prefixEnd_3329569 1709669269309988779675097 := by
  unfold tailWord_3329569
  simp only [CollatzResearch.WordTrace]
  refine ⟨121439358074547632958159761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80959572049698421972106507 121439358074547632958159761)
  ·
    refine ⟨91079518555910724718619821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121439358074547632958159761 91079518555910724718619821)
    ·
      refine ⟨34154819458466521769482433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91079518555910724718619821 34154819458466521769482433)
      ·
        refine ⟨25616114593849891327111825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34154819458466521769482433 25616114593849891327111825)
        ·
          refine ⟨19212085945387418495333869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25616114593849891327111825 19212085945387418495333869)
          ·
            refine ⟨7204532229520281935750201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19212085945387418495333869 7204532229520281935750201)
            ·
              refine ⟨5403399172140211451812651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7204532229520281935750201 5403399172140211451812651)
              ·
                refine ⟨8105098758210317177718977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5403399172140211451812651 8105098758210317177718977)
                ·
                  refine ⟨6078824068657737883289233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8105098758210317177718977 6078824068657737883289233)
                  ·
                    refine ⟨4559118051493303412466925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6078824068657737883289233 4559118051493303412466925)
                    ·
                      refine ⟨1709669269309988779675097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4559118051493303412466925 1709669269309988779675097)
                      ·
                        rfl

theorem cell23_3329569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_3329569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329569 prefixEnd_3329569 := by exact prefixLift 3329569
  have htrace : WordTrace (prefixWord ++ tailWord_3329569) baseStart_3329569 baseEnd_3329569 := by
    simpa [prefixWord, tailWord_3329569, baseEnd_3329569] using wordTrace_append hprefix tailTrace_3329569
  have hstable : (prefixWord ++ tailWord_3329569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329569).length < 2 ^ (prefixWord ++ tailWord_3329569).sum := by decide
  have hdescent : baseEnd_3329569 < baseStart_3329569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329593 : List Nat := [1, 2, 1, 5, 1, 4, 2, 2, 1, 4]
def baseStart_3329593 : Nat := 118140960795 + 3329593 * 2 ^ 59
def prefixEnd_3329593 : Nat := 4983230072969 + 3 ^ 40 * 3329593 * 2
def baseEnd_3329593 : Nat := 569893864281898895258329

theorem tailTrace_3329593 : CollatzResearch.WordTrace tailWord_3329593 prefixEnd_3329593 569893864281898895258329 := by
  unfold tailWord_3329593
  simp only [CollatzResearch.WordTrace]
  refine ⟨121440233426460685057033433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80960155617640456704688955 121440233426460685057033433)
  ·
    refine ⟨91080175069845513792775075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121440233426460685057033433 91080175069845513792775075)
    ·
      refine ⟨136620262604768270689162613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91080175069845513792775075 136620262604768270689162613)
      ·
        refine ⟨12808149619197025377108995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136620262604768270689162613 12808149619197025377108995)
        ·
          refine ⟨19212224428795538065663493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12808149619197025377108995 19212224428795538065663493)
          ·
            refine ⟨3602292080399163387311905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19212224428795538065663493 3602292080399163387311905)
            ·
              refine ⟨2701719060299372540483929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3602292080399163387311905 2701719060299372540483929)
              ·
                refine ⟨2026289295224529405362947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2701719060299372540483929 2026289295224529405362947)
                ·
                  refine ⟨3039433942836794108044421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026289295224529405362947 3039433942836794108044421)
                  ·
                    refine ⟨569893864281898895258329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3039433942836794108044421 569893864281898895258329)
                    ·
                      rfl

theorem cell23_3329593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 1, 4].length) (baseStart_3329593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329593 prefixEnd_3329593 := by exact prefixLift 3329593
  have htrace : WordTrace (prefixWord ++ tailWord_3329593) baseStart_3329593 baseEnd_3329593 := by
    simpa [prefixWord, tailWord_3329593, baseEnd_3329593] using wordTrace_append hprefix tailTrace_3329593
  have hstable : (prefixWord ++ tailWord_3329593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329593).length < 2 ^ (prefixWord ++ tailWord_3329593).sum := by decide
  have hdescent : baseEnd_3329593 < baseStart_3329593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329632 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 4, 4]
def baseStart_3329632 : Nat := 118140960795 + 3329632 * 2 ^ 59
def prefixEnd_3329632 : Nat := 4983230072969 + 3 ^ 40 * 3329632 * 2
def baseEnd_3329632 : Nat := 569900539530407344395769

theorem tailTrace_3329632 : CollatzResearch.WordTrace tailWord_3329632 prefixEnd_3329632 569900539530407344395769 := by
  unfold tailWord_3329632
  simp only [CollatzResearch.WordTrace]
  refine ⟨60720827936659697358851575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80961103915546263145135433 60720827936659697358851575)
  ·
    refine ⟨91081241904989546038277363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60720827936659697358851575 91081241904989546038277363)
    ·
      refine ⟨136621862857484319057416045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91081241904989546038277363 136621862857484319057416045)
      ·
        refine ⟨51233198571556619646531017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136621862857484319057416045 51233198571556619646531017)
        ·
          refine ⟨38424898928667464734898263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51233198571556619646531017 38424898928667464734898263)
          ·
            refine ⟨57637348393001197102347395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38424898928667464734898263 57637348393001197102347395)
            ·
              refine ⟨86456022589501795653521093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57637348393001197102347395 86456022589501795653521093)
              ·
                refine ⟨16210504235531586685035205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86456022589501795653521093 16210504235531586685035205)
                ·
                  refine ⟨3039469544162172503444101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16210504235531586685035205 3039469544162172503444101)
                  ·
                    refine ⟨569900539530407344395769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3039469544162172503444101 569900539530407344395769)
                    ·
                      rfl

theorem cell23_3329632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 4, 4].length) (baseStart_3329632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329632 prefixEnd_3329632 := by exact prefixLift 3329632
  have htrace : WordTrace (prefixWord ++ tailWord_3329632) baseStart_3329632 baseEnd_3329632 := by
    simpa [prefixWord, tailWord_3329632, baseEnd_3329632] using wordTrace_append hprefix tailTrace_3329632
  have hstable : (prefixWord ++ tailWord_3329632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329632).length < 2 ^ (prefixWord ++ tailWord_3329632).sum := by decide
  have hdescent : baseEnd_3329632 < baseStart_3329632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329636 : List Nat := [2, 3, 1, 1, 2, 5, 2, 1, 1, 5]
def baseStart_3329636 : Nat := 118140960795 + 3329636 * 2 ^ 59
def prefixEnd_3329636 : Nat := 4983230072969 + 3 ^ 40 * 3329636 * 2
def baseEnd_3329636 : Nat := 569901224171280005845763

theorem tailTrace_3329636 : CollatzResearch.WordTrace tailWord_3329636 prefixEnd_3329636 569901224171280005845763 := by
  unfold tailWord_3329636
  simp only [CollatzResearch.WordTrace]
  refine ⟨60720900882652451700424381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80961201176869935600565841 60720900882652451700424381)
  ·
    refine ⟨22770337830994669387659143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60720900882652451700424381 22770337830994669387659143)
    ·
      refine ⟨34155506746492004081488715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22770337830994669387659143 34155506746492004081488715)
      ·
        refine ⟨51233260119738006122233073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34155506746492004081488715 51233260119738006122233073)
        ·
          refine ⟨38424945089803504591674805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51233260119738006122233073 38424945089803504591674805)
          ·
            refine ⟨3602338602169078555469513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38424945089803504591674805 3602338602169078555469513)
            ·
              refine ⟨2701753951626808916602135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3602338602169078555469513 2701753951626808916602135)
              ·
                refine ⟨4052630927440213374903203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2701753951626808916602135 4052630927440213374903203)
                ·
                  refine ⟨6078946391160320062354805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052630927440213374903203 6078946391160320062354805)
                  ·
                    refine ⟨569901224171280005845763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6078946391160320062354805 569901224171280005845763)
                    ·
                      rfl

theorem cell23_3329636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_3329636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329636 prefixEnd_3329636 := by exact prefixLift 3329636
  have htrace : WordTrace (prefixWord ++ tailWord_3329636) baseStart_3329636 baseEnd_3329636 := by
    simpa [prefixWord, tailWord_3329636, baseEnd_3329636] using wordTrace_append hprefix tailTrace_3329636
  have hstable : (prefixWord ++ tailWord_3329636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329636).length < 2 ^ (prefixWord ++ tailWord_3329636).sum := by decide
  have hdescent : baseEnd_3329636 < baseStart_3329636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329655 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 7]
def baseStart_3329655 : Nat := 118140960795 + 3329655 * 2 ^ 59
def prefixEnd_3329655 : Nat := 4983230072969 + 3 ^ 40 * 3329655 * 2
def baseEnd_3329655 : Nat := 1709713428646275443199701

theorem tailTrace_3329655 : CollatzResearch.WordTrace tailWord_3329655 prefixEnd_3329655 1709713428646275443199701 := by
  unfold tailWord_3329655
  simp only [CollatzResearch.WordTrace]
  refine ⟨121442494752236069645790419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80961663168157379763860279 121442494752236069645790419)
  ·
    refine ⟨182163742128354104468685629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121442494752236069645790419 182163742128354104468685629)
    ·
      refine ⟨68311403298132789175757111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182163742128354104468685629 68311403298132789175757111)
      ·
        refine ⟨102467104947199183763635667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68311403298132789175757111 102467104947199183763635667)
        ·
          refine ⟨153700657420798775645453501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102467104947199183763635667 153700657420798775645453501)
          ·
            refine ⟨57637746532799540867045063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153700657420798775645453501 57637746532799540867045063)
            ·
              refine ⟨86456619799199311300567595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57637746532799540867045063 86456619799199311300567595)
              ·
                refine ⟨129684929698798966950851393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86456619799199311300567595 129684929698798966950851393)
                ·
                  refine ⟨97263697274099225213138545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129684929698798966950851393 97263697274099225213138545)
                  ·
                    refine ⟨72947772955574418909853909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97263697274099225213138545 72947772955574418909853909)
                    ·
                      refine ⟨1709713428646275443199701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72947772955574418909853909 1709713428646275443199701)
                      ·
                        rfl

theorem cell23_3329655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_3329655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329655 prefixEnd_3329655 := by exact prefixLift 3329655
  have htrace : WordTrace (prefixWord ++ tailWord_3329655) baseStart_3329655 baseEnd_3329655 := by
    simpa [prefixWord, tailWord_3329655, baseEnd_3329655] using wordTrace_append hprefix tailTrace_3329655
  have hstable : (prefixWord ++ tailWord_3329655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329655).length < 2 ^ (prefixWord ++ tailWord_3329655).sum := by decide
  have hdescent : baseEnd_3329655 < baseStart_3329655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329746 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 3, 4, 2]
def baseStart_3329746 : Nat := 118140960795 + 3329746 * 2 ^ 59
def prefixEnd_3329746 : Nat := 4983230072969 + 3 ^ 40 * 3329746 * 2
def baseEnd_3329746 : Nat := 1709760155385834587161783

theorem tailTrace_3329746 : CollatzResearch.WordTrace tailWord_3329746 prefixEnd_3329746 1709760155385834587161783 := by
  unfold tailWord_3329746
  simp only [CollatzResearch.WordTrace]
  refine ⟨30361453448726598046838273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80963875863270928124902061 30361453448726598046838273)
  ·
    refine ⟨22771090086544948535128705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30361453448726598046838273 22771090086544948535128705)
    ·
      refine ⟨17078317564908711401346529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22771090086544948535128705 17078317564908711401346529)
      ·
        refine ⟨12808738173681533551009897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17078317564908711401346529 12808738173681533551009897)
        ·
          refine ⟨9606553630261150163257423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12808738173681533551009897 9606553630261150163257423)
          ·
            refine ⟨14409830445391725244886135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9606553630261150163257423 14409830445391725244886135)
            ·
              refine ⟨21614745668087587867329203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14409830445391725244886135 21614745668087587867329203)
              ·
                refine ⟨32422118502131381800993805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21614745668087587867329203 32422118502131381800993805)
                ·
                  refine ⟨12158294438299268175372677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32422118502131381800993805 12158294438299268175372677)
                  ·
                    refine ⟨2279680207181112782882377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12158294438299268175372677 2279680207181112782882377)
                    ·
                      refine ⟨1709760155385834587161783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2279680207181112782882377 1709760155385834587161783)
                      ·
                        rfl

theorem cell23_3329746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_3329746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329746 prefixEnd_3329746 := by exact prefixLift 3329746
  have htrace : WordTrace (prefixWord ++ tailWord_3329746) baseStart_3329746 baseEnd_3329746 := by
    simpa [prefixWord, tailWord_3329746, baseEnd_3329746] using wordTrace_append hprefix tailTrace_3329746
  have hstable : (prefixWord ++ tailWord_3329746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329746).length < 2 ^ (prefixWord ++ tailWord_3329746).sum := by decide
  have hdescent : baseEnd_3329746 < baseStart_3329746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329780 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_3329780 : Nat := 118140960795 + 3329780 * 2 ^ 59
def prefixEnd_3329780 : Nat := 4983230072969 + 3 ^ 40 * 3329780 * 2
def baseEnd_3329780 : Nat := 1709777613728087454136627

theorem tailTrace_3329780 : CollatzResearch.WordTrace tailWord_3329780 prefixEnd_3329780 1709777613728087454136627 := by
  unfold tailWord_3329780
  simp only [CollatzResearch.WordTrace]
  refine ⟨60723526938391607997045397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80964702584522143996060529 60723526938391607997045397)
  ·
    refine ⟨2846415325237106624861503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60723526938391607997045397 2846415325237106624861503)
    ·
      refine ⟨4269622987855659937292255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2846415325237106624861503 4269622987855659937292255)
      ·
        refine ⟨6404434481783489905938383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4269622987855659937292255 6404434481783489905938383)
        ·
          refine ⟨9606651722675234858907575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6404434481783489905938383 9606651722675234858907575)
          ·
            refine ⟨14409977584012852288361363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9606651722675234858907575 14409977584012852288361363)
            ·
              refine ⟨21614966376019278432542045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14409977584012852288361363 21614966376019278432542045)
              ·
                refine ⟨8105612391007229412203267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21614966376019278432542045 8105612391007229412203267)
                ·
                  refine ⟨12158418586510844118304901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8105612391007229412203267 12158418586510844118304901)
                  ·
                    refine ⟨2279703484970783272182169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12158418586510844118304901 2279703484970783272182169)
                    ·
                      refine ⟨1709777613728087454136627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2279703484970783272182169 1709777613728087454136627)
                      ·
                        rfl

theorem cell23_3329780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_3329780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329780 prefixEnd_3329780 := by exact prefixLift 3329780
  have htrace : WordTrace (prefixWord ++ tailWord_3329780) baseStart_3329780 baseEnd_3329780 := by
    simpa [prefixWord, tailWord_3329780, baseEnd_3329780] using wordTrace_append hprefix tailTrace_3329780
  have hstable : (prefixWord ++ tailWord_3329780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329780).length < 2 ^ (prefixWord ++ tailWord_3329780).sum := by decide
  have hdescent : baseEnd_3329780 < baseStart_3329780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329819 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 3, 6, 2]
def baseStart_3329819 : Nat := 118140960795 + 3329819 * 2 ^ 59
def prefixEnd_3329819 : Nat := 4983230072969 + 3 ^ 40 * 3329819 * 2
def baseEnd_3329819 : Nat := 1709797639473612801548947

theorem tailTrace_3329819 : CollatzResearch.WordTrace tailWord_3329819 prefixEnd_3329819 1709797639473612801548947 := by
  unfold tailWord_3329819
  simp only [CollatzResearch.WordTrace]
  refine ⟨121448476323641925654760511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80965650882427950436507007 121448476323641925654760511)
  ·
    refine ⟨182172714485462888482140767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121448476323641925654760511 182172714485462888482140767)
    ·
      refine ⟨273259071728194332723211151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182172714485462888482140767 273259071728194332723211151)
      ·
        refine ⟨409888607592291499084816727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273259071728194332723211151 409888607592291499084816727)
        ·
          refine ⟨614832911388437248627225091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409888607592291499084816727 614832911388437248627225091)
          ·
            refine ⟨922249367082655872940837637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614832911388437248627225091 922249367082655872940837637)
            ·
              refine ⟨172921756327997976176407057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 922249367082655872940837637 172921756327997976176407057)
              ·
                refine ⟨129691317245998482132305293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172921756327997976176407057 129691317245998482132305293)
                ·
                  refine ⟨48634243967249430799614485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129691317245998482132305293 48634243967249430799614485)
                  ·
                    refine ⟨2279730185964817068731929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48634243967249430799614485 2279730185964817068731929)
                    ·
                      refine ⟨1709797639473612801548947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2279730185964817068731929 1709797639473612801548947)
                      ·
                        rfl

theorem cell23_3329819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 6, 2].length) (baseStart_3329819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329819 prefixEnd_3329819 := by exact prefixLift 3329819
  have htrace : WordTrace (prefixWord ++ tailWord_3329819) baseStart_3329819 baseEnd_3329819 := by
    simpa [prefixWord, tailWord_3329819, baseEnd_3329819] using wordTrace_append hprefix tailTrace_3329819
  have hstable : (prefixWord ++ tailWord_3329819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329819).length < 2 ^ (prefixWord ++ tailWord_3329819).sum := by decide
  have hdescent : baseEnd_3329819 < baseStart_3329819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329836 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 2, 4, 2]
def baseStart_3329836 : Nat := 118140960795 + 3329836 * 2 ^ 59
def prefixEnd_3329836 : Nat := 4983230072969 + 3 ^ 40 * 3329836 * 2
def baseEnd_3329836 : Nat := 1709806368644739235036369

theorem tailTrace_3329836 : CollatzResearch.WordTrace tailWord_3329836 prefixEnd_3329836 1709806368644739235036369 := by
  unfold tailWord_3329836
  simp only [CollatzResearch.WordTrace]
  refine ⟨60724548182290168779064681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80966064243053558372086241 60724548182290168779064681)
  ·
    refine ⟨45543411136717626584298511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60724548182290168779064681 45543411136717626584298511)
    ·
      refine ⟨68315116705076439876447767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45543411136717626584298511 68315116705076439876447767)
      ·
        refine ⟨102472675057614659814671651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68315116705076439876447767 102472675057614659814671651)
        ·
          refine ⟨153709012586421989722007477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102472675057614659814671651 153709012586421989722007477)
          ·
            refine ⟨14410219929977061536438201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153709012586421989722007477 14410219929977061536438201)
            ·
              refine ⟨10807664947482796152328651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14410219929977061536438201 10807664947482796152328651)
              ·
                refine ⟨16211497421224194228492977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10807664947482796152328651 16211497421224194228492977)
                ·
                  refine ⟨12158623065918145671369733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16211497421224194228492977 12158623065918145671369733)
                  ·
                    refine ⟨2279741824859652313381825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12158623065918145671369733 2279741824859652313381825)
                    ·
                      refine ⟨1709806368644739235036369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2279741824859652313381825 1709806368644739235036369)
                      ·
                        rfl

theorem cell23_3329836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 4, 2].length) (baseStart_3329836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329836 prefixEnd_3329836 := by exact prefixLift 3329836
  have htrace : WordTrace (prefixWord ++ tailWord_3329836) baseStart_3329836 baseEnd_3329836 := by
    simpa [prefixWord, tailWord_3329836, baseEnd_3329836] using wordTrace_append hprefix tailTrace_3329836
  have hstable : (prefixWord ++ tailWord_3329836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329836).length < 2 ^ (prefixWord ++ tailWord_3329836).sum := by decide
  have hdescent : baseEnd_3329836 < baseStart_3329836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329839 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 3]
def baseStart_3329839 : Nat := 118140960795 + 3329839 * 2 ^ 59
def prefixEnd_3329839 : Nat := 4983230072969 + 3 ^ 40 * 3329839 * 2
def baseEnd_3329839 : Nat := 1709807909086702723298855

theorem tailTrace_3329839 : CollatzResearch.WordTrace tailWord_3329839 prefixEnd_3329839 1709807909086702723298855 := by
  unfold tailWord_3329839
  simp only [CollatzResearch.WordTrace]
  refine ⟨121449205783569469070488571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80966137189046312713659047 121449205783569469070488571)
  ·
    refine ⟨182173808675354203605732857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121449205783569469070488571 182173808675354203605732857)
    ·
      refine ⟨136630356506515652704299643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182173808675354203605732857 136630356506515652704299643)
      ·
        refine ⟨204945534759773479056449465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136630356506515652704299643 204945534759773479056449465)
        ·
          refine ⟨153709151069830109292337099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204945534759773479056449465 153709151069830109292337099)
          ·
            refine ⟨230563726604745163938505649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153709151069830109292337099 230563726604745163938505649)
            ·
              refine ⟨172922794953558872953879237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230563726604745163938505649 172922794953558872953879237)
              ·
                refine ⟨32423024053792288678852357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172922794953558872953879237 32423024053792288678852357)
                ·
                  refine ⟨6079317010086054127284817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32423024053792288678852357 6079317010086054127284817)
                  ·
                    refine ⟨4559487757564540595463613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6079317010086054127284817 4559487757564540595463613)
                    ·
                      refine ⟨1709807909086702723298855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4559487757564540595463613 1709807909086702723298855)
                      ·
                        rfl

theorem cell23_3329839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 3].length) (baseStart_3329839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329839 prefixEnd_3329839 := by exact prefixLift 3329839
  have htrace : WordTrace (prefixWord ++ tailWord_3329839) baseStart_3329839 baseEnd_3329839 := by
    simpa [prefixWord, tailWord_3329839, baseEnd_3329839] using wordTrace_append hprefix tailTrace_3329839
  have hstable : (prefixWord ++ tailWord_3329839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329839).length < 2 ^ (prefixWord ++ tailWord_3329839).sum := by decide
  have hdescent : baseEnd_3329839 < baseStart_3329839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329863 : List Nat := [1, 1, 4, 1, 2, 1, 5, 3, 1, 4]
def baseStart_3329863 : Nat := 118140960795 + 3329863 * 2 ^ 59
def prefixEnd_3329863 : Nat := 4983230072969 + 3 ^ 40 * 3329863 * 2
def baseEnd_3329863 : Nat := 569940077540803543132915

theorem tailTrace_3329863 : CollatzResearch.WordTrace tailWord_3329863 prefixEnd_3329863 569940077540803543132915 := by
  unfold tailWord_3329863
  simp only [CollatzResearch.WordTrace]
  refine ⟨121450081135482521169362243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80966720756988347446241495 121450081135482521169362243)
  ·
    refine ⟨182175121703223781754043365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121450081135482521169362243 182175121703223781754043365)
    ·
      refine ⟨34157835319354459078883131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182175121703223781754043365 34157835319354459078883131)
      ·
        refine ⟨51236752979031688618324697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34157835319354459078883131 51236752979031688618324697)
        ·
          refine ⟨38427564734273766463743523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51236752979031688618324697 38427564734273766463743523)
          ·
            refine ⟨57641347101410649695615285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38427564734273766463743523 57641347101410649695615285)
            ·
              refine ⟨5403876290757248408963933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57641347101410649695615285 5403876290757248408963933)
              ·
                refine ⟨2026453609033968153361475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5403876290757248408963933 2026453609033968153361475)
                ·
                  refine ⟨3039680413550952230042213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026453609033968153361475 3039680413550952230042213)
                  ·
                    refine ⟨569940077540803543132915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3039680413550952230042213 569940077540803543132915)
                    ·
                      rfl

theorem cell23_3329863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_3329863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329863 prefixEnd_3329863 := by exact prefixLift 3329863
  have htrace : WordTrace (prefixWord ++ tailWord_3329863) baseStart_3329863 baseEnd_3329863 := by
    simpa [prefixWord, tailWord_3329863, baseEnd_3329863] using wordTrace_append hprefix tailTrace_3329863
  have hstable : (prefixWord ++ tailWord_3329863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329863).length < 2 ^ (prefixWord ++ tailWord_3329863).sum := by decide
  have hdescent : baseEnd_3329863 < baseStart_3329863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329889 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 3, 5]
def baseStart_3329889 : Nat := 118140960795 + 3329889 * 2 ^ 59
def prefixEnd_3329889 : Nat := 4983230072969 + 3 ^ 40 * 3329889 * 2
def baseEnd_3329889 : Nat := 569944527706475842557875

theorem tailTrace_3329889 : CollatzResearch.WordTrace tailWord_3329889 prefixEnd_3329889 569944527706475842557875 := by
  unfold tailWord_3329889
  simp only [CollatzResearch.WordTrace]
  refine ⟨121451029433388327609808721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80967352955592218406539147 121451029433388327609808721)
  ·
    refine ⟨91088272075041245707356541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121451029433388327609808721 91088272075041245707356541)
    ·
      refine ⟨34158102028140467140258703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91088272075041245707356541 34158102028140467140258703)
      ·
        refine ⟨51237153042210700710388055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34158102028140467140258703 51237153042210700710388055)
        ·
          refine ⟨76855729563316051065582083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51237153042210700710388055 76855729563316051065582083)
          ·
            refine ⟨115283594344974076598373125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76855729563316051065582083 115283594344974076598373125)
            ·
              refine ⟨21615673939682639362194961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115283594344974076598373125 21615673939682639362194961)
              ·
                refine ⟨16211755454761979521646221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21615673939682639362194961 16211755454761979521646221)
                ·
                  refine ⟨6079408295535742320617333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16211755454761979521646221 6079408295535742320617333)
                  ·
                    refine ⟨569944527706475842557875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6079408295535742320617333 569944527706475842557875)
                    ·
                      rfl

theorem cell23_3329889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_3329889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329889 prefixEnd_3329889 := by exact prefixLift 3329889
  have htrace : WordTrace (prefixWord ++ tailWord_3329889) baseStart_3329889 baseEnd_3329889 := by
    simpa [prefixWord, tailWord_3329889, baseEnd_3329889] using wordTrace_append hprefix tailTrace_3329889
  have hstable : (prefixWord ++ tailWord_3329889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329889).length < 2 ^ (prefixWord ++ tailWord_3329889).sum := by decide
  have hdescent : baseEnd_3329889 < baseStart_3329889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329913 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 2, 3, 2]
def baseStart_3329913 : Nat := 118140960795 + 3329913 * 2 ^ 59
def prefixEnd_3329913 : Nat := 4983230072969 + 3 ^ 40 * 3329913 * 2
def baseEnd_3329913 : Nat := 1709845906655135433773515

theorem tailTrace_3329913 : CollatzResearch.WordTrace tailWord_3329913 prefixEnd_3329913 1709845906655135433773515 := by
  unfold tailWord_3329913
  simp only [CollatzResearch.WordTrace]
  refine ⟨121451904785301379708682393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80967936523534253139121595 121451904785301379708682393)
  ·
    refine ⟨91088928588976034781511795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121451904785301379708682393 91088928588976034781511795)
    ·
      refine ⟨136633392883464052172267693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91088928588976034781511795 136633392883464052172267693)
      ·
        refine ⟨51237522331299019564600385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136633392883464052172267693 51237522331299019564600385)
        ·
          refine ⟨38428141748474264673450289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51237522331299019564600385 38428141748474264673450289)
          ·
            refine ⟨28821106311355698505087717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38428141748474264673450289 28821106311355698505087717)
            ·
              refine ⟨5403957433379193469703947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28821106311355698505087717 5403957433379193469703947)
              ·
                refine ⟨8105936150068790204555921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5403957433379193469703947 8105936150068790204555921)
                ·
                  refine ⟨6079452112551592653416941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8105936150068790204555921 6079452112551592653416941)
                  ·
                    refine ⟨2279794542206847245031353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6079452112551592653416941 2279794542206847245031353)
                    ·
                      refine ⟨1709845906655135433773515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2279794542206847245031353 1709845906655135433773515)
                      ·
                        rfl

theorem cell23_3329913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_3329913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329913 prefixEnd_3329913 := by exact prefixLift 3329913
  have htrace : WordTrace (prefixWord ++ tailWord_3329913) baseStart_3329913 baseEnd_3329913 := by
    simpa [prefixWord, tailWord_3329913, baseEnd_3329913] using wordTrace_append hprefix tailTrace_3329913
  have hstable : (prefixWord ++ tailWord_3329913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329913).length < 2 ^ (prefixWord ++ tailWord_3329913).sum := by decide
  have hdescent : baseEnd_3329913 < baseStart_3329913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329923 : List Nat := [1, 1, 1, 3, 4, 3, 3, 1, 1, 5]
def baseStart_3329923 : Nat := 118140960795 + 3329923 * 2 ^ 59
def prefixEnd_3329923 : Nat := 4983230072969 + 3 ^ 40 * 3329923 * 2
def baseEnd_3329923 : Nat := 569950347153893464882823

theorem tailTrace_3329923 : CollatzResearch.WordTrace tailWord_3329923 prefixEnd_3329923 569950347153893464882823 := by
  unfold tailWord_3329923
  simp only [CollatzResearch.WordTrace]
  refine ⟨121452269515265151416546423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80968179676843434277697615 121452269515265151416546423)
  ·
    refine ⟨182178404272897727124819635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121452269515265151416546423 182178404272897727124819635)
    ·
      refine ⟨273267606409346590687229453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182178404272897727124819635 273267606409346590687229453)
      ·
        refine ⟨102475352403504971507711045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273267606409346590687229453 102475352403504971507711045)
        ·
          refine ⟨19214128575657182157695821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102475352403504971507711045 19214128575657182157695821)
          ·
            refine ⟨7205298215871443309135933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19214128575657182157695821 7205298215871443309135933)
            ·
              refine ⟨2701986830951791240925975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7205298215871443309135933 2701986830951791240925975)
              ·
                refine ⟨4052980246427686861388963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2701986830951791240925975 4052980246427686861388963)
                ·
                  refine ⟨6079470369641530292083445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052980246427686861388963 6079470369641530292083445)
                  ·
                    refine ⟨569950347153893464882823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6079470369641530292083445 569950347153893464882823)
                    ·
                      rfl

theorem cell23_3329923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 1, 5].length) (baseStart_3329923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329923 prefixEnd_3329923 := by exact prefixLift 3329923
  have htrace : WordTrace (prefixWord ++ tailWord_3329923) baseStart_3329923 baseEnd_3329923 := by
    simpa [prefixWord, tailWord_3329923, baseEnd_3329923] using wordTrace_append hprefix tailTrace_3329923
  have hstable : (prefixWord ++ tailWord_3329923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329923).length < 2 ^ (prefixWord ++ tailWord_3329923).sum := by decide
  have hdescent : baseEnd_3329923 < baseStart_3329923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329936 : List Nat := [2, 1, 1, 1, 1, 1, 2, 8, 2, 4]
def baseStart_3329936 : Nat := 118140960795 + 3329936 * 2 ^ 59
def prefixEnd_3329936 : Nat := 4983230072969 + 3 ^ 40 * 3329936 * 2
def baseEnd_3329936 : Nat := 569952572236729614595303

theorem tailTrace_3329936 : CollatzResearch.WordTrace tailWord_3329936 prefixEnd_3329936 569952572236729614595303 := by
  unfold tailWord_3329936
  simp only [CollatzResearch.WordTrace]
  refine ⟨60726371832109027318384831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80968495776145369757846441 60726371832109027318384831)
  ·
    refine ⟨91089557748163540977577247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60726371832109027318384831 91089557748163540977577247)
    ·
      refine ⟨136634336622245311466365871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91089557748163540977577247 136634336622245311466365871)
      ·
        refine ⟨204951504933367967199548807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136634336622245311466365871 204951504933367967199548807)
        ·
          refine ⟨307427257400051950799323211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204951504933367967199548807 307427257400051950799323211)
          ·
            refine ⟨461140886100077926198984817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307427257400051950799323211 461140886100077926198984817)
            ·
              refine ⟨345855664575058444649238613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461140886100077926198984817 345855664575058444649238613)
              ·
                refine ⟨4052996069238966148233265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 345855664575058444649238613 4052996069238966148233265)
                ·
                  refine ⟨3039747051929224611174949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4052996069238966148233265 3039747051929224611174949)
                  ·
                    refine ⟨569952572236729614595303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3039747051929224611174949 569952572236729614595303)
                    ·
                      rfl

theorem cell23_3329936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 2, 4].length) (baseStart_3329936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329936 prefixEnd_3329936 := by exact prefixLift 3329936
  have htrace : WordTrace (prefixWord ++ tailWord_3329936) baseStart_3329936 baseEnd_3329936 := by
    simpa [prefixWord, tailWord_3329936, baseEnd_3329936] using wordTrace_append hprefix tailTrace_3329936
  have hstable : (prefixWord ++ tailWord_3329936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329936).length < 2 ^ (prefixWord ++ tailWord_3329936).sum := by decide
  have hdescent : baseEnd_3329936 < baseStart_3329936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329953 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 1, 6]
def baseStart_3329953 : Nat := 118140960795 + 3329953 * 2 ^ 59
def prefixEnd_3329953 : Nat := 4983230072969 + 3 ^ 40 * 3329953 * 2
def baseEnd_3329953 : Nat := 569955481960438425757777

theorem tailTrace_3329953 : CollatzResearch.WordTrace tailWord_3329953 prefixEnd_3329953 569955481960438425757777 := by
  unfold tailWord_3329953
  simp only [CollatzResearch.WordTrace]
  refine ⟨121453363705156466540138513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80968909136770977693425675 121453363705156466540138513)
  ·
    refine ⟨91090022778867349905103885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121453363705156466540138513 91090022778867349905103885)
    ·
      refine ⟨34158758542075256214413957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91090022778867349905103885 34158758542075256214413957)
      ·
        refine ⟨6404767226639110540202617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34158758542075256214413957 6404767226639110540202617)
        ·
          refine ⟨4803575419979332905151963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6404767226639110540202617 4803575419979332905151963)
          ·
            refine ⟨7205363129968999357727945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4803575419979332905151963 7205363129968999357727945)
            ·
              refine ⟨5404022347476749518295959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7205363129968999357727945 5404022347476749518295959)
              ·
                refine ⟨8106033521215124277443939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5404022347476749518295959 8106033521215124277443939)
                ·
                  refine ⟨12159050281822686416165909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8106033521215124277443939 12159050281822686416165909)
                  ·
                    refine ⟨569955481960438425757777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12159050281822686416165909 569955481960438425757777)
                    ·
                      rfl

theorem cell23_3329953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_3329953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329953 prefixEnd_3329953 := by exact prefixLift 3329953
  have htrace : WordTrace (prefixWord ++ tailWord_3329953) baseStart_3329953 baseEnd_3329953 := by
    simpa [prefixWord, tailWord_3329953, baseEnd_3329953] using wordTrace_append hprefix tailTrace_3329953
  have hstable : (prefixWord ++ tailWord_3329953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329953).length < 2 ^ (prefixWord ++ tailWord_3329953).sum := by decide
  have hdescent : baseEnd_3329953 < baseStart_3329953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329956 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_3329956 : Nat := 118140960795 + 3329956 * 2 ^ 59
def prefixEnd_3329956 : Nat := 4983230072969 + 3 ^ 40 * 3329956 * 2
def baseEnd_3329956 : Nat := 1709867986323278765535817

theorem tailTrace_3329956 : CollatzResearch.WordTrace tailWord_3329956 prefixEnd_3329956 1709867986323278765535817 := by
  unfold tailWord_3329956
  simp only [CollatzResearch.WordTrace]
  refine ⟨60726736562072799026248861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80968982082763732034998481 60726736562072799026248861)
  ·
    refine ⟨22772526210777299634843323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60726736562072799026248861 22772526210777299634843323)
    ·
      refine ⟨34158789316165949452264985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22772526210777299634843323 34158789316165949452264985)
      ·
        refine ⟨25619091987124462089198739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34158789316165949452264985 25619091987124462089198739)
        ·
          refine ⟨38428637980686693133798109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25619091987124462089198739 38428637980686693133798109)
          ·
            refine ⟨14410739242757509925174291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38428637980686693133798109 14410739242757509925174291)
            ·
              refine ⟨21616108864136264887761437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14410739242757509925174291 21616108864136264887761437)
              ·
                refine ⟨8106040824051099332910539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21616108864136264887761437 8106040824051099332910539)
                ·
                  refine ⟨12159061236076648999365809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8106040824051099332910539 12159061236076648999365809)
                  ·
                    refine ⟨9119295927057486749524357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12159061236076648999365809 9119295927057486749524357)
                    ·
                      refine ⟨1709867986323278765535817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9119295927057486749524357 1709867986323278765535817)
                      ·
                        rfl

theorem cell23_3329956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_3329956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329956 prefixEnd_3329956 := by exact prefixLift 3329956
  have htrace : WordTrace (prefixWord ++ tailWord_3329956) baseStart_3329956 baseEnd_3329956 := by
    simpa [prefixWord, tailWord_3329956, baseEnd_3329956] using wordTrace_append hprefix tailTrace_3329956
  have hstable : (prefixWord ++ tailWord_3329956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329956).length < 2 ^ (prefixWord ++ tailWord_3329956).sum := by decide
  have hdescent : baseEnd_3329956 < baseStart_3329956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329976 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 1, 3, 3]
def baseStart_3329976 : Nat := 118140960795 + 3329976 * 2 ^ 59
def prefixEnd_3329976 : Nat := 4983230072969 + 3 ^ 40 * 3329976 * 2
def baseEnd_3329976 : Nat := 1709878255936368687285725

theorem tailTrace_3329976 : CollatzResearch.WordTrace tailWord_3329976 prefixEnd_3329976 1709878255936368687285725 := by
  unfold tailWord_3329976
  simp only [CollatzResearch.WordTrace]
  refine ⟨60727101292036570734112891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80969468389382094312150521 60727101292036570734112891)
  ·
    refine ⟨91090651938054856101169337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60727101292036570734112891 91090651938054856101169337)
    ·
      refine ⟨68317988953541142075877003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91090651938054856101169337 68317988953541142075877003)
      ·
        refine ⟨102476983430311713113815505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68317988953541142075877003 102476983430311713113815505)
        ·
          refine ⟨76857737572733784835361629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102476983430311713113815505 76857737572733784835361629)
          ·
            refine ⟨28821651589775169313260611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76857737572733784835361629 28821651589775169313260611)
            ·
              refine ⟨43232477384662753969890917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28821651589775169313260611 43232477384662753969890917)
              ·
                refine ⟨8106089509624266369354547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43232477384662753969890917 8106089509624266369354547)
                ·
                  refine ⟨12159134264436399554031821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8106089509624266369354547 12159134264436399554031821)
                  ·
                    refine ⟨4559675349163649832761933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12159134264436399554031821 4559675349163649832761933)
                    ·
                      refine ⟨1709878255936368687285725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4559675349163649832761933 1709878255936368687285725)
                      ·
                        rfl

theorem cell23_3329976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_3329976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329976 prefixEnd_3329976 := by exact prefixLift 3329976
  have htrace : WordTrace (prefixWord ++ tailWord_3329976) baseStart_3329976 baseEnd_3329976 := by
    simpa [prefixWord, tailWord_3329976, baseEnd_3329976] using wordTrace_append hprefix tailTrace_3329976
  have hstable : (prefixWord ++ tailWord_3329976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329976).length < 2 ^ (prefixWord ++ tailWord_3329976).sum := by decide
  have hdescent : baseEnd_3329976 < baseStart_3329976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329977 : List Nat := [1, 2, 1, 4, 2, 1, 4, 3, 1, 2, 2]
def baseStart_3329977 : Nat := 118140960795 + 3329977 * 2 ^ 59
def prefixEnd_3329977 : Nat := 4983230072969 + 3 ^ 40 * 3329977 * 2
def baseEnd_3329977 : Nat := 1709878769417023183373221

theorem tailTrace_3329977 : CollatzResearch.WordTrace tailWord_3329977 prefixEnd_3329977 1709878769417023183373221 := by
  unfold tailWord_3329977
  simp only [CollatzResearch.WordTrace]
  refine ⟨121454239057069518639012185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80969492704713012426008123 121454239057069518639012185)
  ·
    refine ⟨91090679292802138979259139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121454239057069518639012185 91090679292802138979259139)
    ·
      refine ⟨136636018939203208468888709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91090679292802138979259139 136636018939203208468888709)
      ·
        refine ⟨25619253551100601587916633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136636018939203208468888709 25619253551100601587916633)
        ·
          refine ⟨19214440163325451190937475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25619253551100601587916633 19214440163325451190937475)
          ·
            refine ⟨28821660244988176786406213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19214440163325451190937475 28821660244988176786406213)
            ·
              refine ⟨5404061295935283147451165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28821660244988176786406213 5404061295935283147451165)
              ·
                refine ⟨2026522985975731180294187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5404061295935283147451165 2026522985975731180294187)
                ·
                  refine ⟨3039784478963596770441281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026522985975731180294187 3039784478963596770441281)
                  ·
                    refine ⟨2279838359222697577830961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3039784478963596770441281 2279838359222697577830961)
                    ·
                      refine ⟨1709878769417023183373221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2279838359222697577830961 1709878769417023183373221)
                      ·
                        rfl

theorem cell23_3329977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_3329977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329977 prefixEnd_3329977 := by exact prefixLift 3329977
  have htrace : WordTrace (prefixWord ++ tailWord_3329977) baseStart_3329977 baseEnd_3329977 := by
    simpa [prefixWord, tailWord_3329977, baseEnd_3329977] using wordTrace_append hprefix tailTrace_3329977
  have hstable : (prefixWord ++ tailWord_3329977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329977).length < 2 ^ (prefixWord ++ tailWord_3329977).sum := by decide
  have hdescent : baseEnd_3329977 < baseStart_3329977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3329989 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 4, 2, 5]
def baseStart_3329989 : Nat := 118140960795 + 3329989 * 2 ^ 59
def prefixEnd_3329989 : Nat := 4983230072969 + 3 ^ 40 * 3329989 * 2
def baseEnd_3329989 : Nat := 1709884931184877136423165

theorem tailTrace_3329989 : CollatzResearch.WordTrace tailWord_3329989 prefixEnd_3329989 1709884931184877136423165 := by
  unfold tailWord_3329989
  simp only [CollatzResearch.WordTrace]
  refine ⟨121454676733026044688449021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80969784488684029792299347 121454676733026044688449021)
  ·
    refine ⟨45545503774884766758168383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121454676733026044688449021 45545503774884766758168383)
    ·
      refine ⟨68318255662327150137252575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45545503774884766758168383 68318255662327150137252575)
      ·
        refine ⟨102477383493490725205878863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68318255662327150137252575 102477383493490725205878863)
        ·
          refine ⟨153716075240236087808818295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102477383493490725205878863 153716075240236087808818295)
          ·
            refine ⟨230574112860354131713227443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153716075240236087808818295 230574112860354131713227443)
            ·
              refine ⟨345861169290531197569841165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230574112860354131713227443 345861169290531197569841165)
              ·
                refine ⟨129697938483949199088690437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345861169290531197569841165 129697938483949199088690437)
                ·
                  refine ⟨24318363465740474829129457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129697938483949199088690437 24318363465740474829129457)
                  ·
                    refine ⟨18238772599305356121847093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24318363465740474829129457 18238772599305356121847093)
                    ·
                      refine ⟨1709884931184877136423165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18238772599305356121847093 1709884931184877136423165)
                      ·
                        rfl

theorem cell23_3329989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_3329989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3329989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3329989 prefixEnd_3329989 := by exact prefixLift 3329989
  have htrace : WordTrace (prefixWord ++ tailWord_3329989) baseStart_3329989 baseEnd_3329989 := by
    simpa [prefixWord, tailWord_3329989, baseEnd_3329989] using wordTrace_append hprefix tailTrace_3329989
  have hstable : (prefixWord ++ tailWord_3329989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3329989).length < 2 ^ (prefixWord ++ tailWord_3329989).sum := by decide
  have hdescent : baseEnd_3329989 < baseStart_3329989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3329989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330010 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3]
def baseStart_3330010 : Nat := 118140960795 + 3330010 * 2 ^ 59
def prefixEnd_3330010 : Nat := 4983230072969 + 3 ^ 40 * 3330010 * 2
def baseEnd_3330010 : Nat := 1709895714278621554260569

theorem tailTrace_3330010 : CollatzResearch.WordTrace tailWord_3330010 prefixEnd_3330010 1709895714278621554260569 := by
  unfold tailWord_3330010
  simp only [CollatzResearch.WordTrace]
  refine ⟨30363860666487491318740871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80970295110633310183308989 30363860666487491318740871)
  ·
    refine ⟨45545790999731236978111307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30363860666487491318740871 45545790999731236978111307)
    ·
      refine ⟨68318686499596855467166961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45545790999731236978111307 68318686499596855467166961)
      ·
        refine ⟨51239014874697641600375221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68318686499596855467166961 51239014874697641600375221)
        ·
          refine ⟨4803657644502903900035177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51239014874697641600375221 4803657644502903900035177)
          ·
            refine ⟨3602743233377177925026383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4803657644502903900035177 3602743233377177925026383)
            ·
              refine ⟨5404114850065766887539575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3602743233377177925026383 5404114850065766887539575)
              ·
                refine ⟨8106172275098650331309363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5404114850065766887539575 8106172275098650331309363)
                ·
                  refine ⟨12159258412647975496964045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8106172275098650331309363 12159258412647975496964045)
                  ·
                    refine ⟨4559721904742990811361517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12159258412647975496964045 4559721904742990811361517)
                    ·
                      refine ⟨1709895714278621554260569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4559721904742990811361517 1709895714278621554260569)
                      ·
                        rfl

theorem cell23_3330010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_3330010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330010 prefixEnd_3330010 := by exact prefixLift 3330010
  have htrace : WordTrace (prefixWord ++ tailWord_3330010) baseStart_3330010 baseEnd_3330010 := by
    simpa [prefixWord, tailWord_3330010, baseEnd_3330010] using wordTrace_append hprefix tailTrace_3330010
  have hstable : (prefixWord ++ tailWord_3330010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330010).length < 2 ^ (prefixWord ++ tailWord_3330010).sum := by decide
  have hdescent : baseEnd_3330010 < baseStart_3330010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330020 : List Nat := [2, 3, 1, 1, 1, 1, 6, 2, 1, 3, 2]
def baseStart_3330020 : Nat := 118140960795 + 3330020 * 2 ^ 59
def prefixEnd_3330020 : Nat := 4983230072969 + 3 ^ 40 * 3330020 * 2
def baseEnd_3330020 : Nat := 1709900849085166515135523

theorem tailTrace_3330020 : CollatzResearch.WordTrace tailWord_3330020 prefixEnd_3330020 1709900849085166515135523 := by
  unfold tailWord_3330020
  simp only [CollatzResearch.WordTrace]
  refine ⟨60727903697956868491413757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80970538263942491321885009 60727903697956868491413757)
  ·
    refine ⟨22772963886733825684280159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60727903697956868491413757 22772963886733825684280159)
    ·
      refine ⟨34159445830100738526420239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22772963886733825684280159 34159445830100738526420239)
      ·
        refine ⟨51239168745151107789630359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34159445830100738526420239 51239168745151107789630359)
        ·
          refine ⟨76858753117726661684445539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51239168745151107789630359 76858753117726661684445539)
          ·
            refine ⟨115288129676589992526668309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76858753117726661684445539 115288129676589992526668309)
            ·
              refine ⟨5404131078590155899687577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115288129676589992526668309 5404131078590155899687577)
              ·
                refine ⟨4053098308942616924765683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5404131078590155899687577 4053098308942616924765683)
                ·
                  refine ⟨6079647463413925387148525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4053098308942616924765683 6079647463413925387148525)
                  ·
                    refine ⟨2279867798780222020180697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6079647463413925387148525 2279867798780222020180697)
                    ·
                      refine ⟨1709900849085166515135523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2279867798780222020180697 1709900849085166515135523)
                      ·
                        rfl

theorem cell23_3330020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_3330020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330020 prefixEnd_3330020 := by exact prefixLift 3330020
  have htrace : WordTrace (prefixWord ++ tailWord_3330020) baseStart_3330020 baseEnd_3330020 := by
    simpa [prefixWord, tailWord_3330020, baseEnd_3330020] using wordTrace_append hprefix tailTrace_3330020
  have hstable : (prefixWord ++ tailWord_3330020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330020).length < 2 ^ (prefixWord ++ tailWord_3330020).sum := by decide
  have hdescent : baseEnd_3330020 < baseStart_3330020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330061 : List Nat := [1, 7, 1, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3330061 : Nat := 118140960795 + 3330061 * 2 ^ 59
def prefixEnd_3330061 : Nat := 4983230072969 + 3 ^ 40 * 3330061 * 2
def baseEnd_3330061 : Nat := 1709921901792000854722835

theorem tailTrace_3330061 : CollatzResearch.WordTrace tailWord_3330061 prefixEnd_3330061 1709921901792000854722835 := by
  unfold tailWord_3330061
  simp only [CollatzResearch.WordTrace]
  refine ⟨121457302788765200985070037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80971535192510133990046691 121457302788765200985070037)
  ·
    refine ⟨2846655534111684398087579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 121457302788765200985070037 2846655534111684398087579)
    ·
      refine ⟨4269983301167526597131369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2846655534111684398087579 4269983301167526597131369)
      ·
        refine ⟨3202487475875644947848527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4269983301167526597131369 3202487475875644947848527)
        ·
          refine ⟨4803731213813467421772791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3202487475875644947848527 4803731213813467421772791)
          ·
            refine ⟨7205596820720201132659187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4803731213813467421772791 7205596820720201132659187)
            ·
              refine ⟨10808395231080301698988781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7205596820720201132659187 10808395231080301698988781)
              ·
                refine ⟨4053148211655113137120793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10808395231080301698988781 4053148211655113137120793)
                ·
                  refine ⟨3039861158741334852840595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4053148211655113137120793 3039861158741334852840595)
                  ·
                    refine ⟨4559791738112002279260893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3039861158741334852840595 4559791738112002279260893)
                    ·
                      refine ⟨1709921901792000854722835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4559791738112002279260893 1709921901792000854722835)
                      ·
                        rfl

theorem cell23_3330061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3330061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330061 prefixEnd_3330061 := by exact prefixLift 3330061
  have htrace : WordTrace (prefixWord ++ tailWord_3330061) baseStart_3330061 baseEnd_3330061 := by
    simpa [prefixWord, tailWord_3330061, baseEnd_3330061] using wordTrace_append hprefix tailTrace_3330061
  have hstable : (prefixWord ++ tailWord_3330061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330061).length < 2 ^ (prefixWord ++ tailWord_3330061).sum := by decide
  have hdescent : baseEnd_3330061 < baseStart_3330061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330067 : List Nat := [1, 1, 1, 2, 1, 4, 6, 1, 2, 2, 2]
def baseStart_3330067 : Nat := 118140960795 + 3330067 * 2 ^ 59
def prefixEnd_3330067 : Nat := 4983230072969 + 3 ^ 40 * 3330067 * 2
def baseEnd_3330067 : Nat := 1709924982675927831247807

theorem tailTrace_3330067 : CollatzResearch.WordTrace tailWord_3330067 prefixEnd_3330067 1709924982675927831247807 := by
  unfold tailWord_3330067
  simp only [CollatzResearch.WordTrace]
  refine ⟨121457521626743464009788455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80971681084495642673192303 121457521626743464009788455)
  ·
    refine ⟨182186282440115196014682683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121457521626743464009788455 182186282440115196014682683)
    ·
      refine ⟨273279423660172794022024025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182186282440115196014682683 273279423660172794022024025)
      ·
        refine ⟨204959567745129595516518019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273279423660172794022024025 204959567745129595516518019)
        ·
          refine ⟨307439351617694393274777029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204959567745129595516518019 307439351617694393274777029)
          ·
            refine ⟨57644878428317698739020693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 307439351617694393274777029 57644878428317698739020693)
            ·
              refine ⟨2702103676327392128391595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57644878428317698739020693 2702103676327392128391595)
              ·
                refine ⟨4053155514491088192587393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2702103676327392128391595 4053155514491088192587393)
                ·
                  refine ⟨3039866635868316144440545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4053155514491088192587393 3039866635868316144440545)
                  ·
                    refine ⟨2279899976901237108330409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3039866635868316144440545 2279899976901237108330409)
                    ·
                      refine ⟨1709924982675927831247807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2279899976901237108330409 1709924982675927831247807)
                      ·
                        rfl

theorem cell23_3330067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 2, 2, 2].length) (baseStart_3330067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330067 prefixEnd_3330067 := by exact prefixLift 3330067
  have htrace : WordTrace (prefixWord ++ tailWord_3330067) baseStart_3330067 baseEnd_3330067 := by
    simpa [prefixWord, tailWord_3330067, baseEnd_3330067] using wordTrace_append hprefix tailTrace_3330067
  have hstable : (prefixWord ++ tailWord_3330067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330067).length < 2 ^ (prefixWord ++ tailWord_3330067).sum := by decide
  have hdescent : baseEnd_3330067 < baseStart_3330067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330096 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 5]
def baseStart_3330096 : Nat := 118140960795 + 3330096 * 2 ^ 59
def prefixEnd_3330096 : Nat := 4983230072969 + 3 ^ 40 * 3330096 * 2
def baseEnd_3330096 : Nat := 1709939873614908217785173

theorem tailTrace_3330096 : CollatzResearch.WordTrace tailWord_3330096 prefixEnd_3330096 1709939873614908217785173 := by
  unfold tailWord_3330096
  simp only [CollatzResearch.WordTrace]
  refine ⟨60729289671819200981297071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80972386229092267975062761 60729289671819200981297071)
  ·
    refine ⟨91093934507728801471945607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60729289671819200981297071 91093934507728801471945607)
    ·
      refine ⟨136640901761593202207918411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91093934507728801471945607 136640901761593202207918411)
      ·
        refine ⟨204961352642389803311877617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136640901761593202207918411 204961352642389803311877617)
        ·
          refine ⟨153721014481792352483908213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204961352642389803311877617 153721014481792352483908213)
          ·
            refine ⟨14411345107668033045366395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153721014481792352483908213 14411345107668033045366395)
            ·
              refine ⟨21617017661502049568049593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14411345107668033045366395 21617017661502049568049593)
              ·
                refine ⟨16212763246126537176037195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21617017661502049568049593 16212763246126537176037195)
                ·
                  refine ⟨24319144869189805764055793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16212763246126537176037195 24319144869189805764055793)
                  ·
                    refine ⟨18239358651892354323041845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24319144869189805764055793 18239358651892354323041845)
                    ·
                      refine ⟨1709939873614908217785173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18239358651892354323041845 1709939873614908217785173)
                      ·
                        rfl

theorem cell23_3330096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_3330096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330096 prefixEnd_3330096 := by exact prefixLift 3330096
  have htrace : WordTrace (prefixWord ++ tailWord_3330096) baseStart_3330096 baseEnd_3330096 := by
    simpa [prefixWord, tailWord_3330096, baseEnd_3330096] using wordTrace_append hprefix tailTrace_3330096
  have hstable : (prefixWord ++ tailWord_3330096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330096).length < 2 ^ (prefixWord ++ tailWord_3330096).sum := by decide
  have hdescent : baseEnd_3330096 < baseStart_3330096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330106 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4]
def baseStart_3330106 : Nat := 118140960795 + 3330106 * 2 ^ 59
def prefixEnd_3330106 : Nat := 4983230072969 + 3 ^ 40 * 3330106 * 2
def baseEnd_3330106 : Nat := 1709945008421453178660127

theorem tailTrace_3330106 : CollatzResearch.WordTrace tailWord_3330106 prefixEnd_3330106 1709945008421453178660127 := by
  unfold tailWord_3330106
  simp only [CollatzResearch.WordTrace]
  refine ⟨30364736018400543417614543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80972629382401449113638781 30364736018400543417614543)
  ·
    refine ⟨45547104027600815126421815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30364736018400543417614543 45547104027600815126421815)
    ·
      refine ⟨68320656041401222689632723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45547104027600815126421815 68320656041401222689632723)
      ·
        refine ⟨102480984062101834034449085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68320656041401222689632723 102480984062101834034449085)
        ·
          refine ⟨38430369023288187762918407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102480984062101834034449085 38430369023288187762918407)
          ·
            refine ⟨57645553534932281644377611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38430369023288187762918407 57645553534932281644377611)
            ·
              refine ⟨86468330302398422466566417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57645553534932281644377611 86468330302398422466566417)
              ·
                refine ⟨64851247726798816849924813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86468330302398422466566417 64851247726798816849924813)
                ·
                  refine ⟨24319217897549556318721805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64851247726798816849924813 24319217897549556318721805)
                  ·
                    refine ⟨9119706711581083619520677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24319217897549556318721805 9119706711581083619520677)
                    ·
                      refine ⟨1709945008421453178660127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9119706711581083619520677 1709945008421453178660127)
                      ·
                        rfl

theorem cell23_3330106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_3330106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330106 prefixEnd_3330106 := by exact prefixLift 3330106
  have htrace : WordTrace (prefixWord ++ tailWord_3330106) baseStart_3330106 baseEnd_3330106 := by
    simpa [prefixWord, tailWord_3330106, baseEnd_3330106] using wordTrace_append hprefix tailTrace_3330106
  have hstable : (prefixWord ++ tailWord_3330106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330106).length < 2 ^ (prefixWord ++ tailWord_3330106).sum := by decide
  have hdescent : baseEnd_3330106 < baseStart_3330106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330113 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3330113 : Nat := 118140960795 + 3330113 * 2 ^ 59
def prefixEnd_3330113 : Nat := 4983230072969 + 3 ^ 40 * 3330113 * 2
def baseEnd_3330113 : Nat := 1709948602786034651272595

theorem tailTrace_3330113 : CollatzResearch.WordTrace tailWord_3330113 prefixEnd_3330113 1709948602786034651272595 := by
  unfold tailWord_3330113
  simp only [CollatzResearch.WordTrace]
  refine ⟨121459199384576813865962993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80972799589717875910641995 121459199384576813865962993)
  ·
    refine ⟨91094399538432610399472245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121459199384576813865962993 91094399538432610399472245)
    ·
      refine ⟨8540099956728057224950523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91094399538432610399472245 8540099956728057224950523)
      ·
        refine ⟨12810149935092085837425785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8540099956728057224950523 12810149935092085837425785)
        ·
          refine ⟨9607612451319064378069339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12810149935092085837425785 9607612451319064378069339)
          ·
            refine ⟨14411418676978596567104009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9607612451319064378069339 14411418676978596567104009)
            ·
              refine ⟨10808564007733947425328007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14411418676978596567104009 10808564007733947425328007)
              ·
                refine ⟨16212846011600921137992011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10808564007733947425328007 16212846011600921137992011)
                ·
                  refine ⟨24319269017401381706988017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16212846011600921137992011 24319269017401381706988017)
                  ·
                    refine ⟨18239451763051036280241013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24319269017401381706988017 18239451763051036280241013)
                    ·
                      refine ⟨1709948602786034651272595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18239451763051036280241013 1709948602786034651272595)
                      ·
                        rfl

theorem cell23_3330113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3330113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330113 prefixEnd_3330113 := by exact prefixLift 3330113
  have htrace : WordTrace (prefixWord ++ tailWord_3330113) baseStart_3330113 baseEnd_3330113 := by
    simpa [prefixWord, tailWord_3330113, baseEnd_3330113] using wordTrace_append hprefix tailTrace_3330113
  have hstable : (prefixWord ++ tailWord_3330113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330113).length < 2 ^ (prefixWord ++ tailWord_3330113).sum := by decide
  have hdescent : baseEnd_3330113 < baseStart_3330113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330123 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 2, 4, 2]
def baseStart_3330123 : Nat := 118140960795 + 3330123 * 2 ^ 59
def prefixEnd_3330123 : Nat := 4983230072969 + 3 ^ 40 * 3330123 * 2
def baseEnd_3330123 : Nat := 1709953737592579612147549

theorem tailTrace_3330123 : CollatzResearch.WordTrace tailWord_3330123 prefixEnd_3330123 1709953737592579612147549 := by
  unfold tailWord_3330123
  simp only [CollatzResearch.WordTrace]
  refine ⟨121459564114540585573827023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80973042743027057049218015 121459564114540585573827023)
  ·
    refine ⟨182189346171810878360740535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121459564114540585573827023 182189346171810878360740535)
    ·
      refine ⟨273284019257716317541110803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182189346171810878360740535 273284019257716317541110803)
      ·
        refine ⟨409926028886574476311666205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273284019257716317541110803 409926028886574476311666205)
        ·
          refine ⟨153722260832465428616874827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409926028886574476311666205 153722260832465428616874827)
          ·
            refine ⟨230583391248698142925312241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153722260832465428616874827 230583391248698142925312241)
            ·
              refine ⟨172937543436523607193984181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230583391248698142925312241 172937543436523607193984181)
              ·
                refine ⟨16212894697174088174436017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172937543436523607193984181 16212894697174088174436017)
                ·
                  refine ⟨12159671022880566130827013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16212894697174088174436017 12159671022880566130827013)
                  ·
                    refine ⟨2279938316790106149530065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12159671022880566130827013 2279938316790106149530065)
                    ·
                      refine ⟨1709953737592579612147549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2279938316790106149530065 1709953737592579612147549)
                      ·
                        rfl

theorem cell23_3330123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 4, 2].length) (baseStart_3330123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330123 prefixEnd_3330123 := by exact prefixLift 3330123
  have htrace : WordTrace (prefixWord ++ tailWord_3330123) baseStart_3330123 baseEnd_3330123 := by
    simpa [prefixWord, tailWord_3330123, baseEnd_3330123] using wordTrace_append hprefix tailTrace_3330123
  have hstable : (prefixWord ++ tailWord_3330123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330123).length < 2 ^ (prefixWord ++ tailWord_3330123).sum := by decide
  have hdescent : baseEnd_3330123 < baseStart_3330123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330133 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 5, 4]
def baseStart_3330133 : Nat := 118140960795 + 3330133 * 2 ^ 59
def prefixEnd_3330133 : Nat := 4983230072969 + 3 ^ 40 * 3330133 * 2
def baseEnd_3330133 : Nat := 569986290799708191007501

theorem tailTrace_3330133 : CollatzResearch.WordTrace tailWord_3330133 prefixEnd_3330133 569986290799708191007501 := by
  unfold tailWord_3330133
  simp only [CollatzResearch.WordTrace]
  refine ⟨121459928844504357281691053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80973285896336238187794035 121459928844504357281691053)
  ·
    refine ⟨45547473316689133980634145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121459928844504357281691053 45547473316689133980634145)
    ·
      refine ⟨34160604987516850485475609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45547473316689133980634145 34160604987516850485475609)
      ·
        refine ⟨25620453740637637864106707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34160604987516850485475609 25620453740637637864106707)
        ·
          refine ⟨38430680610956456796160061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25620453740637637864106707 38430680610956456796160061)
          ·
            refine ⟨14411505229108671298560023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38430680610956456796160061 14411505229108671298560023)
            ·
              refine ⟨21617257843663006947840035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14411505229108671298560023 21617257843663006947840035)
              ·
                refine ⟨32425886765494510421760053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21617257843663006947840035 32425886765494510421760053)
                ·
                  refine ⟨3039926884265110352040005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32425886765494510421760053 3039926884265110352040005)
                  ·
                    refine ⟨569986290799708191007501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3039926884265110352040005 569986290799708191007501)
                    ·
                      rfl

theorem cell23_3330133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_3330133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330133 prefixEnd_3330133 := by exact prefixLift 3330133
  have htrace : WordTrace (prefixWord ++ tailWord_3330133) baseStart_3330133 baseEnd_3330133 := by
    simpa [prefixWord, tailWord_3330133, baseEnd_3330133] using wordTrace_append hprefix tailTrace_3330133
  have hstable : (prefixWord ++ tailWord_3330133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330133).length < 2 ^ (prefixWord ++ tailWord_3330133).sum := by decide
  have hdescent : baseEnd_3330133 < baseStart_3330133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330140 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_3330140 : Nat := 118140960795 + 3330140 * 2 ^ 59
def prefixEnd_3330140 : Nat := 4983230072969 + 3 ^ 40 * 3330140 * 2
def baseEnd_3330140 : Nat := 1709962466763706045634971

theorem tailTrace_3330140 : CollatzResearch.WordTrace tailWord_3330140 prefixEnd_3330140 1709962466763706045634971 := by
  unfold tailWord_3330140
  simp only [CollatzResearch.WordTrace]
  refine ⟨60730092077739498738597937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80973456103652664984797249 60730092077739498738597937)
  ·
    refine ⟨45547569058304624053948453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60730092077739498738597937 45547569058304624053948453)
    ·
      refine ⟨8540169198432117010115335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45547569058304624053948453 8540169198432117010115335)
      ·
        refine ⟨12810253797648175515173003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8540169198432117010115335 12810253797648175515173003)
        ·
          refine ⟨19215380696472263272759505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12810253797648175515173003 19215380696472263272759505)
          ·
            refine ⟨14411535522354197454569629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19215380696472263272759505 14411535522354197454569629)
            ·
              refine ⟨5404325820882824045463611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14411535522354197454569629 5404325820882824045463611)
              ·
                refine ⟨8106488731324236068195417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5404325820882824045463611 8106488731324236068195417)
                ·
                  refine ⟨6079866548493177051146563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8106488731324236068195417 6079866548493177051146563)
                  ·
                    refine ⟨9119799822739765576719845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6079866548493177051146563 9119799822739765576719845)
                    ·
                      refine ⟨1709962466763706045634971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9119799822739765576719845 1709962466763706045634971)
                      ·
                        rfl

theorem cell23_3330140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_3330140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330140 prefixEnd_3330140 := by exact prefixLift 3330140
  have htrace : WordTrace (prefixWord ++ tailWord_3330140) baseStart_3330140 baseEnd_3330140 := by
    simpa [prefixWord, tailWord_3330140, baseEnd_3330140] using wordTrace_append hprefix tailTrace_3330140
  have hstable : (prefixWord ++ tailWord_3330140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330140).length < 2 ^ (prefixWord ++ tailWord_3330140).sum := by decide
  have hdescent : baseEnd_3330140 < baseStart_3330140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330143 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 3]
def baseStart_3330143 : Nat := 118140960795 + 3330143 * 2 ^ 59
def prefixEnd_3330143 : Nat := 4983230072969 + 3 ^ 40 * 3330143 * 2
def baseEnd_3330143 : Nat := 1709964007205669533897457

theorem tailTrace_3330143 : CollatzResearch.WordTrace tailWord_3330143 prefixEnd_3330143 1709964007205669533897457 := by
  unfold tailWord_3330143
  simp only [CollatzResearch.WordTrace]
  refine ⟨121460293574468128989555083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80973529049645419326370055 121460293574468128989555083)
  ·
    refine ⟨182190440361702193484332625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121460293574468128989555083 182190440361702193484332625)
    ·
      refine ⟨136642830271276645113249469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182190440361702193484332625 136642830271276645113249469)
      ·
        refine ⟨51241061351728741917468551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136642830271276645113249469 51241061351728741917468551)
        ·
          refine ⟨76861592027593112876202827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51241061351728741917468551 76861592027593112876202827)
          ·
            refine ⟨115292388041389669314304241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76861592027593112876202827 115292388041389669314304241)
            ·
              refine ⟨86469291031042251985728181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115292388041389669314304241 86469291031042251985728181)
              ·
                refine ⟨8106496034160211123662017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86469291031042251985728181 8106496034160211123662017)
                ·
                  refine ⟨6079872025620158342746513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8106496034160211123662017 6079872025620158342746513)
                  ·
                    refine ⟨4559904019215118757059885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6079872025620158342746513 4559904019215118757059885)
                    ·
                      refine ⟨1709964007205669533897457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4559904019215118757059885 1709964007205669533897457)
                      ·
                        rfl

theorem cell23_3330143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_3330143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330143 prefixEnd_3330143 := by exact prefixLift 3330143
  have htrace : WordTrace (prefixWord ++ tailWord_3330143) baseStart_3330143 baseEnd_3330143 := by
    simpa [prefixWord, tailWord_3330143, baseEnd_3330143] using wordTrace_append hprefix tailTrace_3330143
  have hstable : (prefixWord ++ tailWord_3330143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330143).length < 2 ^ (prefixWord ++ tailWord_3330143).sum := by decide
  have hdescent : baseEnd_3330143 < baseStart_3330143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330180 : List Nat := [2, 3, 2, 1, 2, 1, 5, 1, 6]
def baseStart_3330180 : Nat := 118140960795 + 3330180 * 2 ^ 59
def prefixEnd_3330180 : Nat := 4983230072969 + 3 ^ 40 * 3330180 * 2
def baseEnd_3330180 : Nat := 189998111776653987681643

theorem tailTrace_3330180 : CollatzResearch.WordTrace tailWord_3330180 prefixEnd_3330180 189998111776653987681643 := by
  unfold tailWord_3330180
  simp only [CollatzResearch.WordTrace]
  refine ⟨60730821537667042154325997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80974428716889389539101329 60730821537667042154325997)
  ·
    refine ⟨22774058076625140807872249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60730821537667042154325997 22774058076625140807872249)
    ·
      refine ⟨17080543557468855605904187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22774058076625140807872249 17080543557468855605904187)
      ·
        refine ⟨25620815336203283408856281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17080543557468855605904187 25620815336203283408856281)
        ·
          refine ⟨19215611502152462556642211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25620815336203283408856281 19215611502152462556642211)
          ·
            refine ⟨28823417253228693834963317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19215611502152462556642211 28823417253228693834963317)
            ·
              refine ⟨2702195367490190047027811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28823417253228693834963317 2702195367490190047027811)
              ·
                refine ⟨4053293051235285070541717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2702195367490190047027811 4053293051235285070541717)
                ·
                  refine ⟨189998111776653987681643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4053293051235285070541717 189998111776653987681643)
                  ·
                    rfl

theorem cell23_3330180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_3330180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330180 prefixEnd_3330180 := by exact prefixLift 3330180
  have htrace : WordTrace (prefixWord ++ tailWord_3330180) baseStart_3330180 baseEnd_3330180 := by
    simpa [prefixWord, tailWord_3330180, baseEnd_3330180] using wordTrace_append hprefix tailTrace_3330180
  have hstable : (prefixWord ++ tailWord_3330180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330180).length < 2 ^ (prefixWord ++ tailWord_3330180).sum := by decide
  have hdescent : baseEnd_3330180 < baseStart_3330180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330233 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 1, 1, 5]
def baseStart_3330233 : Nat := 118140960795 + 3330233 * 2 ^ 59
def prefixEnd_3330233 : Nat := 4983230072969 + 3 ^ 40 * 3330233 * 2
def baseEnd_3330233 : Nat := 1710010220464574181772043

theorem tailTrace_3330233 : CollatzResearch.WordTrace tailWord_3330233 prefixEnd_3330233 1710010220464574181772043 := by
  unfold tailWord_3330233
  simp only [CollatzResearch.WordTrace]
  refine ⟨121463576144142074360331353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80975717429428049573554235 121463576144142074360331353)
  ·
    refine ⟨91097682108106555770248515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121463576144142074360331353 91097682108106555770248515)
    ·
      refine ⟨136646523162159833655372773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91097682108106555770248515 136646523162159833655372773)
      ·
        refine ⟨25621223092904968810382395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136646523162159833655372773 25621223092904968810382395)
        ·
          refine ⟨38431834639357453215573593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25621223092904968810382395 38431834639357453215573593)
          ·
            refine ⟨28823875979518089911680195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38431834639357453215573593 28823875979518089911680195)
            ·
              refine ⟨43235813969277134867520293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28823875979518089911680195 43235813969277134867520293)
              ·
                refine ⟨8106715119239462787660055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43235813969277134867520293 8106715119239462787660055)
                ·
                  refine ⟨12160072678859194181490083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8106715119239462787660055 12160072678859194181490083)
                  ·
                    refine ⟨18240109018288791272235125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12160072678859194181490083 18240109018288791272235125)
                    ·
                      refine ⟨1710010220464574181772043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18240109018288791272235125 1710010220464574181772043)
                      ·
                        rfl

theorem cell23_3330233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_3330233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330233 prefixEnd_3330233 := by exact prefixLift 3330233
  have htrace : WordTrace (prefixWord ++ tailWord_3330233) baseStart_3330233 baseEnd_3330233 := by
    simpa [prefixWord, tailWord_3330233, baseEnd_3330233] using wordTrace_append hprefix tailTrace_3330233
  have hstable : (prefixWord ++ tailWord_3330233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330233).length < 2 ^ (prefixWord ++ tailWord_3330233).sum := by decide
  have hdescent : baseEnd_3330233 < baseStart_3330233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330250 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 3, 2, 3]
def baseStart_3330250 : Nat := 118140960795 + 3330250 * 2 ^ 59
def prefixEnd_3330250 : Nat := 4983230072969 + 3 ^ 40 * 3330250 * 2
def baseEnd_3330250 : Nat := 1710018949635700615259465

theorem tailTrace_3330250 : CollatzResearch.WordTrace tailWord_3330250 prefixEnd_3330250 1710018949635700615259465 := by
  unfold tailWord_3330250
  simp only [CollatzResearch.WordTrace]
  refine ⟨30366049046270121565925051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80976130790053657509133469 30366049046270121565925051)
  ·
    refine ⟨45549073569405182348887577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30366049046270121565925051 45549073569405182348887577)
    ·
      refine ⟨34161805177053886761665683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45549073569405182348887577 34161805177053886761665683)
      ·
        refine ⟨51242707765580830142498525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34161805177053886761665683 51242707765580830142498525)
        ·
          refine ⟨19216015412092811303436947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51242707765580830142498525 19216015412092811303436947)
          ·
            refine ⟨28824023118139216955155421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19216015412092811303436947 28824023118139216955155421)
            ·
              refine ⟨10809008669302206358183283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28824023118139216955155421 10809008669302206358183283)
              ·
                refine ⟨16213513003953309537274925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10809008669302206358183283 16213513003953309537274925)
                ·
                  refine ⟨6080067376482491076478097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16213513003953309537274925 6080067376482491076478097)
                  ·
                    refine ⟨4560050532361868307358573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6080067376482491076478097 4560050532361868307358573)
                    ·
                      refine ⟨1710018949635700615259465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4560050532361868307358573 1710018949635700615259465)
                      ·
                        rfl

theorem cell23_3330250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_3330250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330250 prefixEnd_3330250 := by exact prefixLift 3330250
  have htrace : WordTrace (prefixWord ++ tailWord_3330250) baseStart_3330250 baseEnd_3330250 := by
    simpa [prefixWord, tailWord_3330250, baseEnd_3330250] using wordTrace_append hprefix tailTrace_3330250
  have hstable : (prefixWord ++ tailWord_3330250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330250).length < 2 ^ (prefixWord ++ tailWord_3330250).sum := by decide
  have hdescent : baseEnd_3330250 < baseStart_3330250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330275 : List Nat := [1, 1, 1, 8, 2, 1, 2, 2, 1, 1, 3]
def baseStart_3330275 : Nat := 118140960795 + 3330275 * 2 ^ 59
def prefixEnd_3330275 : Nat := 4983230072969 + 3 ^ 40 * 3330275 * 2
def baseEnd_3330275 : Nat := 1710031786652063017446851

theorem tailTrace_3330275 : CollatzResearch.WordTrace tailWord_3330275 prefixEnd_3330275 1710031786652063017446851 := by
  unfold tailWord_3330275
  simp only [CollatzResearch.WordTrace]
  refine ⟨121465108009989915533360279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80976738673326610355573519 121465108009989915533360279)
  ·
    refine ⟨182197662014984873300040419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121465108009989915533360279 182197662014984873300040419)
    ·
      refine ⟨273296493022477309950060629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182197662014984873300040419 273296493022477309950060629)
      ·
        refine ⟨3202693277607155975977273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 273296493022477309950060629 3202693277607155975977273)
        ·
          refine ⟨2402019958205366981982955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3202693277607155975977273 2402019958205366981982955)
          ·
            refine ⟨3603029937308050472974433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2402019958205366981982955 3603029937308050472974433)
            ·
              refine ⟨2702272452981037854730825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3603029937308050472974433 2702272452981037854730825)
              ·
                refine ⟨2026704339735778391048119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2702272452981037854730825 2026704339735778391048119)
                ·
                  refine ⟨3040056509603667586572179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026704339735778391048119 3040056509603667586572179)
                  ·
                    refine ⟨4560084764405501379858269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3040056509603667586572179 4560084764405501379858269)
                    ·
                      refine ⟨1710031786652063017446851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4560084764405501379858269 1710031786652063017446851)
                      ·
                        rfl

theorem cell23_3330275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_3330275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330275 prefixEnd_3330275 := by exact prefixLift 3330275
  have htrace : WordTrace (prefixWord ++ tailWord_3330275) baseStart_3330275 baseEnd_3330275 := by
    simpa [prefixWord, tailWord_3330275, baseEnd_3330275] using wordTrace_append hprefix tailTrace_3330275
  have hstable : (prefixWord ++ tailWord_3330275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330275).length < 2 ^ (prefixWord ++ tailWord_3330275).sum := by decide
  have hdescent : baseEnd_3330275 < baseStart_3330275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330303 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 4]
def baseStart_3330303 : Nat := 118140960795 + 3330303 * 2 ^ 59
def prefixEnd_3330303 : Nat := 4983230072969 + 3 ^ 40 * 3330303 * 2
def baseEnd_3330303 : Nat := 1710046164110388907896721

theorem tailTrace_3330303 : CollatzResearch.WordTrace tailWord_3330303 prefixEnd_3330303 1710046164110388907896721 := by
  unfold tailWord_3330303
  simp only [CollatzResearch.WordTrace]
  refine ⟨121466129253888476315379563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80977419502592317543586375 121466129253888476315379563)
  ·
    refine ⟨182199193880832714473069345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121466129253888476315379563 182199193880832714473069345)
    ·
      refine ⟨136649395410624535854802009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182199193880832714473069345 136649395410624535854802009)
      ·
        refine ⟨102487046557968401891101507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136649395410624535854802009 102487046557968401891101507)
        ·
          refine ⟨153730569836952602836652261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102487046557968401891101507 153730569836952602836652261)
          ·
            refine ⟨28824481844428613031872299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153730569836952602836652261 28824481844428613031872299)
            ·
              refine ⟨43236722766642919547808449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28824481844428613031872299 43236722766642919547808449)
              ·
                refine ⟨32427542074982189660856337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43236722766642919547808449 32427542074982189660856337)
                ·
                  refine ⟨24320656556236642245642253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32427542074982189660856337 24320656556236642245642253)
                  ·
                    refine ⟨9120246208588740842115845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24320656556236642245642253 9120246208588740842115845)
                    ·
                      refine ⟨1710046164110388907896721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9120246208588740842115845 1710046164110388907896721)
                      ·
                        rfl

theorem cell23_3330303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_3330303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330303 prefixEnd_3330303 := by exact prefixLift 3330303
  have htrace : WordTrace (prefixWord ++ tailWord_3330303) baseStart_3330303 baseEnd_3330303 := by
    simpa [prefixWord, tailWord_3330303, baseEnd_3330303] using wordTrace_append hprefix tailTrace_3330303
  have hstable : (prefixWord ++ tailWord_3330303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330303).length < 2 ^ (prefixWord ++ tailWord_3330303).sum := by decide
  have hdescent : baseEnd_3330303 < baseStart_3330303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330307 : List Nat := [1, 1, 1, 3, 2, 3, 2, 4, 1, 3, 2]
def baseStart_3330307 : Nat := 118140960795 + 3330307 * 2 ^ 59
def prefixEnd_3330307 : Nat := 4983230072969 + 3 ^ 40 * 3330307 * 2
def baseEnd_3330307 : Nat := 1710048218033006892246703

theorem tailTrace_3330307 : CollatzResearch.WordTrace tailWord_3330307 prefixEnd_3330307 1710048218033006892246703 := by
  unfold tailWord_3330307
  simp only [CollatzResearch.WordTrace]
  refine ⟨121466275145873984998525175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80977516763915989999016783 121466275145873984998525175)
  ·
    refine ⟨182199412718810977497787763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121466275145873984998525175 182199412718810977497787763)
    ·
      refine ⟨273299119078216466246681645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182199412718810977497787763 273299119078216466246681645)
      ·
        refine ⟨102487169654331174842505617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273299119078216466246681645 102487169654331174842505617)
        ·
          refine ⟨76865377240748381131879213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102487169654331174842505617 76865377240748381131879213)
          ·
            refine ⟨28824516465280642924454705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76865377240748381131879213 28824516465280642924454705)
            ·
              refine ⟨21618387348960482193341029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28824516465280642924454705 21618387348960482193341029)
              ·
                refine ⟨4053447627930090411251443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21618387348960482193341029 4053447627930090411251443)
                ·
                  refine ⟨6080171441895135616877165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4053447627930090411251443 6080171441895135616877165)
                  ·
                    refine ⟨2280064290710675856328937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6080171441895135616877165 2280064290710675856328937)
                    ·
                      refine ⟨1710048218033006892246703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2280064290710675856328937 1710048218033006892246703)
                      ·
                        rfl

theorem cell23_3330307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 3, 2].length) (baseStart_3330307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330307 prefixEnd_3330307 := by exact prefixLift 3330307
  have htrace : WordTrace (prefixWord ++ tailWord_3330307) baseStart_3330307 baseEnd_3330307 := by
    simpa [prefixWord, tailWord_3330307, baseEnd_3330307] using wordTrace_append hprefix tailTrace_3330307
  have hstable : (prefixWord ++ tailWord_3330307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330307).length < 2 ^ (prefixWord ++ tailWord_3330307).sum := by decide
  have hdescent : baseEnd_3330307 < baseStart_3330307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330323 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 5]
def baseStart_3330323 : Nat := 118140960795 + 3330323 * 2 ^ 59
def prefixEnd_3330323 : Nat := 4983230072969 + 3 ^ 40 * 3330323 * 2
def baseEnd_3330323 : Nat := 1710056433723478829646629

theorem tailTrace_3330323 : CollatzResearch.WordTrace tailWord_3330323 prefixEnd_3330323 1710056433723478829646629 := by
  unfold tailWord_3330323
  simp only [CollatzResearch.WordTrace]
  refine ⟨121466858713816019731107623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80977905809210679820738415 121466858713816019731107623)
  ·
    refine ⟨182200288070724029596661435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121466858713816019731107623 182200288070724029596661435)
    ·
      refine ⟨273300432106086044394992153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182200288070724029596661435 273300432106086044394992153)
      ·
        refine ⟨204975324079564533296244115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273300432106086044394992153 204975324079564533296244115)
        ·
          refine ⟨307462986119346799944366173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204975324079564533296244115 307462986119346799944366173)
          ·
            refine ⟨115298619794755049979137315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307462986119346799944366173 115298619794755049979137315)
            ·
              refine ⟨172947929692132574968705973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115298619794755049979137315 172947929692132574968705973)
              ·
                refine ⟨16213868408637428903316185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172947929692132574968705973 16213868408637428903316185)
                ·
                  refine ⟨12160401306478071677487139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16213868408637428903316185 12160401306478071677487139)
                  ·
                    refine ⟨18240601959717107516230709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12160401306478071677487139 18240601959717107516230709)
                    ·
                      refine ⟨1710056433723478829646629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18240601959717107516230709 1710056433723478829646629)
                      ·
                        rfl

theorem cell23_3330323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_3330323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330323 prefixEnd_3330323 := by exact prefixLift 3330323
  have htrace : WordTrace (prefixWord ++ tailWord_3330323) baseStart_3330323 baseEnd_3330323 := by
    simpa [prefixWord, tailWord_3330323, baseEnd_3330323] using wordTrace_append hprefix tailTrace_3330323
  have hstable : (prefixWord ++ tailWord_3330323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330323).length < 2 ^ (prefixWord ++ tailWord_3330323).sum := by decide
  have hdescent : baseEnd_3330323 < baseStart_3330323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330427 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 4]
def baseStart_3330427 : Nat := 118140960795 + 3330427 * 2 ^ 59
def prefixEnd_3330427 : Nat := 4983230072969 + 3 ^ 40 * 3330427 * 2
def baseEnd_3330427 : Nat := 1710109835711546422746151

theorem tailTrace_3330427 : CollatzResearch.WordTrace tailWord_3330427 prefixEnd_3330427 1710109835711546422746151 := by
  unfold tailWord_3330427
  simp only [CollatzResearch.WordTrace]
  refine ⟨121470651905439245492893535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80980434603626163661929023 121470651905439245492893535)
  ·
    refine ⟨182205977858158868239340303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121470651905439245492893535 182205977858158868239340303)
    ·
      refine ⟨273308966787238302359010455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182205977858158868239340303 273308966787238302359010455)
      ·
        refine ⟨409963450180857453538515683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273308966787238302359010455 409963450180857453538515683)
        ·
          refine ⟨614945175271286180307773525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409963450180857453538515683 614945175271286180307773525)
          ·
            refine ⟨7206388772710384925481721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 614945175271286180307773525 7206388772710384925481721)
            ·
              refine ⟨5404791579532788694111291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7206388772710384925481721 5404791579532788694111291)
              ·
                refine ⟨8107187369299183041166937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5404791579532788694111291 8107187369299183041166937)
                ·
                  refine ⟨6080390526974387280875203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8107187369299183041166937 6080390526974387280875203)
                  ·
                    refine ⟨9120585790461580921312805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6080390526974387280875203 9120585790461580921312805)
                    ·
                      refine ⟨1710109835711546422746151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9120585790461580921312805 1710109835711546422746151)
                      ·
                        rfl

theorem cell23_3330427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 4].length) (baseStart_3330427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330427 prefixEnd_3330427 := by exact prefixLift 3330427
  have htrace : WordTrace (prefixWord ++ tailWord_3330427) baseStart_3330427 baseEnd_3330427 := by
    simpa [prefixWord, tailWord_3330427, baseEnd_3330427] using wordTrace_append hprefix tailTrace_3330427
  have hstable : (prefixWord ++ tailWord_3330427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330427).length < 2 ^ (prefixWord ++ tailWord_3330427).sum := by decide
  have hdescent : baseEnd_3330427 < baseStart_3330427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330440 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_3330440 : Nat := 118140960795 + 3330440 * 2 ^ 59
def prefixEnd_3330440 : Nat := 4983230072969 + 3 ^ 40 * 3330440 * 2
def baseEnd_3330440 : Nat := 1710116510960054871883591

theorem tailTrace_3330440 : CollatzResearch.WordTrace tailWord_3330440 prefixEnd_3330440 1710116510960054871883591 := by
  unfold tailWord_3330440
  simp only [CollatzResearch.WordTrace]
  refine ⟨60735563027196074356558387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80980750702928099142077849 60735563027196074356558387)
  ·
    refine ⟨91103344540794111534837581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60735563027196074356558387 91103344540794111534837581)
    ·
      refine ⟨34163754202797791825564093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91103344540794111534837581 34163754202797791825564093)
      ·
        refine ⟨12811407826049171934586535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34163754202797791825564093 12811407826049171934586535)
        ·
          refine ⟨19217111739073757901879803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12811407826049171934586535 19217111739073757901879803)
          ·
            refine ⟨28825667608610636852819705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19217111739073757901879803 28825667608610636852819705)
            ·
              refine ⟨21619250706457977639614779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28825667608610636852819705 21619250706457977639614779)
              ·
                refine ⟨32428876059686966459422169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21619250706457977639614779 32428876059686966459422169)
                ·
                  refine ⟨24321657044765224844566627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32428876059686966459422169 24321657044765224844566627)
                  ·
                    refine ⟨36482485567147837266849941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24321657044765224844566627 36482485567147837266849941)
                    ·
                      refine ⟨1710116510960054871883591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36482485567147837266849941 1710116510960054871883591)
                      ·
                        rfl

theorem cell23_3330440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_3330440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330440 prefixEnd_3330440 := by exact prefixLift 3330440
  have htrace : WordTrace (prefixWord ++ tailWord_3330440) baseStart_3330440 baseEnd_3330440 := by
    simpa [prefixWord, tailWord_3330440, baseEnd_3330440] using wordTrace_append hprefix tailTrace_3330440
  have hstable : (prefixWord ++ tailWord_3330440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330440).length < 2 ^ (prefixWord ++ tailWord_3330440).sum := by decide
  have hdescent : baseEnd_3330440 < baseStart_3330440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330527 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 1, 6]
def baseStart_3330527 : Nat := 118140960795 + 3330527 * 2 ^ 59
def prefixEnd_3330527 : Nat := 4983230072969 + 3 ^ 40 * 3330527 * 2
def baseEnd_3330527 : Nat := 570053727925665343831897

theorem tailTrace_3330527 : CollatzResearch.WordTrace tailWord_3330527 prefixEnd_3330527 570053727925665343831897 := by
  unfold tailWord_3330527
  simp only [CollatzResearch.WordTrace]
  refine ⟨121474299205076962571533835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80982866136717975047689223 121474299205076962571533835)
  ·
    refine ⟨182211448807615443857300753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121474299205076962571533835 182211448807615443857300753)
    ·
      refine ⟨136658586605711582892975565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182211448807615443857300753 136658586605711582892975565)
      ·
        refine ⟨51246969977141843584865837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136658586605711582892975565 51246969977141843584865837)
        ·
          refine ⟨19217613741428191344324689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51246969977141843584865837 19217613741428191344324689)
          ·
            refine ⟨14413210306071143508243517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19217613741428191344324689 14413210306071143508243517)
            ·
              refine ⟨5404953864776678815591319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14413210306071143508243517 5404953864776678815591319)
              ·
                refine ⟨8107430797165018223386979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5404953864776678815591319 8107430797165018223386979)
                ·
                  refine ⟨12161146195747527335080469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8107430797165018223386979 12161146195747527335080469)
                  ·
                    refine ⟨570053727925665343831897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12161146195747527335080469 570053727925665343831897)
                    ·
                      rfl

theorem cell23_3330527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 6].length) (baseStart_3330527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330527 prefixEnd_3330527 := by exact prefixLift 3330527
  have htrace : WordTrace (prefixWord ++ tailWord_3330527) baseStart_3330527 baseEnd_3330527 := by
    simpa [prefixWord, tailWord_3330527, baseEnd_3330527] using wordTrace_append hprefix tailTrace_3330527
  have hstable : (prefixWord ++ tailWord_3330527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330527).length < 2 ^ (prefixWord ++ tailWord_3330527).sum := by decide
  have hdescent : baseEnd_3330527 < baseStart_3330527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330540 : List Nat := [2, 2, 1, 1, 2, 1, 5, 9]
def baseStart_3330540 : Nat := 118140960795 + 3330540 * 2 ^ 59
def prefixEnd_3330540 : Nat := 4983230072969 + 3 ^ 40 * 3330540 * 2
def baseEnd_3330540 : Nat := 63339550334277943727153

theorem tailTrace_3330540 : CollatzResearch.WordTrace tailWord_3330540 prefixEnd_3330540 63339550334277943727153 := by
  unfold tailWord_3330540
  simp only [CollatzResearch.WordTrace]
  refine ⟨60737386677014932895878537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80983182236019910527838049 60737386677014932895878537)
  ·
    refine ⟨45553040007761199671908903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60737386677014932895878537 45553040007761199671908903)
    ·
      refine ⟨68329560011641799507863355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45553040007761199671908903 68329560011641799507863355)
      ·
        refine ⟨102494340017462699261795033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68329560011641799507863355 102494340017462699261795033)
        ·
          refine ⟨76870755013097024446346275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102494340017462699261795033 76870755013097024446346275)
          ·
            refine ⟨115306132519645536669519413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76870755013097024446346275 115306132519645536669519413)
            ·
              refine ⟨10809949923716769062767445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115306132519645536669519413 10809949923716769062767445)
              ·
                refine ⟨63339550334277943727153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10809949923716769062767445 63339550334277943727153)
                ·
                  rfl

theorem cell23_3330540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 9].length) (baseStart_3330540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330540 prefixEnd_3330540 := by exact prefixLift 3330540
  have htrace : WordTrace (prefixWord ++ tailWord_3330540) baseStart_3330540 baseEnd_3330540 := by
    simpa [prefixWord, tailWord_3330540, baseEnd_3330540] using wordTrace_append hprefix tailTrace_3330540
  have hstable : (prefixWord ++ tailWord_3330540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330540).length < 2 ^ (prefixWord ++ tailWord_3330540).sum := by decide
  have hdescent : baseEnd_3330540 < baseStart_3330540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330562 : List Nat := [3, 4, 1, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_3330562 : Nat := 118140960795 + 3330562 * 2 ^ 59
def prefixEnd_3330562 : Nat := 4983230072969 + 3 ^ 40 * 3330562 * 2
def baseEnd_3330562 : Nat := 1710179155599903394558031

theorem tailTrace_3330562 : CollatzResearch.WordTrace tailWord_3330562 prefixEnd_3330562 1710179155599903394558031 := by
  unfold tailWord_3330562
  simp only [CollatzResearch.WordTrace]
  refine ⟨30368893939987540887264485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80983717173300109032705293 30368893939987540887264485)
  ·
    refine ⟨5694167613747663916362091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30368893939987540887264485 5694167613747663916362091)
    ·
      refine ⟨8541251420621495874543137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5694167613747663916362091 8541251420621495874543137)
      ·
        refine ⟨6405938565466121905907353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8541251420621495874543137 6405938565466121905907353)
        ·
          refine ⟨4804453924099591429430515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6405938565466121905907353 4804453924099591429430515)
          ·
            refine ⟨7206680886149387144145773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4804453924099591429430515 7206680886149387144145773)
            ·
              refine ⟨2702505332306020179054665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7206680886149387144145773 2702505332306020179054665)
              ·
                refine ⟨2026878999229515134290999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2702505332306020179054665 2026878999229515134290999)
                ·
                  refine ⟨3040318498844272701436499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026878999229515134290999 3040318498844272701436499)
                  ·
                    refine ⟨4560477748266409052154749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3040318498844272701436499 4560477748266409052154749)
                    ·
                      refine ⟨1710179155599903394558031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4560477748266409052154749 1710179155599903394558031)
                      ·
                        rfl

theorem cell23_3330562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_3330562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330562 prefixEnd_3330562 := by exact prefixLift 3330562
  have htrace : WordTrace (prefixWord ++ tailWord_3330562) baseStart_3330562 baseEnd_3330562 := by
    simpa [prefixWord, tailWord_3330562, baseEnd_3330562] using wordTrace_append hprefix tailTrace_3330562
  have hstable : (prefixWord ++ tailWord_3330562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330562).length < 2 ^ (prefixWord ++ tailWord_3330562).sum := by decide
  have hdescent : baseEnd_3330562 < baseStart_3330562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330605 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3330605 : Nat := 118140960795 + 3330605 * 2 ^ 59
def prefixEnd_3330605 : Nat := 4983230072969 + 3 ^ 40 * 3330605 * 2
def baseEnd_3330605 : Nat := 1710201235268046726320333

theorem tailTrace_3330605 : CollatzResearch.WordTrace tailWord_3330605 prefixEnd_3330605 1710201235268046726320333 := by
  unfold tailWord_3330605
  simp only [CollatzResearch.WordTrace]
  refine ⟨121477144098794381892873269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80984762732529587928582179 121477144098794381892873269)
  ·
    refine ⟨11388482259261973302456869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121477144098794381892873269 11388482259261973302456869)
    ·
      refine ⟨2135340423611619994210663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11388482259261973302456869 2135340423611619994210663)
      ·
        refine ⟨3203010635417429991315995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2135340423611619994210663 3203010635417429991315995)
        ·
          refine ⟨4804515953126144986973993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3203010635417429991315995 4804515953126144986973993)
          ·
            refine ⟨3603386964844608740230495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4804515953126144986973993 3603386964844608740230495)
            ·
              refine ⟨5405080447266913110345743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3603386964844608740230495 5405080447266913110345743)
              ·
                refine ⟨8107620670900369665518615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5405080447266913110345743 8107620670900369665518615)
                ·
                  refine ⟨12161431006350554498277923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8107620670900369665518615 12161431006350554498277923)
                  ·
                    refine ⟨18242146509525831747416885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12161431006350554498277923 18242146509525831747416885)
                    ·
                      refine ⟨1710201235268046726320333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18242146509525831747416885 1710201235268046726320333)
                      ·
                        rfl

theorem cell23_3330605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3330605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330605 prefixEnd_3330605 := by exact prefixLift 3330605
  have htrace : WordTrace (prefixWord ++ tailWord_3330605) baseStart_3330605 baseEnd_3330605 := by
    simpa [prefixWord, tailWord_3330605, baseEnd_3330605] using wordTrace_append hprefix tailTrace_3330605
  have hstable : (prefixWord ++ tailWord_3330605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330605).length < 2 ^ (prefixWord ++ tailWord_3330605).sum := by decide
  have hdescent : baseEnd_3330605 < baseStart_3330605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330617 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 2, 6]
def baseStart_3330617 : Nat := 118140960795 + 3330617 * 2 ^ 59
def prefixEnd_3330617 : Nat := 4983230072969 + 3 ^ 40 * 3330617 * 2
def baseEnd_3330617 : Nat := 570069132345300226456759

theorem tailTrace_3330617 : CollatzResearch.WordTrace tailWord_3330617 prefixEnd_3330617 570069132345300226456759 := by
  unfold tailWord_3330617
  simp only [CollatzResearch.WordTrace]
  refine ⟨121477581774750907942310105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80985054516500605294873403 121477581774750907942310105)
  ·
    refine ⟨91108186331063180956732579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121477581774750907942310105 91108186331063180956732579)
    ·
      refine ⟨136662279496594771435098869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91108186331063180956732579 136662279496594771435098869)
      ·
        refine ⟨12812088702805759822040519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136662279496594771435098869 12812088702805759822040519)
        ·
          refine ⟨19218133054208639733060779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12812088702805759822040519 19218133054208639733060779)
          ·
            refine ⟨28827199581312959599591169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19218133054208639733060779 28827199581312959599591169)
            ·
              refine ⟨21620399685984719699693377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28827199581312959599591169 21620399685984719699693377)
              ·
                refine ⟨16215299764488539774770033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21620399685984719699693377 16215299764488539774770033)
                ·
                  refine ⟨12161474823366404831077525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16215299764488539774770033 12161474823366404831077525)
                  ·
                    refine ⟨570069132345300226456759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12161474823366404831077525 570069132345300226456759)
                    ·
                      rfl

theorem cell23_3330617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 6].length) (baseStart_3330617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330617 prefixEnd_3330617 := by exact prefixLift 3330617
  have htrace : WordTrace (prefixWord ++ tailWord_3330617) baseStart_3330617 baseEnd_3330617 := by
    simpa [prefixWord, tailWord_3330617, baseEnd_3330617] using wordTrace_append hprefix tailTrace_3330617
  have hstable : (prefixWord ++ tailWord_3330617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330617).length < 2 ^ (prefixWord ++ tailWord_3330617).sum := by decide
  have hdescent : baseEnd_3330617 < baseStart_3330617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330641 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 1, 4, 2]
def baseStart_3330641 : Nat := 118140960795 + 3330641 * 2 ^ 59
def prefixEnd_3330641 : Nat := 4983230072969 + 3 ^ 40 * 3330641 * 2
def baseEnd_3330641 : Nat := 1710219720571608585470167

theorem tailTrace_3330641 : CollatzResearch.WordTrace tailWord_3330641 prefixEnd_3330641 1710219720571608585470167 := by
  unfold tailWord_3330641
  simp only [CollatzResearch.WordTrace]
  refine ⟨121478457126663960041183777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80985638084442640027455851 121478457126663960041183777)
  ·
    refine ⟨91108842844997970030887833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121478457126663960041183777 91108842844997970030887833)
    ·
      refine ⟨68331632133748477523165875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91108842844997970030887833 68331632133748477523165875)
      ·
        refine ⟨102497448200622716284748813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68331632133748477523165875 102497448200622716284748813)
        ·
          refine ⟨38436543075233518606780805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102497448200622716284748813 38436543075233518606780805)
          ·
            refine ⟨7206851826606284738771401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38436543075233518606780805 7206851826606284738771401)
            ·
              refine ⟨5405138869954713554078551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7206851826606284738771401 5405138869954713554078551)
              ·
                refine ⟨8107708304932070331117827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5405138869954713554078551 8107708304932070331117827)
                ·
                  refine ⟨12161562457398105496676741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8107708304932070331117827 12161562457398105496676741)
                  ·
                    refine ⟨2280292960762144780626889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12161562457398105496676741 2280292960762144780626889)
                    ·
                      refine ⟨1710219720571608585470167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2280292960762144780626889 1710219720571608585470167)
                      ·
                        rfl

theorem cell23_3330641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 4, 2].length) (baseStart_3330641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330641 prefixEnd_3330641 := by exact prefixLift 3330641
  have htrace : WordTrace (prefixWord ++ tailWord_3330641) baseStart_3330641 baseEnd_3330641 := by
    simpa [prefixWord, tailWord_3330641, baseEnd_3330641] using wordTrace_append hprefix tailTrace_3330641
  have hstable : (prefixWord ++ tailWord_3330641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330641).length < 2 ^ (prefixWord ++ tailWord_3330641).sum := by decide
  have hdescent : baseEnd_3330641 < baseStart_3330641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330647 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 7]
def baseStart_3330647 : Nat := 118140960795 + 3330647 * 2 ^ 59
def prefixEnd_3330647 : Nat := 4983230072969 + 3 ^ 40 * 3330647 * 2
def baseEnd_3330647 : Nat := 190024755717281729110571

theorem tailTrace_3330647 : CollatzResearch.WordTrace tailWord_3330647 prefixEnd_3330647 190024755717281729110571 := by
  unfold tailWord_3330647
  simp only [CollatzResearch.WordTrace]
  refine ⟨121478675964642223065902195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80985783976428148710601463 121478675964642223065902195)
  ·
    refine ⟨182218013946963334598853293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121478675964642223065902195 182218013946963334598853293)
    ·
      refine ⟨68331755230111250474569985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182218013946963334598853293 68331755230111250474569985)
      ·
        refine ⟨51248816422583437855927489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68331755230111250474569985 51248816422583437855927489)
        ·
          refine ⟨38436612316937578391945617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51248816422583437855927489 38436612316937578391945617)
          ·
            refine ⟨28827459237703183793959213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38436612316937578391945617 28827459237703183793959213)
            ·
              refine ⟨10810297214138693922734705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28827459237703183793959213 10810297214138693922734705)
              ·
                refine ⟨8107722910604020442051029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10810297214138693922734705 8107722910604020442051029)
                ·
                  refine ⟨190024755717281729110571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8107722910604020442051029 190024755717281729110571)
                  ·
                    rfl

theorem cell23_3330647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 7].length) (baseStart_3330647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330647 prefixEnd_3330647 := by exact prefixLift 3330647
  have htrace : WordTrace (prefixWord ++ tailWord_3330647) baseStart_3330647 baseEnd_3330647 := by
    simpa [prefixWord, tailWord_3330647, baseEnd_3330647] using wordTrace_append hprefix tailTrace_3330647
  have hstable : (prefixWord ++ tailWord_3330647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330647).length < 2 ^ (prefixWord ++ tailWord_3330647).sum := by decide
  have hdescent : baseEnd_3330647 < baseStart_3330647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330684 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 1, 7, 2]
def baseStart_3330684 : Nat := 118140960795 + 3330684 * 2 ^ 59
def prefixEnd_3330684 : Nat := 4983230072969 + 3 ^ 40 * 3330684 * 2
def baseEnd_3330684 : Nat := 1710241800239751917232469

theorem tailTrace_3330684 : CollatzResearch.WordTrace tailWord_3330684 prefixEnd_3330684 1710241800239751917232469 := by
  unfold tailWord_3330684
  simp only [CollatzResearch.WordTrace]
  refine ⟨60740012732754089192499553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80986683643672118923332737 60740012732754089192499553)
  ·
    refine ⟨45555009549565566894374665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60740012732754089192499553 45555009549565566894374665)
    ·
      refine ⟨34166257162174175170780999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45555009549565566894374665 34166257162174175170780999)
      ·
        refine ⟨51249385743261262756171499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34166257162174175170780999 51249385743261262756171499)
        ·
          refine ⟨76874078614891894134257249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51249385743261262756171499 76874078614891894134257249)
          ·
            refine ⟨57655558961168920600692937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76874078614891894134257249 57655558961168920600692937)
            ·
              refine ⟨43241669220876690450519703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57655558961168920600692937 43241669220876690450519703)
              ·
                refine ⟨64862503831315035675779555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43241669220876690450519703 64862503831315035675779555)
                ·
                  refine ⟨97293755746972553513669333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64862503831315035675779555 97293755746972553513669333)
                  ·
                    refine ⟨2280322400319669222976625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 97293755746972553513669333 2280322400319669222976625)
                    ·
                      refine ⟨1710241800239751917232469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2280322400319669222976625 1710241800239751917232469)
                      ·
                        rfl

theorem cell23_3330684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_3330684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330684 prefixEnd_3330684 := by exact prefixLift 3330684
  have htrace : WordTrace (prefixWord ++ tailWord_3330684) baseStart_3330684 baseEnd_3330684 := by
    simpa [prefixWord, tailWord_3330684, baseEnd_3330684] using wordTrace_append hprefix tailTrace_3330684
  have hstable : (prefixWord ++ tailWord_3330684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330684).length < 2 ^ (prefixWord ++ tailWord_3330684).sum := by decide
  have hdescent : baseEnd_3330684 < baseStart_3330684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330765 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_3330765 : Nat := 118140960795 + 3330765 * 2 ^ 59
def prefixEnd_3330765 : Nat := 4983230072969 + 3 ^ 40 * 3330765 * 2
def baseEnd_3330765 : Nat := 1710283392172766100319597

theorem tailTrace_3330765 : CollatzResearch.WordTrace tailWord_3330765 prefixEnd_3330765 1710283392172766100319597 := by
  unfold tailWord_3330765
  simp only [CollatzResearch.WordTrace]
  refine ⟨121482979778214729218697749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80988653185476486145798499 121482979778214729218697749)
  ·
    refine ⟨5694514677103815432126457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121482979778214729218697749 5694514677103815432126457)
    ·
      refine ⟨4270886007827861574094843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5694514677103815432126457 4270886007827861574094843)
      ·
        refine ⟨6406329011741792361142265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4270886007827861574094843 6406329011741792361142265)
        ·
          refine ⟨4804746758806344270856699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6406329011741792361142265 4804746758806344270856699)
          ·
            refine ⟨7207120138209516406285049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4804746758806344270856699 7207120138209516406285049)
            ·
              refine ⟨5405340103657137304713787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7207120138209516406285049 5405340103657137304713787)
              ·
                refine ⟨8108010155485705957070681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5405340103657137304713787 8108010155485705957070681)
                ·
                  refine ⟨6081007616614279467803011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8108010155485705957070681 6081007616614279467803011)
                  ·
                    refine ⟨9121511424921419201704517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6081007616614279467803011 9121511424921419201704517)
                    ·
                      refine ⟨1710283392172766100319597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9121511424921419201704517 1710283392172766100319597)
                      ·
                        rfl

theorem cell23_3330765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_3330765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330765 prefixEnd_3330765 := by exact prefixLift 3330765
  have htrace : WordTrace (prefixWord ++ tailWord_3330765) baseStart_3330765 baseEnd_3330765 := by
    simpa [prefixWord, tailWord_3330765, baseEnd_3330765] using wordTrace_append hprefix tailTrace_3330765
  have hstable : (prefixWord ++ tailWord_3330765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330765).length < 2 ^ (prefixWord ++ tailWord_3330765).sum := by decide
  have hdescent : baseEnd_3330765 < baseStart_3330765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330792 : List Nat := [2, 1, 4, 1, 4, 2, 2, 2, 1, 4]
def baseStart_3330792 : Nat := 118140960795 + 3330792 * 2 ^ 59
def prefixEnd_3330792 : Nat := 4983230072969 + 3 ^ 40 * 3330792 * 2
def baseEnd_3330792 : Nat := 570099085383479164893991

theorem tailTrace_3330792 : CollatzResearch.WordTrace tailWord_3330792 prefixEnd_3330792 570099085383479164893991 := by
  unfold tailWord_3330792
  simp only [CollatzResearch.WordTrace]
  refine ⟨60741982274558456414965315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80989309699411275219953753 60741982274558456414965315)
  ·
    refine ⟨91112973411837684622447973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60741982274558456414965315 91112973411837684622447973)
    ·
      refine ⟨17083682514719565866708995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91112973411837684622447973 17083682514719565866708995)
      ·
        refine ⟨25625523772079348800063493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17083682514719565866708995 25625523772079348800063493)
        ·
          refine ⟨4804785707264877900011905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25625523772079348800063493 4804785707264877900011905)
          ·
            refine ⟨3603589280448658425008929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4804785707264877900011905 3603589280448658425008929)
            ·
              refine ⟨2702691960336493818756697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3603589280448658425008929 2702691960336493818756697)
              ·
                refine ⟨2027018970252370364067523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2702691960336493818756697 2027018970252370364067523)
                ·
                  refine ⟨3040528455378555546101285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027018970252370364067523 3040528455378555546101285)
                  ·
                    refine ⟨570099085383479164893991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3040528455378555546101285 570099085383479164893991)
                    ·
                      rfl

theorem cell23_3330792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_3330792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330792 prefixEnd_3330792 := by exact prefixLift 3330792
  have htrace : WordTrace (prefixWord ++ tailWord_3330792) baseStart_3330792 baseEnd_3330792 := by
    simpa [prefixWord, tailWord_3330792, baseEnd_3330792] using wordTrace_append hprefix tailTrace_3330792
  have hstable : (prefixWord ++ tailWord_3330792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330792).length < 2 ^ (prefixWord ++ tailWord_3330792).sum := by decide
  have hdescent : baseEnd_3330792 < baseStart_3330792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330844 : List Nat := [2, 2, 3, 1, 1, 4, 10]
def baseStart_3330844 : Nat := 118140960795 + 3330844 * 2 ^ 59
def prefixEnd_3330844 : Nat := 4983230072969 + 3 ^ 40 * 3330844 * 2
def baseEnd_3330844 : Nat := 21115110582030509768293

theorem tailTrace_3330844 : CollatzResearch.WordTrace tailWord_3330844 prefixEnd_3330844 21115110582030509768293 := by
  unfold tailWord_3330844
  simp only [CollatzResearch.WordTrace]
  refine ⟨60742930572464262855411793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80990574096619017140549057 60742930572464262855411793)
  ·
    refine ⟨45557197929348197141558845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60742930572464262855411793 45557197929348197141558845)
    ·
      refine ⟨17083949223505573928084567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45557197929348197141558845 17083949223505573928084567)
      ·
        refine ⟨25625923835258360892126851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17083949223505573928084567 25625923835258360892126851)
        ·
          refine ⟨38438885752887541338190277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25625923835258360892126851 38438885752887541338190277)
          ·
            refine ⟨7207291078666414000910677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38438885752887541338190277 7207291078666414000910677)
            ·
              refine ⟨21115110582030509768293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7207291078666414000910677 21115110582030509768293)
              ·
                rfl

theorem cell23_3330844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 10].length) (baseStart_3330844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330844 prefixEnd_3330844 := by exact prefixLift 3330844
  have htrace : WordTrace (prefixWord ++ tailWord_3330844) baseStart_3330844 baseEnd_3330844 := by
    simpa [prefixWord, tailWord_3330844, baseEnd_3330844] using wordTrace_append hprefix tailTrace_3330844
  have hstable : (prefixWord ++ tailWord_3330844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330844).length < 2 ^ (prefixWord ++ tailWord_3330844).sum := by decide
  have hdescent : baseEnd_3330844 < baseStart_3330844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330848 : List Nat := [2, 1, 1, 5, 1, 2, 3, 2, 2, 4]
def baseStart_3330848 : Nat := 118140960795 + 3330848 * 2 ^ 59
def prefixEnd_3330848 : Nat := 4983230072969 + 3 ^ 40 * 3330848 * 2
def baseEnd_3330848 : Nat := 570108670355696425193905

theorem tailTrace_3330848 : CollatzResearch.WordTrace tailWord_3330848 prefixEnd_3330848 570108670355696425193905 := by
  unfold tailWord_3330848
  simp only [CollatzResearch.WordTrace]
  refine ⟨60743003518457017196984599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80990671357942689595979465 60743003518457017196984599)
  ·
    refine ⟨91114505277685525795476899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60743003518457017196984599 91114505277685525795476899)
    ·
      refine ⟨136671757916528288693215349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91114505277685525795476899 136671757916528288693215349)
      ·
        refine ⟨12812977304674527064988939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136671757916528288693215349 12812977304674527064988939)
        ·
          refine ⟨19219465957011790597483409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12812977304674527064988939 19219465957011790597483409)
          ·
            refine ⟨14414599467758842948112557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19219465957011790597483409 14414599467758842948112557)
            ·
              refine ⟨5405474800409566105542209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14414599467758842948112557 5405474800409566105542209)
              ·
                refine ⟨4054106100307174579156657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5405474800409566105542209 4054106100307174579156657)
                ·
                  refine ⟨3040579575230380934367493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4054106100307174579156657 3040579575230380934367493)
                  ·
                    refine ⟨570108670355696425193905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3040579575230380934367493 570108670355696425193905)
                    ·
                      rfl

theorem cell23_3330848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 2, 4].length) (baseStart_3330848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330848 prefixEnd_3330848 := by exact prefixLift 3330848
  have htrace : WordTrace (prefixWord ++ tailWord_3330848) baseStart_3330848 baseEnd_3330848 := by
    simpa [prefixWord, tailWord_3330848, baseEnd_3330848] using wordTrace_append hprefix tailTrace_3330848
  have hstable : (prefixWord ++ tailWord_3330848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330848).length < 2 ^ (prefixWord ++ tailWord_3330848).sum := by decide
  have hdescent : baseEnd_3330848 < baseStart_3330848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330868 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_3330868 : Nat := 118140960795 + 3330868 * 2 ^ 59
def prefixEnd_3330868 : Nat := 4983230072969 + 3 ^ 40 * 3330868 * 2
def baseEnd_3330868 : Nat := 1710336280680179197331623

theorem tailTrace_3330868 : CollatzResearch.WordTrace tailWord_3330868 prefixEnd_3330868 1710336280680179197331623 := by
  unfold tailWord_3330868
  simp only [CollatzResearch.WordTrace]
  refine ⟨60743368248420788904848629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80991157664561051873131505 60743368248420788904848629)
  ·
    refine ⟨5694690773289448959829559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60743368248420788904848629 5694690773289448959829559)
    ·
      refine ⟨8542036159934173439744339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5694690773289448959829559 8542036159934173439744339)
      ·
        refine ⟨12813054239901260159616509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8542036159934173439744339 12813054239901260159616509)
        ·
          refine ⟨4804895339962972559856191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12813054239901260159616509 4804895339962972559856191)
          ·
            refine ⟨7207343009944458839784287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4804895339962972559856191 7207343009944458839784287)
            ·
              refine ⟨10811014514916688259676431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7207343009944458839784287 10811014514916688259676431)
              ·
                refine ⟨16216521772375032389514647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10811014514916688259676431 16216521772375032389514647)
                ·
                  refine ⟨24324782658562548584271971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16216521772375032389514647 24324782658562548584271971)
                  ·
                    refine ⟨36487173987843822876407957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24324782658562548584271971 36487173987843822876407957)
                    ·
                      refine ⟨1710336280680179197331623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36487173987843822876407957 1710336280680179197331623)
                      ·
                        rfl

theorem cell23_3330868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_3330868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330868 prefixEnd_3330868 := by exact prefixLift 3330868
  have htrace : WordTrace (prefixWord ++ tailWord_3330868) baseStart_3330868 baseEnd_3330868 := by
    simpa [prefixWord, tailWord_3330868, baseEnd_3330868] using wordTrace_append hprefix tailTrace_3330868
  have hstable : (prefixWord ++ tailWord_3330868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330868).length < 2 ^ (prefixWord ++ tailWord_3330868).sum := by decide
  have hdescent : baseEnd_3330868 < baseStart_3330868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330894 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_3330894 : Nat := 118140960795 + 3330894 * 2 ^ 59
def prefixEnd_3330894 : Nat := 4983230072969 + 3 ^ 40 * 3330894 * 2
def baseEnd_3330894 : Nat := 1710349631177196095606503

theorem tailTrace_3330894 : CollatzResearch.WordTrace tailWord_3330894 prefixEnd_3330894 1710349631177196095606503 := by
  unfold tailWord_3330894
  simp only [CollatzResearch.WordTrace]
  refine ⟨15185960599343423031267967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80991789863164922833429157 15185960599343423031267967)
  ·
    refine ⟨22778940899015134546901951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15185960599343423031267967 22778940899015134546901951)
    ·
      refine ⟨34168411348522701820352927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22778940899015134546901951 34168411348522701820352927)
      ·
        refine ⟨51252617022784052730529391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34168411348522701820352927 51252617022784052730529391)
        ·
          refine ⟨76878925534176079095794087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51252617022784052730529391 76878925534176079095794087)
          ·
            refine ⟨115318388301264118643691131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76878925534176079095794087 115318388301264118643691131)
            ·
              refine ⟨172977582451896177965536697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115318388301264118643691131 172977582451896177965536697)
              ·
                refine ⟨129733186838922133474152523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172977582451896177965536697 129733186838922133474152523)
                ·
                  refine ⟨194599780258383200211228785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129733186838922133474152523 194599780258383200211228785)
                  ·
                    refine ⟨145949835193787400158421589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 194599780258383200211228785 145949835193787400158421589)
                    ·
                      refine ⟨1710349631177196095606503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 145949835193787400158421589 1710349631177196095606503)
                      ·
                        rfl

theorem cell23_3330894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_3330894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330894 prefixEnd_3330894 := by exact prefixLift 3330894
  have htrace : WordTrace (prefixWord ++ tailWord_3330894) baseStart_3330894 baseEnd_3330894 := by
    simpa [prefixWord, tailWord_3330894, baseEnd_3330894] using wordTrace_append hprefix tailTrace_3330894
  have hstable : (prefixWord ++ tailWord_3330894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330894).length < 2 ^ (prefixWord ++ tailWord_3330894).sum := by decide
  have hdescent : baseEnd_3330894 < baseStart_3330894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330904 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 4, 6]
def baseStart_3330904 : Nat := 118140960795 + 3330904 * 2 ^ 59
def prefixEnd_3330904 : Nat := 4983230072969 + 3 ^ 40 * 3330904 * 2
def baseEnd_3330904 : Nat := 570118255327913685493819

theorem tailTrace_3330904 : CollatzResearch.WordTrace tailWord_3330904 prefixEnd_3330904 570118255327913685493819 := by
  unfold tailWord_3330904
  simp only [CollatzResearch.WordTrace]
  refine ⟨60744024762355577979003883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80992033016474103972005177 60744024762355577979003883)
  ·
    refine ⟨91116037143533366968505825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60744024762355577979003883 91116037143533366968505825)
    ·
      refine ⟨68337027857650025226379369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91116037143533366968505825 68337027857650025226379369)
      ·
        refine ⟨51252770893237518919784527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68337027857650025226379369 51252770893237518919784527)
        ·
          refine ⟨76879156339856278379676791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51252770893237518919784527 76879156339856278379676791)
          ·
            refine ⟨115318734509784417569515187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76879156339856278379676791 115318734509784417569515187)
            ·
              refine ⟨172978101764676626354272781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115318734509784417569515187 172978101764676626354272781)
              ·
                refine ⟨64866788161753734882852293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172978101764676626354272781 64866788161753734882852293)
                ·
                  refine ⟨12162522780328825290534805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64866788161753734882852293 12162522780328825290534805)
                  ·
                    refine ⟨570118255327913685493819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12162522780328825290534805 570118255327913685493819)
                    ·
                      rfl

theorem cell23_3330904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_3330904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330904 prefixEnd_3330904 := by exact prefixLift 3330904
  have htrace : WordTrace (prefixWord ++ tailWord_3330904) baseStart_3330904 baseEnd_3330904 := by
    simpa [prefixWord, tailWord_3330904, baseEnd_3330904] using wordTrace_append hprefix tailTrace_3330904
  have hstable : (prefixWord ++ tailWord_3330904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330904).length < 2 ^ (prefixWord ++ tailWord_3330904).sum := by decide
  have hdescent : baseEnd_3330904 < baseStart_3330904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330944 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 7]
def baseStart_3330944 : Nat := 118140960795 + 3330944 * 2 ^ 59
def prefixEnd_3330944 : Nat := 4983230072969 + 3 ^ 40 * 3330944 * 2
def baseEnd_3330944 : Nat := 1710375305209920899981273

theorem tailTrace_3330944 : CollatzResearch.WordTrace tailWord_3330944 prefixEnd_3330944 1710375305209920899981273 := by
  unfold tailWord_3330944
  simp only [CollatzResearch.WordTrace]
  refine ⟨60744754222283121394731943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80993005629710828526309257 60744754222283121394731943)
  ·
    refine ⟨91117131333424682092097915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60744754222283121394731943 91117131333424682092097915)
    ·
      refine ⟨136675697000137023138146873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91117131333424682092097915 136675697000137023138146873)
      ·
        refine ⟨102506772750102767353610155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136675697000137023138146873 102506772750102767353610155)
        ·
          refine ⟨153760159125154151030415233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102506772750102767353610155 153760159125154151030415233)
          ·
            refine ⟨115320119343865613272811425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153760159125154151030415233 115320119343865613272811425)
            ·
              refine ⟨86490089507899209954608569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115320119343865613272811425 86490089507899209954608569)
              ·
                refine ⟨64867567130924407465956427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86490089507899209954608569 64867567130924407465956427)
                ·
                  refine ⟨97301350696386611198934641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64867567130924407465956427 97301350696386611198934641)
                  ·
                    refine ⟨72976013022289958399200981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97301350696386611198934641 72976013022289958399200981)
                    ·
                      refine ⟨1710375305209920899981273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72976013022289958399200981 1710375305209920899981273)
                      ·
                        rfl

theorem cell23_3330944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_3330944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330944 prefixEnd_3330944 := by exact prefixLift 3330944
  have htrace : WordTrace (prefixWord ++ tailWord_3330944) baseStart_3330944 baseEnd_3330944 := by
    simpa [prefixWord, tailWord_3330944, baseEnd_3330944] using wordTrace_append hprefix tailTrace_3330944
  have hstable : (prefixWord ++ tailWord_3330944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330944).length < 2 ^ (prefixWord ++ tailWord_3330944).sum := by decide
  have hdescent : baseEnd_3330944 < baseStart_3330944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330961 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 3]
def baseStart_3330961 : Nat := 118140960795 + 3330961 * 2 ^ 59
def prefixEnd_3330961 : Nat := 4983230072969 + 3 ^ 40 * 3330961 * 2
def baseEnd_3330961 : Nat := 1710384034381047333468695

theorem tailTrace_3330961 : CollatzResearch.WordTrace tailWord_3330961 prefixEnd_3330961 1710384034381047333468695 := by
  unfold tailWord_3330961
  simp only [CollatzResearch.WordTrace]
  refine ⟨121490128485504654692832737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80993418990336436461888491 121490128485504654692832737)
  ·
    refine ⟨91117596364128491019624553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121490128485504654692832737 91117596364128491019624553)
    ·
      refine ⟨68338197273096368264718415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91117596364128491019624553 68338197273096368264718415)
      ·
        refine ⟨102507295909644552397077623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68338197273096368264718415 102507295909644552397077623)
        ·
          refine ⟨153760943864466828595616435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102507295909644552397077623 153760943864466828595616435)
          ·
            refine ⟨230641415796700242893424653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153760943864466828595616435 230641415796700242893424653)
            ·
              refine ⟨86490530923762591085034245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230641415796700242893424653 86490530923762591085034245)
              ·
                refine ⟨16216974548205485828443921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86490530923762591085034245 16216974548205485828443921)
                ·
                  refine ⟨12162730911154114371332941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16216974548205485828443921 12162730911154114371332941)
                  ·
                    refine ⟨4561024091682792889249853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12162730911154114371332941 4561024091682792889249853)
                    ·
                      refine ⟨1710384034381047333468695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4561024091682792889249853 1710384034381047333468695)
                      ·
                        rfl

theorem cell23_3330961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_3330961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330961 prefixEnd_3330961 := by exact prefixLift 3330961
  have htrace : WordTrace (prefixWord ++ tailWord_3330961) baseStart_3330961 baseEnd_3330961 := by
    simpa [prefixWord, tailWord_3330961, baseEnd_3330961] using wordTrace_append hprefix tailTrace_3330961
  have hstable : (prefixWord ++ tailWord_3330961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330961).length < 2 ^ (prefixWord ++ tailWord_3330961).sum := by decide
  have hdescent : baseEnd_3330961 < baseStart_3330961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3330978 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_3330978 : Nat := 118140960795 + 3330978 * 2 ^ 59
def prefixEnd_3330978 : Nat := 4983230072969 + 3 ^ 40 * 3330978 * 2
def baseEnd_3330978 : Nat := 1710392763552173766956117

theorem tailTrace_3330978 : CollatzResearch.WordTrace tailWord_3330978 prefixEnd_3330978 1710392763552173766956117 := by
  unfold tailWord_3330978
  simp only [CollatzResearch.WordTrace]
  refine ⟨30372687131610766649050397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80993832350962044397467725 30372687131610766649050397)
  ·
    refine ⟨11389757674354037493393899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30372687131610766649050397 11389757674354037493393899)
    ·
      refine ⟨17084636511531056240090849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11389757674354037493393899 17084636511531056240090849)
      ·
        refine ⟨12813477383648292180068137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17084636511531056240090849 12813477383648292180068137)
        ·
          refine ⟨9610108037736219135051103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12813477383648292180068137 9610108037736219135051103)
          ·
            refine ⟨14415162056604328702576655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9610108037736219135051103 14415162056604328702576655)
            ·
              refine ⟨21622743084906493053864983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14415162056604328702576655 21622743084906493053864983)
              ·
                refine ⟨32434114627359739580797475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21622743084906493053864983 32434114627359739580797475)
                ·
                  refine ⟨48651171941039609371196213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32434114627359739580797475 48651171941039609371196213)
                  ·
                    refine ⟨4561047369472463378549645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48651171941039609371196213 4561047369472463378549645)
                    ·
                      refine ⟨1710392763552173766956117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4561047369472463378549645 1710392763552173766956117)
                      ·
                        rfl

theorem cell23_3330978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_3330978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3330978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3330978 prefixEnd_3330978 := by exact prefixLift 3330978
  have htrace : WordTrace (prefixWord ++ tailWord_3330978) baseStart_3330978 baseEnd_3330978 := by
    simpa [prefixWord, tailWord_3330978, baseEnd_3330978] using wordTrace_append hprefix tailTrace_3330978
  have hstable : (prefixWord ++ tailWord_3330978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3330978).length < 2 ^ (prefixWord ++ tailWord_3330978).sum := by decide
  have hdescent : baseEnd_3330978 < baseStart_3330978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3330978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331071 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 7, 5]
def baseStart_3331071 : Nat := 118140960795 + 3331071 * 2 ^ 59
def prefixEnd_3331071 : Nat := 4983230072969 + 3 ^ 40 * 3331071 * 2
def baseEnd_3331071 : Nat := 570146839084347301031063

theorem tailTrace_3331071 : CollatzResearch.WordTrace tailWord_3331071 prefixEnd_3331071 570146839084347301031063 := by
  unfold tailWord_3331071
  simp only [CollatzResearch.WordTrace]
  refine ⟨121494140515106143479337067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80996093676737428986224711 121494140515106143479337067)
  ·
    refine ⟨182241210772659215219005601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121494140515106143479337067 182241210772659215219005601)
    ·
      refine ⟨136680908079494411414254201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182241210772659215219005601 136680908079494411414254201)
      ·
        refine ⟨102510681059620808560690651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136680908079494411414254201 102510681059620808560690651)
        ·
          refine ⟨153766021589431212841035977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102510681059620808560690651 153766021589431212841035977)
          ·
            refine ⟨115324516192073409630776983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153766021589431212841035977 115324516192073409630776983)
            ·
              refine ⟨172986774288110114446165475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115324516192073409630776983 172986774288110114446165475)
              ·
                refine ⟨259480161432165171669248213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172986774288110114446165475 259480161432165171669248213)
                ·
                  refine ⟨6081566283566371210998005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 259480161432165171669248213 6081566283566371210998005)
                  ·
                    refine ⟨570146839084347301031063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6081566283566371210998005 570146839084347301031063)
                    ·
                      rfl

theorem cell23_3331071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 5].length) (baseStart_3331071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331071 prefixEnd_3331071 := by exact prefixLift 3331071
  have htrace : WordTrace (prefixWord ++ tailWord_3331071) baseStart_3331071 baseEnd_3331071 := by
    simpa [prefixWord, tailWord_3331071, baseEnd_3331071] using wordTrace_append hprefix tailTrace_3331071
  have hstable : (prefixWord ++ tailWord_3331071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331071).length < 2 ^ (prefixWord ++ tailWord_3331071).sum := by decide
  have hdescent : baseEnd_3331071 < baseStart_3331071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331091 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 4]
def baseStart_3331091 : Nat := 118140960795 + 3331091 * 2 ^ 59
def prefixEnd_3331091 : Nat := 4983230072969 + 3 ^ 40 * 3331091 * 2
def baseEnd_3331091 : Nat := 1710450786866131824843097

theorem tailTrace_3331091 : CollatzResearch.WordTrace tailWord_3331091 prefixEnd_3331091 1710450786866131824843097 := by
  unfold tailWord_3331091
  simp only [CollatzResearch.WordTrace]
  refine ⟨121494869975033686895065127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80996579983355791263376751 121494869975033686895065127)
  ·
    refine ⟨182242304962550530342597691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121494869975033686895065127 182242304962550530342597691)
    ·
      refine ⟨273363457443825795513896537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182242304962550530342597691 273363457443825795513896537)
      ·
        refine ⟨205022593082869346635422403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273363457443825795513896537 205022593082869346635422403)
        ·
          refine ⟨307533889624304019953133605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205022593082869346635422403 307533889624304019953133605)
          ·
            refine ⟨57662604304557003741212551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 307533889624304019953133605 57662604304557003741212551)
            ·
              refine ⟨86493906456835505611818827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57662604304557003741212551 86493906456835505611818827)
              ·
                refine ⟨129740859685253258417728241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86493906456835505611818827 129740859685253258417728241)
                ·
                  refine ⟨97305644763939943813296181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129740859685253258417728241 97305644763939943813296181)
                  ·
                    refine ⟨9122404196619369732496517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97305644763939943813296181 9122404196619369732496517)
                    ·
                      refine ⟨1710450786866131824843097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9122404196619369732496517 1710450786866131824843097)
                      ·
                        rfl

theorem cell23_3331091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_3331091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331091 prefixEnd_3331091 := by exact prefixLift 3331091
  have htrace : WordTrace (prefixWord ++ tailWord_3331091) baseStart_3331091 baseEnd_3331091 := by
    simpa [prefixWord, tailWord_3331091, baseEnd_3331091] using wordTrace_append hprefix tailTrace_3331091
  have hstable : (prefixWord ++ tailWord_3331091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331091).length < 2 ^ (prefixWord ++ tailWord_3331091).sum := by decide
  have hdescent : baseEnd_3331091 < baseStart_3331091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331105 : List Nat := [1, 2, 3, 2, 3, 1, 3, 2, 1, 5]
def baseStart_3331105 : Nat := 118140960795 + 3331105 * 2 ^ 59
def prefixEnd_3331105 : Nat := 4983230072969 + 3 ^ 40 * 3331105 * 2
def baseEnd_3331105 : Nat := 570152658531764923356011

theorem tailTrace_3331105 : CollatzResearch.WordTrace tailWord_3331105 prefixEnd_3331105 570152658531764923356011 := by
  unfold tailWord_3331105
  simp only [CollatzResearch.WordTrace]
  refine ⟨121495380596982967286074769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80996920397988644857383179 121495380596982967286074769)
  ·
    refine ⟨91121535447737225464556077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121495380596982967286074769 91121535447737225464556077)
    ·
      refine ⟨34170575792901459549208529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91121535447737225464556077 34170575792901459549208529)
      ·
        refine ⟨25627931844676094661906397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34170575792901459549208529 25627931844676094661906397)
        ·
          refine ⟨9610474441753535498214899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25627931844676094661906397 9610474441753535498214899)
          ·
            refine ⟨14415711662630303247322349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9610474441753535498214899 14415711662630303247322349)
            ·
              refine ⟨5405891873486363717745881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14415711662630303247322349 5405891873486363717745881)
              ·
                refine ⟨4054418905114772788309411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5405891873486363717745881 4054418905114772788309411)
                ·
                  refine ⟨6081628357672159182464117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4054418905114772788309411 6081628357672159182464117)
                  ·
                    refine ⟨570152658531764923356011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6081628357672159182464117 570152658531764923356011)
                    ·
                      rfl

theorem cell23_3331105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_3331105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331105 prefixEnd_3331105 := by exact prefixLift 3331105
  have htrace : WordTrace (prefixWord ++ tailWord_3331105) baseStart_3331105 baseEnd_3331105 := by
    simpa [prefixWord, tailWord_3331105, baseEnd_3331105] using wordTrace_append hprefix tailTrace_3331105
  have hstable : (prefixWord ++ tailWord_3331105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331105).length < 2 ^ (prefixWord ++ tailWord_3331105).sum := by decide
  have hdescent : baseEnd_3331105 < baseStart_3331105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331142 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3331142 : Nat := 118140960795 + 3331142 * 2 ^ 59
def prefixEnd_3331142 : Nat := 4983230072969 + 3 ^ 40 * 3331142 * 2
def baseEnd_3331142 : Nat := 1710476974379511125305363

theorem tailTrace_3331142 : CollatzResearch.WordTrace tailWord_3331142 prefixEnd_3331142 1710476974379511125305363 := by
  unfold tailWord_3331142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3796772815557778831411615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80997820065232615070114453 3796772815557778831411615)
  ·
    refine ⟨5695159223336668247117423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3796772815557778831411615 5695159223336668247117423)
    ·
      refine ⟨8542738835005002370676135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5695159223336668247117423 8542738835005002370676135)
      ·
        refine ⟨12814108252507503556014203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8542738835005002370676135 12814108252507503556014203)
        ·
          refine ⟨19221162378761255334021305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12814108252507503556014203 19221162378761255334021305)
          ·
            refine ⟨14415871784070941500515979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19221162378761255334021305 14415871784070941500515979)
            ·
              refine ⟨21623807676106412250773969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14415871784070941500515979 21623807676106412250773969)
              ·
                refine ⟨16217855757079809188080477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21623807676106412250773969 16217855757079809188080477)
                ·
                  refine ⟨6081695908904928445530179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16217855757079809188080477 6081695908904928445530179)
                  ·
                    refine ⟨9122543863357392668295269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6081695908904928445530179 9122543863357392668295269)
                    ·
                      refine ⟨1710476974379511125305363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9122543863357392668295269 1710476974379511125305363)
                      ·
                        rfl

theorem cell23_3331142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3331142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331142 prefixEnd_3331142 := by exact prefixLift 3331142
  have htrace : WordTrace (prefixWord ++ tailWord_3331142) baseStart_3331142 baseEnd_3331142 := by
    simpa [prefixWord, tailWord_3331142, baseEnd_3331142] using wordTrace_append hprefix tailTrace_3331142
  have hstable : (prefixWord ++ tailWord_3331142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331142).length < 2 ^ (prefixWord ++ tailWord_3331142).sum := by decide
  have hdescent : baseEnd_3331142 < baseStart_3331142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331175 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_3331175 : Nat := 118140960795 + 3331175 * 2 ^ 59
def prefixEnd_3331175 : Nat := 4983230072969 + 3 ^ 40 * 3331175 * 2
def baseEnd_3331175 : Nat := 1710493919241109496192711

theorem tailTrace_3331175 : CollatzResearch.WordTrace tailWord_3331175 prefixEnd_3331175 1710493919241109496192711 := by
  unfold tailWord_3331175
  simp only [CollatzResearch.WordTrace]
  refine ⟨121497933706729369241122979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80998622471152912827415319 121497933706729369241122979)
  ·
    refine ⟨182246900560094053861684469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121497933706729369241122979 182246900560094053861684469)
    ·
      refine ⟨17085646927508817549532919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182246900560094053861684469 17085646927508817549532919)
      ·
        refine ⟨25628470391263226324299379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17085646927508817549532919 25628470391263226324299379)
        ·
          refine ⟨38442705586894839486449069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25628470391263226324299379 38442705586894839486449069)
          ·
            refine ⟨14416014595085564807418401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38442705586894839486449069 14416014595085564807418401)
            ·
              refine ⟨10812010946314173605563801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14416014595085564807418401 10812010946314173605563801)
              ·
                refine ⟨8109008209735630204172851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10812010946314173605563801 8109008209735630204172851)
                ·
                  refine ⟨12163512314603445306259277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8109008209735630204172851 12163512314603445306259277)
                  ·
                    refine ⟨4561317117976291989847229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12163512314603445306259277 4561317117976291989847229)
                    ·
                      refine ⟨1710493919241109496192711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4561317117976291989847229 1710493919241109496192711)
                      ·
                        rfl

theorem cell23_3331175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_3331175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331175 prefixEnd_3331175 := by exact prefixLift 3331175
  have htrace : WordTrace (prefixWord ++ tailWord_3331175) baseStart_3331175 baseEnd_3331175 := by
    simpa [prefixWord, tailWord_3331175, baseEnd_3331175] using wordTrace_append hprefix tailTrace_3331175
  have hstable : (prefixWord ++ tailWord_3331175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331175).length < 2 ^ (prefixWord ++ tailWord_3331175).sum := by decide
  have hdescent : baseEnd_3331175 < baseStart_3331175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331176 : List Nat := [2, 1, 4, 4, 1, 2, 2, 1, 1, 1, 4]
def baseStart_3331176 : Nat := 118140960795 + 3331176 * 2 ^ 59
def prefixEnd_3331176 : Nat := 4983230072969 + 3 ^ 40 * 3331176 * 2
def baseEnd_3331176 : Nat := 1710494432721763992280207

theorem tailTrace_3331176 : CollatzResearch.WordTrace tailWord_3331176 prefixEnd_3331176 1710494432721763992280207 := by
  unfold tailWord_3331176
  simp only [CollatzResearch.WordTrace]
  refine ⟨60748985089862873205954691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80998646786483830941272921 60748985089862873205954691)
  ·
    refine ⟨91123477634794309808932037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60748985089862873205954691 91123477634794309808932037)
    ·
      refine ⟨17085652056523933089174757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91123477634794309808932037 17085652056523933089174757)
      ·
        refine ⟨3203559760598237454220267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17085652056523933089174757 3203559760598237454220267)
        ·
          refine ⟨4805339640897356181330401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3203559760598237454220267 4805339640897356181330401)
          ·
            refine ⟨3604004730673017135997801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4805339640897356181330401 3604004730673017135997801)
            ·
              refine ⟨2703003548004762851998351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3604004730673017135997801 2703003548004762851998351)
              ·
                refine ⟨4054505322007144277997527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2703003548004762851998351 4054505322007144277997527)
                ·
                  refine ⟨6081757983010716416996291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4054505322007144277997527 6081757983010716416996291)
                  ·
                    refine ⟨9122636974516074625494437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6081757983010716416996291 9122636974516074625494437)
                    ·
                      refine ⟨1710494432721763992280207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9122636974516074625494437 1710494432721763992280207)
                      ·
                        rfl

theorem cell23_3331176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_3331176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331176 prefixEnd_3331176 := by exact prefixLift 3331176
  have htrace : WordTrace (prefixWord ++ tailWord_3331176) baseStart_3331176 baseEnd_3331176 := by
    simpa [prefixWord, tailWord_3331176, baseEnd_3331176] using wordTrace_append hprefix tailTrace_3331176
  have hstable : (prefixWord ++ tailWord_3331176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331176).length < 2 ^ (prefixWord ++ tailWord_3331176).sum := by decide
  have hdescent : baseEnd_3331176 < baseStart_3331176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331185 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 5, 3, 2]
def baseStart_3331185 : Nat := 118140960795 + 3331185 * 2 ^ 59
def prefixEnd_3331185 : Nat := 4983230072969 + 3 ^ 40 * 3331185 * 2
def baseEnd_3331185 : Nat := 1710499054047654457067665

theorem tailTrace_3331185 : CollatzResearch.WordTrace tailWord_3331185 prefixEnd_3331185 1710499054047654457067665 := by
  unfold tailWord_3331185
  simp only [CollatzResearch.WordTrace]
  refine ⟨121498298436693140948987009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80998865624462093965991339 121498298436693140948987009)
  ·
    refine ⟨91123723827519855711740257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121498298436693140948987009 91123723827519855711740257)
    ·
      refine ⟨68342792870639891783805193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91123723827519855711740257 68342792870639891783805193)
      ·
        refine ⟨51257094652979918837853895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68342792870639891783805193 51257094652979918837853895)
        ·
          refine ⟨76885641979469878256780843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51257094652979918837853895 76885641979469878256780843)
          ·
            refine ⟨115328462969204817385171265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76885641979469878256780843 115328462969204817385171265)
            ·
              refine ⟨86496347226903613038878449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115328462969204817385171265 86496347226903613038878449)
              ·
                refine ⟨64872260420177709779158837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86496347226903613038878449 64872260420177709779158837)
                ·
                  refine ⟨6081774414391660291796141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64872260420177709779158837 6081774414391660291796141)
                  ·
                    refine ⟨2280665405396872609423553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6081774414391660291796141 2280665405396872609423553)
                    ·
                      refine ⟨1710499054047654457067665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2280665405396872609423553 1710499054047654457067665)
                      ·
                        rfl

theorem cell23_3331185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_3331185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331185 prefixEnd_3331185 := by exact prefixLift 3331185
  have htrace : WordTrace (prefixWord ++ tailWord_3331185) baseStart_3331185 baseEnd_3331185 := by
    simpa [prefixWord, tailWord_3331185, baseEnd_3331185] using wordTrace_append hprefix tailTrace_3331185
  have hstable : (prefixWord ++ tailWord_3331185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331185).length < 2 ^ (prefixWord ++ tailWord_3331185).sum := by decide
  have hdescent : baseEnd_3331185 < baseStart_3331185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331192 : List Nat := [2, 1, 2, 1, 1, 1, 7, 2, 2, 1, 3]
def baseStart_3331192 : Nat := 118140960795 + 3331192 * 2 ^ 59
def prefixEnd_3331192 : Nat := 4983230072969 + 3 ^ 40 * 3331192 * 2
def baseEnd_3331192 : Nat := 1710502648412235929680133

theorem tailTrace_3331192 : CollatzResearch.WordTrace tailWord_3331192 prefixEnd_3331192 1710502648412235929680133 := by
  unfold tailWord_3331192
  simp only [CollatzResearch.WordTrace]
  refine ⟨60749276873833890572245915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80999035831778520762994553 60749276873833890572245915)
  ·
    refine ⟨91123915310750835858368873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60749276873833890572245915 91123915310750835858368873)
    ·
      refine ⟨68342936483063126893776655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91123915310750835858368873 68342936483063126893776655)
      ·
        refine ⟨102514404724594690340664983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68342936483063126893776655 102514404724594690340664983)
        ·
          refine ⟨153771607086892035510997475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102514404724594690340664983 153771607086892035510997475)
          ·
            refine ⟨230657410630338053266496213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153771607086892035510997475 230657410630338053266496213)
            ·
              refine ⟨5406033061648548123433505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 230657410630338053266496213 5406033061648548123433505)
              ·
                refine ⟨4054524796236411092575129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5406033061648548123433505 4054524796236411092575129)
                ·
                  refine ⟨3040893597177308319431347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4054524796236411092575129 3040893597177308319431347)
                  ·
                    refine ⟨4561340395765962479147021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3040893597177308319431347 4561340395765962479147021)
                    ·
                      refine ⟨1710502648412235929680133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4561340395765962479147021 1710502648412235929680133)
                      ·
                        rfl

theorem cell23_3331192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 2, 1, 3].length) (baseStart_3331192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331192 prefixEnd_3331192 := by exact prefixLift 3331192
  have htrace : WordTrace (prefixWord ++ tailWord_3331192) baseStart_3331192 baseEnd_3331192 := by
    simpa [prefixWord, tailWord_3331192, baseEnd_3331192] using wordTrace_append hprefix tailTrace_3331192
  have hstable : (prefixWord ++ tailWord_3331192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331192).length < 2 ^ (prefixWord ++ tailWord_3331192).sum := by decide
  have hdescent : baseEnd_3331192 < baseStart_3331192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331209 : List Nat := [1, 2, 1, 1, 4, 4, 3, 1, 2, 1, 3]
def baseStart_3331209 : Nat := 118140960795 + 3331209 * 2 ^ 59
def prefixEnd_3331209 : Nat := 4983230072969 + 3 ^ 40 * 3331209 * 2
def baseEnd_3331209 : Nat := 1710511377583362363167555

theorem tailTrace_3331209 : CollatzResearch.WordTrace tailWord_3331209 prefixEnd_3331209 1710511377583362363167555 := by
  unfold tailWord_3331209
  simp only [CollatzResearch.WordTrace]
  refine ⟨121499173788606193047860681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80999449192404128698573787 121499173788606193047860681)
  ·
    refine ⟨91124380341454644785895511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121499173788606193047860681 91124380341454644785895511)
    ·
      refine ⟨136686570512181967178843267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91124380341454644785895511 136686570512181967178843267)
      ·
        refine ⟨205029855768272950768264901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136686570512181967178843267 205029855768272950768264901)
        ·
          refine ⟨38443097956551178269049669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205029855768272950768264901 38443097956551178269049669)
          ·
            refine ⟨7208080866853345925446813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38443097956551178269049669 7208080866853345925446813)
            ·
              refine ⟨2703030325070004722042555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7208080866853345925446813 2703030325070004722042555)
              ·
                refine ⟨4054545487605007083063833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2703030325070004722042555 4054545487605007083063833)
                ·
                  refine ⟨3040909115703755312297875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4054545487605007083063833 3040909115703755312297875)
                  ·
                    refine ⟨4561363673555632968446813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3040909115703755312297875 4561363673555632968446813)
                    ·
                      refine ⟨1710511377583362363167555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4561363673555632968446813 1710511377583362363167555)
                      ·
                        rfl

theorem cell23_3331209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 2, 1, 3].length) (baseStart_3331209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331209 prefixEnd_3331209 := by exact prefixLift 3331209
  have htrace : WordTrace (prefixWord ++ tailWord_3331209) baseStart_3331209 baseEnd_3331209 := by
    simpa [prefixWord, tailWord_3331209, baseEnd_3331209] using wordTrace_append hprefix tailTrace_3331209
  have hstable : (prefixWord ++ tailWord_3331209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331209).length < 2 ^ (prefixWord ++ tailWord_3331209).sum := by decide
  have hdescent : baseEnd_3331209 < baseStart_3331209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331232 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 6, 2, 2]
def baseStart_3331232 : Nat := 118140960795 + 3331232 * 2 ^ 59
def prefixEnd_3331232 : Nat := 4983230072969 + 3 ^ 40 * 3331232 * 2
def baseEnd_3331232 : Nat := 1710523187638415773179949

theorem tailTrace_3331232 : CollatzResearch.WordTrace tailWord_3331232 prefixEnd_3331232 1710523187638415773179949 := by
  unfold tailWord_3331232
  simp only [CollatzResearch.WordTrace]
  refine ⟨60750006333761433987973975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81000008445015245317298633 60750006333761433987973975)
  ·
    refine ⟨91125009500642150981960963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60750006333761433987973975 91125009500642150981960963)
    ·
      refine ⟨136687514250963226472941445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91125009500642150981960963 136687514250963226472941445)
      ·
        refine ⟨25628908922055604963676521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136687514250963226472941445 25628908922055604963676521)
        ·
          refine ⟨19221681691541703722757391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25628908922055604963676521 19221681691541703722757391)
          ·
            refine ⟨28832522537312555584136087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19221681691541703722757391 28832522537312555584136087)
            ·
              refine ⟨43248783805968833376204131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28832522537312555584136087 43248783805968833376204131)
              ·
                refine ⟨64873175708953250064306197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43248783805968833376204131 64873175708953250064306197)
                ·
                  refine ⟨3040930111357183596764353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64873175708953250064306197 3040930111357183596764353)
                  ·
                    refine ⟨2280697583517887697573265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3040930111357183596764353 2280697583517887697573265)
                    ·
                      refine ⟨1710523187638415773179949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2280697583517887697573265 1710523187638415773179949)
                      ·
                        rfl

theorem cell23_3331232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_3331232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331232 prefixEnd_3331232 := by exact prefixLift 3331232
  have htrace : WordTrace (prefixWord ++ tailWord_3331232) baseStart_3331232 baseEnd_3331232 := by
    simpa [prefixWord, tailWord_3331232, baseEnd_3331232] using wordTrace_append hprefix tailTrace_3331232
  have hstable : (prefixWord ++ tailWord_3331232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331232).length < 2 ^ (prefixWord ++ tailWord_3331232).sum := by decide
  have hdescent : baseEnd_3331232 < baseStart_3331232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331249 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 4, 2, 2]
def baseStart_3331249 : Nat := 118140960795 + 3331249 * 2 ^ 59
def prefixEnd_3331249 : Nat := 4983230072969 + 3 ^ 40 * 3331249 * 2
def baseEnd_3331249 : Nat := 1710531916809542206667371

theorem tailTrace_3331249 : CollatzResearch.WordTrace tailWord_3331249 prefixEnd_3331249 1710531916809542206667371 := by
  unfold tailWord_3331249
  simp only [CollatzResearch.WordTrace]
  refine ⟨121500632708461279879316801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81000421805640853252877867 121500632708461279879316801)
  ·
    refine ⟨91125474531345959909487601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121500632708461279879316801 91125474531345959909487601)
    ·
      refine ⟨68344105898509469932115701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91125474531345959909487601 68344105898509469932115701)
      ·
        refine ⟨6407259927985262806135847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68344105898509469932115701 6407259927985262806135847)
        ·
          refine ⟨9610889891977894209203771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6407259927985262806135847 9610889891977894209203771)
          ·
            refine ⟨14416334837966841313805657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9610889891977894209203771 14416334837966841313805657)
            ·
              refine ⟨10812251128475130985354243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14416334837966841313805657 10812251128475130985354243)
              ·
                refine ⟨16218376692712696478031365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10812251128475130985354243 16218376692712696478031365)
                ·
                  refine ⟨3040945629883630589630881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16218376692712696478031365 3040945629883630589630881)
                  ·
                    refine ⟨2280709222412722942223161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3040945629883630589630881 2280709222412722942223161)
                    ·
                      refine ⟨1710531916809542206667371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2280709222412722942223161 1710531916809542206667371)
                      ·
                        rfl

theorem cell23_3331249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_3331249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331249 prefixEnd_3331249 := by exact prefixLift 3331249
  have htrace : WordTrace (prefixWord ++ tailWord_3331249) baseStart_3331249 baseEnd_3331249 := by
    simpa [prefixWord, tailWord_3331249, baseEnd_3331249] using wordTrace_append hprefix tailTrace_3331249
  have hstable : (prefixWord ++ tailWord_3331249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331249).length < 2 ^ (prefixWord ++ tailWord_3331249).sum := by decide
  have hdescent : baseEnd_3331249 < baseStart_3331249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331275 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 4, 5, 2]
def baseStart_3331275 : Nat := 118140960795 + 3331275 * 2 ^ 59
def prefixEnd_3331275 : Nat := 4983230072969 + 3 ^ 40 * 3331275 * 2
def baseEnd_3331275 : Nat := 1710545267306559104942251

theorem tailTrace_3331275 : CollatzResearch.WordTrace tailWord_3331275 prefixEnd_3331275 1710545267306559104942251 := by
  unfold tailWord_3331275
  simp only [CollatzResearch.WordTrace]
  refine ⟨121501581006367086319763279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81001054004244724213175519 121501581006367086319763279)
  ·
    refine ⟨182252371509550629479644919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121501581006367086319763279 182252371509550629479644919)
    ·
      refine ⟨273378557264325944219467379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182252371509550629479644919 273378557264325944219467379)
      ·
        refine ⟨410067835896488916329201069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273378557264325944219467379 410067835896488916329201069)
        ·
          refine ⟨153775438461183343623450401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410067835896488916329201069 153775438461183343623450401)
          ·
            refine ⟨115331578845887507717587801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153775438461183343623450401 115331578845887507717587801)
            ·
              refine ⟨86498684134415630788190851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115331578845887507717587801 86498684134415630788190851)
              ·
                refine ⟨129748026201623446182286277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86498684134415630788190851 129748026201623446182286277)
                ·
                  refine ⟨24327754912804396159178677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129748026201623446182286277 24327754912804396159178677)
                  ·
                    refine ⟨2280727023075412139923001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24327754912804396159178677 2280727023075412139923001)
                    ·
                      refine ⟨1710545267306559104942251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2280727023075412139923001 1710545267306559104942251)
                      ·
                        rfl

theorem cell23_3331275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 5, 2].length) (baseStart_3331275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331275 prefixEnd_3331275 := by exact prefixLift 3331275
  have htrace : WordTrace (prefixWord ++ tailWord_3331275) baseStart_3331275 baseEnd_3331275 := by
    simpa [prefixWord, tailWord_3331275, baseEnd_3331275] using wordTrace_append hprefix tailTrace_3331275
  have hstable : (prefixWord ++ tailWord_3331275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331275).length < 2 ^ (prefixWord ++ tailWord_3331275).sum := by decide
  have hdescent : baseEnd_3331275 < baseStart_3331275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331322 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2]
def baseStart_3331322 : Nat := 118140960795 + 3331322 * 2 ^ 59
def prefixEnd_3331322 : Nat := 4983230072969 + 3 ^ 40 * 3331322 * 2
def baseEnd_3331322 : Nat := 1710569400897320421054535

theorem tailTrace_3331322 : CollatzResearch.WordTrace tailWord_3331322 prefixEnd_3331322 1710569400897320421054535 := by
  unfold tailWord_3331322
  simp only [CollatzResearch.WordTrace]
  refine ⟨30375823809299203336681055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81002196824797875564482813 30375823809299203336681055)
  ·
    refine ⟨45563735713948805005021583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30375823809299203336681055 45563735713948805005021583)
    ·
      refine ⟨68345603570923207507532375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45563735713948805005021583 68345603570923207507532375)
      ·
        refine ⟨102518405356384811261298563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68345603570923207507532375 102518405356384811261298563)
        ·
          refine ⟨153777608034577216891947845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102518405356384811261298563 153777608034577216891947845)
          ·
            refine ⟨28833301506483228167240221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153777608034577216891947845 28833301506483228167240221)
            ·
              refine ⟨10812488064931210562715083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28833301506483228167240221 10812488064931210562715083)
              ·
                refine ⟨16218732097396815844072625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10812488064931210562715083 16218732097396815844072625)
                ·
                  refine ⟨12164049073047611883054469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16218732097396815844072625 12164049073047611883054469)
                  ·
                    refine ⟨2280759201196427228072713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12164049073047611883054469 2280759201196427228072713)
                    ·
                      refine ⟨1710569400897320421054535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2280759201196427228072713 1710569400897320421054535)
                      ·
                        rfl

theorem cell23_3331322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2].length) (baseStart_3331322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331322 prefixEnd_3331322 := by exact prefixLift 3331322
  have htrace : WordTrace (prefixWord ++ tailWord_3331322) baseStart_3331322 baseEnd_3331322 := by
    simpa [prefixWord, tailWord_3331322, baseEnd_3331322] using wordTrace_append hprefix tailTrace_3331322
  have hstable : (prefixWord ++ tailWord_3331322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331322).length < 2 ^ (prefixWord ++ tailWord_3331322).sum := by decide
  have hdescent : baseEnd_3331322 < baseStart_3331322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331328 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 10]
def baseStart_3331328 : Nat := 118140960795 + 3331328 * 2 ^ 59
def prefixEnd_3331328 : Nat := 4983230072969 + 3 ^ 40 * 3331328 * 2
def baseEnd_3331328 : Nat := 190063609086805266397723

theorem tailTrace_3331328 : CollatzResearch.WordTrace tailWord_3331328 prefixEnd_3331328 190063609086805266397723 := by
  unfold tailWord_3331328
  simp only [CollatzResearch.WordTrace]
  refine ⟨60751757037587538185721319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81002342716783384247628425 60751757037587538185721319)
  ·
    refine ⟨91127635556381307278581979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60751757037587538185721319 91127635556381307278581979)
    ·
      refine ⟨136691453334571960917872969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91127635556381307278581979 136691453334571960917872969)
      ·
        refine ⟨102518590000928970688404727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136691453334571960917872969 102518590000928970688404727)
        ·
          refine ⟨153777885001393456032607091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102518590000928970688404727 153777885001393456032607091)
          ·
            refine ⟨230666827502090184048910637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153777885001393456032607091 230666827502090184048910637)
            ·
              refine ⟨86500060313283819018341489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230666827502090184048910637 86500060313283819018341489)
              ·
                refine ⟨64875045234962864263756117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86500060313283819018341489 64875045234962864263756117)
                ·
                  refine ⟨190063609086805266397723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 64875045234962864263756117 190063609086805266397723)
                  ·
                    rfl

theorem cell23_3331328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 10].length) (baseStart_3331328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331328 prefixEnd_3331328 := by exact prefixLift 3331328
  have htrace : WordTrace (prefixWord ++ tailWord_3331328) baseStart_3331328 baseEnd_3331328 := by
    simpa [prefixWord, tailWord_3331328, baseEnd_3331328] using wordTrace_append hprefix tailTrace_3331328
  have hstable : (prefixWord ++ tailWord_3331328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331328).length < 2 ^ (prefixWord ++ tailWord_3331328).sum := by decide
  have hdescent : baseEnd_3331328 < baseStart_3331328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331332 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 5, 4]
def baseStart_3331332 : Nat := 118140960795 + 3331332 * 2 ^ 59
def prefixEnd_3331332 : Nat := 4983230072969 + 3 ^ 40 * 3331332 * 2
def baseEnd_3331332 : Nat := 570191511901288460643163

theorem tailTrace_3331332 : CollatzResearch.WordTrace tailWord_3331332 prefixEnd_3331332 570191511901288460643163 := by
  unfold tailWord_3331332
  simp only [CollatzResearch.WordTrace]
  refine ⟨60751829983580292527294125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81002439978107056703058833 60751829983580292527294125)
  ·
    refine ⟨22781936243842609697735297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60751829983580292527294125 22781936243842609697735297)
    ·
      refine ⟨17086452182881957273301473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22781936243842609697735297 17086452182881957273301473)
      ·
        refine ⟨12814839137161467954976105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17086452182881957273301473 12814839137161467954976105)
        ·
          refine ⟨9611129352871100966232079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12814839137161467954976105 9611129352871100966232079)
          ·
            refine ⟨14416694029306651449348119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9611129352871100966232079 14416694029306651449348119)
            ·
              refine ⟨21625041043959977174022179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14416694029306651449348119 21625041043959977174022179)
              ·
                refine ⟨32437561565939965761033269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21625041043959977174022179 32437561565939965761033269)
                ·
                  refine ⟨3041021396806871790096869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32437561565939965761033269 3041021396806871790096869)
                  ·
                    refine ⟨570191511901288460643163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3041021396806871790096869 570191511901288460643163)
                    ·
                      rfl

theorem cell23_3331332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_3331332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331332 prefixEnd_3331332 := by exact prefixLift 3331332
  have htrace : WordTrace (prefixWord ++ tailWord_3331332) baseStart_3331332 baseEnd_3331332 := by
    simpa [prefixWord, tailWord_3331332, baseEnd_3331332] using wordTrace_append hprefix tailTrace_3331332
  have hstable : (prefixWord ++ tailWord_3331332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331332).length < 2 ^ (prefixWord ++ tailWord_3331332).sum := by decide
  have hdescent : baseEnd_3331332 < baseStart_3331332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331342 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3]
def baseStart_3331342 : Nat := 118140960795 + 3331342 * 2 ^ 59
def prefixEnd_3331342 : Nat := 4983230072969 + 3 ^ 40 * 3331342 * 2
def baseEnd_3331342 : Nat := 1710579670510410342804443

theorem tailTrace_3331342 : CollatzResearch.WordTrace tailWord_3331342 prefixEnd_3331342 1710579670510410342804443 := by
  unfold tailWord_3331342
  simp only [CollatzResearch.WordTrace]
  refine ⟨15188003087140544595306535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81002683131416237841634853 15188003087140544595306535)
  ·
    refine ⟨22782004630710816892959803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15188003087140544595306535 22782004630710816892959803)
    ·
      refine ⟨34173006946066225339439705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22782004630710816892959803 34173006946066225339439705)
      ·
        refine ⟨25629755209549669004579779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34173006946066225339439705 25629755209549669004579779)
        ·
          refine ⟨38444632814324503506869669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25629755209549669004579779 38444632814324503506869669)
          ·
            refine ⟨7208368652685844407538063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38444632814324503506869669 7208368652685844407538063)
            ·
              refine ⟨10812552979028766611307095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7208368652685844407538063 10812552979028766611307095)
              ·
                refine ⟨16218829468543149916960643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10812552979028766611307095 16218829468543149916960643)
                ·
                  refine ⟨24328244202814724875440965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16218829468543149916960643 24328244202814724875440965)
                  ·
                    refine ⟨4561545788027760914145181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24328244202814724875440965 4561545788027760914145181)
                    ·
                      refine ⟨1710579670510410342804443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4561545788027760914145181 1710579670510410342804443)
                      ·
                        rfl

theorem cell23_3331342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_3331342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331342 prefixEnd_3331342 := by exact prefixLift 3331342
  have htrace : WordTrace (prefixWord ++ tailWord_3331342) baseStart_3331342 baseEnd_3331342 := by
    simpa [prefixWord, tailWord_3331342, baseEnd_3331342] using wordTrace_append hprefix tailTrace_3331342
  have hstable : (prefixWord ++ tailWord_3331342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331342).length < 2 ^ (prefixWord ++ tailWord_3331342).sum := by decide
  have hdescent : baseEnd_3331342 < baseStart_3331342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331362 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 8]
def baseStart_3331362 : Nat := 118140960795 + 3331362 * 2 ^ 59
def prefixEnd_3331362 : Nat := 4983230072969 + 3 ^ 40 * 3331362 * 2
def baseEnd_3331362 : Nat := 190065548902611140506039

theorem tailTrace_3331362 : CollatzResearch.WordTrace tailWord_3331362 prefixEnd_3331362 190065548902611140506039 := by
  unfold tailWord_3331362
  simp only [CollatzResearch.WordTrace]
  refine ⟨30376188539262975044545085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81003169438034600118786893 30376188539262975044545085)
  ·
    refine ⟨11391070702223615641704407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30376188539262975044545085 11391070702223615641704407)
    ·
      refine ⟨17086606053335423462556611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11391070702223615641704407 17086606053335423462556611)
      ·
        refine ⟨25629909080003135193834917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17086606053335423462556611 25629909080003135193834917)
        ·
          refine ⟨4805607952500587848844047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25629909080003135193834917 4805607952500587848844047)
          ·
            refine ⟨7208411928750881773266071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4805607952500587848844047 7208411928750881773266071)
            ·
              refine ⟨10812617893126322659899107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7208411928750881773266071 10812617893126322659899107)
              ·
                refine ⟨16218926839689483989848661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10812617893126322659899107 16218926839689483989848661)
                ·
                  refine ⟨190065548902611140506039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16218926839689483989848661 190065548902611140506039)
                  ·
                    rfl

theorem cell23_3331362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_3331362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331362 prefixEnd_3331362 := by exact prefixLift 3331362
  have htrace : WordTrace (prefixWord ++ tailWord_3331362) baseStart_3331362 baseEnd_3331362 := by
    simpa [prefixWord, tailWord_3331362, baseEnd_3331362] using wordTrace_append hprefix tailTrace_3331362
  have hstable : (prefixWord ++ tailWord_3331362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331362).length < 2 ^ (prefixWord ++ tailWord_3331362).sum := by decide
  have hdescent : baseEnd_3331362 < baseStart_3331362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331365 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 1, 2, 6]
def baseStart_3331365 : Nat := 118140960795 + 3331365 * 2 ^ 59
def prefixEnd_3331365 : Nat := 4983230072969 + 3 ^ 40 * 3331365 * 2
def baseEnd_3331365 : Nat := 1710591480565463752816837

theorem tailTrace_3331365 : CollatzResearch.WordTrace tailWord_3331365 prefixEnd_3331365 1710591480565463752816837 := by
  unfold tailWord_3331365
  simp only [CollatzResearch.WordTrace]
  refine ⟨121504863576041031690539549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81003242384027354460359699 121504863576041031690539549)
  ·
    refine ⟨45564323841015386883952331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121504863576041031690539549 45564323841015386883952331)
    ·
      refine ⟨68346485761523080325928497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45564323841015386883952331 68346485761523080325928497)
      ·
        refine ⟨51259864321142310244446373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68346485761523080325928497 51259864321142310244446373)
        ·
          refine ⟨9611224560214183170833695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51259864321142310244446373 9611224560214183170833695)
          ·
            refine ⟨14416836840321274756250543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9611224560214183170833695 14416836840321274756250543)
            ·
              refine ⟨21625255260481912134375815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14416836840321274756250543 21625255260481912134375815)
              ·
                refine ⟨32437882890722868201563723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21625255260481912134375815 32437882890722868201563723)
                ·
                  refine ⟨48656824336084302302345585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32437882890722868201563723 48656824336084302302345585)
                  ·
                    refine ⟨36492618252063226726759189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48656824336084302302345585 36492618252063226726759189)
                    ·
                      refine ⟨1710591480565463752816837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36492618252063226726759189 1710591480565463752816837)
                      ·
                        rfl

theorem cell23_3331365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_3331365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331365 prefixEnd_3331365 := by exact prefixLift 3331365
  have htrace : WordTrace (prefixWord ++ tailWord_3331365) baseStart_3331365 baseEnd_3331365 := by
    simpa [prefixWord, tailWord_3331365, baseEnd_3331365] using wordTrace_append hprefix tailTrace_3331365
  have hstable : (prefixWord ++ tailWord_3331365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331365).length < 2 ^ (prefixWord ++ tailWord_3331365).sum := by decide
  have hdescent : baseEnd_3331365 < baseStart_3331365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331392 : List Nat := [2, 1, 1, 2, 2, 1, 6, 2, 1, 5]
def baseStart_3331392 : Nat := 118140960795 + 3331392 * 2 ^ 59
def prefixEnd_3331392 : Nat := 4983230072969 + 3 ^ 40 * 3331392 * 2
def baseEnd_3331392 : Nat := 570201781514378382393071

theorem tailTrace_3331392 : CollatzResearch.WordTrace tailWord_3331392 prefixEnd_3331392 570201781514378382393071 := by
  unfold tailWord_3331392
  simp only [CollatzResearch.WordTrace]
  refine ⟨60752924173471607650886215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81003898897962143534514953 60752924173471607650886215)
  ·
    refine ⟨91129386260207411476329323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60752924173471607650886215 91129386260207411476329323)
    ·
      refine ⟨136694079390311117214493985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91129386260207411476329323 136694079390311117214493985)
      ·
        refine ⟨102520559542733337910870489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136694079390311117214493985 102520559542733337910870489)
        ·
          refine ⟨76890419657050003433152867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102520559542733337910870489 76890419657050003433152867)
          ·
            refine ⟨115335629485575005149729301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76890419657050003433152867 115335629485575005149729301)
            ·
              refine ⟨5406357632136328366393561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115335629485575005149729301 5406357632136328366393561)
              ·
                refine ⟨4054768224102246274795171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5406357632136328366393561 4054768224102246274795171)
                ·
                  refine ⟨6082152336153369412192757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4054768224102246274795171 6082152336153369412192757)
                  ·
                    refine ⟨570201781514378382393071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6082152336153369412192757 570201781514378382393071)
                    ·
                      rfl

theorem cell23_3331392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 1, 5].length) (baseStart_3331392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331392 prefixEnd_3331392 := by exact prefixLift 3331392
  have htrace : WordTrace (prefixWord ++ tailWord_3331392) baseStart_3331392 baseEnd_3331392 := by
    simpa [prefixWord, tailWord_3331392, baseEnd_3331392] using wordTrace_append hprefix tailTrace_3331392
  have hstable : (prefixWord ++ tailWord_3331392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331392).length < 2 ^ (prefixWord ++ tailWord_3331392).sum := by decide
  have hdescent : baseEnd_3331392 < baseStart_3331392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331442 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_3331442 : Nat := 118140960795 + 3331442 * 2 ^ 59
def prefixEnd_3331442 : Nat := 4983230072969 + 3 ^ 40 * 3331442 * 2
def baseEnd_3331442 : Nat := 1710631018575859951553983

theorem tailTrace_3331442 : CollatzResearch.WordTrace tailWord_3331442 prefixEnd_3331442 1710631018575859951553983 := by
  unfold tailWord_3331442
  simp only [CollatzResearch.WordTrace]
  refine ⟨30376917999190518460273145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81005114664508049227395053 30376917999190518460273145)
  ·
    refine ⟨22782688499392888845204859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30376917999190518460273145 22782688499392888845204859)
    ·
      refine ⟨34174032749089333267807289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22782688499392888845204859 34174032749089333267807289)
      ·
        refine ⟨25630524561816999950855467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34174032749089333267807289 25630524561816999950855467)
        ·
          refine ⟨38445786842725499926283201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25630524561816999950855467 38445786842725499926283201)
          ·
            refine ⟨28834340132044124944712401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38445786842725499926283201 28834340132044124944712401)
            ·
              refine ⟨21625755099033093708534301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28834340132044124944712401 21625755099033093708534301)
              ·
                refine ⟨8109658162137410140700363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21625755099033093708534301 8109658162137410140700363)
                ·
                  refine ⟨12164487243206115211050545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8109658162137410140700363 12164487243206115211050545)
                  ·
                    refine ⟨9123365432404586408287909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12164487243206115211050545 9123365432404586408287909)
                    ·
                      refine ⟨1710631018575859951553983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9123365432404586408287909 1710631018575859951553983)
                      ·
                        rfl

theorem cell23_3331442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_3331442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331442 prefixEnd_3331442 := by exact prefixLift 3331442
  have htrace : WordTrace (prefixWord ++ tailWord_3331442) baseStart_3331442 baseEnd_3331442 := by
    simpa [prefixWord, tailWord_3331442, baseEnd_3331442] using wordTrace_append hprefix tailTrace_3331442
  have hstable : (prefixWord ++ tailWord_3331442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331442).length < 2 ^ (prefixWord ++ tailWord_3331442).sum := by decide
  have hdescent : baseEnd_3331442 < baseStart_3331442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331449 : List Nat := [1, 2, 1, 3, 2, 1, 5, 2, 1, 2, 3]
def baseStart_3331449 : Nat := 118140960795 + 3331449 * 2 ^ 59
def prefixEnd_3331449 : Nat := 4983230072969 + 3 ^ 40 * 3331449 * 2
def baseEnd_3331449 : Nat := 1710634612940441424166451

theorem tailTrace_3331449 : CollatzResearch.WordTrace tailWord_3331449 prefixEnd_3331449 1710634612940441424166451 := by
  unfold tailWord_3331449
  simp only [CollatzResearch.WordTrace]
  refine ⟨121507927307736714036597401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81005284871824476024398267 121507927307736714036597401)
  ·
    refine ⟨91130945480802535527448051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121507927307736714036597401 91130945480802535527448051)
    ·
      refine ⟨136696418221203803291172077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91130945480802535527448051 136696418221203803291172077)
      ·
        refine ⟨51261156832951426234189529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136696418221203803291172077 51261156832951426234189529)
        ·
          refine ⟨38445867624713569675642147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51261156832951426234189529 38445867624713569675642147)
          ·
            refine ⟨57668801437070354513463221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38445867624713569675642147 57668801437070354513463221)
            ·
              refine ⟨5406450134725345735637177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57668801437070354513463221 5406450134725345735637177)
              ·
                refine ⟨4054837601044009301727883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5406450134725345735637177 4054837601044009301727883)
                ·
                  refine ⟨6082256401566013952591825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4054837601044009301727883 6082256401566013952591825)
                  ·
                    refine ⟨4561692301174510464443869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6082256401566013952591825 4561692301174510464443869)
                    ·
                      refine ⟨1710634612940441424166451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4561692301174510464443869 1710634612940441424166451)
                      ·
                        rfl

theorem cell23_3331449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_3331449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331449 prefixEnd_3331449 := by exact prefixLift 3331449
  have htrace : WordTrace (prefixWord ++ tailWord_3331449) baseStart_3331449 baseEnd_3331449 := by
    simpa [prefixWord, tailWord_3331449, baseEnd_3331449] using wordTrace_append hprefix tailTrace_3331449
  have hstable : (prefixWord ++ tailWord_3331449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331449).length < 2 ^ (prefixWord ++ tailWord_3331449).sum := by decide
  have hdescent : baseEnd_3331449 < baseStart_3331449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331474 : List Nat := [3, 2, 3, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_3331474 : Nat := 118140960795 + 3331474 * 2 ^ 59
def prefixEnd_3331474 : Nat := 4983230072969 + 3 ^ 40 * 3331474 * 2
def baseEnd_3331474 : Nat := 1710647449956803826353837

theorem tailTrace_3331474 : CollatzResearch.WordTrace tailWord_3331474 prefixEnd_3331474 1710647449956803826353837 := by
  unfold tailWord_3331474
  simp only [CollatzResearch.WordTrace]
  refine ⟨30377209783161535826564369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81005892755097428870838317 30377209783161535826564369)
  ·
    refine ⟨22782907337371151869923277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30377209783161535826564369 22782907337371151869923277)
    ·
      refine ⟨8543590251514181951221229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22782907337371151869923277 8543590251514181951221229)
      ·
        refine ⟨3203846344317818231707961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8543590251514181951221229 3203846344317818231707961)
        ·
          refine ⟨2402884758238363673780971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3203846344317818231707961 2402884758238363673780971)
          ·
            refine ⟨3604327137357545510671457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2402884758238363673780971 3604327137357545510671457)
            ·
              refine ⟨2703245353018159133003593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3604327137357545510671457 2703245353018159133003593)
              ·
                refine ⟨2027434014763619349752695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2703245353018159133003593 2027434014763619349752695)
                ·
                  refine ⟨3041151022145429024629043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027434014763619349752695 3041151022145429024629043)
                  ·
                    refine ⟨4561726533218143536943565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3041151022145429024629043 4561726533218143536943565)
                    ·
                      refine ⟨1710647449956803826353837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4561726533218143536943565 1710647449956803826353837)
                      ·
                        rfl

theorem cell23_3331474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_3331474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331474 prefixEnd_3331474 := by exact prefixLift 3331474
  have htrace : WordTrace (prefixWord ++ tailWord_3331474) baseStart_3331474 baseEnd_3331474 := by
    simpa [prefixWord, tailWord_3331474, baseEnd_3331474] using wordTrace_append hprefix tailTrace_3331474
  have hstable : (prefixWord ++ tailWord_3331474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331474).length < 2 ^ (prefixWord ++ tailWord_3331474).sum := by decide
  have hdescent : baseEnd_3331474 < baseStart_3331474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331480 : List Nat := [2, 1, 2, 5, 2, 1, 1, 4, 1, 2, 2]
def baseStart_3331480 : Nat := 118140960795 + 3331480 * 2 ^ 59
def prefixEnd_3331480 : Nat := 4983230072969 + 3 ^ 40 * 3331480 * 2
def baseEnd_3331480 : Nat := 1710650530840730802878809

theorem tailTrace_3331480 : CollatzResearch.WordTrace tailWord_3331480 prefixEnd_3331480 1710650530840730802878809 := by
  unfold tailWord_3331480
  simp only [CollatzResearch.WordTrace]
  refine ⟨60754528985312203165487947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81006038647082937553983929 60754528985312203165487947)
  ·
    refine ⟨91131793477968304748231921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60754528985312203165487947 91131793477968304748231921)
    ·
      refine ⟨68348845108476228561173941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91131793477968304748231921 68348845108476228561173941)
      ·
        refine ⟨6407704228919646427610057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68348845108476228561173941 6407704228919646427610057)
        ·
          refine ⟨4805778171689734820707543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6407704228919646427610057 4805778171689734820707543)
          ·
            refine ⟨7208667257534602231061315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4805778171689734820707543 7208667257534602231061315)
            ·
              refine ⟨10813000886301903346591973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7208667257534602231061315 10813000886301903346591973)
              ·
                refine ⟨2027437666181606877485995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10813000886301903346591973 2027437666181606877485995)
                ·
                  refine ⟨3041156499272410316228993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027437666181606877485995 3041156499272410316228993)
                  ·
                    refine ⟨2280867374454307737171745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3041156499272410316228993 2280867374454307737171745)
                    ·
                      refine ⟨1710650530840730802878809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2280867374454307737171745 1710650530840730802878809)
                      ·
                        rfl

theorem cell23_3331480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_3331480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331480 prefixEnd_3331480 := by exact prefixLift 3331480
  have htrace : WordTrace (prefixWord ++ tailWord_3331480) baseStart_3331480 baseEnd_3331480 := by
    simpa [prefixWord, tailWord_3331480, baseEnd_3331480] using wordTrace_append hprefix tailTrace_3331480
  have hstable : (prefixWord ++ tailWord_3331480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331480).length < 2 ^ (prefixWord ++ tailWord_3331480).sum := by decide
  have hdescent : baseEnd_3331480 < baseStart_3331480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331486 : List Nat := [4, 3, 1, 2, 2, 2, 1, 8]
def baseStart_3331486 : Nat := 118140960795 + 3331486 * 2 ^ 59
def prefixEnd_3331486 : Nat := 4983230072969 + 3 ^ 40 * 3331486 * 2
def baseEnd_3331486 : Nat := 63357541174987325163103

theorem tailTrace_3331486 : CollatzResearch.WordTrace tailWord_3331486 prefixEnd_3331486 63357541174987325163103 := by
  unfold tailWord_3331486
  simp only [CollatzResearch.WordTrace]
  refine ⟨15188659601075333669461789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81006184539068446237129541 15188659601075333669461789)
  ·
    refine ⟨5695747350403250126048171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15188659601075333669461789 5695747350403250126048171)
    ·
      refine ⟨8543621025604875189072257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5695747350403250126048171 8543621025604875189072257)
      ·
        refine ⟨6407715769203656391804193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8543621025604875189072257 6407715769203656391804193)
        ·
          refine ⟨4805786826902742293853145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6407715769203656391804193 4805786826902742293853145)
          ·
            refine ⟨3604340120177056720389859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4805786826902742293853145 3604340120177056720389859)
            ·
              refine ⟨5406510180265585080584789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3604340120177056720389859 5406510180265585080584789)
              ·
                refine ⟨63357541174987325163103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5406510180265585080584789 63357541174987325163103)
                ·
                  rfl

theorem cell23_3331486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 8].length) (baseStart_3331486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331486 prefixEnd_3331486 := by exact prefixLift 3331486
  have htrace : WordTrace (prefixWord ++ tailWord_3331486) baseStart_3331486 baseEnd_3331486 := by
    simpa [prefixWord, tailWord_3331486, baseEnd_3331486] using wordTrace_append hprefix tailTrace_3331486
  have hstable : (prefixWord ++ tailWord_3331486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331486).length < 2 ^ (prefixWord ++ tailWord_3331486).sum := by decide
  have hdescent : baseEnd_3331486 < baseStart_3331486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331549 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_3331549 : Nat := 118140960795 + 3331549 * 2 ^ 59
def prefixEnd_3331549 : Nat := 4983230072969 + 3 ^ 40 * 3331549 * 2
def baseEnd_3331549 : Nat := 1710685961005891032915991

theorem tailTrace_3331549 : CollatzResearch.WordTrace tailWord_3331549 prefixEnd_3331549 1710685961005891032915991 := by
  unfold tailWord_3331549
  simp only [CollatzResearch.WordTrace]
  refine ⟨121511574607374431115237701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81007716404916287410158467 121511574607374431115237701)
  ·
    refine ⟨22783420238882705834107069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121511574607374431115237701 22783420238882705834107069)
    ·
      refine ⟨8543782589581014687790151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22783420238882705834107069 8543782589581014687790151)
      ·
        refine ⟨12815673884371522031685227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8543782589581014687790151 12815673884371522031685227)
        ·
          refine ⟨19223510826557283047527841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12815673884371522031685227 19223510826557283047527841)
          ·
            refine ⟨14417633119917962285645881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19223510826557283047527841 14417633119917962285645881)
            ·
              refine ⟨10813224839938471714234411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14417633119917962285645881 10813224839938471714234411)
              ·
                refine ⟨16219837259907707571351617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10813224839938471714234411 16219837259907707571351617)
                ·
                  refine ⟨12164877944930780678513713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16219837259907707571351617 12164877944930780678513713)
                  ·
                    refine ⟨9123658458698085508885285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12164877944930780678513713 9123658458698085508885285)
                    ·
                      refine ⟨1710685961005891032915991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9123658458698085508885285 1710685961005891032915991)
                      ·
                        rfl

theorem cell23_3331549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_3331549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331549 prefixEnd_3331549 := by exact prefixLift 3331549
  have htrace : WordTrace (prefixWord ++ tailWord_3331549) baseStart_3331549 baseEnd_3331549 := by
    simpa [prefixWord, tailWord_3331549, baseEnd_3331549] using wordTrace_append hprefix tailTrace_3331549
  have hstable : (prefixWord ++ tailWord_3331549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331549).length < 2 ^ (prefixWord ++ tailWord_3331549).sum := by decide
  have hdescent : baseEnd_3331549 < baseStart_3331549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331552 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 3]
def baseStart_3331552 : Nat := 118140960795 + 3331552 * 2 ^ 59
def prefixEnd_3331552 : Nat := 4983230072969 + 3 ^ 40 * 3331552 * 2
def baseEnd_3331552 : Nat := 1710687501447854521178477

theorem tailTrace_3331552 : CollatzResearch.WordTrace tailWord_3331552 prefixEnd_3331552 1710687501447854521178477 := by
  unfold tailWord_3331552
  simp only [CollatzResearch.WordTrace]
  refine ⟨60755842013181781313798455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81007789350909041751731273 60755842013181781313798455)
  ·
    refine ⟨91133763019772671970697683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60755842013181781313798455 91133763019772671970697683)
    ·
      refine ⟨136700644529659007956046525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91133763019772671970697683 136700644529659007956046525)
      ·
        refine ⟨51262741698622127983517447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136700644529659007956046525 51262741698622127983517447)
        ·
          refine ⟨76894112547933191975276171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51262741698622127983517447 76894112547933191975276171)
          ·
            refine ⟨115341168821899787962914257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76894112547933191975276171 115341168821899787962914257)
            ·
              refine ⟨86505876616424840972185693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115341168821899787962914257 86505876616424840972185693)
              ·
                refine ⟨32439703731159315364569635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86505876616424840972185693 32439703731159315364569635)
                ·
                  refine ⟨48659555596738973046854453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32439703731159315364569635 48659555596738973046854453)
                  ·
                    refine ⟨4561833337194278723142605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48659555596738973046854453 4561833337194278723142605)
                    ·
                      refine ⟨1710687501447854521178477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4561833337194278723142605 1710687501447854521178477)
                      ·
                        rfl

theorem cell23_3331552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_3331552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331552 prefixEnd_3331552 := by exact prefixLift 3331552
  have htrace : WordTrace (prefixWord ++ tailWord_3331552) baseStart_3331552 baseEnd_3331552 := by
    simpa [prefixWord, tailWord_3331552, baseEnd_3331552] using wordTrace_append hprefix tailTrace_3331552
  have hstable : (prefixWord ++ tailWord_3331552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331552).length < 2 ^ (prefixWord ++ tailWord_3331552).sum := by decide
  have hdescent : baseEnd_3331552 < baseStart_3331552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331576 : List Nat := [2, 1, 2, 1, 1, 7, 1, 3, 5]
def baseStart_3331576 : Nat := 118140960795 + 3331576 * 2 ^ 59
def prefixEnd_3331576 : Nat := 4983230072969 + 3 ^ 40 * 3331576 * 2
def baseEnd_3331576 : Nat := 190077758331506936364263

theorem tailTrace_3331576 : CollatzResearch.WordTrace tailWord_3331576 prefixEnd_3331576 190077758331506936364263 := by
  unfold tailWord_3331576
  simp only [CollatzResearch.WordTrace]
  refine ⟨60756279689138307363235291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81008372918851076484313721 60756279689138307363235291)
  ·
    refine ⟨91134419533707461044852937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60756279689138307363235291 91134419533707461044852937)
    ·
      refine ⟨68350814650280595783639703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91134419533707461044852937 68350814650280595783639703)
      ·
        refine ⟨102526221975420893675459555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68350814650280595783639703 102526221975420893675459555)
        ·
          refine ⟨153789332963131340513189333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102526221975420893675459555 153789332963131340513189333)
          ·
            refine ⟨3604437491323390793277875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 153789332963131340513189333 3604437491323390793277875)
            ·
              refine ⟨5406656236985086189916813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3604437491323390793277875 5406656236985086189916813)
              ·
                refine ⟨2027496088869407321218805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5406656236985086189916813 2027496088869407321218805)
                ·
                  refine ⟨190077758331506936364263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2027496088869407321218805 190077758331506936364263)
                  ·
                    rfl

theorem cell23_3331576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 5].length) (baseStart_3331576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331576 prefixEnd_3331576 := by exact prefixLift 3331576
  have htrace : WordTrace (prefixWord ++ tailWord_3331576) baseStart_3331576 baseEnd_3331576 := by
    simpa [prefixWord, tailWord_3331576, baseEnd_3331576] using wordTrace_append hprefix tailTrace_3331576
  have hstable : (prefixWord ++ tailWord_3331576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331576).length < 2 ^ (prefixWord ++ tailWord_3331576).sum := by decide
  have hdescent : baseEnd_3331576 < baseStart_3331576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331604 : List Nat := [2, 4, 3, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_3331604 : Nat := 118140960795 + 3331604 * 2 ^ 59
def prefixEnd_3331604 : Nat := 4983230072969 + 3 ^ 40 * 3331604 * 2
def baseEnd_3331604 : Nat := 1710714202441888317728239

theorem tailTrace_3331604 : CollatzResearch.WordTrace tailWord_3331604 prefixEnd_3331604 1710714202441888317728239 := by
  unfold tailWord_3331604
  simp only [CollatzResearch.WordTrace]
  refine ⟨60756790311087587754244933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81009053748116783672326577 60756790311087587754244933)
  ·
    refine ⟨11391898183328922703920925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60756790311087587754244933 11391898183328922703920925)
    ·
      refine ⟨4271961818748346013970347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11391898183328922703920925 4271961818748346013970347)
      ·
        refine ⟨6407942728122519020955521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4271961818748346013970347 6407942728122519020955521)
        ·
          refine ⟨4805957046091889265716641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6407942728122519020955521 4805957046091889265716641)
          ·
            refine ⟨3604467784568916949287481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4805957046091889265716641 3604467784568916949287481)
            ·
              refine ⟨2703350838426687711965611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3604467784568916949287481 2703350838426687711965611)
              ·
                refine ⟨4055026257640031567948417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2703350838426687711965611 4055026257640031567948417)
                ·
                  refine ⟨3041269693230023675961313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4055026257640031567948417 3041269693230023675961313)
                  ·
                    refine ⟨2280952269922517756970985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3041269693230023675961313 2280952269922517756970985)
                    ·
                      refine ⟨1710714202441888317728239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2280952269922517756970985 1710714202441888317728239)
                      ·
                        rfl

theorem cell23_3331604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_3331604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331604 prefixEnd_3331604 := by exact prefixLift 3331604
  have htrace : WordTrace (prefixWord ++ tailWord_3331604) baseStart_3331604 baseEnd_3331604 := by
    simpa [prefixWord, tailWord_3331604, baseEnd_3331604] using wordTrace_append hprefix tailTrace_3331604
  have hstable : (prefixWord ++ tailWord_3331604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331604).length < 2 ^ (prefixWord ++ tailWord_3331604).sum := by decide
  have hdescent : baseEnd_3331604 < baseStart_3331604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331626 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_3331626 : Nat := 118140960795 + 3331626 * 2 ^ 59
def prefixEnd_3331626 : Nat := 4983230072969 + 3 ^ 40 * 3331626 * 2
def baseEnd_3331626 : Nat := 1710725499016287231653137

theorem tailTrace_3331626 : CollatzResearch.WordTrace tailWord_3331626 prefixEnd_3331626 1710725499016287231653137 := by
  unfold tailWord_3331626
  simp only [CollatzResearch.WordTrace]
  refine ⟨30378595757023868316447683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81009588685396982177193821 30378595757023868316447683)
  ·
    refine ⟨45567893635535802474671525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30378595757023868316447683 45567893635535802474671525)
    ·
      refine ⟨8543980056662962964000911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45567893635535802474671525 8543980056662962964000911)
      ·
        refine ⟨12815970084994444446001367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8543980056662962964000911 12815970084994444446001367)
        ·
          refine ⟨19223955127491666669002051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12815970084994444446001367 19223955127491666669002051)
          ·
            refine ⟨28835932691237500003503077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19223955127491666669002051 28835932691237500003503077)
            ·
              refine ⟨5406737379607031250656827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28835932691237500003503077 5406737379607031250656827)
              ·
                refine ⟨8110106069410546875985241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5406737379607031250656827 8110106069410546875985241)
                ·
                  refine ⟨6082579552057910156988931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8110106069410546875985241 6082579552057910156988931)
                  ·
                    refine ⟨9123869328086865235483397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6082579552057910156988931 9123869328086865235483397)
                    ·
                      refine ⟨1710725499016287231653137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9123869328086865235483397 1710725499016287231653137)
                      ·
                        rfl

theorem cell23_3331626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_3331626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331626 prefixEnd_3331626 := by exact prefixLift 3331626
  have htrace : WordTrace (prefixWord ++ tailWord_3331626) baseStart_3331626 baseEnd_3331626 := by
    simpa [prefixWord, tailWord_3331626, baseEnd_3331626] using wordTrace_append hprefix tailTrace_3331626
  have hstable : (prefixWord ++ tailWord_3331626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331626).length < 2 ^ (prefixWord ++ tailWord_3331626).sum := by decide
  have hdescent : baseEnd_3331626 < baseStart_3331626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331672 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 1, 3, 7]
def baseStart_3331672 : Nat := 118140960795 + 3331672 * 2 ^ 59
def prefixEnd_3331672 : Nat := 4983230072969 + 3 ^ 40 * 3331672 * 2
def baseEnd_3331672 : Nat := 1710749119126394051677925

theorem tailTrace_3331672 : CollatzResearch.WordTrace tailWord_3331672 prefixEnd_3331672 1710749119126394051677925 := by
  unfold tailWord_3331672
  simp only [CollatzResearch.WordTrace]
  refine ⟨60758030392964411560982635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81010707190619215414643513 60758030392964411560982635)
  ·
    refine ⟨91137045589446617341473953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60758030392964411560982635 91137045589446617341473953)
    ·
      refine ⟨68352784192084963006105465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91137045589446617341473953 68352784192084963006105465)
      ·
        refine ⟨51264588144063722254579099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68352784192084963006105465 51264588144063722254579099)
        ·
          refine ⟨76896882216095583381868649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51264588144063722254579099 76896882216095583381868649)
          ·
            refine ⟨57672661662071687536401487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76896882216095583381868649 57672661662071687536401487)
            ·
              refine ⟨86508992493107531304602231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57672661662071687536401487 86508992493107531304602231)
              ·
                refine ⟨129763488739661296956903347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86508992493107531304602231 129763488739661296956903347)
                ·
                  refine ⟨194645233109491945435355021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129763488739661296956903347 194645233109491945435355021)
                  ·
                    refine ⟨72991962416059479538258133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 194645233109491945435355021 72991962416059479538258133)
                    ·
                      refine ⟨1710749119126394051677925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72991962416059479538258133 1710749119126394051677925)
                      ·
                        rfl

theorem cell23_3331672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_3331672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331672 prefixEnd_3331672 := by exact prefixLift 3331672
  have htrace : WordTrace (prefixWord ++ tailWord_3331672) baseStart_3331672 baseEnd_3331672 := by
    simpa [prefixWord, tailWord_3331672, baseEnd_3331672] using wordTrace_append hprefix tailTrace_3331672
  have hstable : (prefixWord ++ tailWord_3331672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331672).length < 2 ^ (prefixWord ++ tailWord_3331672).sum := by decide
  have hdescent : baseEnd_3331672 < baseStart_3331672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331677 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_3331677 : Nat := 118140960795 + 3331677 * 2 ^ 59
def prefixEnd_3331677 : Nat := 4983230072969 + 3 ^ 40 * 3331677 * 2
def baseEnd_3331677 : Nat := 1710751686529666532115403

theorem tailTrace_3331677 : CollatzResearch.WordTrace tailWord_3331677 prefixEnd_3331677 1710751686529666532115403 := by
  unfold tailWord_3331677
  simp only [CollatzResearch.WordTrace]
  refine ⟨121516243150910708975897285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81010828767273805983931523 121516243150910708975897285)
  ·
    refine ⟨22784295590795757932980741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121516243150910708975897285 22784295590795757932980741)
    ·
      refine ⟨4272055423274204612433889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22784295590795757932980741 4272055423274204612433889)
      ·
        refine ⟨3204041567455653459325417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4272055423274204612433889 3204041567455653459325417)
        ·
          refine ⟨2403031175591740094494063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3204041567455653459325417 2403031175591740094494063)
          ·
            refine ⟨3604546763387610141741095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2403031175591740094494063 3604546763387610141741095)
            ·
              refine ⟨5406820145081415212611643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3604546763387610141741095 5406820145081415212611643)
              ·
                refine ⟨8110230217622122818917465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5406820145081415212611643 8110230217622122818917465)
                ·
                  refine ⟨6082672663216592114188099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8110230217622122818917465 6082672663216592114188099)
                  ·
                    refine ⟨9124008994824888171282149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6082672663216592114188099 9124008994824888171282149)
                    ·
                      refine ⟨1710751686529666532115403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9124008994824888171282149 1710751686529666532115403)
                      ·
                        rfl

theorem cell23_3331677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_3331677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331677 prefixEnd_3331677 := by exact prefixLift 3331677
  have htrace : WordTrace (prefixWord ++ tailWord_3331677) baseStart_3331677 baseEnd_3331677 := by
    simpa [prefixWord, tailWord_3331677, baseEnd_3331677] using wordTrace_append hprefix tailTrace_3331677
  have hstable : (prefixWord ++ tailWord_3331677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331677).length < 2 ^ (prefixWord ++ tailWord_3331677).sum := by decide
  have hdescent : baseEnd_3331677 < baseStart_3331677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331696 : List Nat := [2, 1, 1, 1, 6, 2, 1, 3, 1, 5]
def baseStart_3331696 : Nat := 118140960795 + 3331696 * 2 ^ 59
def prefixEnd_3331696 : Nat := 4983230072969 + 3 ^ 40 * 3331696 * 2
def baseEnd_3331696 : Nat := 570253814220700652592605

theorem tailTrace_3331696 : CollatzResearch.WordTrace tailWord_3331696 prefixEnd_3331696 570253814220700652592605 := by
  unfold tailWord_3331696
  simp only [CollatzResearch.WordTrace]
  refine ⟨60758468068920937610419471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81011290758561250147225961 60758468068920937610419471)
  ·
    refine ⟨91137702103381406415629207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60758468068920937610419471 91137702103381406415629207)
    ·
      refine ⟨136706553155072109623443811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91137702103381406415629207 136706553155072109623443811)
      ·
        refine ⟨205059829732608164435165717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136706553155072109623443811 205059829732608164435165717)
        ·
          refine ⟨9612179518716007707898393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 205059829732608164435165717 9612179518716007707898393)
          ·
            refine ⟨7209134639037005780923795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9612179518716007707898393 7209134639037005780923795)
            ·
              refine ⟨10813701958555508671385693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7209134639037005780923795 10813701958555508671385693)
              ·
                refine ⟨4055138234458315751769635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10813701958555508671385693 4055138234458315751769635)
                ·
                  refine ⟨6082707351687473627654453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4055138234458315751769635 6082707351687473627654453)
                  ·
                    refine ⟨570253814220700652592605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6082707351687473627654453 570253814220700652592605)
                    ·
                      rfl

theorem cell23_3331696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 1, 5].length) (baseStart_3331696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331696 prefixEnd_3331696 := by exact prefixLift 3331696
  have htrace : WordTrace (prefixWord ++ tailWord_3331696) baseStart_3331696 baseEnd_3331696 := by
    simpa [prefixWord, tailWord_3331696, baseEnd_3331696] using wordTrace_append hprefix tailTrace_3331696
  have hstable : (prefixWord ++ tailWord_3331696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331696).length < 2 ^ (prefixWord ++ tailWord_3331696).sum := by decide
  have hdescent : baseEnd_3331696 < baseStart_3331696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331719 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_3331719 : Nat := 118140960795 + 3331719 * 2 ^ 59
def prefixEnd_3331719 : Nat := 4983230072969 + 3 ^ 40 * 3331719 * 2
def baseEnd_3331719 : Nat := 1710773252717155367790209

theorem tailTrace_3331719 : CollatzResearch.WordTrace tailWord_3331719 prefixEnd_3331719 1710773252717155367790209 := by
  unfold tailWord_3331719
  simp only [CollatzResearch.WordTrace]
  refine ⟨121517775016758550148926211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81011850011172366765950807 121517775016758550148926211)
  ·
    refine ⟨182276662525137825223389317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121517775016758550148926211 182276662525137825223389317)
    ·
      refine ⟨34176874223463342229385497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182276662525137825223389317 34176874223463342229385497)
      ·
        refine ⟨25632655667597506672039123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34176874223463342229385497 25632655667597506672039123)
        ·
          refine ⟨38448983501396260008058685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25632655667597506672039123 38448983501396260008058685)
          ·
            refine ⟨14418368813023597503022007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38448983501396260008058685 14418368813023597503022007)
            ·
              refine ⟨21627553219535396254533011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14418368813023597503022007 21627553219535396254533011)
              ·
                refine ⟨32441329829303094381799517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21627553219535396254533011 32441329829303094381799517)
                ·
                  refine ⟨12165498685988660393174819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32441329829303094381799517 12165498685988660393174819)
                  ·
                    refine ⟨18248248028982990589762229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12165498685988660393174819 18248248028982990589762229)
                    ·
                      refine ⟨1710773252717155367790209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18248248028982990589762229 1710773252717155367790209)
                      ·
                        rfl

theorem cell23_3331719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_3331719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331719 prefixEnd_3331719 := by exact prefixLift 3331719
  have htrace : WordTrace (prefixWord ++ tailWord_3331719) baseStart_3331719 baseEnd_3331719 := by
    simpa [prefixWord, tailWord_3331719, baseEnd_3331719] using wordTrace_append hprefix tailTrace_3331719
  have hstable : (prefixWord ++ tailWord_3331719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331719).length < 2 ^ (prefixWord ++ tailWord_3331719).sum := by decide
  have hdescent : baseEnd_3331719 < baseStart_3331719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331726 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 1, 6]
def baseStart_3331726 : Nat := 118140960795 + 3331726 * 2 ^ 59
def prefixEnd_3331726 : Nat := 4983230072969 + 3 ^ 40 * 3331726 * 2
def baseEnd_3331726 : Nat := 570258949027245613467559

theorem tailTrace_3331726 : CollatzResearch.WordTrace tailWord_3331726 prefixEnd_3331726 570258949027245613467559 := by
  unfold tailWord_3331726
  simp only [CollatzResearch.WordTrace]
  refine ⟨15189753790966648793053879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81012020218488793562954021 15189753790966648793053879)
  ·
    refine ⟨22784630686449973189580819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15189753790966648793053879 22784630686449973189580819)
    ·
      refine ⟨34176946029674959784371229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22784630686449973189580819 34176946029674959784371229)
      ·
        refine ⟨12816354761128109919139211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34176946029674959784371229 12816354761128109919139211)
        ·
          refine ⟨19224532141692164878708817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12816354761128109919139211 19224532141692164878708817)
          ·
            refine ⟨14418399106269123659031613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19224532141692164878708817 14418399106269123659031613)
            ·
              refine ⟨5406899664850921372136855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14418399106269123659031613 5406899664850921372136855)
              ·
                refine ⟨8110349497276382058205283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5406899664850921372136855 8110349497276382058205283)
                ·
                  refine ⟨12165524245914573087307925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8110349497276382058205283 12165524245914573087307925)
                  ·
                    refine ⟨570258949027245613467559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12165524245914573087307925 570258949027245613467559)
                    ·
                      rfl

theorem cell23_3331726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_3331726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331726 prefixEnd_3331726 := by exact prefixLift 3331726
  have htrace : WordTrace (prefixWord ++ tailWord_3331726) baseStart_3331726 baseEnd_3331726 := by
    simpa [prefixWord, tailWord_3331726, baseEnd_3331726] using wordTrace_append hprefix tailTrace_3331726
  have hstable : (prefixWord ++ tailWord_3331726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331726).length < 2 ^ (prefixWord ++ tailWord_3331726).sum := by decide
  have hdescent : baseEnd_3331726 < baseStart_3331726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331729 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 4]
def baseStart_3331729 : Nat := 118140960795 + 3331729 * 2 ^ 59
def prefixEnd_3331729 : Nat := 4983230072969 + 3 ^ 40 * 3331729 * 2
def baseEnd_3331729 : Nat := 1710778387523700328665163

theorem tailTrace_3331729 : CollatzResearch.WordTrace tailWord_3331729 prefixEnd_3331729 1710778387523700328665163 := by
  unfold tailWord_3331729
  simp only [CollatzResearch.WordTrace]
  refine ⟨121518139746722321856790241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81012093164481547904526827 121518139746722321856790241)
  ·
    refine ⟨91138604810041741392592681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121518139746722321856790241 91138604810041741392592681)
    ·
      refine ⟨68353953607531306044444511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91138604810041741392592681 68353953607531306044444511)
      ·
        refine ⟨102530930411296959066666767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68353953607531306044444511 102530930411296959066666767)
        ·
          refine ⟨153796395616945438600000151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102530930411296959066666767 153796395616945438600000151)
          ·
            refine ⟨230694593425418157900000227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153796395616945438600000151 230694593425418157900000227)
            ·
              refine ⟨346041890138127236850000341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230694593425418157900000227 346041890138127236850000341)
              ·
                refine ⟨8110356800112357113671883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 346041890138127236850000341 8110356800112357113671883)
                ·
                  refine ⟨12165535200168535670507825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8110356800112357113671883 12165535200168535670507825)
                  ·
                    refine ⟨9124151400126401752880869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12165535200168535670507825 9124151400126401752880869)
                    ·
                      refine ⟨1710778387523700328665163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9124151400126401752880869 1710778387523700328665163)
                      ·
                        rfl

theorem cell23_3331729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_3331729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331729 prefixEnd_3331729 := by exact prefixLift 3331729
  have htrace : WordTrace (prefixWord ++ tailWord_3331729) baseStart_3331729 baseEnd_3331729 := by
    simpa [prefixWord, tailWord_3331729, baseEnd_3331729] using wordTrace_append hprefix tailTrace_3331729
  have hstable : (prefixWord ++ tailWord_3331729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331729).length < 2 ^ (prefixWord ++ tailWord_3331729).sum := by decide
  have hdescent : baseEnd_3331729 < baseStart_3331729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331783 : List Nat := [1, 1, 4, 1, 1, 1, 5, 3, 2, 1, 3]
def baseStart_3331783 : Nat := 118140960795 + 3331783 * 2 ^ 59
def prefixEnd_3331783 : Nat := 4983230072969 + 3 ^ 40 * 3331783 * 2
def baseEnd_3331783 : Nat := 1710806115479043117389915

theorem tailTrace_3331783 : CollatzResearch.WordTrace tailWord_3331783 prefixEnd_3331783 1710806115479043117389915 := by
  unfold tailWord_3331783
  simp only [CollatzResearch.WordTrace]
  refine ⟨121520109288526689079256003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81013406192351126052837335 121520109288526689079256003)
  ·
    refine ⟨182280163932790033618884005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121520109288526689079256003 182280163932790033618884005)
    ·
      refine ⟨34177530737398131303540751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182280163932790033618884005 34177530737398131303540751)
      ·
        refine ⟨51266296106097196955311127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34177530737398131303540751 51266296106097196955311127)
        ·
          refine ⟨76899444159145795432966691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51266296106097196955311127 76899444159145795432966691)
          ·
            refine ⟨115349166238718693149450037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76899444159145795432966691 115349166238718693149450037)
            ·
              refine ⟨10813984334879877482760941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115349166238718693149450037 10813984334879877482760941)
              ·
                refine ⟨4055244125579954056035353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10813984334879877482760941 4055244125579954056035353)
                ·
                  refine ⟨3041433094184965542026515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4055244125579954056035353 3041433094184965542026515)
                  ·
                    refine ⟨4562149641277448313039773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3041433094184965542026515 4562149641277448313039773)
                    ·
                      refine ⟨1710806115479043117389915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4562149641277448313039773 1710806115479043117389915)
                      ·
                        rfl

theorem cell23_3331783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_3331783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331783 prefixEnd_3331783 := by exact prefixLift 3331783
  have htrace : WordTrace (prefixWord ++ tailWord_3331783) baseStart_3331783 baseEnd_3331783 := by
    simpa [prefixWord, tailWord_3331783, baseEnd_3331783] using wordTrace_append hprefix tailTrace_3331783
  have hstable : (prefixWord ++ tailWord_3331783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331783).length < 2 ^ (prefixWord ++ tailWord_3331783).sum := by decide
  have hdescent : baseEnd_3331783 < baseStart_3331783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331793 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 3, 3, 2]
def baseStart_3331793 : Nat := 118140960795 + 3331793 * 2 ^ 59
def prefixEnd_3331793 : Nat := 4983230072969 + 3 ^ 40 * 3331793 * 2
def baseEnd_3331793 : Nat := 1710811250285588078264869

theorem tailTrace_3331793 : CollatzResearch.WordTrace tailWord_3331793 prefixEnd_3331793 1710811250285588078264869 := by
  unfold tailWord_3331793
  simp only [CollatzResearch.WordTrace]
  refine ⟨121520474018490460787120033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81013649345660307191413355 121520474018490460787120033)
  ·
    refine ⟨91140355513867845590340025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121520474018490460787120033 91140355513867845590340025)
    ·
      refine ⟨68355266635400884192755019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91140355513867845590340025 68355266635400884192755019)
      ·
        refine ⟨102532899953101326289132529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68355266635400884192755019 102532899953101326289132529)
        ·
          refine ⟨76899674964825994716849397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102532899953101326289132529 76899674964825994716849397)
          ·
            refine ⟨7209344527952437004704631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76899674964825994716849397 7209344527952437004704631)
            ·
              refine ⟨10814016791928655507056947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7209344527952437004704631 10814016791928655507056947)
              ·
                refine ⟨16221025187892983260585421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10814016791928655507056947 16221025187892983260585421)
                ·
                  refine ⟨6082884445459868722719533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16221025187892983260585421 6082884445459868722719533)
                  ·
                    refine ⟨2281081667047450771019825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6082884445459868722719533 2281081667047450771019825)
                    ·
                      refine ⟨1710811250285588078264869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2281081667047450771019825 1710811250285588078264869)
                      ·
                        rfl

theorem cell23_3331793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 3, 2].length) (baseStart_3331793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331793 prefixEnd_3331793 := by exact prefixLift 3331793
  have htrace : WordTrace (prefixWord ++ tailWord_3331793) baseStart_3331793 baseEnd_3331793 := by
    simpa [prefixWord, tailWord_3331793, baseEnd_3331793] using wordTrace_append hprefix tailTrace_3331793
  have hstable : (prefixWord ++ tailWord_3331793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331793).length < 2 ^ (prefixWord ++ tailWord_3331793).sum := by decide
  have hdescent : baseEnd_3331793 < baseStart_3331793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331826 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 1, 6, 3]
def baseStart_3331826 : Nat := 118140960795 + 3331826 * 2 ^ 59
def prefixEnd_3331826 : Nat := 4983230072969 + 3 ^ 40 * 3331826 * 2
def baseEnd_3331826 : Nat := 1710828195147186449152217

theorem tailTrace_3331826 : CollatzResearch.WordTrace tailWord_3331826 prefixEnd_3331826 1710828195147186449152217 := by
  unfold tailWord_3331826
  simp only [CollatzResearch.WordTrace]
  refine ⟨30380419406842726855767833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81014451751580604948714221 30380419406842726855767833)
  ·
    refine ⟨22785314555132045141825875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30380419406842726855767833 22785314555132045141825875)
    ·
      refine ⟨34177971832698067712738813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22785314555132045141825875 34177971832698067712738813)
      ·
        refine ⟨12816739437261775392277055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34177971832698067712738813 12816739437261775392277055)
        ·
          refine ⟨19225109155892663088415583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12816739437261775392277055 19225109155892663088415583)
          ·
            refine ⟨28837663733838994632623375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19225109155892663088415583 28837663733838994632623375)
            ·
              refine ⟨43256495600758491948935063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28837663733838994632623375 43256495600758491948935063)
              ·
                refine ⟨64884743401137737923402595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43256495600758491948935063 64884743401137737923402595)
                ·
                  refine ⟨97327115101706606885103893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64884743401137737923402595 97327115101706606885103893)
                  ·
                    refine ⟨4562208520392497197739245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97327115101706606885103893 4562208520392497197739245)
                    ·
                      refine ⟨1710828195147186449152217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4562208520392497197739245 1710828195147186449152217)
                      ·
                        rfl

theorem cell23_3331826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_3331826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331826 prefixEnd_3331826 := by exact prefixLift 3331826
  have htrace : WordTrace (prefixWord ++ tailWord_3331826) baseStart_3331826 baseEnd_3331826 := by
    simpa [prefixWord, tailWord_3331826, baseEnd_3331826] using wordTrace_append hprefix tailTrace_3331826
  have hstable : (prefixWord ++ tailWord_3331826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331826).length < 2 ^ (prefixWord ++ tailWord_3331826).sum := by decide
  have hdescent : baseEnd_3331826 < baseStart_3331826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331836 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_3331836 : Nat := 118140960795 + 3331836 * 2 ^ 59
def prefixEnd_3331836 : Nat := 4983230072969 + 3 ^ 40 * 3331836 * 2
def baseEnd_3331836 : Nat := 1710833329953731410027171

theorem tailTrace_3331836 : CollatzResearch.WordTrace tailWord_3331836 prefixEnd_3331836 1710833329953731410027171 := by
  unfold tailWord_3331836
  simp only [CollatzResearch.WordTrace]
  refine ⟨60761021178667339565467681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81014694904889786087290241 60761021178667339565467681)
  ·
    refine ⟨45570765884000504674100761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60761021178667339565467681 45570765884000504674100761)
    ·
      refine ⟨34178074413000378505575571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45570765884000504674100761 34178074413000378505575571)
      ·
        refine ⟨51267111619500567758363357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34178074413000378505575571 51267111619500567758363357)
        ·
          refine ⟨19225166857312712909386259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51267111619500567758363357 19225166857312712909386259)
          ·
            refine ⟨28837750285969069364079389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19225166857312712909386259 28837750285969069364079389)
            ·
              refine ⟨10814156357238401011529771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28837750285969069364079389 10814156357238401011529771)
              ·
                refine ⟨16221234535857601517294657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10814156357238401011529771 16221234535857601517294657)
                ·
                  refine ⟨12165925901893201137970993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16221234535857601517294657 12165925901893201137970993)
                  ·
                    refine ⟨9124444426419900853478245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12165925901893201137970993 9124444426419900853478245)
                    ·
                      refine ⟨1710833329953731410027171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9124444426419900853478245 1710833329953731410027171)
                      ·
                        rfl

theorem cell23_3331836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_3331836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331836 prefixEnd_3331836 := by exact prefixLift 3331836
  have htrace : WordTrace (prefixWord ++ tailWord_3331836) baseStart_3331836 baseEnd_3331836 := by
    simpa [prefixWord, tailWord_3331836, baseEnd_3331836] using wordTrace_append hprefix tailTrace_3331836
  have hstable : (prefixWord ++ tailWord_3331836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331836).length < 2 ^ (prefixWord ++ tailWord_3331836).sum := by decide
  have hdescent : baseEnd_3331836 < baseStart_3331836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331863 : List Nat := [1, 1, 3, 4, 2, 1, 1, 5, 5]
def baseStart_3331863 : Nat := 118140960795 + 3331863 * 2 ^ 59
def prefixEnd_3331863 : Nat := 4983230072969 + 3 ^ 40 * 3331863 * 2
def baseEnd_3331863 : Nat := 190094132659044756043283

theorem tailTrace_3331863 : CollatzResearch.WordTrace tailWord_3331863 prefixEnd_3331863 190094132659044756043283 := by
  unfold tailWord_3331863
  simp only [CollatzResearch.WordTrace]
  refine ⟨121523027128236862742168243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81015351418824575161445495 121523027128236862742168243)
  ·
    refine ⟨182284540692355294113252365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121523027128236862742168243 182284540692355294113252365)
    ·
      refine ⟨68356702759633235292469637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182284540692355294113252365 68356702759633235292469637)
      ·
        refine ⟨12816881767431231617338057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68356702759633235292469637 12816881767431231617338057)
        ·
          refine ⟨9612661325573423713003543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12816881767431231617338057 9612661325573423713003543)
          ·
            refine ⟨14418991988360135569505315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9612661325573423713003543 14418991988360135569505315)
            ·
              refine ⟨21628487982540203354257973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14418991988360135569505315 21628487982540203354257973)
              ·
                refine ⟨2027670748363144064461685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21628487982540203354257973 2027670748363144064461685)
                ·
                  refine ⟨190094132659044756043283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2027670748363144064461685 190094132659044756043283)
                  ·
                    rfl

theorem cell23_3331863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 5].length) (baseStart_3331863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331863 prefixEnd_3331863 := by exact prefixLift 3331863
  have htrace : WordTrace (prefixWord ++ tailWord_3331863) baseStart_3331863 baseEnd_3331863 := by
    simpa [prefixWord, tailWord_3331863, baseEnd_3331863] using wordTrace_append hprefix tailTrace_3331863
  have hstable : (prefixWord ++ tailWord_3331863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331863).length < 2 ^ (prefixWord ++ tailWord_3331863).sum := by decide
  have hdescent : baseEnd_3331863 < baseStart_3331863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331896 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 1, 3, 4]
def baseStart_3331896 : Nat := 118140960795 + 3331896 * 2 ^ 59
def prefixEnd_3331896 : Nat := 4983230072969 + 3 ^ 40 * 3331896 * 2
def baseEnd_3331896 : Nat := 1710864138793001175276895

theorem tailTrace_3331896 : CollatzResearch.WordTrace tailWord_3331896 prefixEnd_3331896 1710864138793001175276895 := by
  unfold tailWord_3331896
  simp only [CollatzResearch.WordTrace]
  refine ⟨60762115368558654689059771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81016153824744872918746361 60762115368558654689059771)
  ·
    refine ⟨91143173052837982033589657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60762115368558654689059771 91143173052837982033589657)
    ·
      refine ⟨68357379789628486525192243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91143173052837982033589657 68357379789628486525192243)
      ·
        refine ⟨102536069684442729787788365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68357379789628486525192243 102536069684442729787788365)
        ·
          refine ⟨38451026131666023670420637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102536069684442729787788365 38451026131666023670420637)
          ·
            refine ⟨14419134799374758876407739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38451026131666023670420637 14419134799374758876407739)
            ·
              refine ⟨21628702199062138314611609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14419134799374758876407739 21628702199062138314611609)
              ·
                refine ⟨16221526649296603735958707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21628702199062138314611609 16221526649296603735958707)
                ·
                  refine ⟨24332289973944905603938061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16221526649296603735958707 24332289973944905603938061)
                  ·
                    refine ⟨9124608740229339601476773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24332289973944905603938061 9124608740229339601476773)
                    ·
                      refine ⟨1710864138793001175276895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9124608740229339601476773 1710864138793001175276895)
                      ·
                        rfl

theorem cell23_3331896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_3331896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331896 prefixEnd_3331896 := by exact prefixLift 3331896
  have htrace : WordTrace (prefixWord ++ tailWord_3331896) baseStart_3331896 baseEnd_3331896 := by
    simpa [prefixWord, tailWord_3331896, baseEnd_3331896] using wordTrace_append hprefix tailTrace_3331896
  have hstable : (prefixWord ++ tailWord_3331896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331896).length < 2 ^ (prefixWord ++ tailWord_3331896).sum := by decide
  have hdescent : baseEnd_3331896 < baseStart_3331896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331910 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_3331910 : Nat := 118140960795 + 3331910 * 2 ^ 59
def prefixEnd_3331910 : Nat := 4983230072969 + 3 ^ 40 * 3331910 * 2
def baseEnd_3331910 : Nat := 570290442507388040167277

theorem tailTrace_3331910 : CollatzResearch.WordTrace tailWord_3331910 prefixEnd_3331910 570290442507388040167277 := by
  unfold tailWord_3331910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3797648167470830930285287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81016494239377726512752789 3797648167470830930285287)
  ·
    refine ⟨5696472251206246395427931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3797648167470830930285287 5696472251206246395427931)
    ·
      refine ⟨8544708376809369593141897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5696472251206246395427931 8544708376809369593141897)
      ·
        refine ⟨6408531282607027194856423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8544708376809369593141897 6408531282607027194856423)
        ·
          refine ⟨9612796923910540792284635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6408531282607027194856423 9612796923910540792284635)
          ·
            refine ⟨14419195385865811188426953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9612796923910540792284635 14419195385865811188426953)
            ·
              refine ⟨10814396539399358391320215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14419195385865811188426953 10814396539399358391320215)
              ·
                refine ⟨16221594809099037586980323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10814396539399358391320215 16221594809099037586980323)
                ·
                  refine ⟨24332392213648556380470485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16221594809099037586980323 24332392213648556380470485)
                  ·
                    refine ⟨570290442507388040167277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24332392213648556380470485 570290442507388040167277)
                    ·
                      rfl

theorem cell23_3331910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_3331910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331910 prefixEnd_3331910 := by exact prefixLift 3331910
  have htrace : WordTrace (prefixWord ++ tailWord_3331910) baseStart_3331910 baseEnd_3331910 := by
    simpa [prefixWord, tailWord_3331910, baseEnd_3331910] using wordTrace_append hprefix tailTrace_3331910
  have hstable : (prefixWord ++ tailWord_3331910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331910).length < 2 ^ (prefixWord ++ tailWord_3331910).sum := by decide
  have hdescent : baseEnd_3331910 < baseStart_3331910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331936 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 8]
def baseStart_3331936 : Nat := 118140960795 + 3331936 * 2 ^ 59
def prefixEnd_3331936 : Nat := 4983230072969 + 3 ^ 40 * 3331936 * 2
def baseEnd_3331936 : Nat := 190098297557686779864079

theorem tailTrace_3331936 : CollatzResearch.WordTrace tailWord_3331936 prefixEnd_3331936 190098297557686779864079 := by
  unfold tailWord_3331936
  simp only [CollatzResearch.WordTrace]
  refine ⟨60762844828486198104787831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81017126437981597473050441 60762844828486198104787831)
  ·
    refine ⟨91144267242729297157181747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60762844828486198104787831 91144267242729297157181747)
    ·
      refine ⟨136716400864093945735772621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91144267242729297157181747 136716400864093945735772621)
      ·
        refine ⟨51268650324035229650914733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136716400864093945735772621 51268650324035229650914733)
        ·
          refine ⟨19225743871513211119093025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51268650324035229650914733 19225743871513211119093025)
          ·
            refine ⟨14419307903634908339319769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19225743871513211119093025 14419307903634908339319769)
            ·
              refine ⟨10814480927726181254489827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14419307903634908339319769 10814480927726181254489827)
              ·
                refine ⟨16221721391589271881734741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10814480927726181254489827 16221721391589271881734741)
                ·
                  refine ⟨190098297557686779864079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16221721391589271881734741 190098297557686779864079)
                  ·
                    rfl

theorem cell23_3331936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 8].length) (baseStart_3331936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331936 prefixEnd_3331936 := by exact prefixLift 3331936
  have htrace : WordTrace (prefixWord ++ tailWord_3331936) baseStart_3331936 baseEnd_3331936 := by
    simpa [prefixWord, tailWord_3331936, baseEnd_3331936] using wordTrace_append hprefix tailTrace_3331936
  have hstable : (prefixWord ++ tailWord_3331936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331936).length < 2 ^ (prefixWord ++ tailWord_3331936).sum := by decide
  have hdescent : baseEnd_3331936 < baseStart_3331936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331963 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 5, 1, 3]
def baseStart_3331963 : Nat := 118140960795 + 3331963 * 2 ^ 59
def prefixEnd_3331963 : Nat := 4983230072969 + 3 ^ 40 * 3331963 * 2
def baseEnd_3331963 : Nat := 1710898541996852413139087

theorem tailTrace_3331963 : CollatzResearch.WordTrace tailWord_3331963 prefixEnd_3331963 1710898541996852413139087 := by
  unfold tailWord_3331963
  simp only [CollatzResearch.WordTrace]
  refine ⟨121526674427874579820808543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81017782951916386547205695 121526674427874579820808543)
  ·
    refine ⟨182290011641811869731212815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121526674427874579820808543 182290011641811869731212815)
    ·
      refine ⟨273435017462717804596819223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182290011641811869731212815 273435017462717804596819223)
      ·
        refine ⟨410152526194076706895228835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273435017462717804596819223 410152526194076706895228835)
        ·
          refine ⟨615228789291115060342843253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410152526194076706895228835 615228789291115060342843253)
          ·
            refine ⟨57677698996042036907141555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 615228789291115060342843253 57677698996042036907141555)
            ·
              refine ⟨86516548494063055360712333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57677698996042036907141555 86516548494063055360712333)
              ·
                refine ⟨32443705685273645760267125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86516548494063055360712333 32443705685273645760267125)
                ·
                  refine ⟨3041597407994404290025043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32443705685273645760267125 3041597407994404290025043)
                  ·
                    refine ⟨4562396111991606435037565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3041597407994404290025043 4562396111991606435037565)
                    ·
                      refine ⟨1710898541996852413139087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4562396111991606435037565 1710898541996852413139087)
                      ·
                        rfl

theorem cell23_3331963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 1, 3].length) (baseStart_3331963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3331963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3331963 prefixEnd_3331963 := by exact prefixLift 3331963
  have htrace : WordTrace (prefixWord ++ tailWord_3331963) baseStart_3331963 baseEnd_3331963 := by
    simpa [prefixWord, tailWord_3331963, baseEnd_3331963] using wordTrace_append hprefix tailTrace_3331963
  have hstable : (prefixWord ++ tailWord_3331963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331963).length < 2 ^ (prefixWord ++ tailWord_3331963).sum := by decide
  have hdescent : baseEnd_3331963 < baseStart_3331963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332003 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 2, 6, 2]
def baseStart_3332003 : Nat := 118140960795 + 3332003 * 2 ^ 59
def prefixEnd_3332003 : Nat := 4983230072969 + 3 ^ 40 * 3332003 * 2
def baseEnd_3332003 : Nat := 1710919081223032256638903

theorem tailTrace_3332003 : CollatzResearch.WordTrace tailWord_3332003 prefixEnd_3332003 1710919081223032256638903 := by
  unfold tailWord_3332003
  simp only [CollatzResearch.WordTrace]
  refine ⟨121528133347729666652264663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81018755565153111101509775 121528133347729666652264663)
  ·
    refine ⟨182292200021594499978396995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121528133347729666652264663 182292200021594499978396995)
    ·
      refine ⟨273438300032391749967595493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182292200021594499978396995 273438300032391749967595493)
      ·
        refine ⟨51269681256073453118924155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273438300032391749967595493 51269681256073453118924155)
        ·
          refine ⟨76904521884110179678386233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51269681256073453118924155 76904521884110179678386233)
          ·
            refine ⟨57678391413082634758789675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76904521884110179678386233 57678391413082634758789675)
            ·
              refine ⟨86517587119623952138184513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57678391413082634758789675 86517587119623952138184513)
              ·
                refine ⟨64888190339717964103638385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86517587119623952138184513 64888190339717964103638385)
                ·
                  refine ⟨48666142754788473077728789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64888190339717964103638385 48666142754788473077728789)
                  ·
                    refine ⟨2281225441630709675518537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48666142754788473077728789 2281225441630709675518537)
                    ·
                      refine ⟨1710919081223032256638903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2281225441630709675518537 1710919081223032256638903)
                      ·
                        rfl

theorem cell23_3332003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_3332003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332003 prefixEnd_3332003 := by exact prefixLift 3332003
  have htrace : WordTrace (prefixWord ++ tailWord_3332003) baseStart_3332003 baseEnd_3332003 := by
    simpa [prefixWord, tailWord_3332003, baseEnd_3332003] using wordTrace_append hprefix tailTrace_3332003
  have hstable : (prefixWord ++ tailWord_3332003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332003).length < 2 ^ (prefixWord ++ tailWord_3332003).sum := by decide
  have hdescent : baseEnd_3332003 < baseStart_3332003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332080 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 3, 3, 2]
def baseStart_3332080 : Nat := 118140960795 + 3332080 * 2 ^ 59
def prefixEnd_3332080 : Nat := 4983230072969 + 3 ^ 40 * 3332080 * 2
def baseEnd_3332080 : Nat := 1710958619233428455376049

theorem tailTrace_3332080 : CollatzResearch.WordTrace tailWord_3332080 prefixEnd_3332080 1710958619233428455376049 := by
  unfold tailWord_3332080
  simp only [CollatzResearch.WordTrace]
  refine ⟨60765470884225354401408847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81020627845633805868545129 60765470884225354401408847)
  ·
    refine ⟨91148206326338031602113271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60765470884225354401408847 91148206326338031602113271)
    ·
      refine ⟨136722309489507047403169907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91148206326338031602113271 136722309489507047403169907)
      ·
        refine ⟨205083464234260571104754861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136722309489507047403169907 205083464234260571104754861)
        ·
          refine ⟨76906299087847714164283073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205083464234260571104754861 76906299087847714164283073)
          ·
            refine ⟨57679724315885785623212305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76906299087847714164283073 57679724315885785623212305)
            ·
              refine ⟨43259793236914339217409229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57679724315885785623212305 43259793236914339217409229)
              ·
                refine ⟨16222422463842877206528461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43259793236914339217409229 16222422463842877206528461)
                ·
                  refine ⟨6083408423941078952448173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16222422463842877206528461 6083408423941078952448173)
                  ·
                    refine ⟨2281278158977904607168065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6083408423941078952448173 2281278158977904607168065)
                    ·
                      refine ⟨1710958619233428455376049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2281278158977904607168065 1710958619233428455376049)
                      ·
                        rfl

theorem cell23_3332080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 3, 3, 2].length) (baseStart_3332080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332080 prefixEnd_3332080 := by exact prefixLift 3332080
  have htrace : WordTrace (prefixWord ++ tailWord_3332080) baseStart_3332080 baseEnd_3332080 := by
    simpa [prefixWord, tailWord_3332080, baseEnd_3332080] using wordTrace_append hprefix tailTrace_3332080
  have hstable : (prefixWord ++ tailWord_3332080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332080).length < 2 ^ (prefixWord ++ tailWord_3332080).sum := by decide
  have hdescent : baseEnd_3332080 < baseStart_3332080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332097 : List Nat := [1, 2, 4, 1, 2, 1, 1, 5, 1, 3, 2]
def baseStart_3332097 : Nat := 118140960795 + 3332097 * 2 ^ 59
def prefixEnd_3332097 : Nat := 4983230072969 + 3 ^ 40 * 3332097 * 2
def baseEnd_3332097 : Nat := 1710967348404554888863471

theorem tailTrace_3332097 : CollatzResearch.WordTrace tailWord_3332097 prefixEnd_3332097 1710967348404554888863471 := by
  unfold tailWord_3332097
  simp only [CollatzResearch.WordTrace]
  refine ⟨121531561809389120706186545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81021041206259413804124363 121531561809389120706186545)
  ·
    refine ⟨91148671357041840529639909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121531561809389120706186545 91148671357041840529639909)
    ·
      refine ⟨17090375879445345099307483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91148671357041840529639909 17090375879445345099307483)
      ·
        refine ⟨25635563819168017648961225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17090375879445345099307483 25635563819168017648961225)
        ·
          refine ⟨19226672864376013236720919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25635563819168017648961225 19226672864376013236720919)
          ·
            refine ⟨28840009296564019855081379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19226672864376013236720919 28840009296564019855081379)
            ·
              refine ⟨43260013944846029782622069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28840009296564019855081379 43260013944846029782622069)
              ·
                refine ⟨4055626307329315292120819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43260013944846029782622069 4055626307329315292120819)
                ·
                  refine ⟨6083439460993972938181229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4055626307329315292120819 6083439460993972938181229)
                  ·
                    refine ⟨2281289797872739851817961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6083439460993972938181229 2281289797872739851817961)
                    ·
                      refine ⟨1710967348404554888863471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2281289797872739851817961 1710967348404554888863471)
                      ·
                        rfl

theorem cell23_3332097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_3332097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332097 prefixEnd_3332097 := by exact prefixLift 3332097
  have htrace : WordTrace (prefixWord ++ tailWord_3332097) baseStart_3332097 baseEnd_3332097 := by
    simpa [prefixWord, tailWord_3332097, baseEnd_3332097] using wordTrace_append hprefix tailTrace_3332097
  have hstable : (prefixWord ++ tailWord_3332097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332097).length < 2 ^ (prefixWord ++ tailWord_3332097).sum := by decide
  have hdescent : baseEnd_3332097 < baseStart_3332097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332143 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 3]
def baseStart_3332143 : Nat := 118140960795 + 3332143 * 2 ^ 59
def prefixEnd_3332143 : Nat := 4983230072969 + 3 ^ 40 * 3332143 * 2
def baseEnd_3332143 : Nat := 1710990968514661708888259

theorem tailTrace_3332143 : CollatzResearch.WordTrace tailWord_3332143 prefixEnd_3332143 1710990968514661708888259 := by
  unfold tailWord_3332143
  simp only [CollatzResearch.WordTrace]
  refine ⟨121533239567222470562361083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81022159711481647041574055 121533239567222470562361083)
  ·
    refine ⟨182299859350833705843541625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121533239567222470562361083 182299859350833705843541625)
    ·
      refine ⟨136724894513125279382656219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182299859350833705843541625 136724894513125279382656219)
      ·
        refine ⟨205087341769687919073984329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136724894513125279382656219 205087341769687919073984329)
        ·
          refine ⟨153815506327265939305488247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205087341769687919073984329 153815506327265939305488247)
          ·
            refine ⟨230723259490898908958232371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153815506327265939305488247 230723259490898908958232371)
            ·
              refine ⟨346084889236348363437348557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230723259490898908958232371 346084889236348363437348557)
              ·
                refine ⟨129781833463630636289005709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346084889236348363437348557 129781833463630636289005709)
                ·
                  refine ⟨48668187548861488608377141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129781833463630636289005709 48668187548861488608377141)
                  ·
                    refine ⟨4562642582705764557035357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48668187548861488608377141 4562642582705764557035357)
                    ·
                      refine ⟨1710990968514661708888259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4562642582705764557035357 1710990968514661708888259)
                      ·
                        rfl

theorem cell23_3332143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 3].length) (baseStart_3332143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332143 prefixEnd_3332143 := by exact prefixLift 3332143
  have htrace : WordTrace (prefixWord ++ tailWord_3332143) baseStart_3332143 baseEnd_3332143 := by
    simpa [prefixWord, tailWord_3332143, baseEnd_3332143] using wordTrace_append hprefix tailTrace_3332143
  have hstable : (prefixWord ++ tailWord_3332143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332143).length < 2 ^ (prefixWord ++ tailWord_3332143).sum := by decide
  have hdescent : baseEnd_3332143 < baseStart_3332143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332148 : List Nat := [2, 5, 1, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_3332148 : Nat := 118140960795 + 3332148 * 2 ^ 59
def prefixEnd_3332148 : Nat := 4983230072969 + 3 ^ 40 * 3332148 * 2
def baseEnd_3332148 : Nat := 1710993535917934189325737

theorem tailTrace_3332148 : CollatzResearch.WordTrace tailWord_3332148 prefixEnd_3332148 1710993535917934189325737 := by
  unfold tailWord_3332148
  simp only [CollatzResearch.WordTrace]
  refine ⟨60766710966102178208146549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81022281288136237610862065 60766710966102178208146549)
  ·
    refine ⟨5696879153072079207013739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60766710966102178208146549 5696879153072079207013739)
    ·
      refine ⟨8545318729608118810520609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5696879153072079207013739 8545318729608118810520609)
      ·
        refine ⟨6408989047206089107890457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8545318729608118810520609 6408989047206089107890457)
        ·
          refine ⟨4806741785404566830917843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6408989047206089107890457 4806741785404566830917843)
          ·
            refine ⟨7210112678106850246376765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4806741785404566830917843 7210112678106850246376765)
            ·
              refine ⟨2703792254290068842391287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7210112678106850246376765 2703792254290068842391287)
              ·
                refine ⟨4055688381435103263586931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2703792254290068842391287 4055688381435103263586931)
                ·
                  refine ⟨6083532572152654895380397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4055688381435103263586931 6083532572152654895380397)
                  ·
                    refine ⟨2281324714557245585767649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6083532572152654895380397 2281324714557245585767649)
                    ·
                      refine ⟨1710993535917934189325737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2281324714557245585767649 1710993535917934189325737)
                      ·
                        rfl

theorem cell23_3332148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_3332148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332148 prefixEnd_3332148 := by exact prefixLift 3332148
  have htrace : WordTrace (prefixWord ++ tailWord_3332148) baseStart_3332148 baseEnd_3332148 := by
    simpa [prefixWord, tailWord_3332148, baseEnd_3332148] using wordTrace_append hprefix tailTrace_3332148
  have hstable : (prefixWord ++ tailWord_3332148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332148).length < 2 ^ (prefixWord ++ tailWord_3332148).sum := by decide
  have hdescent : baseEnd_3332148 < baseStart_3332148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332161 : List Nat := [1, 2, 5, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_3332161 : Nat := 118140960795 + 3332161 * 2 ^ 59
def prefixEnd_3332161 : Nat := 4983230072969 + 3 ^ 40 * 3332161 * 2
def baseEnd_3332161 : Nat := 1711000211166442638463177

theorem tailTrace_3332161 : CollatzResearch.WordTrace tailWord_3332161 prefixEnd_3332161 1711000211166442638463177 := by
  unfold tailWord_3332161
  simp only [CollatzResearch.WordTrace]
  refine ⟨121533896081157259636516337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81022597387438173091010891 121533896081157259636516337)
  ·
    refine ⟨91150422060867944727387253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121533896081157259636516337 91150422060867944727387253)
    ·
      refine ⟨8545352068206369818192555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91150422060867944727387253 8545352068206369818192555)
      ·
        refine ⟨12818028102309554727288833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8545352068206369818192555 12818028102309554727288833)
        ·
          refine ⟨9613521076732166045466625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12818028102309554727288833 9613521076732166045466625)
          ·
            refine ⟨7210140807549124534099969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9613521076732166045466625 7210140807549124534099969)
            ·
              refine ⟨5407605605661843400574977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7210140807549124534099969 5407605605661843400574977)
              ·
                refine ⟨4055704204246382550431233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5407605605661843400574977 4055704204246382550431233)
                ·
                  refine ⟨3041778153184786912823425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4055704204246382550431233 3041778153184786912823425)
                  ·
                    refine ⟨2281333614888590184617569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3041778153184786912823425 2281333614888590184617569)
                    ·
                      refine ⟨1711000211166442638463177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2281333614888590184617569 1711000211166442638463177)
                      ·
                        rfl

theorem cell23_3332161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_3332161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332161 prefixEnd_3332161 := by exact prefixLift 3332161
  have htrace : WordTrace (prefixWord ++ tailWord_3332161) baseStart_3332161 baseEnd_3332161 := by
    simpa [prefixWord, tailWord_3332161, baseEnd_3332161] using wordTrace_append hprefix tailTrace_3332161
  have hstable : (prefixWord ++ tailWord_3332161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332161).length < 2 ^ (prefixWord ++ tailWord_3332161).sum := by decide
  have hdescent : baseEnd_3332161 < baseStart_3332161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332163 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 4, 5]
def baseStart_3332163 : Nat := 118140960795 + 3332163 * 2 ^ 59
def prefixEnd_3332163 : Nat := 4983230072969 + 3 ^ 40 * 3332163 * 2
def baseEnd_3332163 : Nat := 570333746042583876879389

theorem tailTrace_3332163 : CollatzResearch.WordTrace tailWord_3332163 prefixEnd_3332163 570333746042583876879389 := by
  unfold tailWord_3332163
  simp only [CollatzResearch.WordTrace]
  refine ⟨121533969027150013978089143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81022646018100009318726095 121533969027150013978089143)
  ·
    refine ⟨182300953540725020967133715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121533969027150013978089143 182300953540725020967133715)
    ·
      refine ⟨273451430311087531450700573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182300953540725020967133715 273451430311087531450700573)
      ·
        refine ⟨102544286366657824294012715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273451430311087531450700573 102544286366657824294012715)
        ·
          refine ⟨153816429549986736441019073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102544286366657824294012715 153816429549986736441019073)
          ·
            refine ⟨115362322162490052330764305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153816429549986736441019073 115362322162490052330764305)
            ·
              refine ⟨86521741621867539248073229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115362322162490052330764305 86521741621867539248073229)
              ·
                refine ⟨32445653108200327218027461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86521741621867539248073229 32445653108200327218027461)
                ·
                  refine ⟨6083559957787561353380149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32445653108200327218027461 6083559957787561353380149)
                  ·
                    refine ⟨570333746042583876879389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6083559957787561353380149 570333746042583876879389)
                    ·
                      rfl

theorem cell23_3332163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 5].length) (baseStart_3332163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332163 prefixEnd_3332163 := by exact prefixLift 3332163
  have htrace : WordTrace (prefixWord ++ tailWord_3332163) baseStart_3332163 baseEnd_3332163 := by
    simpa [prefixWord, tailWord_3332163, baseEnd_3332163] using wordTrace_append hprefix tailTrace_3332163
  have hstable : (prefixWord ++ tailWord_3332163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332163).length < 2 ^ (prefixWord ++ tailWord_3332163).sum := by decide
  have hdescent : baseEnd_3332163 < baseStart_3332163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332197 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 2, 5]
def baseStart_3332197 : Nat := 118140960795 + 3332197 * 2 ^ 59
def prefixEnd_3332197 : Nat := 4983230072969 + 3 ^ 40 * 3332197 * 2
def baseEnd_3332197 : Nat := 570339565490001499204337

theorem tailTrace_3332197 : CollatzResearch.WordTrace tailWord_3332197 prefixEnd_3332197 570339565490001499204337 := by
  unfold tailWord_3332197
  simp only [CollatzResearch.WordTrace]
  refine ⟨121535209109026837784826845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81023472739351225189884563 121535209109026837784826845)
  ·
    refine ⟨45575703415885064169310067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121535209109026837784826845 45575703415885064169310067)
    ·
      refine ⟨68363555123827596253965101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45575703415885064169310067 68363555123827596253965101)
      ·
        refine ⟨25636333171435348595236913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68363555123827596253965101 25636333171435348595236913)
        ·
          refine ⟨19227249878576511446427685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25636333171435348595236913 19227249878576511446427685)
          ·
            refine ⟨3605109352233095896205191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19227249878576511446427685 3605109352233095896205191)
            ·
              refine ⟨5407664028349643844307787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3605109352233095896205191 5407664028349643844307787)
              ·
                refine ⟨8111496042524465766461681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5407664028349643844307787 8111496042524465766461681)
                ·
                  refine ⟨6083622031893349324846261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8111496042524465766461681 6083622031893349324846261)
                  ·
                    refine ⟨570339565490001499204337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6083622031893349324846261 570339565490001499204337)
                    ·
                      rfl

theorem cell23_3332197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_3332197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332197 prefixEnd_3332197 := by exact prefixLift 3332197
  have htrace : WordTrace (prefixWord ++ tailWord_3332197) baseStart_3332197 baseEnd_3332197 := by
    simpa [prefixWord, tailWord_3332197, baseEnd_3332197] using wordTrace_append hprefix tailTrace_3332197
  have hstable : (prefixWord ++ tailWord_3332197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332197).length < 2 ^ (prefixWord ++ tailWord_3332197).sum := by decide
  have hdescent : baseEnd_3332197 < baseStart_3332197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332217 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 2, 4, 2]
def baseStart_3332217 : Nat := 118140960795 + 3332217 * 2 ^ 59
def prefixEnd_3332217 : Nat := 4983230072969 + 3 ^ 40 * 3332217 * 2
def baseEnd_3332217 : Nat := 1711028966083094419362919

theorem tailTrace_3332217 : CollatzResearch.WordTrace tailWord_3332217 prefixEnd_3332217 1711028966083094419362919 := by
  unfold tailWord_3332217
  simp only [CollatzResearch.WordTrace]
  refine ⟨121535938568954381200554905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81023959045969587467036603 121535938568954381200554905)
  ·
    refine ⟨91151953926715785900416179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121535938568954381200554905 91151953926715785900416179)
    ·
      refine ⟨136727930890073678850624269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91151953926715785900416179 136727930890073678850624269)
      ·
        refine ⟨51272974083777629568984101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136727930890073678850624269 51272974083777629568984101)
        ·
          refine ⟨9613682640708305544184519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51272974083777629568984101 9613682640708305544184519)
          ·
            refine ⟨14420523961062458316276779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9613682640708305544184519 14420523961062458316276779)
            ·
              refine ⟨21630785941593687474415169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14420523961062458316276779 21630785941593687474415169)
              ·
                refine ⟨16223089456195265605811377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21630785941593687474415169 16223089456195265605811377)
                ·
                  refine ⟨12167317092146449204358533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16223089456195265605811377 12167317092146449204358533)
                  ·
                    refine ⟨2281371954777459225817225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12167317092146449204358533 2281371954777459225817225)
                    ·
                      refine ⟨1711028966083094419362919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2281371954777459225817225 1711028966083094419362919)
                      ·
                        rfl

theorem cell23_3332217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_3332217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332217 prefixEnd_3332217 := by exact prefixLift 3332217
  have htrace : WordTrace (prefixWord ++ tailWord_3332217) baseStart_3332217 baseEnd_3332217 := by
    simpa [prefixWord, tailWord_3332217, baseEnd_3332217] using wordTrace_append hprefix tailTrace_3332217
  have hstable : (prefixWord ++ tailWord_3332217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332217).length < 2 ^ (prefixWord ++ tailWord_3332217).sum := by decide
  have hdescent : baseEnd_3332217 < baseStart_3332217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332227 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 3, 4]
def baseStart_3332227 : Nat := 118140960795 + 3332227 * 2 ^ 59
def prefixEnd_3332227 : Nat := 4983230072969 + 3 ^ 40 * 3332227 * 2
def baseEnd_3332227 : Nat := 570344700296546460079291

theorem tailTrace_3332227 : CollatzResearch.WordTrace tailWord_3332227 prefixEnd_3332227 570344700296546460079291 := by
  unfold tailWord_3332227
  simp only [CollatzResearch.WordTrace]
  refine ⟨121536303298918152908418935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81024202199278768605612623 121536303298918152908418935)
  ·
    refine ⟨182304454948377229362628403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121536303298918152908418935 182304454948377229362628403)
    ·
      refine ⟨273456682422565844043942605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182304454948377229362628403 273456682422565844043942605)
      ·
        refine ⟨102546255908462191516478477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273456682422565844043942605 102546255908462191516478477)
        ·
          refine ⟨38454845965673321818679429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102546255908462191516478477 38454845965673321818679429)
          ·
            refine ⟨7210283618563747841002393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38454845965673321818679429 7210283618563747841002393)
            ·
              refine ⟨5407712713922810880751795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7210283618563747841002393 5407712713922810880751795)
              ·
                refine ⟨8111569070884216321127693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5407712713922810880751795 8111569070884216321127693)
                ·
                  refine ⟨3041838401581581120422885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8111569070884216321127693 3041838401581581120422885)
                  ·
                    refine ⟨570344700296546460079291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3041838401581581120422885 570344700296546460079291)
                    ·
                      rfl

theorem cell23_3332227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 4].length) (baseStart_3332227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332227 prefixEnd_3332227 := by exact prefixLift 3332227
  have htrace : WordTrace (prefixWord ++ tailWord_3332227) baseStart_3332227 baseEnd_3332227 := by
    simpa [prefixWord, tailWord_3332227, baseEnd_3332227] using wordTrace_append hprefix tailTrace_3332227
  have hstable : (prefixWord ++ tailWord_3332227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332227).length < 2 ^ (prefixWord ++ tailWord_3332227).sum := by decide
  have hdescent : baseEnd_3332227 < baseStart_3332227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332243 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 6]
def baseStart_3332243 : Nat := 118140960795 + 3332243 * 2 ^ 59
def prefixEnd_3332243 : Nat := 4983230072969 + 3 ^ 40 * 3332243 * 2
def baseEnd_3332243 : Nat := 1711042316580111317637799

theorem tailTrace_3332243 : CollatzResearch.WordTrace tailWord_3332243 prefixEnd_3332243 1711042316580111317637799 := by
  unfold tailWord_3332243
  simp only [CollatzResearch.WordTrace]
  refine ⟨121536886866860187641001383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81024591244573458427334255 121536886866860187641001383)
  ·
    refine ⟨182305330300290281461502075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121536886866860187641001383 182305330300290281461502075)
    ·
      refine ⟨273457995450435422192253113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182305330300290281461502075 273457995450435422192253113)
      ·
        refine ⟨205093496587826566644189835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273457995450435422192253113 205093496587826566644189835)
        ·
          refine ⟨307640244881739849966284753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205093496587826566644189835 307640244881739849966284753)
          ·
            refine ⟨230730183661304887474713565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307640244881739849966284753 230730183661304887474713565)
            ·
              refine ⟨86523818872989332803017587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230730183661304887474713565 86523818872989332803017587)
              ·
                refine ⟨129785728309483999204526381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86523818872989332803017587 129785728309483999204526381)
                ·
                  refine ⟨48669648116056499701697393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129785728309483999204526381 48669648116056499701697393)
                  ·
                    refine ⟨36502236087042374776273045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48669648116056499701697393 36502236087042374776273045)
                    ·
                      refine ⟨1711042316580111317637799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36502236087042374776273045 1711042316580111317637799)
                      ·
                        rfl

theorem cell23_3332243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_3332243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332243 prefixEnd_3332243 := by exact prefixLift 3332243
  have htrace : WordTrace (prefixWord ++ tailWord_3332243) baseStart_3332243 baseEnd_3332243 := by
    simpa [prefixWord, tailWord_3332243, baseEnd_3332243] using wordTrace_append hprefix tailTrace_3332243
  have hstable : (prefixWord ++ tailWord_3332243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332243).length < 2 ^ (prefixWord ++ tailWord_3332243).sum := by decide
  have hdescent : baseEnd_3332243 < baseStart_3332243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332317 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 3, 6]
def baseStart_3332317 : Nat := 118140960795 + 3332317 * 2 ^ 59
def prefixEnd_3332317 : Nat := 4983230072969 + 3 ^ 40 * 3332317 * 2
def baseEnd_3332317 : Nat := 570360104716181342704153

theorem tailTrace_3332317 : CollatzResearch.WordTrace tailWord_3332317 prefixEnd_3332317 570360104716181342704153 := by
  unfold tailWord_3332317
  simp only [CollatzResearch.WordTrace]
  refine ⟨121539585868592098279195205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81026390579061398852796803 121539585868592098279195205)
  ·
    refine ⟨22788672350361018427349101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121539585868592098279195205 22788672350361018427349101)
    ·
      refine ⟨8545752131385381910255913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22788672350361018427349101 8545752131385381910255913)
      ·
        refine ⟨6409314098539036432691935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8545752131385381910255913 6409314098539036432691935)
        ·
          refine ⟨9613971147808554649037903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6409314098539036432691935 9613971147808554649037903)
          ·
            refine ⟨14420956721712831973556855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9613971147808554649037903 14420956721712831973556855)
            ·
              refine ⟨21631435082569247960335283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14420956721712831973556855 21631435082569247960335283)
              ·
                refine ⟨32447152623853871940502925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21631435082569247960335283 32447152623853871940502925)
                ·
                  refine ⟨12167682233945201977688597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32447152623853871940502925 12167682233945201977688597)
                  ·
                    refine ⟨570360104716181342704153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12167682233945201977688597 570360104716181342704153)
                    ·
                      rfl

theorem cell23_3332317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_3332317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332317 prefixEnd_3332317 := by exact prefixLift 3332317
  have htrace : WordTrace (prefixWord ++ tailWord_3332317) baseStart_3332317 baseEnd_3332317 := by
    simpa [prefixWord, tailWord_3332317, baseEnd_3332317] using wordTrace_append hprefix tailTrace_3332317
  have hstable : (prefixWord ++ tailWord_3332317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332317).length < 2 ^ (prefixWord ++ tailWord_3332317).sum := by decide
  have hdescent : baseEnd_3332317 < baseStart_3332317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332354 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_3332354 : Nat := 118140960795 + 3332354 * 2 ^ 59
def prefixEnd_3332354 : Nat := 4983230072969 + 3 ^ 40 * 3332354 * 2
def baseEnd_3332354 : Nat := 1711099312932760383349789

theorem tailTrace_3332354 : CollatzResearch.WordTrace tailWord_3332354 prefixEnd_3332354 1711099312932760383349789 := by
  unfold tailWord_3332354
  simp only [CollatzResearch.WordTrace]
  refine ⟨30385233842364513399573029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81027290246305369065528077 30385233842364513399573029)
  ·
    refine ⟨5697231345443346262419943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30385233842364513399573029 5697231345443346262419943)
    ·
      refine ⟨8545847018165019393629915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5697231345443346262419943 8545847018165019393629915)
      ·
        refine ⟨12818770527247529090444873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8545847018165019393629915 12818770527247529090444873)
        ·
          refine ⟨9614077895435646817833655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12818770527247529090444873 9614077895435646817833655)
          ·
            refine ⟨14421116843153470226750483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9614077895435646817833655 14421116843153470226750483)
            ·
              refine ⟨21631675264730205340125725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14421116843153470226750483 21631675264730205340125725)
              ·
                refine ⟨8111878224273827002547147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21631675264730205340125725 8111878224273827002547147)
                ·
                  refine ⟨12167817336410740503820721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8111878224273827002547147 12167817336410740503820721)
                  ·
                    refine ⟨9125863002308055377865541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12167817336410740503820721 9125863002308055377865541)
                    ·
                      refine ⟨1711099312932760383349789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9125863002308055377865541 1711099312932760383349789)
                      ·
                        rfl

theorem cell23_3332354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_3332354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332354 prefixEnd_3332354 := by exact prefixLift 3332354
  have htrace : WordTrace (prefixWord ++ tailWord_3332354) baseStart_3332354 baseEnd_3332354 := by
    simpa [prefixWord, tailWord_3332354, baseEnd_3332354] using wordTrace_append hprefix tailTrace_3332354
  have hstable : (prefixWord ++ tailWord_3332354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332354).length < 2 ^ (prefixWord ++ tailWord_3332354).sum := by decide
  have hdescent : baseEnd_3332354 < baseStart_3332354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332378 : List Nat := [3, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3]
def baseStart_3332378 : Nat := 118140960795 + 3332378 * 2 ^ 59
def prefixEnd_3332378 : Nat := 4983230072969 + 3 ^ 40 * 3332378 * 2
def baseEnd_3332378 : Nat := 1711111636468468289449679

theorem tailTrace_3332378 : CollatzResearch.WordTrace tailWord_3332378 prefixEnd_3332378 1711111636468468289449679 := by
  unfold tailWord_3332378
  simp only [CollatzResearch.WordTrace]
  refine ⟨30385452680342776424291447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81027873814247403798110525 30385452680342776424291447)
  ·
    refine ⟨45578179020514164636437171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30385452680342776424291447 45578179020514164636437171)
    ·
      refine ⟨68367268530771246954655757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45578179020514164636437171 68367268530771246954655757)
      ·
        refine ⟨25637725699039217607995909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68367268530771246954655757 25637725699039217607995909)
        ·
          refine ⟨4807073568569853301499233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25637725699039217607995909 4807073568569853301499233)
          ·
            refine ⟨3605305176427389976124425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4807073568569853301499233 3605305176427389976124425)
            ·
              refine ⟨2703978882320542482093319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3605305176427389976124425 2703978882320542482093319)
              ·
                refine ⟨4055968323480813723139979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2703978882320542482093319 4055968323480813723139979)
                ·
                  refine ⟨6083952485221220584709969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4055968323480813723139979 6083952485221220584709969)
                  ·
                    refine ⟨4562964363915915438532477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6083952485221220584709969 4562964363915915438532477)
                    ·
                      refine ⟨1711111636468468289449679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4562964363915915438532477 1711111636468468289449679)
                      ·
                        rfl

theorem cell23_3332378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_3332378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332378 prefixEnd_3332378 := by exact prefixLift 3332378
  have htrace : WordTrace (prefixWord ++ tailWord_3332378) baseStart_3332378 baseEnd_3332378 := by
    simpa [prefixWord, tailWord_3332378, baseEnd_3332378] using wordTrace_append hprefix tailTrace_3332378
  have hstable : (prefixWord ++ tailWord_3332378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332378).length < 2 ^ (prefixWord ++ tailWord_3332378).sum := by decide
  have hdescent : baseEnd_3332378 < baseStart_3332378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332400 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 5]
def baseStart_3332400 : Nat := 118140960795 + 3332400 * 2 ^ 59
def prefixEnd_3332400 : Nat := 4983230072969 + 3 ^ 40 * 3332400 * 2
def baseEnd_3332400 : Nat := 1711122933042867203374577

theorem tailTrace_3332400 : CollatzResearch.WordTrace tailWord_3332400 prefixEnd_3332400 1711122933042867203374577 := by
  unfold tailWord_3332400
  simp only [CollatzResearch.WordTrace]
  refine ⟨60771306563645701727233327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81028408751527602302977769 60771306563645701727233327)
  ·
    refine ⟨91156959845468552590849991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60771306563645701727233327 91156959845468552590849991)
    ·
      refine ⟨136735439768202828886274987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91156959845468552590849991 136735439768202828886274987)
      ·
        refine ⟨205103159652304243329412481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136735439768202828886274987 205103159652304243329412481)
        ·
          refine ⟨153827369739228182497059361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205103159652304243329412481 153827369739228182497059361)
          ·
            refine ⟨115370527304421136872794521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153827369739228182497059361 115370527304421136872794521)
            ·
              refine ⟨86527895478315852654595891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115370527304421136872794521 86527895478315852654595891)
              ·
                refine ⟨129791843217473778981893837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86527895478315852654595891 129791843217473778981893837)
                ·
                  refine ⟨48671941206552667118210189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129791843217473778981893837 48671941206552667118210189)
                  ·
                    refine ⟨18251977952457250169328821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48671941206552667118210189 18251977952457250169328821)
                    ·
                      refine ⟨1711122933042867203374577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18251977952457250169328821 1711122933042867203374577)
                      ·
                        rfl

theorem cell23_3332400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_3332400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332400 prefixEnd_3332400 := by exact prefixLift 3332400
  have htrace : WordTrace (prefixWord ++ tailWord_3332400) baseStart_3332400 baseEnd_3332400 := by
    simpa [prefixWord, tailWord_3332400, baseEnd_3332400] using wordTrace_append hprefix tailTrace_3332400
  have hstable : (prefixWord ++ tailWord_3332400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332400).length < 2 ^ (prefixWord ++ tailWord_3332400).sum := by decide
  have hdescent : baseEnd_3332400 < baseStart_3332400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332447 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 3]
def baseStart_3332447 : Nat := 118140960795 + 3332447 * 2 ^ 59
def prefixEnd_3332447 : Nat := 4983230072969 + 3 ^ 40 * 3332447 * 2
def baseEnd_3332447 : Nat := 1711147066633628519486861

theorem tailTrace_3332447 : CollatzResearch.WordTrace tailWord_3332447 prefixEnd_3332447 1711147066633628519486861 := by
  unfold tailWord_3332447
  simp only [CollatzResearch.WordTrace]
  refine ⟨121544327358121130481427595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81029551572080753654285063 121544327358121130481427595)
  ·
    refine ⟨182316491037181695722141393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121544327358121130481427595 182316491037181695722141393)
    ·
      refine ⟨136737368277886271791606045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182316491037181695722141393 136737368277886271791606045)
      ·
        refine ⟨51276513104207351921852267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136737368277886271791606045 51276513104207351921852267)
        ·
          refine ⟨76914769656311027882778401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51276513104207351921852267 76914769656311027882778401)
          ·
            refine ⟨57686077242233270912083801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76914769656311027882778401 57686077242233270912083801)
            ·
              refine ⟨43264557931674953184062851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57686077242233270912083801 43264557931674953184062851)
              ·
                refine ⟨64896836897512429776094277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43264557931674953184062851 64896836897512429776094277)
                ·
                  refine ⟨12168156918283580583017677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64896836897512429776094277 12168156918283580583017677)
                  ·
                    refine ⟨4563058844356342718631629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12168156918283580583017677 4563058844356342718631629)
                    ·
                      refine ⟨1711147066633628519486861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4563058844356342718631629 1711147066633628519486861)
                      ·
                        rfl

theorem cell23_3332447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_3332447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332447 prefixEnd_3332447 := by exact prefixLift 3332447
  have htrace : WordTrace (prefixWord ++ tailWord_3332447) baseStart_3332447 baseEnd_3332447 := by
    simpa [prefixWord, tailWord_3332447, baseEnd_3332447] using wordTrace_append hprefix tailTrace_3332447
  have hstable : (prefixWord ++ tailWord_3332447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332447).length < 2 ^ (prefixWord ++ tailWord_3332447).sum := by decide
  have hdescent : baseEnd_3332447 < baseStart_3332447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332484 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 2, 5]
def baseStart_3332484 : Nat := 118140960795 + 3332484 * 2 ^ 59
def prefixEnd_3332484 : Nat := 4983230072969 + 3 ^ 40 * 3332484 * 2
def baseEnd_3332484 : Nat := 570388688472614958241397

theorem tailTrace_3332484 : CollatzResearch.WordTrace tailWord_3332484 prefixEnd_3332484 570388688472614958241397 := by
  unfold tailWord_3332484
  simp only [CollatzResearch.WordTrace]
  refine ⟨60772838429493542900262253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81030451239324723867016337 60772838429493542900262253)
  ·
    refine ⟨22789814411060078587598345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60772838429493542900262253 22789814411060078587598345)
    ·
      refine ⟨17092360808295058940698759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22789814411060078587598345 17092360808295058940698759)
      ·
        refine ⟨25638541212442588411048139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17092360808295058940698759 25638541212442588411048139)
        ·
          refine ⟨38457811818663882616572209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25638541212442588411048139 38457811818663882616572209)
          ·
            refine ⟨28843358863997911962429157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38457811818663882616572209 28843358863997911962429157)
            ·
              refine ⟨5408129786999608492955467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28843358863997911962429157 5408129786999608492955467)
              ·
                refine ⟨8112194680499412739433201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5408129786999608492955467 8112194680499412739433201)
                ·
                  refine ⟨6084146010374559554574901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8112194680499412739433201 6084146010374559554574901)
                  ·
                    refine ⟨570388688472614958241397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6084146010374559554574901 570388688472614958241397)
                    ·
                      rfl

theorem cell23_3332484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_3332484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332484 prefixEnd_3332484 := by exact prefixLift 3332484
  have htrace : WordTrace (prefixWord ++ tailWord_3332484) baseStart_3332484 baseEnd_3332484 := by
    simpa [prefixWord, tailWord_3332484, baseEnd_3332484] using wordTrace_append hprefix tailTrace_3332484
  have hstable : (prefixWord ++ tailWord_3332484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332484).length < 2 ^ (prefixWord ++ tailWord_3332484).sum := by decide
  have hdescent : baseEnd_3332484 < baseStart_3332484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332494 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3332494 : Nat := 118140960795 + 3332494 * 2 ^ 59
def prefixEnd_3332494 : Nat := 4983230072969 + 3 ^ 40 * 3332494 * 2
def baseEnd_3332494 : Nat := 1711171200224389835599145

theorem tailTrace_3332494 : CollatzResearch.WordTrace tailWord_3332494 prefixEnd_3332494 1711171200224389835599145 := by
  unfold tailWord_3332494
  simp only [CollatzResearch.WordTrace]
  refine ⟨15193255198618857188548567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81030694392633905005592357 15193255198618857188548567)
  ·
    refine ⟨22789882797928285782822851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15193255198618857188548567 22789882797928285782822851)
    ·
      refine ⟨34184824196892428674234277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22789882797928285782822851 34184824196892428674234277)
      ·
        refine ⟨6409654536917330376418927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34184824196892428674234277 6409654536917330376418927)
        ·
          refine ⟨9614481805375995564628391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6409654536917330376418927 9614481805375995564628391)
          ·
            refine ⟨14421722708063993346942587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9614481805375995564628391 14421722708063993346942587)
            ·
              refine ⟨21632584062095990020413881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14421722708063993346942587 21632584062095990020413881)
              ·
                refine ⟨16224438046571992515310411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21632584062095990020413881 16224438046571992515310411)
                ·
                  refine ⟨24336657069857988772965617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16224438046571992515310411 24336657069857988772965617)
                  ·
                    refine ⟨18252492802393491579724213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24336657069857988772965617 18252492802393491579724213)
                    ·
                      refine ⟨1711171200224389835599145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18252492802393491579724213 1711171200224389835599145)
                      ·
                        rfl

theorem cell23_3332494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3332494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332494 prefixEnd_3332494 := by exact prefixLift 3332494
  have htrace : WordTrace (prefixWord ++ tailWord_3332494) baseStart_3332494 baseEnd_3332494 := by
    simpa [prefixWord, tailWord_3332494, baseEnd_3332494] using wordTrace_append hprefix tailTrace_3332494
  have hstable : (prefixWord ++ tailWord_3332494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332494).length < 2 ^ (prefixWord ++ tailWord_3332494).sum := by decide
  have hdescent : baseEnd_3332494 < baseStart_3332494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332541 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 2, 2, 3]
def baseStart_3332541 : Nat := 118140960795 + 3332541 * 2 ^ 59
def prefixEnd_3332541 : Nat := 4983230072969 + 3 ^ 40 * 3332541 * 2
def baseEnd_3332541 : Nat := 1711195333815151151711429

theorem tailTrace_3332541 : CollatzResearch.WordTrace tailWord_3332541 prefixEnd_3332541 1711195333815151151711429 := by
  unfold tailWord_3332541
  simp only [CollatzResearch.WordTrace]
  refine ⟨121547755819780584535349477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81031837213187056356899651 121547755819780584535349477)
  ·
    refine ⟨22790204216208859600378027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121547755819780584535349477 22790204216208859600378027)
    ·
      refine ⟨34185306324313289400567041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22790204216208859600378027 34185306324313289400567041)
      ·
        refine ⟨25638979743234967050425281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34185306324313289400567041 25638979743234967050425281)
        ·
          refine ⟨19229234807426225287818961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25638979743234967050425281 19229234807426225287818961)
          ·
            refine ⟨14421926105569668965864221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19229234807426225287818961 14421926105569668965864221)
            ·
              refine ⟨5408222289588625862199083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14421926105569668965864221 5408222289588625862199083)
              ·
                refine ⟨8112333434382938793298625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5408222289588625862199083 8112333434382938793298625)
                ·
                  refine ⟨6084250075787204094973969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8112333434382938793298625 6084250075787204094973969)
                  ·
                    refine ⟨4563187556840403071230477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6084250075787204094973969 4563187556840403071230477)
                    ·
                      refine ⟨1711195333815151151711429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4563187556840403071230477 1711195333815151151711429)
                      ·
                        rfl

theorem cell23_3332541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_3332541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332541 prefixEnd_3332541 := by exact prefixLift 3332541
  have htrace : WordTrace (prefixWord ++ tailWord_3332541) baseStart_3332541 baseEnd_3332541 := by
    simpa [prefixWord, tailWord_3332541, baseEnd_3332541] using wordTrace_append hprefix tailTrace_3332541
  have hstable : (prefixWord ++ tailWord_3332541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332541).length < 2 ^ (prefixWord ++ tailWord_3332541).sum := by decide
  have hdescent : baseEnd_3332541 < baseStart_3332541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332564 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_3332564 : Nat := 118140960795 + 3332564 * 2 ^ 59
def prefixEnd_3332564 : Nat := 4983230072969 + 3 ^ 40 * 3332564 * 2
def baseEnd_3332564 : Nat := 1711207143870204561723823

theorem tailTrace_3332564 : CollatzResearch.WordTrace tailWord_3332564 prefixEnd_3332564 1711207143870204561723823 := by
  unfold tailWord_3332564
  simp only [CollatzResearch.WordTrace]
  refine ⟨60774297349348629731718373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81032396465798172975624497 60774297349348629731718373)
  ·
    refine ⟨11395180753002868074697195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60774297349348629731718373 11395180753002868074697195)
    ·
      refine ⟨17092771129504302112045793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11395180753002868074697195 17092771129504302112045793)
      ·
        refine ⟨12819578347128226584034345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17092771129504302112045793 12819578347128226584034345)
        ·
          refine ⟨9614683760346169938025759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12819578347128226584034345 9614683760346169938025759)
          ·
            refine ⟨14422025640519254907038639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9614683760346169938025759 14422025640519254907038639)
            ·
              refine ⟨21633038460778882360557959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14422025640519254907038639 21633038460778882360557959)
              ·
                refine ⟨32449557691168323540836939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21633038460778882360557959 32449557691168323540836939)
                ·
                  refine ⟨48674336536752485311255409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32449557691168323540836939 48674336536752485311255409)
                  ·
                    refine ⟨36505752402564363983441557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48674336536752485311255409 36505752402564363983441557)
                    ·
                      refine ⟨1711207143870204561723823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36505752402564363983441557 1711207143870204561723823)
                      ·
                        rfl

theorem cell23_3332564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_3332564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332564 prefixEnd_3332564 := by exact prefixLift 3332564
  have htrace : WordTrace (prefixWord ++ tailWord_3332564) baseStart_3332564 baseEnd_3332564 := by
    simpa [prefixWord, tailWord_3332564, baseEnd_3332564] using wordTrace_append hprefix tailTrace_3332564
  have hstable : (prefixWord ++ tailWord_3332564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332564).length < 2 ^ (prefixWord ++ tailWord_3332564).sum := by decide
  have hdescent : baseEnd_3332564 < baseStart_3332564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332598 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2]
def baseStart_3332598 : Nat := 118140960795 + 3332598 * 2 ^ 59
def prefixEnd_3332598 : Nat := 4983230072969 + 3 ^ 40 * 3332598 * 2
def baseEnd_3332598 : Nat := 1711224602212457428698667

theorem tailTrace_3332598 : CollatzResearch.WordTrace tailWord_3332598 prefixEnd_3332598 1711224602212457428698667 := by
  unfold tailWord_3332598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7596864673785880204385903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81033223187049388846782965 7596864673785880204385903)
  ·
    refine ⟨11395297010678820306578855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7596864673785880204385903 11395297010678820306578855)
    ·
      refine ⟨17092945516018230459868283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11395297010678820306578855 17092945516018230459868283)
      ·
        refine ⟨25639418274027345689802425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17092945516018230459868283 25639418274027345689802425)
        ·
          refine ⟨19229563705520509267351819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25639418274027345689802425 19229563705520509267351819)
          ·
            refine ⟨28844345558280763901027729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19229563705520509267351819 28844345558280763901027729)
            ·
              refine ⟨21633259168710572925770797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28844345558280763901027729 21633259168710572925770797)
              ·
                refine ⟨8112472188266464847164049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21633259168710572925770797 8112472188266464847164049)
                ·
                  refine ⟨6084354141199848635373037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8112472188266464847164049 6084354141199848635373037)
                  ·
                    refine ⟨2281632802949943238264889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6084354141199848635373037 2281632802949943238264889)
                    ·
                      refine ⟨1711224602212457428698667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2281632802949943238264889 1711224602212457428698667)
                      ·
                        rfl

theorem cell23_3332598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_3332598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332598 prefixEnd_3332598 := by exact prefixLift 3332598
  have htrace : WordTrace (prefixWord ++ tailWord_3332598) baseStart_3332598 baseEnd_3332598 := by
    simpa [prefixWord, tailWord_3332598, baseEnd_3332598] using wordTrace_append hprefix tailTrace_3332598
  have hstable : (prefixWord ++ tailWord_3332598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332598).length < 2 ^ (prefixWord ++ tailWord_3332598).sum := by decide
  have hdescent : baseEnd_3332598 < baseStart_3332598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332622 : List Nat := [4, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3]
def baseStart_3332622 : Nat := 118140960795 + 3332622 * 2 ^ 59
def prefixEnd_3332622 : Nat := 4983230072969 + 3 ^ 40 * 3332622 * 2
def baseEnd_3332622 : Nat := 1711236925748165334798557

theorem tailTrace_3332622 : CollatzResearch.WordTrace tailWord_3332622 prefixEnd_3332622 1711236925748165334798557 := by
  unfold tailWord_3332622
  simp only [CollatzResearch.WordTrace]
  refine ⟨15193838766560891921131015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81033806754991423579365413 15193838766560891921131015)
  ·
    refine ⟨22790758149841337881696523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15193838766560891921131015 22790758149841337881696523)
    ·
      refine ⟨34186137224762006822544785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22790758149841337881696523 34186137224762006822544785)
      ·
        refine ⟨25639602918571505116908589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34186137224762006822544785 25639602918571505116908589)
        ·
          refine ⟨9614851094464314418840721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25639602918571505116908589 9614851094464314418840721)
          ·
            refine ⟨7211138320848235814130541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9614851094464314418840721 7211138320848235814130541)
            ·
              refine ⟨2704176870318088430298953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7211138320848235814130541 2704176870318088430298953)
              ·
                refine ⟨2028132652738566322724215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2704176870318088430298953 2028132652738566322724215)
                ·
                  refine ⟨3042198979107849484086323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2028132652738566322724215 3042198979107849484086323)
                  ·
                    refine ⟨4563298468661774226129485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3042198979107849484086323 4563298468661774226129485)
                    ·
                      refine ⟨1711236925748165334798557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4563298468661774226129485 1711236925748165334798557)
                      ·
                        rfl

theorem cell23_3332622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_3332622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332622 prefixEnd_3332622 := by exact prefixLift 3332622
  have htrace : WordTrace (prefixWord ++ tailWord_3332622) baseStart_3332622 baseEnd_3332622 := by
    simpa [prefixWord, tailWord_3332622, baseEnd_3332622] using wordTrace_append hprefix tailTrace_3332622
  have hstable : (prefixWord ++ tailWord_3332622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332622).length < 2 ^ (prefixWord ++ tailWord_3332622).sum := by decide
  have hdescent : baseEnd_3332622 < baseStart_3332622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332648 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_3332648 : Nat := 118140960795 + 3332648 * 2 ^ 59
def prefixEnd_3332648 : Nat := 4983230072969 + 3 ^ 40 * 3332648 * 2
def baseEnd_3332648 : Nat := 1711250276245182233073437

theorem tailTrace_3332648 : CollatzResearch.WordTrace tailWord_3332648 prefixEnd_3332648 1711250276245182233073437 := by
  unfold tailWord_3332648
  simp only [CollatzResearch.WordTrace]
  refine ⟨60775829215196470904747299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81034438953595294539663065 60775829215196470904747299)
  ·
    refine ⟨91163743822794706357120949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60775829215196470904747299 91163743822794706357120949)
    ·
      refine ⟨8546600983387003720980089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91163743822794706357120949 8546600983387003720980089)
      ·
        refine ⟨6409950737540252790735067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8546600983387003720980089 6409950737540252790735067)
        ·
          refine ⟨9614926106310379186102601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6409950737540252790735067 9614926106310379186102601)
          ·
            refine ⟨7211194579732784389576951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9614926106310379186102601 7211194579732784389576951)
            ·
              refine ⟨10816791869599176584365427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7211194579732784389576951 10816791869599176584365427)
              ·
                refine ⟨16225187804398764876548141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10816791869599176584365427 16225187804398764876548141)
                ·
                  refine ⟨6084445426649536828705553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16225187804398764876548141 6084445426649536828705553)
                  ·
                    refine ⟨4563334069987152621529165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6084445426649536828705553 4563334069987152621529165)
                    ·
                      refine ⟨1711250276245182233073437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4563334069987152621529165 1711250276245182233073437)
                      ·
                        rfl

theorem cell23_3332648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_3332648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332648 prefixEnd_3332648 := by exact prefixLift 3332648
  have htrace : WordTrace (prefixWord ++ tailWord_3332648) baseStart_3332648 baseEnd_3332648 := by
    simpa [prefixWord, tailWord_3332648, baseEnd_3332648] using wordTrace_append hprefix tailTrace_3332648
  have hstable : (prefixWord ++ tailWord_3332648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332648).length < 2 ^ (prefixWord ++ tailWord_3332648).sum := by decide
  have hdescent : baseEnd_3332648 < baseStart_3332648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332661 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_3332661 : Nat := 118140960795 + 3332661 * 2 ^ 59
def prefixEnd_3332661 : Nat := 4983230072969 + 3 ^ 40 * 3332661 * 2
def baseEnd_3332661 : Nat := 1711256951493690682210877

theorem tailTrace_3332661 : CollatzResearch.WordTrace tailWord_3332661 prefixEnd_3332661 1711256951493690682210877 := by
  unfold tailWord_3332661
  simp only [CollatzResearch.WordTrace]
  refine ⟨121552132579345845029717837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81034755052897230019811891 121552132579345845029717837)
  ·
    refine ⟨45582049717254691886144189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121552132579345845029717837 45582049717254691886144189)
    ·
      refine ⟨17093268643970509457304071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45582049717254691886144189 17093268643970509457304071)
      ·
        refine ⟨25639902965955764185956107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17093268643970509457304071 25639902965955764185956107)
        ·
          refine ⟨38459854448933646278934161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25639902965955764185956107 38459854448933646278934161)
          ·
            refine ⟨28844890836700234709200621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38459854448933646278934161 28844890836700234709200621)
            ·
              refine ⟨10816834063762588015950233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28844890836700234709200621 10816834063762588015950233)
              ·
                refine ⟨8112625547821941011962675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10816834063762588015950233 8112625547821941011962675)
                ·
                  refine ⟨12168938321732911517944013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8112625547821941011962675 12168938321732911517944013)
                  ·
                    refine ⟨4563351870649841819229005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12168938321732911517944013 4563351870649841819229005)
                    ·
                      refine ⟨1711256951493690682210877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4563351870649841819229005 1711256951493690682210877)
                      ·
                        rfl

theorem cell23_3332661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_3332661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332661 prefixEnd_3332661 := by exact prefixLift 3332661
  have htrace : WordTrace (prefixWord ++ tailWord_3332661) baseStart_3332661 baseEnd_3332661 := by
    simpa [prefixWord, tailWord_3332661, baseEnd_3332661] using wordTrace_append hprefix tailTrace_3332661
  have hstable : (prefixWord ++ tailWord_3332661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332661).length < 2 ^ (prefixWord ++ tailWord_3332661).sum := by decide
  have hdescent : baseEnd_3332661 < baseStart_3332661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332679 : List Nat := [1, 1, 4, 1, 4, 3, 2, 2, 1, 2, 2]
def baseStart_3332679 : Nat := 118140960795 + 3332679 * 2 ^ 59
def prefixEnd_3332679 : Nat := 4983230072969 + 3 ^ 40 * 3332679 * 2
def baseEnd_3332679 : Nat := 1711266194145471611785795

theorem tailTrace_3332679 : CollatzResearch.WordTrace tailWord_3332679 prefixEnd_3332679 1711266194145471611785795 := by
  unfold tailWord_3332679
  simp only [CollatzResearch.WordTrace]
  refine ⟨121552789093280634103873091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81035192728853756069248727 121552789093280634103873091)
  ·
    refine ⟨182329183639920951155809637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121552789093280634103873091 182329183639920951155809637)
    ·
      refine ⟨34186721932485178341714307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182329183639920951155809637 34186721932485178341714307)
      ·
        refine ⟨51280082898727767512571461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34186721932485178341714307 51280082898727767512571461)
        ·
          refine ⟨9615015543511456408607149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51280082898727767512571461 9615015543511456408607149)
          ·
            refine ⟨3605630828816796153227681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9615015543511456408607149 3605630828816796153227681)
            ·
              refine ⟨2704223121612597114920761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3605630828816796153227681 2704223121612597114920761)
              ·
                refine ⟨2028167341209447836190571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2704223121612597114920761 2028167341209447836190571)
                ·
                  refine ⟨3042251011814171754285857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2028167341209447836190571 3042251011814171754285857)
                  ·
                    refine ⟨2281688258860628815714393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3042251011814171754285857 2281688258860628815714393)
                    ·
                      refine ⟨1711266194145471611785795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2281688258860628815714393 1711266194145471611785795)
                      ·
                        rfl

theorem cell23_3332679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_3332679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332679 prefixEnd_3332679 := by exact prefixLift 3332679
  have htrace : WordTrace (prefixWord ++ tailWord_3332679) baseStart_3332679 baseEnd_3332679 := by
    simpa [prefixWord, tailWord_3332679, baseEnd_3332679] using wordTrace_append hprefix tailTrace_3332679
  have hstable : (prefixWord ++ tailWord_3332679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332679).length < 2 ^ (prefixWord ++ tailWord_3332679).sum := by decide
  have hdescent : baseEnd_3332679 < baseStart_3332679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332684 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 1, 5, 4]
def baseStart_3332684 : Nat := 118140960795 + 3332684 * 2 ^ 59
def prefixEnd_3332684 : Nat := 4983230072969 + 3 ^ 40 * 3332684 * 2
def baseEnd_3332684 : Nat := 1711268761548744092223271

theorem tailTrace_3332684 : CollatzResearch.WordTrace tailWord_3332684 prefixEnd_3332684 1711268761548744092223271 := by
  unfold tailWord_3332684
  simp only [CollatzResearch.WordTrace]
  refine ⟨60776485729131259978902553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81035314305508346638536737 60776485729131259978902553)
  ·
    refine ⟨45582364296848444984176915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60776485729131259978902553 45582364296848444984176915)
    ·
      refine ⟨68373546445272667476265373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45582364296848444984176915 68373546445272667476265373)
      ·
        refine ⟨25640079916977250303599515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68373546445272667476265373 25640079916977250303599515)
        ·
          refine ⟨38460119875465875455399273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25640079916977250303599515 38460119875465875455399273)
          ·
            refine ⟨28845089906599406591549455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38460119875465875455399273 28845089906599406591549455)
            ·
              refine ⟨43267634859899109887324183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28845089906599406591549455 43267634859899109887324183)
              ·
                refine ⟨64901452289848664830986275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43267634859899109887324183 64901452289848664830986275)
                ·
                  refine ⟨97352178434772997246479413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64901452289848664830986275 97352178434772997246479413)
                  ·
                    refine ⟨9126766728259968491857445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97352178434772997246479413 9126766728259968491857445)
                    ·
                      refine ⟨1711268761548744092223271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9126766728259968491857445 1711268761548744092223271)
                      ·
                        rfl

theorem cell23_3332684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_3332684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332684 prefixEnd_3332684 := by exact prefixLift 3332684
  have htrace : WordTrace (prefixWord ++ tailWord_3332684) baseStart_3332684 baseEnd_3332684 := by
    simpa [prefixWord, tailWord_3332684, baseEnd_3332684] using wordTrace_append hprefix tailTrace_3332684
  have hstable : (prefixWord ++ tailWord_3332684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332684).length < 2 ^ (prefixWord ++ tailWord_3332684).sum := by decide
  have hdescent : baseEnd_3332684 < baseStart_3332684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332702 : List Nat := [4, 4, 1, 2, 1, 1, 3, 7]
def baseStart_3332702 : Nat := 118140960795 + 3332702 * 2 ^ 59
def prefixEnd_3332702 : Nat := 4983230072969 + 3 ^ 40 * 3332702 * 2
def baseEnd_3332702 : Nat := 63380666822241667474007

theorem tailTrace_3332702 : CollatzResearch.WordTrace tailWord_3332702 prefixEnd_3332702 63380666822241667474007 := by
  unfold tailWord_3332702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15194203496524663628995045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81035751981464872687973573 15194203496524663628995045)
  ·
    refine ⟨2848913155598374430436571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15194203496524663628995045 2848913155598374430436571)
    ·
      refine ⟨4273369733397561645654857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2848913155598374430436571 4273369733397561645654857)
      ·
        refine ⟨3205027300048171234241143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4273369733397561645654857 3205027300048171234241143)
        ·
          refine ⟨4807540950072256851361715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3205027300048171234241143 4807540950072256851361715)
          ·
            refine ⟨7211311425108385277042573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4807540950072256851361715 7211311425108385277042573)
            ·
              refine ⟨2704241784415644478890965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7211311425108385277042573 2704241784415644478890965)
              ·
                refine ⟨63380666822241667474007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2704241784415644478890965 63380666822241667474007)
                ·
                  rfl

theorem cell23_3332702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 7].length) (baseStart_3332702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332702 prefixEnd_3332702 := by exact prefixLift 3332702
  have htrace : WordTrace (prefixWord ++ tailWord_3332702) baseStart_3332702 baseEnd_3332702 := by
    simpa [prefixWord, tailWord_3332702, baseEnd_3332702] using wordTrace_append hprefix tailTrace_3332702
  have hstable : (prefixWord ++ tailWord_3332702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332702).length < 2 ^ (prefixWord ++ tailWord_3332702).sum := by decide
  have hdescent : baseEnd_3332702 < baseStart_3332702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332704 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 5]
def baseStart_3332704 : Nat := 118140960795 + 3332704 * 2 ^ 59
def prefixEnd_3332704 : Nat := 4983230072969 + 3 ^ 40 * 3332704 * 2
def baseEnd_3332704 : Nat := 1711279031161834013973179

theorem tailTrace_3332704 : CollatzResearch.WordTrace tailWord_3332704 prefixEnd_3332704 1711279031161834013973179 := by
  unfold tailWord_3332704
  simp only [CollatzResearch.WordTrace]
  refine ⟨60776850459095031686766583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81035800612126708915688777 60776850459095031686766583)
  ·
    refine ⟨91165275688642547530149875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60776850459095031686766583 91165275688642547530149875)
    ·
      refine ⟨136747913532963821295224813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91165275688642547530149875 136747913532963821295224813)
      ·
        refine ⟨51280467574861432985709305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136747913532963821295224813 51280467574861432985709305)
        ·
          refine ⟨38460350681146074739281979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51280467574861432985709305 38460350681146074739281979)
          ·
            refine ⟨57690526021719112108922969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38460350681146074739281979 57690526021719112108922969)
            ·
              refine ⟨43267894516289334081692227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57690526021719112108922969 43267894516289334081692227)
              ·
                refine ⟨64901841774434001122538341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43267894516289334081692227 64901841774434001122538341)
                ·
                  refine ⟨12169095332706375210475939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64901841774434001122538341 12169095332706375210475939)
                  ·
                    refine ⟨18253642999059562815713909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12169095332706375210475939 18253642999059562815713909)
                    ·
                      refine ⟨1711279031161834013973179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18253642999059562815713909 1711279031161834013973179)
                      ·
                        rfl

theorem cell23_3332704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_3332704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332704 prefixEnd_3332704 := by exact prefixLift 3332704
  have htrace : WordTrace (prefixWord ++ tailWord_3332704) baseStart_3332704 baseEnd_3332704 := by
    simpa [prefixWord, tailWord_3332704, baseEnd_3332704] using wordTrace_append hprefix tailTrace_3332704
  have hstable : (prefixWord ++ tailWord_3332704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332704).length < 2 ^ (prefixWord ++ tailWord_3332704).sum := by decide
  have hdescent : baseEnd_3332704 < baseStart_3332704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332741 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 7]
def baseStart_3332741 : Nat := 118140960795 + 3332741 * 2 ^ 59
def prefixEnd_3332741 : Nat := 4983230072969 + 3 ^ 40 * 3332741 * 2
def baseEnd_3332741 : Nat := 190144225549561152134501

theorem tailTrace_3332741 : CollatzResearch.WordTrace tailWord_3332741 prefixEnd_3332741 190144225549561152134501 := by
  unfold tailWord_3332741
  simp only [CollatzResearch.WordTrace]
  refine ⟨121555050419056018692630077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81036700279370679128420051 121555050419056018692630077)
  ·
    refine ⟨45583143907146007009736279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121555050419056018692630077 45583143907146007009736279)
    ·
      refine ⟨68374715860719010514604419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45583143907146007009736279 68374715860719010514604419)
      ·
        refine ⟨102562073791078515771906629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68374715860719010514604419 102562073791078515771906629)
        ·
          refine ⟨19230388835827221707232493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102562073791078515771906629 19230388835827221707232493)
          ·
            refine ⟨7211395813435208140212185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19230388835827221707232493 7211395813435208140212185)
            ·
              refine ⟨5408546860076406105159139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7211395813435208140212185 5408546860076406105159139)
              ·
                refine ⟨8112820290114609157738709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5408546860076406105159139 8112820290114609157738709)
                ·
                  refine ⟨190144225549561152134501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8112820290114609157738709 190144225549561152134501)
                  ·
                    rfl

theorem cell23_3332741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 7].length) (baseStart_3332741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332741 prefixEnd_3332741 := by exact prefixLift 3332741
  have htrace : WordTrace (prefixWord ++ tailWord_3332741) baseStart_3332741 baseEnd_3332741 := by
    simpa [prefixWord, tailWord_3332741, baseEnd_3332741] using wordTrace_append hprefix tailTrace_3332741
  have hstable : (prefixWord ++ tailWord_3332741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332741).length < 2 ^ (prefixWord ++ tailWord_3332741).sum := by decide
  have hdescent : baseEnd_3332741 < baseStart_3332741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332861 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 5, 5]
def baseStart_3332861 : Nat := 118140960795 + 3332861 * 2 ^ 59
def prefixEnd_3332861 : Nat := 4983230072969 + 3 ^ 40 * 3332861 * 2
def baseEnd_3332861 : Nat := 570453215874863299903319

theorem tailTrace_3332861 : CollatzResearch.WordTrace tailWord_3332861 prefixEnd_3332861 570453215874863299903319 := by
  unfold tailWord_3332861
  simp only [CollatzResearch.WordTrace]
  refine ⟨121559427178621279186998437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81039618119080852791332291 121559427178621279186998437)
  ·
    refine ⟨22792392595991489847562207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121559427178621279186998437 22792392595991489847562207)
    ·
      refine ⟨34188588893987234771343311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22792392595991489847562207 34188588893987234771343311)
      ·
        refine ⟨51282883340980852157014967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34188588893987234771343311 51282883340980852157014967)
        ·
          refine ⟨76924325011471278235522451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51282883340980852157014967 76924325011471278235522451)
          ·
            refine ⟨115386487517206917353283677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76924325011471278235522451 115386487517206917353283677)
            ·
              refine ⟨43269932818952594007481379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115386487517206917353283677 43269932818952594007481379)
              ·
                refine ⟨64904899228428891011222069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43269932818952594007481379 64904899228428891011222069)
                ·
                  refine ⟨6084834302665208532302069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64904899228428891011222069 6084834302665208532302069)
                  ·
                    refine ⟨570453215874863299903319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6084834302665208532302069 570453215874863299903319)
                    ·
                      rfl

theorem cell23_3332861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_3332861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332861 prefixEnd_3332861 := by exact prefixLift 3332861
  have htrace : WordTrace (prefixWord ++ tailWord_3332861) baseStart_3332861 baseEnd_3332861 := by
    simpa [prefixWord, tailWord_3332861, baseEnd_3332861] using wordTrace_append hprefix tailTrace_3332861
  have hstable : (prefixWord ++ tailWord_3332861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332861).length < 2 ^ (prefixWord ++ tailWord_3332861).sum := by decide
  have hdescent : baseEnd_3332861 < baseStart_3332861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332878 : List Nat := [4, 1, 1, 2, 1, 1, 1, 6, 1, 5]
def baseStart_3332878 : Nat := 118140960795 + 3332878 * 2 ^ 59
def prefixEnd_3332878 : Nat := 4983230072969 + 3 ^ 40 * 3332878 * 2
def baseEnd_3332878 : Nat := 570456125598572111065793

theorem tailTrace_3332878 : CollatzResearch.WordTrace tailWord_3332878 prefixEnd_3332878 570456125598572111065793 := by
  unfold tailWord_3332878
  simp only [CollatzResearch.WordTrace]
  refine ⟨15195005902444961386295911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81040031479706460726911525 15195005902444961386295911)
  ·
    refine ⟨22792508853667442079443867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15195005902444961386295911 22792508853667442079443867)
    ·
      refine ⟨34188763280501163119165801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22792508853667442079443867 34188763280501163119165801)
      ·
        refine ⟨25641572460375872339374351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34188763280501163119165801 25641572460375872339374351)
        ·
          refine ⟨38462358690563808509061527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25641572460375872339374351 38462358690563808509061527)
          ·
            refine ⟨57693538035845712763592291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38462358690563808509061527 57693538035845712763592291)
            ·
              refine ⟨86540307053768569145388437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57693538035845712763592291 86540307053768569145388437)
              ·
                refine ⟨4056576893145401678690083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86540307053768569145388437 4056576893145401678690083)
                ·
                  refine ⟨6084865339718102518035125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4056576893145401678690083 6084865339718102518035125)
                  ·
                    refine ⟨570456125598572111065793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6084865339718102518035125 570456125598572111065793)
                    ·
                      rfl

theorem cell23_3332878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_3332878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332878 prefixEnd_3332878 := by exact prefixLift 3332878
  have htrace : WordTrace (prefixWord ++ tailWord_3332878) baseStart_3332878 baseEnd_3332878 := by
    simpa [prefixWord, tailWord_3332878, baseEnd_3332878] using wordTrace_append hprefix tailTrace_3332878
  have hstable : (prefixWord ++ tailWord_3332878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332878).length < 2 ^ (prefixWord ++ tailWord_3332878).sum := by decide
  have hdescent : baseEnd_3332878 < baseStart_3332878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332892 : List Nat := [2, 2, 3, 1, 1, 3, 1, 5, 1, 1, 3]
def baseStart_3332892 : Nat := 118140960795 + 3332892 * 2 ^ 59
def prefixEnd_3332892 : Nat := 4983230072969 + 3 ^ 40 * 3332892 * 2
def baseEnd_3332892 : Nat := 1711375565524879278422315

theorem tailTrace_3332892 : CollatzResearch.WordTrace tailWord_3332892 prefixEnd_3332892 1711375565524879278422315 := by
  unfold tailWord_3332892
  simp only [CollatzResearch.WordTrace]
  refine ⟨60780278920754485740688465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81040371894339314320917953 60780278920754485740688465)
  ·
    refine ⟨45585209190565864305516349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60780278920754485740688465 45585209190565864305516349)
    ·
      refine ⟨17094453446462199114568631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45585209190565864305516349 17094453446462199114568631)
      ·
        refine ⟨25641680169693298671852947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17094453446462199114568631 25641680169693298671852947)
        ·
          refine ⟨38462520254539948007779421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25641680169693298671852947 38462520254539948007779421)
          ·
            refine ⟨14423445095452480502917283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38462520254539948007779421 14423445095452480502917283)
            ·
              refine ⟨21635167643178720754375925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14423445095452480502917283 21635167643178720754375925)
              ·
                refine ⟨2028296966548005070722743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21635167643178720754375925 2028296966548005070722743)
                ·
                  refine ⟨3042445449822007606084115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2028296966548005070722743 3042445449822007606084115)
                  ·
                    refine ⟨4563668174733011409126173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3042445449822007606084115 4563668174733011409126173)
                    ·
                      refine ⟨1711375565524879278422315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4563668174733011409126173 1711375565524879278422315)
                      ·
                        rfl

theorem cell23_3332892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_3332892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332892 prefixEnd_3332892 := by exact prefixLift 3332892
  have htrace : WordTrace (prefixWord ++ tailWord_3332892) baseStart_3332892 baseEnd_3332892 := by
    simpa [prefixWord, tailWord_3332892, baseEnd_3332892] using wordTrace_append hprefix tailTrace_3332892
  have hstable : (prefixWord ++ tailWord_3332892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332892).length < 2 ^ (prefixWord ++ tailWord_3332892).sum := by decide
  have hdescent : baseEnd_3332892 < baseStart_3332892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332895 : List Nat := [1, 1, 2, 4, 2, 2, 4, 1, 1, 5]
def baseStart_3332895 : Nat := 118140960795 + 3332895 * 2 ^ 59
def prefixEnd_3332895 : Nat := 4983230072969 + 3 ^ 40 * 3332895 * 2
def baseEnd_3332895 : Nat := 570459035322280922228267

theorem tailTrace_3332895 : CollatzResearch.WordTrace tailWord_3332895 prefixEnd_3332895 570459035322280922228267 := by
  unfold tailWord_3332895
  simp only [CollatzResearch.WordTrace]
  refine ⟨121560667260498102993736139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81040444840332068662490759 121560667260498102993736139)
  ·
    refine ⟨182341000890747154490604209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121560667260498102993736139 182341000890747154490604209)
    ·
      refine ⟨136755750668060365867953157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182341000890747154490604209 136755750668060365867953157)
      ·
        refine ⟨25641703250261318600241217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136755750668060365867953157 25641703250261318600241217)
        ·
          refine ⟨19231277437695988950180913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25641703250261318600241217 19231277437695988950180913)
          ·
            refine ⟨14423458078271991712635685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19231277437695988950180913 14423458078271991712635685)
            ·
              refine ⟨2704398389675998446119191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14423458078271991712635685 2704398389675998446119191)
              ·
                refine ⟨4056597584513997669178787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2704398389675998446119191 4056597584513997669178787)
                ·
                  refine ⟨6084896376770996503768181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4056597584513997669178787 6084896376770996503768181)
                  ·
                    refine ⟨570459035322280922228267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6084896376770996503768181 570459035322280922228267)
                    ·
                      rfl

theorem cell23_3332895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 1, 5].length) (baseStart_3332895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332895 prefixEnd_3332895 := by exact prefixLift 3332895
  have htrace : WordTrace (prefixWord ++ tailWord_3332895) baseStart_3332895 baseEnd_3332895 := by
    simpa [prefixWord, tailWord_3332895, baseEnd_3332895] using wordTrace_append hprefix tailTrace_3332895
  have hstable : (prefixWord ++ tailWord_3332895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332895).length < 2 ^ (prefixWord ++ tailWord_3332895).sum := by decide
  have hdescent : baseEnd_3332895 < baseStart_3332895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332908 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 4, 4]
def baseStart_3332908 : Nat := 118140960795 + 3332908 * 2 ^ 59
def prefixEnd_3332908 : Nat := 4983230072969 + 3 ^ 40 * 3332908 * 2
def baseEnd_3332908 : Nat := 570461260405117071940747

theorem tailTrace_3332908 : CollatzResearch.WordTrace tailWord_3332908 prefixEnd_3332908 570461260405117071940747 := by
  unfold tailWord_3332908
  simp only [CollatzResearch.WordTrace]
  refine ⟨60780570704725503106979689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81040760939634004142639585 60780570704725503106979689)
  ·
    refine ⟨45585428028544127330234767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60780570704725503106979689 45585428028544127330234767)
    ·
      refine ⟨68378142042816190995352151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45585428028544127330234767 68378142042816190995352151)
      ·
        refine ⟨102567213064224286493028227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68378142042816190995352151 102567213064224286493028227)
        ·
          refine ⟨153850819596336429739542341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102567213064224286493028227 153850819596336429739542341)
          ·
            refine ⟨28847028674313080576164189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153850819596336429739542341 28847028674313080576164189)
            ·
              refine ⟨10817635752867405216061571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28847028674313080576164189 10817635752867405216061571)
              ·
                refine ⟨16226453629301107824092357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10817635752867405216061571 16226453629301107824092357)
                ·
                  refine ⟨3042460055493957717017317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16226453629301107824092357 3042460055493957717017317)
                  ·
                    refine ⟨570461260405117071940747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3042460055493957717017317 570461260405117071940747)
                    ·
                      rfl

theorem cell23_3332908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_3332908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332908 prefixEnd_3332908 := by exact prefixLift 3332908
  have htrace : WordTrace (prefixWord ++ tailWord_3332908) baseStart_3332908 baseEnd_3332908 := by
    simpa [prefixWord, tailWord_3332908, baseEnd_3332908] using wordTrace_append hprefix tailTrace_3332908
  have hstable : (prefixWord ++ tailWord_3332908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332908).length < 2 ^ (prefixWord ++ tailWord_3332908).sum := by decide
  have hdescent : baseEnd_3332908 < baseStart_3332908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3332965 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 4, 1, 3]
def baseStart_3332965 : Nat := 118140960795 + 3332965 * 2 ^ 59
def prefixEnd_3332965 : Nat := 4983230072969 + 3 ^ 40 * 3332965 * 2
def baseEnd_3332965 : Nat := 1711413049612657492809479

theorem tailTrace_3332965 : CollatzResearch.WordTrace tailWord_3332965 prefixEnd_3332965 1711413049612657492809479 := by
  unfold tailWord_3332965
  simp only [CollatzResearch.WordTrace]
  refine ⟨121563220370244504948784349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81042146913496336632522899 121563220370244504948784349)
  ·
    refine ⟨45586207638841689355794131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121563220370244504948784349 45586207638841689355794131)
    ·
      refine ⟨68379311458262534033691197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45586207638841689355794131 68379311458262534033691197)
      ·
        refine ⟨25642241796848450262634199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68379311458262534033691197 25642241796848450262634199)
        ·
          refine ⟨38463362695272675393951299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25642241796848450262634199 38463362695272675393951299)
          ·
            refine ⟨57695044042909013090926949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38463362695272675393951299 57695044042909013090926949)
            ·
              refine ⟨10817820758045439954548803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57695044042909013090926949 10817820758045439954548803)
              ·
                refine ⟨16226731137068159931823205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10817820758045439954548803 16226731137068159931823205)
                ·
                  refine ⟨3042512088200279987216851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16226731137068159931823205 3042512088200279987216851)
                  ·
                    refine ⟨4563768132300419980825277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3042512088200279987216851 4563768132300419980825277)
                    ·
                      refine ⟨1711413049612657492809479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4563768132300419980825277 1711413049612657492809479)
                      ·
                        rfl

theorem cell23_3332965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_3332965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3332965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3332965 prefixEnd_3332965 := by exact prefixLift 3332965
  have htrace : WordTrace (prefixWord ++ tailWord_3332965) baseStart_3332965 baseEnd_3332965 := by
    simpa [prefixWord, tailWord_3332965, baseEnd_3332965] using wordTrace_append hprefix tailTrace_3332965
  have hstable : (prefixWord ++ tailWord_3332965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3332965).length < 2 ^ (prefixWord ++ tailWord_3332965).sum := by decide
  have hdescent : baseEnd_3332965 < baseStart_3332965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3332965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333011 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 11]
def baseStart_3333011 : Nat := 118140960795 + 3333011 * 2 ^ 59
def prefixEnd_3333011 : Nat := 4983230072969 + 3 ^ 40 * 3333011 * 2
def baseEnd_3333011 : Nat := 190159629969196034759363

theorem tailTrace_3333011 : CollatzResearch.WordTrace tailWord_3333011 prefixEnd_3333011 190159629969196034759363 := by
  unfold tailWord_3333011
  simp only [CollatzResearch.WordTrace]
  refine ⟨121564898128077854804958887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81043265418718569869972591 121564898128077854804958887)
  ·
    refine ⟨182347347192116782207438331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121564898128077854804958887 182347347192116782207438331)
    ·
      refine ⟨273521020788175173311157497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182347347192116782207438331 273521020788175173311157497)
      ·
        refine ⟨205140765591131379983368123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273521020788175173311157497 205140765591131379983368123)
        ·
          refine ⟨307711148386697069975052185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205140765591131379983368123 307711148386697069975052185)
          ·
            refine ⟨230783361290022802481289139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307711148386697069975052185 230783361290022802481289139)
            ·
              refine ⟨346175041935034203721933709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230783361290022802481289139 346175041935034203721933709)
              ·
                refine ⟨129815640725637826395725141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346175041935034203721933709 129815640725637826395725141)
                ·
                  refine ⟨190159629969196034759363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 129815640725637826395725141 190159629969196034759363)
                  ·
                    rfl

theorem cell23_3333011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 11].length) (baseStart_3333011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333011 prefixEnd_3333011 := by exact prefixLift 3333011
  have htrace : WordTrace (prefixWord ++ tailWord_3333011) baseStart_3333011 baseEnd_3333011 := by
    simpa [prefixWord, tailWord_3333011, baseEnd_3333011] using wordTrace_append hprefix tailTrace_3333011
  have hstable : (prefixWord ++ tailWord_3333011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333011).length < 2 ^ (prefixWord ++ tailWord_3333011).sum := by decide
  have hdescent : baseEnd_3333011 < baseStart_3333011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333025 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 2, 4, 3]
def baseStart_3333025 : Nat := 118140960795 + 3333025 * 2 ^ 59
def prefixEnd_3333025 : Nat := 4983230072969 + 3 ^ 40 * 3333025 * 2
def baseEnd_3333025 : Nat := 1711443858451927258059203

theorem tailTrace_3333025 : CollatzResearch.WordTrace tailWord_3333025 prefixEnd_3333025 1711443858451927258059203 := by
  unfold tailWord_3333025
  simp only [CollatzResearch.WordTrace]
  refine ⟨121565408750027135195968529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81043605833351423463979019 121565408750027135195968529)
  ·
    refine ⟨91174056562520351396976397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121565408750027135195968529 91174056562520351396976397)
    ·
      refine ⟨34190271210945131773866149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91174056562520351396976397 34190271210945131773866149)
      ·
        refine ⟨6410675852052212207599903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34190271210945131773866149 6410675852052212207599903)
        ·
          refine ⟨9616013778078318311399855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6410675852052212207599903 9616013778078318311399855)
          ·
            refine ⟨14424020667117477467099783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9616013778078318311399855 14424020667117477467099783)
            ·
              refine ⟨21636031000676216200649675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14424020667117477467099783 21636031000676216200649675)
              ·
                refine ⟨32454046501014324300974513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21636031000676216200649675 32454046501014324300974513)
                ·
                  refine ⟨24340534875760743225730885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32454046501014324300974513 24340534875760743225730885)
                  ·
                    refine ⟨4563850289205139354824541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24340534875760743225730885 4563850289205139354824541)
                    ·
                      refine ⟨1711443858451927258059203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4563850289205139354824541 1711443858451927258059203)
                      ·
                        rfl

theorem cell23_3333025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_3333025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333025 prefixEnd_3333025 := by exact prefixLift 3333025
  have htrace : WordTrace (prefixWord ++ tailWord_3333025) baseStart_3333025 baseEnd_3333025 := by
    simpa [prefixWord, tailWord_3333025, baseEnd_3333025] using wordTrace_append hprefix tailTrace_3333025
  have hstable : (prefixWord ++ tailWord_3333025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333025).length < 2 ^ (prefixWord ++ tailWord_3333025).sum := by decide
  have hdescent : baseEnd_3333025 < baseStart_3333025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333028 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 7]
def baseStart_3333028 : Nat := 118140960795 + 3333028 * 2 ^ 59
def prefixEnd_3333028 : Nat := 4983230072969 + 3 ^ 40 * 3333028 * 2
def baseEnd_3333028 : Nat := 190160599877098971813521

theorem tailTrace_3333028 : CollatzResearch.WordTrace tailWord_3333028 prefixEnd_3333028 190160599877098971813521 := by
  unfold tailWord_3333028
  simp only [CollatzResearch.WordTrace]
  refine ⟨60782759084508133354163869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81043678779344177805551825 60782759084508133354163869)
  ·
    refine ⟨22793534656690550007811451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60782759084508133354163869 22793534656690550007811451)
    ·
      refine ⟨34190301985035825011717177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22793534656690550007811451 34190301985035825011717177)
      ·
        refine ⟨25642726488776868758787883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34190301985035825011717177 25642726488776868758787883)
        ·
          refine ⟨38464089733165303138181825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25642726488776868758787883 38464089733165303138181825)
          ·
            refine ⟨28848067299873977353636369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38464089733165303138181825 28848067299873977353636369)
            ·
              refine ⟨21636050474905483015227277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28848067299873977353636369 21636050474905483015227277)
              ·
                refine ⟨8113518928089556130710229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21636050474905483015227277 8113518928089556130710229)
                ·
                  refine ⟨190160599877098971813521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8113518928089556130710229 190160599877098971813521)
                  ·
                    rfl

theorem cell23_3333028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_3333028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333028 prefixEnd_3333028 := by exact prefixLift 3333028
  have htrace : WordTrace (prefixWord ++ tailWord_3333028) baseStart_3333028 baseEnd_3333028 := by
    simpa [prefixWord, tailWord_3333028, baseEnd_3333028] using wordTrace_append hprefix tailTrace_3333028
  have hstable : (prefixWord ++ tailWord_3333028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333028).length < 2 ^ (prefixWord ++ tailWord_3333028).sum := by decide
  have hdescent : baseEnd_3333028 < baseStart_3333028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333060 : List Nat := [2, 3, 3, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_3333060 : Nat := 118140960795 + 3333060 * 2 ^ 59
def prefixEnd_3333060 : Nat := 4983230072969 + 3 ^ 40 * 3333060 * 2
def baseEnd_3333060 : Nat := 1711461830274834621121543

theorem tailTrace_3333060 : CollatzResearch.WordTrace tailWord_3333060 prefixEnd_3333060 1711461830274834621121543 := by
  unfold tailWord_3333060
  simp only [CollatzResearch.WordTrace]
  refine ⟨60783342652450168086746317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81044456869933557448995089 60783342652450168086746317)
  ·
    refine ⟨22793753494668813032529869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60783342652450168086746317 22793753494668813032529869)
    ·
      refine ⟨8547657560500804887198701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22793753494668813032529869 8547657560500804887198701)
      ·
        refine ⟨3205371585187801832699513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8547657560500804887198701 3205371585187801832699513)
        ·
          refine ⟨2404028688890851374524635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3205371585187801832699513 2404028688890851374524635)
          ·
            refine ⟨3606043033336277061786953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2404028688890851374524635 3606043033336277061786953)
            ·
              refine ⟨2704532275002207796340215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3606043033336277061786953 2704532275002207796340215)
              ·
                refine ⟨4056798412503311694510323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2704532275002207796340215 4056798412503311694510323)
                ·
                  refine ⟨6085197618754967541765485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4056798412503311694510323 6085197618754967541765485)
                  ·
                    refine ⟨2281949107033112828162057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6085197618754967541765485 2281949107033112828162057)
                    ·
                      refine ⟨1711461830274834621121543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2281949107033112828162057 1711461830274834621121543)
                      ·
                        rfl

theorem cell23_3333060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_3333060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333060 prefixEnd_3333060 := by exact prefixLift 3333060
  have htrace : WordTrace (prefixWord ++ tailWord_3333060) baseStart_3333060 baseEnd_3333060 := by
    simpa [prefixWord, tailWord_3333060, baseEnd_3333060] using wordTrace_append hprefix tailTrace_3333060
  have hstable : (prefixWord ++ tailWord_3333060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333060).length < 2 ^ (prefixWord ++ tailWord_3333060).sum := by decide
  have hdescent : baseEnd_3333060 < baseStart_3333060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333095 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3333095 : Nat := 118140960795 + 3333095 * 2 ^ 59
def prefixEnd_3333095 : Nat := 4983230072969 + 3 ^ 40 * 3333095 * 2
def baseEnd_3333095 : Nat := 1711479802097741984183881

theorem tailTrace_3333095 : CollatzResearch.WordTrace tailWord_3333095 prefixEnd_3333095 1711479802097741984183881 := by
  unfold tailWord_3333095
  simp only [CollatzResearch.WordTrace]
  refine ⟨121567961859773537151016739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81045307906515691434011159 121567961859773537151016739)
  ·
    refine ⟨182351942789660305726525109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121567961859773537151016739 182351942789660305726525109)
    ·
      refine ⟨17095494636530653661861729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182351942789660305726525109 17095494636530653661861729)
      ·
        refine ⟨12821620977397990246396297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17095494636530653661861729 12821620977397990246396297)
        ·
          refine ⟨9616215733048492684797223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12821620977397990246396297 9616215733048492684797223)
          ·
            refine ⟨14424323599572739027195835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9616215733048492684797223 14424323599572739027195835)
            ·
              refine ⟨21636485399359108540793753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14424323599572739027195835 21636485399359108540793753)
              ·
                refine ⟨16227364049519331405595315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21636485399359108540793753 16227364049519331405595315)
                ·
                  refine ⟨24341046074278997108392973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16227364049519331405595315 24341046074278997108392973)
                  ·
                    refine ⟨9127892277854623915647365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24341046074278997108392973 9127892277854623915647365)
                    ·
                      refine ⟨1711479802097741984183881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9127892277854623915647365 1711479802097741984183881)
                      ·
                        rfl

theorem cell23_3333095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3333095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333095 prefixEnd_3333095 := by exact prefixLift 3333095
  have htrace : WordTrace (prefixWord ++ tailWord_3333095) baseStart_3333095 baseEnd_3333095 := by
    simpa [prefixWord, tailWord_3333095, baseEnd_3333095] using wordTrace_append hprefix tailTrace_3333095
  have hstable : (prefixWord ++ tailWord_3333095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333095).length < 2 ^ (prefixWord ++ tailWord_3333095).sum := by decide
  have hdescent : baseEnd_3333095 < baseStart_3333095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333115 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 3]
def baseStart_3333115 : Nat := 118140960795 + 3333115 * 2 ^ 59
def prefixEnd_3333115 : Nat := 4983230072969 + 3 ^ 40 * 3333115 * 2
def baseEnd_3333115 : Nat := 1711490071710831905933789

theorem tailTrace_3333115 : CollatzResearch.WordTrace tailWord_3333115 prefixEnd_3333115 1711490071710831905933789 := by
  unfold tailWord_3333115
  simp only [CollatzResearch.WordTrace]
  refine ⟨121568691319701080566744799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81045794213134053711163199 121568691319701080566744799)
  ·
    refine ⟨182353036979551620850117199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121568691319701080566744799 182353036979551620850117199)
    ·
      refine ⟨273529555469327431275175799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182353036979551620850117199 273529555469327431275175799)
      ·
        refine ⟨410294333203991146912763699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273529555469327431275175799 410294333203991146912763699)
        ·
          refine ⟨615441499805986720369145549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410294333203991146912763699 615441499805986720369145549)
          ·
            refine ⟨230790562427245020138429581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 615441499805986720369145549 230790562427245020138429581)
            ·
              refine ⟨86546460910216882551911093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230790562427245020138429581 86546460910216882551911093)
              ·
                refine ⟨8113730710332832739241665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86546460910216882551911093 8113730710332832739241665)
                ·
                  refine ⟨6085298032749624554431249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8113730710332832739241665 6085298032749624554431249)
                  ·
                    refine ⟨4563973524562218415823437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6085298032749624554431249 4563973524562218415823437)
                    ·
                      refine ⟨1711490071710831905933789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4563973524562218415823437 1711490071710831905933789)
                      ·
                        rfl

theorem cell23_3333115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 3].length) (baseStart_3333115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333115 prefixEnd_3333115 := by exact prefixLift 3333115
  have htrace : WordTrace (prefixWord ++ tailWord_3333115) baseStart_3333115 baseEnd_3333115 := by
    simpa [prefixWord, tailWord_3333115, baseEnd_3333115] using wordTrace_append hprefix tailTrace_3333115
  have hstable : (prefixWord ++ tailWord_3333115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333115).length < 2 ^ (prefixWord ++ tailWord_3333115).sum := by decide
  have hdescent : baseEnd_3333115 < baseStart_3333115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333132 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 2, 2, 3]
def baseStart_3333132 : Nat := 118140960795 + 3333132 * 2 ^ 59
def prefixEnd_3333132 : Nat := 4983230072969 + 3 ^ 40 * 3333132 * 2
def baseEnd_3333132 : Nat := 1711498800881958339421211

theorem tailTrace_3333132 : CollatzResearch.WordTrace tailWord_3333132 prefixEnd_3333132 1711498800881958339421211 := by
  unfold tailWord_3333132
  simp only [CollatzResearch.WordTrace]
  refine ⟨60784655680319746235056825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81046207573759661646742433 60784655680319746235056825)
  ·
    refine ⟨45588491760239809676292619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60784655680319746235056825 45588491760239809676292619)
    ·
      refine ⟨68382737640359714514438929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45588491760239809676292619 68382737640359714514438929)
      ·
        refine ⟨51287053230269785885829197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68382737640359714514438929 51287053230269785885829197)
        ·
          refine ⟨19232644961351169707185949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51287053230269785885829197 19232644961351169707185949)
          ·
            refine ⟨7212241860506688640194731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19232644961351169707185949 7212241860506688640194731)
            ·
              refine ⟨10818362790760032960292097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7212241860506688640194731 10818362790760032960292097)
              ·
                refine ⟨8113772093070024720219073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10818362790760032960292097 8113772093070024720219073)
                ·
                  refine ⟨6085329069802518540164305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8113772093070024720219073 6085329069802518540164305)
                  ·
                    refine ⟨4563996802351888905123229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6085329069802518540164305 4563996802351888905123229)
                    ·
                      refine ⟨1711498800881958339421211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4563996802351888905123229 1711498800881958339421211)
                      ·
                        rfl

theorem cell23_3333132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_3333132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333132 prefixEnd_3333132 := by exact prefixLift 3333132
  have htrace : WordTrace (prefixWord ++ tailWord_3333132) baseStart_3333132 baseEnd_3333132 := by
    simpa [prefixWord, tailWord_3333132, baseEnd_3333132] using wordTrace_append hprefix tailTrace_3333132
  have hstable : (prefixWord ++ tailWord_3333132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333132).length < 2 ^ (prefixWord ++ tailWord_3333132).sum := by decide
  have hdescent : baseEnd_3333132 < baseStart_3333132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333190 : List Nat := [6, 1, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_3333190 : Nat := 118140960795 + 3333190 * 2 ^ 59
def prefixEnd_3333190 : Nat := 4983230072969 + 3 ^ 40 * 3333190 * 2
def baseEnd_3333190 : Nat := 570509527586639704165315

theorem tailTrace_3333190 : CollatzResearch.WordTrace tailWord_3333190 prefixEnd_3333190 570509527586639704165315 := by
  unfold tailWord_3333190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3799107087325917761741407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81047617862952912250483349 3799107087325917761741407)
  ·
    refine ⟨5698660630988876642612111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3799107087325917761741407 5698660630988876642612111)
    ·
      refine ⟨8547990946483314963918167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5698660630988876642612111 8547990946483314963918167)
      ·
        refine ⟨12821986419724972445877251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8547990946483314963918167 12821986419724972445877251)
        ·
          refine ⟨19232979629587458668815877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12821986419724972445877251 19232979629587458668815877)
          ·
            refine ⟨3606183680547648500402977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19232979629587458668815877 3606183680547648500402977)
            ·
              refine ⟨2704637760410736375302233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3606183680547648500402977 2704637760410736375302233)
              ·
                refine ⟨2028478320308052281476675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2704637760410736375302233 2028478320308052281476675)
                ·
                  refine ⟨3042717480462078422215013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2028478320308052281476675 3042717480462078422215013)
                  ·
                    refine ⟨570509527586639704165315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3042717480462078422215013 570509527586639704165315)
                    ·
                      rfl

theorem cell23_3333190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_3333190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333190 prefixEnd_3333190 := by exact prefixLift 3333190
  have htrace : WordTrace (prefixWord ++ tailWord_3333190) baseStart_3333190 baseEnd_3333190 := by
    simpa [prefixWord, tailWord_3333190, baseEnd_3333190] using wordTrace_append hprefix tailTrace_3333190
  have hstable : (prefixWord ++ tailWord_3333190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333190).length < 2 ^ (prefixWord ++ tailWord_3333190).sum := by decide
  have hdescent : baseEnd_3333190 < baseStart_3333190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333202 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_3333202 : Nat := 118140960795 + 3333202 * 2 ^ 59
def prefixEnd_3333202 : Nat := 4983230072969 + 3 ^ 40 * 3333202 * 2
def baseEnd_3333202 : Nat := 1711534744527773065545889

theorem tailTrace_3333202 : CollatzResearch.WordTrace tailWord_3333202 prefixEnd_3333202 1711534744527773065545889 := by
  unfold tailWord_3333202
  simp only [CollatzResearch.WordTrace]
  refine ⟨30392966117596473606290465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81047909646923929616774573 30392966117596473606290465)
  ·
    refine ⟨22794724588197355204717849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30392966117596473606290465 22794724588197355204717849)
    ·
      refine ⟨17096043441148016403538387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22794724588197355204717849 17096043441148016403538387)
      ·
        refine ⟨25644065161722024605307581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17096043441148016403538387 25644065161722024605307581)
        ·
          refine ⟨9616524435645759226990343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25644065161722024605307581 9616524435645759226990343)
          ·
            refine ⟨14424786653468638840485515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9616524435645759226990343 14424786653468638840485515)
            ·
              refine ⟨21637179980202958260728273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14424786653468638840485515 21637179980202958260728273)
              ·
                refine ⟨16227884985152218695546205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21637179980202958260728273 16227884985152218695546205)
                ·
                  refine ⟨6085456869432082010829827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16227884985152218695546205 6085456869432082010829827)
                  ·
                    refine ⟨9128185304148123016244741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6085456869432082010829827 9128185304148123016244741)
                    ·
                      refine ⟨1711534744527773065545889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9128185304148123016244741 1711534744527773065545889)
                      ·
                        rfl

theorem cell23_3333202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_3333202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333202 prefixEnd_3333202 := by exact prefixLift 3333202
  have htrace : WordTrace (prefixWord ++ tailWord_3333202) baseStart_3333202 baseEnd_3333202 := by
    simpa [prefixWord, tailWord_3333202, baseEnd_3333202] using wordTrace_append hprefix tailTrace_3333202
  have hstable : (prefixWord ++ tailWord_3333202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333202).length < 2 ^ (prefixWord ++ tailWord_3333202).sum := by decide
  have hdescent : baseEnd_3333202 < baseStart_3333202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333205 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_3333205 : Nat := 118140960795 + 3333205 * 2 ^ 59
def prefixEnd_3333205 : Nat := 4983230072969 + 3 ^ 40 * 3333205 * 2
def baseEnd_3333205 : Nat := 1711536284969736553808375

theorem tailTrace_3333205 : CollatzResearch.WordTrace tailWord_3333205 prefixEnd_3333205 1711536284969736553808375 := by
  unfold tailWord_3333205
  simp only [CollatzResearch.WordTrace]
  refine ⟨121571973889375025937521069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81047982592916683958347379 121571973889375025937521069)
  ·
    refine ⟨45589490208515634726570401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121571973889375025937521069 45589490208515634726570401)
    ·
      refine ⟨34192117656386726044927801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45589490208515634726570401 34192117656386726044927801)
      ·
        refine ⟨25644088242290044533695851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34192117656386726044927801 25644088242290044533695851)
        ·
          refine ⟨38466132363435066800543777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25644088242290044533695851 38466132363435066800543777)
          ·
            refine ⟨28849599272576300100407833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38466132363435066800543777 28849599272576300100407833)
            ·
              refine ⟨21637199454432225075305875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28849599272576300100407833 21637199454432225075305875)
              ·
                refine ⟨32455799181648337612958813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21637199454432225075305875 32455799181648337612958813)
                ·
                  refine ⟨12170924693118126604859555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32455799181648337612958813 12170924693118126604859555)
                  ·
                    refine ⟨18256387039677189907289333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12170924693118126604859555 18256387039677189907289333)
                    ·
                      refine ⟨1711536284969736553808375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18256387039677189907289333 1711536284969736553808375)
                      ·
                        rfl

theorem cell23_3333205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_3333205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333205 prefixEnd_3333205 := by exact prefixLift 3333205
  have htrace : WordTrace (prefixWord ++ tailWord_3333205) baseStart_3333205 baseEnd_3333205 := by
    simpa [prefixWord, tailWord_3333205, baseEnd_3333205] using wordTrace_append hprefix tailTrace_3333205
  have hstable : (prefixWord ++ tailWord_3333205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333205).length < 2 ^ (prefixWord ++ tailWord_3333205).sum := by decide
  have hdescent : baseEnd_3333205 < baseStart_3333205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333212 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 1, 6]
def baseStart_3333212 : Nat := 118140960795 + 3333212 * 2 ^ 59
def prefixEnd_3333212 : Nat := 4983230072969 + 3 ^ 40 * 3333212 * 2
def baseEnd_3333212 : Nat := 570513293111439342140281

theorem tailTrace_3333212 : CollatzResearch.WordTrace tailWord_3333212 prefixEnd_3333212 570513293111439342140281 := by
  unfold tailWord_3333212
  simp only [CollatzResearch.WordTrace]
  refine ⟨60786114600174833066512945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81048152800233110755350593 60786114600174833066512945)
  ·
    refine ⟨45589585950131124799884709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60786114600174833066512945 45589585950131124799884709)
    ·
      refine ⟨8548047365649585899978383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45589585950131124799884709 8548047365649585899978383)
      ·
        refine ⟨12822071048474378849967575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8548047365649585899978383 12822071048474378849967575)
        ·
          refine ⟨19233106572711568274951363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12822071048474378849967575 19233106572711568274951363)
          ·
            refine ⟨28849659859067352412427045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19233106572711568274951363 28849659859067352412427045)
            ·
              refine ⟨5409311223575128577330071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28849659859067352412427045 5409311223575128577330071)
              ·
                refine ⟨8113966835362692865995107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5409311223575128577330071 8113966835362692865995107)
                ·
                  refine ⟨12170950253044039298992661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8113966835362692865995107 12170950253044039298992661)
                  ·
                    refine ⟨570513293111439342140281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12170950253044039298992661 570513293111439342140281)
                    ·
                      rfl

theorem cell23_3333212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_3333212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333212 prefixEnd_3333212 := by exact prefixLift 3333212
  have htrace : WordTrace (prefixWord ++ tailWord_3333212) baseStart_3333212 baseEnd_3333212 := by
    simpa [prefixWord, tailWord_3333212, baseEnd_3333212] using wordTrace_append hprefix tailTrace_3333212
  have hstable : (prefixWord ++ tailWord_3333212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333212).length < 2 ^ (prefixWord ++ tailWord_3333212).sum := by decide
  have hdescent : baseEnd_3333212 < baseStart_3333212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333295 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 5]
def baseStart_3333295 : Nat := 118140960795 + 3333295 * 2 ^ 59
def prefixEnd_3333295 : Nat := 4983230072969 + 3 ^ 40 * 3333295 * 2
def baseEnd_3333295 : Nat := 1711582498228641201682961

theorem tailTrace_3333295 : CollatzResearch.WordTrace tailWord_3333295 prefixEnd_3333295 1711582498228641201682961 := by
  unfold tailWord_3333295
  simp only [CollatzResearch.WordTrace]
  refine ⟨121575256459048971308297339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81050170972699314205531559 121575256459048971308297339)
  ·
    refine ⟨182362884688573456962446009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121575256459048971308297339 182362884688573456962446009)
    ·
      refine ⟨136772163516430092721834507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182362884688573456962446009 136772163516430092721834507)
      ·
        refine ⟨205158245274645139082751761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136772163516430092721834507 205158245274645139082751761)
        ·
          refine ⟨153868683955983854312063821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205158245274645139082751761 153868683955983854312063821)
          ·
            refine ⟨57700756483493945367023933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153868683955983854312063821 57700756483493945367023933)
            ·
              refine ⟨21637783681310229512633975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57700756483493945367023933 21637783681310229512633975)
              ·
                refine ⟨32456675521965344268950963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21637783681310229512633975 32456675521965344268950963)
                ·
                  refine ⟨48685013282948016403426445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32456675521965344268950963 48685013282948016403426445)
                  ·
                    refine ⟨18256879981105506151284917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48685013282948016403426445 18256879981105506151284917)
                    ·
                      refine ⟨1711582498228641201682961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18256879981105506151284917 1711582498228641201682961)
                      ·
                        rfl

theorem cell23_3333295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_3333295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333295 prefixEnd_3333295 := by exact prefixLift 3333295
  have htrace : WordTrace (prefixWord ++ tailWord_3333295) baseStart_3333295 baseEnd_3333295 := by
    simpa [prefixWord, tailWord_3333295, baseEnd_3333295] using wordTrace_append hprefix tailTrace_3333295
  have hstable : (prefixWord ++ tailWord_3333295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333295).length < 2 ^ (prefixWord ++ tailWord_3333295).sum := by decide
  have hdescent : baseEnd_3333295 < baseStart_3333295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333315 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 7]
def baseStart_3333315 : Nat := 118140960795 + 3333315 * 2 ^ 59
def prefixEnd_3333315 : Nat := 4983230072969 + 3 ^ 40 * 3333315 * 2
def baseEnd_3333315 : Nat := 190176974204636791492541

theorem tailTrace_3333315 : CollatzResearch.WordTrace tailWord_3333315 prefixEnd_3333315 190176974204636791492541 := by
  unfold tailWord_3333315
  simp only [CollatzResearch.WordTrace]
  refine ⟨121575985918976514724025399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81050657279317676482683599 121575985918976514724025399)
  ·
    refine ⟨182363978878464772086038099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121575985918976514724025399 182363978878464772086038099)
    ·
      refine ⟨273545968317697158129057149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182363978878464772086038099 273545968317697158129057149)
      ·
        refine ⟨102579738119136434298396431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273545968317697158129057149 102579738119136434298396431)
        ·
          refine ⟨153869607178704651447594647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102579738119136434298396431 153869607178704651447594647)
          ·
            refine ⟨230804410768056977171391971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153869607178704651447594647 230804410768056977171391971)
            ·
              refine ⟨346206616152085465757087957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230804410768056977171391971 346206616152085465757087957)
              ·
                refine ⟨8114217566064503103681749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 346206616152085465757087957 8114217566064503103681749)
                ·
                  refine ⟨190176974204636791492541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8114217566064503103681749 190176974204636791492541)
                  ·
                    rfl

theorem cell23_3333315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 7].length) (baseStart_3333315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333315 prefixEnd_3333315 := by exact prefixLift 3333315
  have htrace : WordTrace (prefixWord ++ tailWord_3333315) baseStart_3333315 baseEnd_3333315 := by
    simpa [prefixWord, tailWord_3333315, baseEnd_3333315] using wordTrace_append hprefix tailTrace_3333315
  have hstable : (prefixWord ++ tailWord_3333315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333315).length < 2 ^ (prefixWord ++ tailWord_3333315).sum := by decide
  have hdescent : baseEnd_3333315 < baseStart_3333315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333399 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 1, 6, 2]
def baseStart_3333399 : Nat := 118140960795 + 3333399 * 2 ^ 59
def prefixEnd_3333399 : Nat := 4983230072969 + 3 ^ 40 * 3333399 * 2
def baseEnd_3333399 : Nat := 1711635900216708794782483

theorem tailTrace_3333399 : CollatzResearch.WordTrace tailWord_3333399 prefixEnd_3333399 1711635900216708794782483 := by
  unfold tailWord_3333399
  simp only [CollatzResearch.WordTrace]
  refine ⟨121579049650672197070083251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81052699767114798046722167 121579049650672197070083251)
  ·
    refine ⟨182368574476008295605124877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121579049650672197070083251 182368574476008295605124877)
    ·
      refine ⟨68388215428503110851921829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182368574476008295605124877 68388215428503110851921829)
      ·
        refine ⟨12822790392844333284735343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68388215428503110851921829 12822790392844333284735343)
        ·
          refine ⟨19234185589266499927103015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12822790392844333284735343 19234185589266499927103015)
          ·
            refine ⟨28851278383899749890654523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19234185589266499927103015 28851278383899749890654523)
            ·
              refine ⟨43276917575849624835981785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28851278383899749890654523 43276917575849624835981785)
              ·
                refine ⟨32457688181887218626986339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43276917575849624835981785 32457688181887218626986339)
                ·
                  refine ⟨48686532272830827940479509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32457688181887218626986339 48686532272830827940479509)
                  ·
                    refine ⟨2282181200288945059709977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48686532272830827940479509 2282181200288945059709977)
                    ·
                      refine ⟨1711635900216708794782483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2282181200288945059709977 1711635900216708794782483)
                      ·
                        rfl

theorem cell23_3333399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_3333399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333399 prefixEnd_3333399 := by exact prefixLift 3333399
  have htrace : WordTrace (prefixWord ++ tailWord_3333399) baseStart_3333399 baseEnd_3333399 := by
    simpa [prefixWord, tailWord_3333399, baseEnd_3333399] using wordTrace_append hprefix tailTrace_3333399
  have hstable : (prefixWord ++ tailWord_3333399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333399).length < 2 ^ (prefixWord ++ tailWord_3333399).sum := by decide
  have hdescent : baseEnd_3333399 < baseStart_3333399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333412 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_3333412 : Nat := 118140960795 + 3333412 * 2 ^ 59
def prefixEnd_3333412 : Nat := 4983230072969 + 3 ^ 40 * 3333412 * 2
def baseEnd_3333412 : Nat := 1711642575465217243919923

theorem tailTrace_3333412 : CollatzResearch.WordTrace tailWord_3333412 prefixEnd_3333412 1711642575465217243919923 := by
  unfold tailWord_3333412
  simp only [CollatzResearch.WordTrace]
  refine ⟨60789761899812550145153245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81053015866416733526870993 60789761899812550145153245)
  ·
    refine ⟨22796160712429706304432467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60789761899812550145153245 22796160712429706304432467)
    ·
      refine ⟨34194241068644559456648701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22796160712429706304432467 34194241068644559456648701)
      ·
        refine ⟨12822840400741709796243263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34194241068644559456648701 12822840400741709796243263)
        ·
          refine ⟨19234260601112564694364895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12822840400741709796243263 19234260601112564694364895)
          ·
            refine ⟨28851390901668847041547343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19234260601112564694364895 28851390901668847041547343)
            ·
              refine ⟨43277086352503270562321015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28851390901668847041547343 43277086352503270562321015)
              ·
                refine ⟨64915629528754905843481523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43277086352503270562321015 64915629528754905843481523)
                ·
                  refine ⟨97373444293132358765222285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64915629528754905843481523 97373444293132358765222285)
                  ·
                    refine ⟨36515041609924634536958357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97373444293132358765222285 36515041609924634536958357)
                    ·
                      refine ⟨1711642575465217243919923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36515041609924634536958357 1711642575465217243919923)
                      ·
                        rfl

theorem cell23_3333412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_3333412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333412 prefixEnd_3333412 := by exact prefixLift 3333412
  have htrace : WordTrace (prefixWord ++ tailWord_3333412) baseStart_3333412 baseEnd_3333412 := by
    simpa [prefixWord, tailWord_3333412, baseEnd_3333412] using wordTrace_append hprefix tailTrace_3333412
  have hstable : (prefixWord ++ tailWord_3333412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333412).length < 2 ^ (prefixWord ++ tailWord_3333412).sum := by decide
  have hdescent : baseEnd_3333412 < baseStart_3333412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333416 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_3333416 : Nat := 118140960795 + 3333416 * 2 ^ 59
def prefixEnd_3333416 : Nat := 4983230072969 + 3 ^ 40 * 3333416 * 2
def baseEnd_3333416 : Nat := 1711644629387835228269905

theorem tailTrace_3333416 : CollatzResearch.WordTrace tailWord_3333416 prefixEnd_3333416 1711644629387835228269905 := by
  unfold tailWord_3333416
  simp only [CollatzResearch.WordTrace]
  refine ⟨60789834845805304486726051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81053113127740405982301401 60789834845805304486726051)
  ·
    refine ⟨91184752268707956730089077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60789834845805304486726051 91184752268707956730089077)
    ·
      refine ⟨8548570525191370943445851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91184752268707956730089077 8548570525191370943445851)
      ·
        refine ⟨12822855787787056415168777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8548570525191370943445851 12822855787787056415168777)
        ·
          refine ⟨9617141840840292311376583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12822855787787056415168777 9617141840840292311376583)
          ·
            refine ⟨14425712761260438467064875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9617141840840292311376583 14425712761260438467064875)
            ·
              refine ⟨21638569141890657700597313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14425712761260438467064875 21638569141890657700597313)
              ·
                refine ⟨16228926856417993275447985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21638569141890657700597313 16228926856417993275447985)
                ·
                  refine ⟨12171695142313494956585989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16228926856417993275447985 12171695142313494956585989)
                  ·
                    refine ⟨2282192839183780304359873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12171695142313494956585989 2282192839183780304359873)
                    ·
                      refine ⟨1711644629387835228269905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2282192839183780304359873 1711644629387835228269905)
                      ·
                        rfl

theorem cell23_3333416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_3333416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333416 prefixEnd_3333416 := by exact prefixLift 3333416
  have htrace : WordTrace (prefixWord ++ tailWord_3333416) baseStart_3333416 baseEnd_3333416 := by
    simpa [prefixWord, tailWord_3333416, baseEnd_3333416] using wordTrace_append hprefix tailTrace_3333416
  have hstable : (prefixWord ++ tailWord_3333416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333416).length < 2 ^ (prefixWord ++ tailWord_3333416).sum := by decide
  have hdescent : baseEnd_3333416 < baseStart_3333416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333426 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 3, 4]
def baseStart_3333426 : Nat := 118140960795 + 3333426 * 2 ^ 59
def prefixEnd_3333426 : Nat := 4983230072969 + 3 ^ 40 * 3333426 * 2
def baseEnd_3333426 : Nat := 570549921398126729714953

theorem tailTrace_3333426 : CollatzResearch.WordTrace tailWord_3333426 prefixEnd_3333426 570549921398126729714953 := by
  unfold tailWord_3333426
  simp only [CollatzResearch.WordTrace]
  refine ⟨30395008605393595170329033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81053356281049587120877421 30395008605393595170329033)
  ·
    refine ⟨22796256454045196377746775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30395008605393595170329033 22796256454045196377746775)
    ·
      refine ⟨34194384681067794566620163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22796256454045196377746775 34194384681067794566620163)
      ·
        refine ⟨51291577021601691849930245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34194384681067794566620163 51291577021601691849930245)
        ·
          refine ⟨9617170691550317221861921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51291577021601691849930245 9617170691550317221861921)
          ·
            refine ⟨7212878018662737916396441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9617170691550317221861921 7212878018662737916396441)
            ·
              refine ⟨5409658513997053437297331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7212878018662737916396441 5409658513997053437297331)
              ·
                refine ⟨8114487770995580155945997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5409658513997053437297331 8114487770995580155945997)
                ·
                  refine ⟨3042932914123342558479749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8114487770995580155945997 3042932914123342558479749)
                  ·
                    refine ⟨570549921398126729714953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3042932914123342558479749 570549921398126729714953)
                    ·
                      rfl

theorem cell23_3333426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_3333426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333426 prefixEnd_3333426 := by exact prefixLift 3333426
  have htrace : WordTrace (prefixWord ++ tailWord_3333426) baseStart_3333426 baseEnd_3333426 := by
    simpa [prefixWord, tailWord_3333426, baseEnd_3333426] using wordTrace_append hprefix tailTrace_3333426
  have hstable : (prefixWord ++ tailWord_3333426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333426).length < 2 ^ (prefixWord ++ tailWord_3333426).sum := by decide
  have hdescent : baseEnd_3333426 < baseStart_3333426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333459 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 1, 5, 2]
def baseStart_3333459 : Nat := 118140960795 + 3333459 * 2 ^ 59
def prefixEnd_3333459 : Nat := 4983230072969 + 3 ^ 40 * 3333459 * 2
def baseEnd_3333459 : Nat := 1711666709055978560032207

theorem tailTrace_3333459 : CollatzResearch.WordTrace tailWord_3333459 prefixEnd_3333459 1711666709055978560032207 := by
  unfold tailWord_3333459
  simp only [CollatzResearch.WordTrace]
  refine ⟨121581238030454827317267431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81054158686969884878178287 121581238030454827317267431)
  ·
    refine ⟨182371857045682240975901147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121581238030454827317267431 182371857045682240975901147)
    ·
      refine ⟨273557785568523361463851721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182371857045682240975901147 273557785568523361463851721)
      ·
        refine ⟨205168339176392521097888791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273557785568523361463851721 205168339176392521097888791)
        ·
          refine ⟨307752508764588781646833187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205168339176392521097888791 307752508764588781646833187)
          ·
            refine ⟨461628763146883172470249781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307752508764588781646833187 461628763146883172470249781)
            ·
              refine ⟨43277696545020297419085917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 461628763146883172470249781 43277696545020297419085917)
              ·
                refine ⟨16229136204382611532157219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43277696545020297419085917 16229136204382611532157219)
                ·
                  refine ⟨24343704306573917298235829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16229136204382611532157219 24343704306573917298235829)
                  ·
                    refine ⟨2282222278741304746709609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24343704306573917298235829 2282222278741304746709609)
                    ·
                      refine ⟨1711666709055978560032207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2282222278741304746709609 1711666709055978560032207)
                      ·
                        rfl

theorem cell23_3333459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 5, 2].length) (baseStart_3333459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333459 prefixEnd_3333459 := by exact prefixLift 3333459
  have htrace : WordTrace (prefixWord ++ tailWord_3333459) baseStart_3333459 baseEnd_3333459 := by
    simpa [prefixWord, tailWord_3333459, baseEnd_3333459] using wordTrace_append hprefix tailTrace_3333459
  have hstable : (prefixWord ++ tailWord_3333459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333459).length < 2 ^ (prefixWord ++ tailWord_3333459).sum := by decide
  have hdescent : baseEnd_3333459 < baseStart_3333459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333476 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 4, 3, 2]
def baseStart_3333476 : Nat := 118140960795 + 3333476 * 2 ^ 59
def prefixEnd_3333476 : Nat := 4983230072969 + 3 ^ 40 * 3333476 * 2
def baseEnd_3333476 : Nat := 1711675438227104993519629

theorem tailTrace_3333476 : CollatzResearch.WordTrace tailWord_3333476 prefixEnd_3333476 1711675438227104993519629 := by
  unfold tailWord_3333476
  simp only [CollatzResearch.WordTrace]
  refine ⟨60790929035696619610318141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81054572047595492813757521 60790929035696619610318141)
  ·
    refine ⟨22796598388386232353869303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60790929035696619610318141 22796598388386232353869303)
    ·
      refine ⟨34194897582579348530803955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22796598388386232353869303 34194897582579348530803955)
      ·
        refine ⟨51292346373869022796205933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34194897582579348530803955 51292346373869022796205933)
        ·
          refine ⟨19234629890200883548577225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51292346373869022796205933 19234629890200883548577225)
          ·
            refine ⟨14425972417650662661432919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19234629890200883548577225 14425972417650662661432919)
            ·
              refine ⟨21638958626475993992149379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14425972417650662661432919 21638958626475993992149379)
              ·
                refine ⟨32458437939713990988224069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21638958626475993992149379 32458437939713990988224069)
                ·
                  refine ⟨6085957113696373310292013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32458437939713990988224069 6085957113696373310292013)
                  ·
                    refine ⟨2282233917636139991359505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6085957113696373310292013 2282233917636139991359505)
                    ·
                      refine ⟨1711675438227104993519629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2282233917636139991359505 1711675438227104993519629)
                      ·
                        rfl

theorem cell23_3333476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_3333476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333476 prefixEnd_3333476 := by exact prefixLift 3333476
  have htrace : WordTrace (prefixWord ++ tailWord_3333476) baseStart_3333476 baseEnd_3333476 := by
    simpa [prefixWord, tailWord_3333476, baseEnd_3333476] using wordTrace_append hprefix tailTrace_3333476
  have hstable : (prefixWord ++ tailWord_3333476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333476).length < 2 ^ (prefixWord ++ tailWord_3333476).sum := by decide
  have hdescent : baseEnd_3333476 < baseStart_3333476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333533 : List Nat := [1, 4, 2, 1, 3, 2, 2, 2, 2, 4]
def baseStart_3333533 : Nat := 118140960795 + 3333533 * 2 ^ 59
def prefixEnd_3333533 : Nat := 4983230072969 + 3 ^ 40 * 3333533 * 2
def baseEnd_3333533 : Nat := 570568235541470423502289

theorem tailTrace_3333533 : CollatzResearch.WordTrace tailWord_3333533 prefixEnd_3333533 570568235541470423502289 := by
  unfold tailWord_3333533
  simp only [CollatzResearch.WordTrace]
  refine ⟨121583937032186737955461253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81055958021457825303640835 121583937032186737955461253)
  ·
    refine ⟨22796988193535013366648985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121583937032186737955461253 22796988193535013366648985)
    ·
      refine ⟨17097741145151260024986739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22796988193535013366648985 17097741145151260024986739)
      ·
        refine ⟨25646611717726890037480109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17097741145151260024986739 25646611717726890037480109)
        ·
          refine ⟨9617479394147583764055041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25646611717726890037480109 9617479394147583764055041)
          ·
            refine ⟨7213109545610687823041281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9617479394147583764055041 7213109545610687823041281)
            ·
              refine ⟨5409832159208015867280961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7213109545610687823041281 5409832159208015867280961)
              ·
                refine ⟨4057374119406011900460721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5409832159208015867280961 4057374119406011900460721)
                ·
                  refine ⟨3043030589554508925345541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4057374119406011900460721 3043030589554508925345541)
                  ·
                    refine ⟨570568235541470423502289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3043030589554508925345541 570568235541470423502289)
                    ·
                      rfl

theorem cell23_3333533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_3333533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333533 prefixEnd_3333533 := by exact prefixLift 3333533
  have htrace : WordTrace (prefixWord ++ tailWord_3333533) baseStart_3333533 baseEnd_3333533 := by
    simpa [prefixWord, tailWord_3333533, baseEnd_3333533] using wordTrace_append hprefix tailTrace_3333533
  have hstable : (prefixWord ++ tailWord_3333533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333533).length < 2 ^ (prefixWord ++ tailWord_3333533).sum := by decide
  have hdescent : baseEnd_3333533 < baseStart_3333533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333539 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 3]
def baseStart_3333539 : Nat := 118140960795 + 3333539 * 2 ^ 59
def prefixEnd_3333539 : Nat := 4983230072969 + 3 ^ 40 * 3333539 * 2
def baseEnd_3333539 : Nat := 1711707787508338247031839

theorem tailTrace_3333539 : CollatzResearch.WordTrace tailWord_3333539 prefixEnd_3333539 1711707787508338247031839 := by
  unfold tailWord_3333539
  simp only [CollatzResearch.WordTrace]
  refine ⟨121584155870165000980179671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81056103913443333986786447 121584155870165000980179671)
  ·
    refine ⟨182376233805247501470269507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121584155870165000980179671 182376233805247501470269507)
    ·
      refine ⟨273564350707871252205404261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182376233805247501470269507 273564350707871252205404261)
      ·
        refine ⟨51293315757725859788513299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273564350707871252205404261 51293315757725859788513299)
        ·
          refine ⟨76939973636588789682769949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51293315757725859788513299 76939973636588789682769949)
          ·
            refine ⟨28852490113720796131038731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76939973636588789682769949 28852490113720796131038731)
            ·
              refine ⟨43278735170581194196558097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28852490113720796131038731 43278735170581194196558097)
              ·
                refine ⟨32459051377935895647418573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43278735170581194196558097 32459051377935895647418573)
                ·
                  refine ⟨12172144266725960867781965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32459051377935895647418573 12172144266725960867781965)
                  ·
                    refine ⟨4564554100022235325418237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12172144266725960867781965 4564554100022235325418237)
                    ·
                      refine ⟨1711707787508338247031839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4564554100022235325418237 1711707787508338247031839)
                      ·
                        rfl

theorem cell23_3333539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_3333539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333539 prefixEnd_3333539 := by exact prefixLift 3333539
  have htrace : WordTrace (prefixWord ++ tailWord_3333539) baseStart_3333539 baseEnd_3333539 := by
    simpa [prefixWord, tailWord_3333539, baseEnd_3333539] using wordTrace_append hprefix tailTrace_3333539
  have hstable : (prefixWord ++ tailWord_3333539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333539).length < 2 ^ (prefixWord ++ tailWord_3333539).sum := by decide
  have hdescent : baseEnd_3333539 < baseStart_3333539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333589 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 4, 6]
def baseStart_3333589 : Nat := 118140960795 + 3333589 * 2 ^ 59
def prefixEnd_3333589 : Nat := 4983230072969 + 3 ^ 40 * 3333589 * 2
def baseEnd_3333589 : Nat := 570577820513687683802203

theorem tailTrace_3333589 : CollatzResearch.WordTrace tailWord_3333589 prefixEnd_3333589 570577820513687683802203 := by
  unfold tailWord_3333589
  simp only [CollatzResearch.WordTrace]
  refine ⟨121585979519983859519499821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81057319679989239679666547 121585979519983859519499821)
  ·
    refine ⟨45594742319993947319812433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121585979519983859519499821 45594742319993947319812433)
    ·
      refine ⟨34196056739995460489859325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45594742319993947319812433 34196056739995460489859325)
      ·
        refine ⟨12823521277498297683697247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34196056739995460489859325 12823521277498297683697247)
        ·
          refine ⟨19235281916247446525545871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12823521277498297683697247 19235281916247446525545871)
          ·
            refine ⟨28852922874371169788318807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19235281916247446525545871 28852922874371169788318807)
            ·
              refine ⟨43279384311556754682478211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28852922874371169788318807 43279384311556754682478211)
              ·
                refine ⟨64919076467335132023717317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43279384311556754682478211 64919076467335132023717317)
                ·
                  refine ⟨12172326837625337254446997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64919076467335132023717317 12172326837625337254446997)
                  ·
                    refine ⟨570577820513687683802203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12172326837625337254446997 570577820513687683802203)
                    ·
                      rfl

theorem cell23_3333589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_3333589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333589 prefixEnd_3333589 := by exact prefixLift 3333589
  have htrace : WordTrace (prefixWord ++ tailWord_3333589) baseStart_3333589 baseEnd_3333589 := by
    simpa [prefixWord, tailWord_3333589, baseEnd_3333589] using wordTrace_append hprefix tailTrace_3333589
  have hstable : (prefixWord ++ tailWord_3333589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333589).length < 2 ^ (prefixWord ++ tailWord_3333589).sum := by decide
  have hdescent : baseEnd_3333589 < baseStart_3333589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333590 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_3333590 : Nat := 118140960795 + 3333590 * 2 ^ 59
def prefixEnd_3333590 : Nat := 4983230072969 + 3 ^ 40 * 3333590 * 2
def baseEnd_3333590 : Nat := 1711733975021717547494105

theorem tailTrace_3333590 : CollatzResearch.WordTrace tailWord_3333590 prefixEnd_3333590 1711733975021717547494105 := by
  unfold tailWord_3333590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7599125999561264793142889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81057343995320157793524149 7599125999561264793142889)
  ·
    refine ⟨5699344499670948594857167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7599125999561264793142889 5699344499670948594857167)
    ·
      refine ⟨8549016749506422892285751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5699344499670948594857167 8549016749506422892285751)
      ·
        refine ⟨12823525124259634338428627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8549016749506422892285751 12823525124259634338428627)
        ·
          refine ⟨19235287686389451507642941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12823525124259634338428627 19235287686389451507642941)
          ·
            refine ⟨7213232882396044315366103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19235287686389451507642941 7213232882396044315366103)
            ·
              refine ⟨10819849323594066473049155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7213232882396044315366103 10819849323594066473049155)
              ·
                refine ⟨16229773985391099709573733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10819849323594066473049155 16229773985391099709573733)
                ·
                  refine ⟨3043082622260831195545075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16229773985391099709573733 3043082622260831195545075)
                  ·
                    refine ⟨4564623933391246793317613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3043082622260831195545075 4564623933391246793317613)
                    ·
                      refine ⟨1711733975021717547494105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4564623933391246793317613 1711733975021717547494105)
                      ·
                        rfl

theorem cell23_3333590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_3333590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333590 prefixEnd_3333590 := by exact prefixLift 3333590
  have htrace : WordTrace (prefixWord ++ tailWord_3333590) baseStart_3333590 baseEnd_3333590 := by
    simpa [prefixWord, tailWord_3333590, baseEnd_3333590] using wordTrace_append hprefix tailTrace_3333590
  have hstable : (prefixWord ++ tailWord_3333590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333590).length < 2 ^ (prefixWord ++ tailWord_3333590).sum := by decide
  have hdescent : baseEnd_3333590 < baseStart_3333590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333664 : List Nat := [2, 1, 1, 6, 1, 3, 2, 1, 2, 2, 2]
def baseStart_3333664 : Nat := 118140960795 + 3333664 * 2 ^ 59
def prefixEnd_3333664 : Nat := 4983230072969 + 3 ^ 40 * 3333664 * 2
def baseEnd_3333664 : Nat := 1711771972590150257968765

theorem tailTrace_3333664 : CollatzResearch.WordTrace tailWord_3333664 prefixEnd_3333664 1711771972590150257968765 := by
  unfold tailWord_3333664
  simp only [CollatzResearch.WordTrace]
  refine ⟨60794357497356073664240023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81059143329808098218986697 60794357497356073664240023)
  ·
    refine ⟨91191536246034110496360035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60794357497356073664240023 91191536246034110496360035)
    ·
      refine ⟨136787304369051165744540053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91191536246034110496360035 136787304369051165744540053)
      ·
        refine ⟨6411904892299273394275315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 136787304369051165744540053 6411904892299273394275315)
        ·
          refine ⟨9617857338448910091412973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6411904892299273394275315 9617857338448910091412973)
          ·
            refine ⟨3606696501918341284279865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9617857338448910091412973 3606696501918341284279865)
            ·
              refine ⟨2705022376438755963209899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3606696501918341284279865 2705022376438755963209899)
              ·
                refine ⟨4057533564658133944814849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2705022376438755963209899 4057533564658133944814849)
                ·
                  refine ⟨3043150173493600458611137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4057533564658133944814849 3043150173493600458611137)
                  ·
                    refine ⟨2282362630120200343958353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3043150173493600458611137 2282362630120200343958353)
                    ·
                      refine ⟨1711771972590150257968765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2282362630120200343958353 1711771972590150257968765)
                      ·
                        rfl

theorem cell23_3333664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_3333664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333664 prefixEnd_3333664 := by exact prefixLift 3333664
  have htrace : WordTrace (prefixWord ++ tailWord_3333664) baseStart_3333664 baseEnd_3333664 := by
    simpa [prefixWord, tailWord_3333664, baseEnd_3333664] using wordTrace_append hprefix tailTrace_3333664
  have hstable : (prefixWord ++ tailWord_3333664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333664).length < 2 ^ (prefixWord ++ tailWord_3333664).sum := by decide
  have hdescent : baseEnd_3333664 < baseStart_3333664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333753 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 5, 1, 3]
def baseStart_3333753 : Nat := 118140960795 + 3333753 * 2 ^ 59
def prefixEnd_3333753 : Nat := 4983230072969 + 3 ^ 40 * 3333753 * 2
def baseEnd_3333753 : Nat := 1711817672368400409755855

theorem tailTrace_3333753 : CollatzResearch.WordTrace tailWord_3333753 prefixEnd_3333753 1711817672368400409755855 := by
  unfold tailWord_3333753
  simp only [CollatzResearch.WordTrace]
  refine ⟨121591961091389715528469913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81061307394259810352313275 121591961091389715528469913)
  ·
    refine ⟨91193970818542286646352435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121591961091389715528469913 91193970818542286646352435)
    ·
      refine ⟨136790956227813429969528653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91193970818542286646352435 136790956227813429969528653)
      ·
        refine ⟨51296608585430036238573245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136790956227813429969528653 51296608585430036238573245)
        ·
          refine ⟨19236228219536263589464967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51296608585430036238573245 19236228219536263589464967)
          ·
            refine ⟨28854342329304395384197451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19236228219536263589464967 28854342329304395384197451)
            ·
              refine ⟨43281513493956593076296177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28854342329304395384197451 43281513493956593076296177)
              ·
                refine ⟨32461135120467444807222133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43281513493956593076296177 32461135120467444807222133)
                ·
                  refine ⟨3043231417543822950677075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32461135120467444807222133 3043231417543822950677075)
                  ·
                    refine ⟨4564847126315734426015613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3043231417543822950677075 4564847126315734426015613)
                    ·
                      refine ⟨1711817672368400409755855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4564847126315734426015613 1711817672368400409755855)
                      ·
                        rfl

theorem cell23_3333753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_3333753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333753 prefixEnd_3333753 := by exact prefixLift 3333753
  have htrace : WordTrace (prefixWord ++ tailWord_3333753) baseStart_3333753 baseEnd_3333753 := by
    simpa [prefixWord, tailWord_3333753, baseEnd_3333753] using wordTrace_append hprefix tailTrace_3333753
  have hstable : (prefixWord ++ tailWord_3333753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333753).length < 2 ^ (prefixWord ++ tailWord_3333753).sum := by decide
  have hdescent : baseEnd_3333753 < baseStart_3333753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333763 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 4, 3, 2]
def baseStart_3333763 : Nat := 118140960795 + 3333763 * 2 ^ 59
def prefixEnd_3333763 : Nat := 4983230072969 + 3 ^ 40 * 3333763 * 2
def baseEnd_3333763 : Nat := 1711822807174945370630809

theorem tailTrace_3333763 : CollatzResearch.WordTrace tailWord_3333763 prefixEnd_3333763 1711822807174945370630809 := by
  unfold tailWord_3333763
  simp only [CollatzResearch.WordTrace]
  refine ⟨121592325821353487236333943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81061550547568991490889295 121592325821353487236333943)
  ·
    refine ⟨182388488732030230854500915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121592325821353487236333943 182388488732030230854500915)
    ·
      refine ⟨273582733098045346281751373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182388488732030230854500915 273582733098045346281751373)
      ·
        refine ⟨102593524911767004855656765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273582733098045346281751373 102593524911767004855656765)
        ·
          refine ⟨38472571841912626820871287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102593524911767004855656765 38472571841912626820871287)
          ·
            refine ⟨57708857762868940231306931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38472571841912626820871287 57708857762868940231306931)
            ·
              refine ⟨86563286644303410346960397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57708857762868940231306931 86563286644303410346960397)
              ·
                refine ⟨32461232491613778880110149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86563286644303410346960397 32461232491613778880110149)
                ·
                  refine ⟨6086481092177583540020653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32461232491613778880110149 6086481092177583540020653)
                  ·
                    refine ⟨2282430409566593827507745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6086481092177583540020653 2282430409566593827507745)
                    ·
                      refine ⟨1711822807174945370630809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2282430409566593827507745 1711822807174945370630809)
                      ·
                        rfl

theorem cell23_3333763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 3, 2].length) (baseStart_3333763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333763 prefixEnd_3333763 := by exact prefixLift 3333763
  have htrace : WordTrace (prefixWord ++ tailWord_3333763) baseStart_3333763 baseEnd_3333763 := by
    simpa [prefixWord, tailWord_3333763, baseEnd_3333763] using wordTrace_append hprefix tailTrace_3333763
  have hstable : (prefixWord ++ tailWord_3333763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333763).length < 2 ^ (prefixWord ++ tailWord_3333763).sum := by decide
  have hdescent : baseEnd_3333763 < baseStart_3333763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333770 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 3, 1, 3]
def baseStart_3333770 : Nat := 118140960795 + 3333770 * 2 ^ 59
def prefixEnd_3333770 : Nat := 4983230072969 + 3 ^ 40 * 3333770 * 2
def baseEnd_3333770 : Nat := 1711826401539526843243277

theorem tailTrace_3333770 : CollatzResearch.WordTrace tailWord_3333770 prefixEnd_3333770 1711826401539526843243277 := by
  unfold tailWord_3333770
  simp only [CollatzResearch.WordTrace]
  refine ⟨30398145283082031857959691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81061720754885418287892509 30398145283082031857959691)
  ·
    refine ⟨45597217924623047786939537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30398145283082031857959691 45597217924623047786939537)
    ·
      refine ⟨34197913443467285840204653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45597217924623047786939537 34197913443467285840204653)
      ·
        refine ⟨12824217541300232190076745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34197913443467285840204653 12824217541300232190076745)
        ·
          refine ⟨9618163155975174142557559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12824217541300232190076745 9618163155975174142557559)
          ·
            refine ⟨14427244733962761213836339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9618163155975174142557559 14427244733962761213836339)
            ·
              refine ⟨21640867100944141820754509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14427244733962761213836339 21640867100944141820754509)
              ·
                refine ⟨8115325162854053182782941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21640867100944141820754509 8115325162854053182782941)
                ·
                  refine ⟨3043246936070269943543603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8115325162854053182782941 3043246936070269943543603)
                  ·
                    refine ⟨4564870404105404915315405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3043246936070269943543603 4564870404105404915315405)
                    ·
                      refine ⟨1711826401539526843243277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4564870404105404915315405 1711826401539526843243277)
                      ·
                        rfl

theorem cell23_3333770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_3333770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333770 prefixEnd_3333770 := by exact prefixLift 3333770
  have htrace : WordTrace (prefixWord ++ tailWord_3333770) baseStart_3333770 baseEnd_3333770 := by
    simpa [prefixWord, tailWord_3333770, baseEnd_3333770] using wordTrace_append hprefix tailTrace_3333770
  have hstable : (prefixWord ++ tailWord_3333770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333770).length < 2 ^ (prefixWord ++ tailWord_3333770).sum := by decide
  have hdescent : baseEnd_3333770 < baseStart_3333770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333776 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 4]
def baseStart_3333776 : Nat := 118140960795 + 3333776 * 2 ^ 59
def prefixEnd_3333776 : Nat := 4983230072969 + 3 ^ 40 * 3333776 * 2
def baseEnd_3333776 : Nat := 1711829482423453819768249

theorem tailTrace_3333776 : CollatzResearch.WordTrace tailWord_3333776 prefixEnd_3333776 1711829482423453819768249 := by
  unfold tailWord_3333776
  simp only [CollatzResearch.WordTrace]
  refine ⟨60796399985153195228278591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81061866646870926971038121 60796399985153195228278591)
  ·
    refine ⟨91194599977729792842417887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60796399985153195228278591 91194599977729792842417887)
    ·
      refine ⟨136791899966594689263626831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91194599977729792842417887 136791899966594689263626831)
      ·
        refine ⟨205187849949892033895440247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136791899966594689263626831 205187849949892033895440247)
        ·
          refine ⟨307781774924838050843160371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205187849949892033895440247 307781774924838050843160371)
          ·
            refine ⟨461672662387257076264740557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307781774924838050843160371 461672662387257076264740557)
            ·
              refine ⟨173127248395221403599277709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 461672662387257076264740557 173127248395221403599277709)
              ·
                refine ⟨64922718148208026349729141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173127248395221403599277709 64922718148208026349729141)
                ·
                  refine ⟨6086504826394502470287107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64922718148208026349729141 6086504826394502470287107)
                  ·
                    refine ⟨9129757239591753705430661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6086504826394502470287107 9129757239591753705430661)
                    ·
                      refine ⟨1711829482423453819768249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9129757239591753705430661 1711829482423453819768249)
                      ·
                        rfl

theorem cell23_3333776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 4].length) (baseStart_3333776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333776 prefixEnd_3333776 := by exact prefixLift 3333776
  have htrace : WordTrace (prefixWord ++ tailWord_3333776) baseStart_3333776 baseEnd_3333776 := by
    simpa [prefixWord, tailWord_3333776, baseEnd_3333776] using wordTrace_append hprefix tailTrace_3333776
  have hstable : (prefixWord ++ tailWord_3333776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333776).length < 2 ^ (prefixWord ++ tailWord_3333776).sum := by decide
  have hdescent : baseEnd_3333776 < baseStart_3333776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333790 : List Nat := [4, 3, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_3333790 : Nat := 118140960795 + 3333790 * 2 ^ 59
def prefixEnd_3333790 : Nat := 4983230072969 + 3 ^ 40 * 3333790 * 2
def baseEnd_3333790 : Nat := 570612223717538921664395

theorem tailTrace_3333790 : CollatzResearch.WordTrace tailWord_3333790 prefixEnd_3333790 570612223717538921664395 := by
  unfold tailWord_3333790
  simp only [CollatzResearch.WordTrace]
  refine ⟨15199163824031958855945853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81062207061503780565044549 15199163824031958855945853)
  ·
    refine ⟨5699686434011984570979695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15199163824031958855945853 5699686434011984570979695)
    ·
      refine ⟨8549529651017976856469543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5699686434011984570979695 8549529651017976856469543)
      ·
        refine ⟨12824294476526965284704315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8549529651017976856469543 12824294476526965284704315)
        ·
          refine ⟨19236441714790447927056473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12824294476526965284704315 19236441714790447927056473)
          ·
            refine ⟨14427331286092835945292355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19236441714790447927056473 14427331286092835945292355)
            ·
              refine ⟨21640996929139253917938533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14427331286092835945292355 21640996929139253917938533)
              ·
                refine ⟨4057686924213610109613475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21640996929139253917938533 4057686924213610109613475)
                ·
                  refine ⟨6086530386320415164420213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4057686924213610109613475 6086530386320415164420213)
                  ·
                    refine ⟨570612223717538921664395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6086530386320415164420213 570612223717538921664395)
                    ·
                      rfl

theorem cell23_3333790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_3333790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333790 prefixEnd_3333790 := by exact prefixLift 3333790
  have htrace : WordTrace (prefixWord ++ tailWord_3333790) baseStart_3333790 baseEnd_3333790 := by
    simpa [prefixWord, tailWord_3333790, baseEnd_3333790] using wordTrace_append hprefix tailTrace_3333790
  have hstable : (prefixWord ++ tailWord_3333790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333790).length < 2 ^ (prefixWord ++ tailWord_3333790).sum := by decide
  have hdescent : baseEnd_3333790 < baseStart_3333790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333810 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2]
def baseStart_3333810 : Nat := 118140960795 + 3333810 * 2 ^ 59
def prefixEnd_3333810 : Nat := 4983230072969 + 3 ^ 40 * 3333810 * 2
def baseEnd_3333810 : Nat := 1711846940765706686743093

theorem tailTrace_3333810 : CollatzResearch.WordTrace tailWord_3333810 prefixEnd_3333810 1711846940765706686743093 := by
  unfold tailWord_3333810
  simp only [CollatzResearch.WordTrace]
  refine ⟨30398510013045803565823721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81062693368122142842196589 30398510013045803565823721)
  ·
    refine ⟨22798882509784352674367791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30398510013045803565823721 22798882509784352674367791)
    ·
      refine ⟨34198323764676529011551687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22798882509784352674367791 34198323764676529011551687)
      ·
        refine ⟨51297485647014793517327531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34198323764676529011551687 51297485647014793517327531)
        ·
          refine ⟨76946228470522190275991297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51297485647014793517327531 76946228470522190275991297)
          ·
            refine ⟨57709671352891642706993473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76946228470522190275991297 57709671352891642706993473)
            ·
              refine ⟨43282253514668732030245105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57709671352891642706993473 43282253514668732030245105)
              ·
                refine ⟨32461690136001549022683829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43282253514668732030245105 32461690136001549022683829)
                ·
                  refine ⟨3043283450250145220876609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32461690136001549022683829 3043283450250145220876609)
                  ·
                    refine ⟨2282462587687608915657457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3043283450250145220876609 2282462587687608915657457)
                    ·
                      refine ⟨1711846940765706686743093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2282462587687608915657457 1711846940765706686743093)
                      ·
                        rfl

theorem cell23_3333810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_3333810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333810 prefixEnd_3333810 := by exact prefixLift 3333810
  have htrace : WordTrace (prefixWord ++ tailWord_3333810) baseStart_3333810 baseEnd_3333810 := by
    simpa [prefixWord, tailWord_3333810, baseEnd_3333810] using wordTrace_append hprefix tailTrace_3333810
  have hstable : (prefixWord ++ tailWord_3333810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333810).length < 2 ^ (prefixWord ++ tailWord_3333810).sum := by decide
  have hdescent : baseEnd_3333810 < baseStart_3333810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333814 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_3333814 : Nat := 118140960795 + 3333814 * 2 ^ 59
def prefixEnd_3333814 : Nat := 4983230072969 + 3 ^ 40 * 3333814 * 2
def baseEnd_3333814 : Nat := 1711848994688324671093075

theorem tailTrace_3333814 : CollatzResearch.WordTrace tailWord_3333814 prefixEnd_3333814 1711848994688324671093075 := by
  unfold tailWord_3333814
  simp only [CollatzResearch.WordTrace]
  refine ⟨7599636621510545184152531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81062790629445815297626997 7599636621510545184152531)
  ·
    refine ⟨11399454932265817776228797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7599636621510545184152531 11399454932265817776228797)
    ·
      refine ⟨4274795599599681666085799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11399454932265817776228797 4274795599599681666085799)
      ·
        refine ⟨6412193399399522499128699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4274795599599681666085799 6412193399399522499128699)
        ·
          refine ⟨9618290099099283748693049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6412193399399522499128699 9618290099099283748693049)
          ·
            refine ⟨7213717574324462811519787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9618290099099283748693049 7213717574324462811519787)
            ·
              refine ⟨10820576361486694217279681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7213717574324462811519787 10820576361486694217279681)
              ·
                refine ⟨8115432271115020662959761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10820576361486694217279681 8115432271115020662959761)
                ·
                  refine ⟨6086574203336265497219821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8115432271115020662959761 6086574203336265497219821)
                  ·
                    refine ⟨2282465326251099561457433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6086574203336265497219821 2282465326251099561457433)
                    ·
                      refine ⟨1711848994688324671093075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2282465326251099561457433 1711848994688324671093075)
                      ·
                        rfl

theorem cell23_3333814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_3333814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333814 prefixEnd_3333814 := by exact prefixLift 3333814
  have htrace : WordTrace (prefixWord ++ tailWord_3333814) baseStart_3333814 baseEnd_3333814 := by
    simpa [prefixWord, tailWord_3333814, baseEnd_3333814] using wordTrace_append hprefix tailTrace_3333814
  have hstable : (prefixWord ++ tailWord_3333814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333814).length < 2 ^ (prefixWord ++ tailWord_3333814).sum := by decide
  have hdescent : baseEnd_3333814 < baseStart_3333814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333856 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 5]
def baseStart_3333856 : Nat := 118140960795 + 3333856 * 2 ^ 59
def prefixEnd_3333856 : Nat := 4983230072969 + 3 ^ 40 * 3333856 * 2
def baseEnd_3333856 : Nat := 1711870560875813506767881

theorem tailTrace_3333856 : CollatzResearch.WordTrace tailWord_3333856 prefixEnd_3333856 1711870560875813506767881 := by
  unfold tailWord_3333856
  simp only [CollatzResearch.WordTrace]
  refine ⟨60797858905008282059734711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81063811873344376079646281 60797858905008282059734711)
  ·
    refine ⟨91196788357512423089602067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60797858905008282059734711 91196788357512423089602067)
    ·
      refine ⟨136795182536268634634403101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91196788357512423089602067 136795182536268634634403101)
      ·
        refine ⟨51298193451100737987901163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136795182536268634634403101 51298193451100737987901163)
        ·
          refine ⟨76947290176651106981851745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51298193451100737987901163 76947290176651106981851745)
          ·
            refine ⟨57710467632488330236388809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76947290176651106981851745 57710467632488330236388809)
            ·
              refine ⟨43282850724366247677291607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57710467632488330236388809 43282850724366247677291607)
              ·
                refine ⟨64924276086549371515937411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43282850724366247677291607 64924276086549371515937411)
                ·
                  refine ⟨97386414129824057273906117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64924276086549371515937411 97386414129824057273906117)
                  ·
                    refine ⟨18259952649342010738857397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97386414129824057273906117 18259952649342010738857397)
                    ·
                      refine ⟨1711870560875813506767881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18259952649342010738857397 1711870560875813506767881)
                      ·
                        rfl

theorem cell23_3333856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_3333856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333856 prefixEnd_3333856 := by exact prefixLift 3333856
  have htrace : WordTrace (prefixWord ++ tailWord_3333856) baseStart_3333856 baseEnd_3333856 := by
    simpa [prefixWord, tailWord_3333856, baseEnd_3333856] using wordTrace_append hprefix tailTrace_3333856
  have hstable : (prefixWord ++ tailWord_3333856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333856).length < 2 ^ (prefixWord ++ tailWord_3333856).sum := by decide
  have hdescent : baseEnd_3333856 < baseStart_3333856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333878 : List Nat := [5, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2]
def baseStart_3333878 : Nat := 118140960795 + 3333878 * 2 ^ 59
def prefixEnd_3333878 : Nat := 4983230072969 + 3 ^ 40 * 3333878 * 2
def baseEnd_3333878 : Nat := 1711881857450212420692781

theorem tailTrace_3333878 : CollatzResearch.WordTrace tailWord_3333878 prefixEnd_3333878 1711881857450212420692781 := by
  unfold tailWord_3333878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7599782513496053867298143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81064346810624574584513525 7599782513496053867298143)
  ·
    refine ⟨11399673770244080800947215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7599782513496053867298143 11399673770244080800947215)
    ·
      refine ⟨17099510655366121201420823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11399673770244080800947215 17099510655366121201420823)
      ·
        refine ⟨25649265983049181802131235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17099510655366121201420823 25649265983049181802131235)
        ·
          refine ⟨38473898974573772703196853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25649265983049181802131235 38473898974573772703196853)
          ·
            refine ⟨3606928028866291190924705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38473898974573772703196853 3606928028866291190924705)
            ·
              refine ⟨2705196021649718393193529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3606928028866291190924705 2705196021649718393193529)
              ·
                refine ⟨2028897016237288794895147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2705196021649718393193529 2028897016237288794895147)
                ·
                  refine ⟨3043345524355933192342721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2028897016237288794895147 3043345524355933192342721)
                  ·
                    refine ⟨2282509143266949894257041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3043345524355933192342721 2282509143266949894257041)
                    ·
                      refine ⟨1711881857450212420692781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2282509143266949894257041 1711881857450212420692781)
                      ·
                        rfl

theorem cell23_3333878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_3333878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333878 prefixEnd_3333878 := by exact prefixLift 3333878
  have htrace : WordTrace (prefixWord ++ tailWord_3333878) baseStart_3333878 baseEnd_3333878 := by
    simpa [prefixWord, tailWord_3333878, baseEnd_3333878] using wordTrace_append hprefix tailTrace_3333878
  have hstable : (prefixWord ++ tailWord_3333878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333878).length < 2 ^ (prefixWord ++ tailWord_3333878).sum := by decide
  have hdescent : baseEnd_3333878 < baseStart_3333878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333900 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 1, 4, 2]
def baseStart_3333900 : Nat := 118140960795 + 3333900 * 2 ^ 59
def prefixEnd_3333900 : Nat := 4983230072969 + 3 ^ 40 * 3333900 * 2
def baseEnd_3333900 : Nat := 1711893154024611334617679

theorem tailTrace_3333900 : CollatzResearch.WordTrace tailWord_3333900 prefixEnd_3333900 1711893154024611334617679 := by
  unfold tailWord_3333900
  simp only [CollatzResearch.WordTrace]
  refine ⟨60798661310928579817035577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81064881747904773089380769 60798661310928579817035577)
  ·
    refine ⟨45598995983196434862776683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60798661310928579817035577 45598995983196434862776683)
    ·
      refine ⟨68398493974794652294165025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45598995983196434862776683 68398493974794652294165025)
      ·
        refine ⟨51298870481095989220623769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68398493974794652294165025 51298870481095989220623769)
        ·
          refine ⟨38474152860821991915467827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51298870481095989220623769 38474152860821991915467827)
          ·
            refine ⟨57711229291232987873201741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38474152860821991915467827 57711229291232987873201741)
            ·
              refine ⟨21641710984212370452450653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57711229291232987873201741 21641710984212370452450653)
              ·
                refine ⟨8115641619079638919668995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21641710984212370452450653 8115641619079638919668995)
                ·
                  refine ⟨12173462428619458379503493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8115641619079638919668995 12173462428619458379503493)
                  ·
                    refine ⟨2282524205366148446156905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12173462428619458379503493 2282524205366148446156905)
                    ·
                      refine ⟨1711893154024611334617679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2282524205366148446156905 1711893154024611334617679)
                      ·
                        rfl

theorem cell23_3333900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_3333900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333900 prefixEnd_3333900 := by exact prefixLift 3333900
  have htrace : WordTrace (prefixWord ++ tailWord_3333900) baseStart_3333900 baseEnd_3333900 := by
    simpa [prefixWord, tailWord_3333900, baseEnd_3333900] using wordTrace_append hprefix tailTrace_3333900
  have hstable : (prefixWord ++ tailWord_3333900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333900).length < 2 ^ (prefixWord ++ tailWord_3333900).sum := by decide
  have hdescent : baseEnd_3333900 < baseStart_3333900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333901 : List Nat := [1, 7, 2, 1, 1, 1, 3, 7]
def baseStart_3333901 : Nat := 118140960795 + 3333901 * 2 ^ 59
def prefixEnd_3333901 : Nat := 4983230072969 + 3 ^ 40 * 3333901 * 2
def baseEnd_3333901 : Nat := 63403469166861697433525

theorem tailTrace_3333901 : CollatzResearch.WordTrace tailWord_3333901 prefixEnd_3333901 63403469166861697433525 := by
  unfold tailWord_3333901
  simp only [CollatzResearch.WordTrace]
  refine ⟨121597359094853536804857557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81064906063235691203238371 121597359094853536804857557)
  ·
    refine ⟨2849938103785629768863849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 121597359094853536804857557 2849938103785629768863849)
    ·
      refine ⟨2137453577839222326647887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2849938103785629768863849 2137453577839222326647887)
      ·
        refine ⟨3206180366758833489971831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2137453577839222326647887 3206180366758833489971831)
        ·
          refine ⟨4809270550138250234957747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3206180366758833489971831 4809270550138250234957747)
          ·
            refine ⟨7213905825207375352436621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4809270550138250234957747 7213905825207375352436621)
            ·
              refine ⟨2705214684452765757163733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7213905825207375352436621 2705214684452765757163733)
              ·
                refine ⟨63403469166861697433525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2705214684452765757163733 63403469166861697433525)
                ·
                  rfl

theorem cell23_3333901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 7].length) (baseStart_3333901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333901 prefixEnd_3333901 := by exact prefixLift 3333901
  have htrace : WordTrace (prefixWord ++ tailWord_3333901) baseStart_3333901 baseEnd_3333901 := by
    simpa [prefixWord, tailWord_3333901, baseEnd_3333901] using wordTrace_append hprefix tailTrace_3333901
  have hstable : (prefixWord ++ tailWord_3333901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333901).length < 2 ^ (prefixWord ++ tailWord_3333901).sum := by decide
  have hdescent : baseEnd_3333901 < baseStart_3333901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333940 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 7]
def baseStart_3333940 : Nat := 118140960795 + 3333940 * 2 ^ 59
def prefixEnd_3333940 : Nat := 4983230072969 + 3 ^ 40 * 3333940 * 2
def baseEnd_3333940 : Nat := 190212632583421242013055

theorem tailTrace_3333940 : CollatzResearch.WordTrace tailWord_3333940 prefixEnd_3333940 190212632583421242013055 := by
  unfold tailWord_3333940
  simp only [CollatzResearch.WordTrace]
  refine ⟨60799390770856123232763637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81065854361141497643684849 60799390770856123232763637)
  ·
    refine ⟨5699942884767761553071591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60799390770856123232763637 5699942884767761553071591)
    ·
      refine ⟨8549914327151642329607387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5699942884767761553071591 8549914327151642329607387)
      ·
        refine ⟨12824871490727463494411081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8549914327151642329607387 12824871490727463494411081)
        ·
          refine ⟨9618653618045597620808311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12824871490727463494411081 9618653618045597620808311)
          ·
            refine ⟨14427980427068396431212467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9618653618045597620808311 14427980427068396431212467)
            ·
              refine ⟨21641970640602594646818701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14427980427068396431212467 21641970640602594646818701)
              ·
                refine ⟨8115738990225972992557013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21641970640602594646818701 8115738990225972992557013)
                ·
                  refine ⟨190212632583421242013055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8115738990225972992557013 190212632583421242013055)
                  ·
                    rfl

theorem cell23_3333940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_3333940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333940 prefixEnd_3333940 := by exact prefixLift 3333940
  have htrace : WordTrace (prefixWord ++ tailWord_3333940) baseStart_3333940 baseEnd_3333940 := by
    simpa [prefixWord, tailWord_3333940, baseEnd_3333940] using wordTrace_append hprefix tailTrace_3333940
  have hstable : (prefixWord ++ tailWord_3333940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333940).length < 2 ^ (prefixWord ++ tailWord_3333940).sum := by decide
  have hdescent : baseEnd_3333940 < baseStart_3333940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3333951 : List Nat := [1, 1, 2, 2, 6, 1, 3, 1, 2, 2, 2]
def baseStart_3333951 : Nat := 118140960795 + 3333951 * 2 ^ 59
def prefixEnd_3333951 : Nat := 4983230072969 + 3 ^ 40 * 3333951 * 2
def baseEnd_3333951 : Nat := 1711919341537990635079945

theorem tailTrace_3333951 : CollatzResearch.WordTrace tailWord_3333951 prefixEnd_3333951 1711919341537990635079945 := by
  unfold tailWord_3333951
  simp only [CollatzResearch.WordTrace]
  refine ⟨121599182744672395344177707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81066121829781596896118471 121599182744672395344177707)
  ·
    refine ⟨182398774117008593016266561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121599182744672395344177707 182398774117008593016266561)
    ·
      refine ⟨136799080587756444762199921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182398774117008593016266561 136799080587756444762199921)
      ·
        refine ⟨102599310440817333571649941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136799080587756444762199921 102599310440817333571649941)
        ·
          refine ⟨4809342676913312511171091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102599310440817333571649941 4809342676913312511171091)
          ·
            refine ⟨7214014015369968766756637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4809342676913312511171091 7214014015369968766756637)
            ·
              refine ⟨2705255255763738287533739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7214014015369968766756637 2705255255763738287533739)
              ·
                refine ⟨4057882883645607431300609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2705255255763738287533739 4057882883645607431300609)
                ·
                  refine ⟨3043412162734205573475457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4057882883645607431300609 3043412162734205573475457)
                  ·
                    refine ⟨2282559122050654180106593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3043412162734205573475457 2282559122050654180106593)
                    ·
                      refine ⟨1711919341537990635079945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2282559122050654180106593 1711919341537990635079945)
                      ·
                        rfl

theorem cell23_3333951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 2, 2, 2].length) (baseStart_3333951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3333951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3333951 prefixEnd_3333951 := by exact prefixLift 3333951
  have htrace : WordTrace (prefixWord ++ tailWord_3333951) baseStart_3333951 baseEnd_3333951 := by
    simpa [prefixWord, tailWord_3333951, baseEnd_3333951] using wordTrace_append hprefix tailTrace_3333951
  have hstable : (prefixWord ++ tailWord_3333951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3333951).length < 2 ^ (prefixWord ++ tailWord_3333951).sum := by decide
  have hdescent : baseEnd_3333951 < baseStart_3333951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3333951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334047 : List Nat := [1, 1, 2, 5, 3, 1, 2, 2, 6]
def baseStart_3334047 : Nat := 118140960795 + 3334047 * 2 ^ 59
def prefixEnd_3334047 : Nat := 4983230072969 + 3 ^ 40 * 3334047 * 2
def baseEnd_3334047 : Nat := 190218737297869139942167

theorem tailTrace_3334047 : CollatzResearch.WordTrace tailWord_3334047 prefixEnd_3334047 190218737297869139942167 := by
  unfold tailWord_3334047
  simp only [CollatzResearch.WordTrace]
  refine ⟨121602684152324603739672395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81068456101549735826448263 121602684152324603739672395)
  ·
    refine ⟨182404026228486905609508593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121602684152324603739672395 182404026228486905609508593)
    ·
      refine ⟨136803019671365179207131445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182404026228486905609508593 136803019671365179207131445)
      ·
        refine ⟨12825283094190485550668573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136803019671365179207131445 12825283094190485550668573)
        ·
          refine ⟨4809481160321432081500715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12825283094190485550668573 4809481160321432081500715)
          ·
            refine ⟨7214221740482148122251073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4809481160321432081500715 7214221740482148122251073)
            ·
              refine ⟨5410666305361611091688305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7214221740482148122251073 5410666305361611091688305)
              ·
                refine ⟨4057999729021208318766229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5410666305361611091688305 4057999729021208318766229)
                ·
                  refine ⟨190218737297869139942167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4057999729021208318766229 190218737297869139942167)
                  ·
                    rfl

theorem cell23_3334047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 6].length) (baseStart_3334047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334047 prefixEnd_3334047 := by exact prefixLift 3334047
  have htrace : WordTrace (prefixWord ++ tailWord_3334047) baseStart_3334047 baseEnd_3334047 := by
    simpa [prefixWord, tailWord_3334047, baseEnd_3334047] using wordTrace_append hprefix tailTrace_3334047
  have hstable : (prefixWord ++ tailWord_3334047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334047).length < 2 ^ (prefixWord ++ tailWord_3334047).sum := by decide
  have hdescent : baseEnd_3334047 < baseStart_3334047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334053 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 2, 4, 5]
def baseStart_3334053 : Nat := 118140960795 + 3334053 * 2 ^ 59
def prefixEnd_3334053 : Nat := 4983230072969 + 3 ^ 40 * 3334053 * 2
def baseEnd_3334053 : Nat := 1711971716564749236004475

theorem tailTrace_3334053 : CollatzResearch.WordTrace tailWord_3334053 prefixEnd_3334053 1711971716564749236004475 := by
  unfold tailWord_3334053
  simp only [CollatzResearch.WordTrace]
  refine ⟨121602902990302866764390813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81068601993535244509593875 121602902990302866764390813)
  ·
    refine ⟨45601088621363575036646555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121602902990302866764390813 45601088621363575036646555)
    ·
      refine ⟨68401632932045362554969833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45601088621363575036646555 68401632932045362554969833)
      ·
        refine ⟨51301224699034021916227375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68401632932045362554969833 51301224699034021916227375)
        ·
          refine ⟨76951837048551032874341063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51301224699034021916227375 76951837048551032874341063)
          ·
            refine ⟨115427755572826549311511595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76951837048551032874341063 115427755572826549311511595)
            ·
              refine ⟨173141633359239823967267393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115427755572826549311511595 173141633359239823967267393)
              ·
                refine ⟨129856225019429867975450545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173141633359239823967267393 129856225019429867975450545)
                ·
                  refine ⟨97392168764572400981587909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129856225019429867975450545 97392168764572400981587909)
                  ·
                    refine ⟨18261031643357325184047733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97392168764572400981587909 18261031643357325184047733)
                    ·
                      refine ⟨1711971716564749236004475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18261031643357325184047733 1711971716564749236004475)
                      ·
                        rfl

theorem cell23_3334053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_3334053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334053 prefixEnd_3334053 := by exact prefixLift 3334053
  have htrace : WordTrace (prefixWord ++ tailWord_3334053) baseStart_3334053 baseEnd_3334053 := by
    simpa [prefixWord, tailWord_3334053, baseEnd_3334053] using wordTrace_append hprefix tailTrace_3334053
  have hstable : (prefixWord ++ tailWord_3334053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334053).length < 2 ^ (prefixWord ++ tailWord_3334053).sum := by decide
  have hdescent : baseEnd_3334053 < baseStart_3334053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334080 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 4]
def baseStart_3334080 : Nat := 118140960795 + 3334080 * 2 ^ 59
def prefixEnd_3334080 : Nat := 4983230072969 + 3 ^ 40 * 3334080 * 2
def baseEnd_3334080 : Nat := 1711985580542420630366851

theorem tailTrace_3334080 : CollatzResearch.WordTrace tailWord_3334080 prefixEnd_3334080 1711985580542420630366851 := by
  unfold tailWord_3334080
  simp only [CollatzResearch.WordTrace]
  refine ⟨60801943880602525187811847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81069258507470033583749129 60801943880602525187811847)
  ·
    refine ⟨91202915820903787781717771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60801943880602525187811847 91202915820903787781717771)
    ·
      refine ⟨136804373731355681672576657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91202915820903787781717771 136804373731355681672576657)
      ·
        refine ⟨102603280298516761254432493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136804373731355681672576657 102603280298516761254432493)
        ·
          refine ⟨38476230111943785470412185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102603280298516761254432493 38476230111943785470412185)
          ·
            refine ⟨28857172583957839102809139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38476230111943785470412185 28857172583957839102809139)
            ·
              refine ⟨43285758875936758654213709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28857172583957839102809139 43285758875936758654213709)
              ·
                refine ⟨16232159578476284495330141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43285758875936758654213709 16232159578476284495330141)
                ·
                  refine ⟨6087059841928606685748803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16232159578476284495330141 6087059841928606685748803)
                  ·
                    refine ⟨9130589762892910028623205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6087059841928606685748803 9130589762892910028623205)
                    ·
                      refine ⟨1711985580542420630366851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9130589762892910028623205 1711985580542420630366851)
                      ·
                        rfl

theorem cell23_3334080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_3334080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334080 prefixEnd_3334080 := by exact prefixLift 3334080
  have htrace : WordTrace (prefixWord ++ tailWord_3334080) baseStart_3334080 baseEnd_3334080 := by
    simpa [prefixWord, tailWord_3334080, baseEnd_3334080] using wordTrace_append hprefix tailTrace_3334080
  have hstable : (prefixWord ++ tailWord_3334080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334080).length < 2 ^ (prefixWord ++ tailWord_3334080).sum := by decide
  have hdescent : baseEnd_3334080 < baseStart_3334080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334083 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 5]
def baseStart_3334083 : Nat := 118140960795 + 3334083 * 2 ^ 59
def prefixEnd_3334083 : Nat := 4983230072969 + 3 ^ 40 * 3334083 * 2
def baseEnd_3334083 : Nat := 1711987120984384118629337

theorem tailTrace_3334083 : CollatzResearch.WordTrace tailWord_3334083 prefixEnd_3334083 1711987120984384118629337 := by
  unfold tailWord_3334083
  simp only [CollatzResearch.WordTrace]
  refine ⟨121603997180194181887982903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81069331453462787925321935 121603997180194181887982903)
  ·
    refine ⟨182405995770291272831974355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121603997180194181887982903 182405995770291272831974355)
    ·
      refine ⟨273608993655436909247961533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182405995770291272831974355 273608993655436909247961533)
      ·
        refine ⟨102603372620788840967985575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273608993655436909247961533 102603372620788840967985575)
        ·
          refine ⟨153905058931183261451978363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102603372620788840967985575 153905058931183261451978363)
          ·
            refine ⟨230857588396774892177967545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153905058931183261451978363 230857588396774892177967545)
            ·
              refine ⟨173143191297581169133475659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230857588396774892177967545 173143191297581169133475659)
              ·
                refine ⟨259714786946371753700213489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173143191297581169133475659 259714786946371753700213489)
                ·
                  refine ⟨194786090209778815275160117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259714786946371753700213489 194786090209778815275160117)
                  ·
                    refine ⟨18261195957166763932046261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 194786090209778815275160117 18261195957166763932046261)
                    ·
                      refine ⟨1711987120984384118629337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18261195957166763932046261 1711987120984384118629337)
                      ·
                        rfl

theorem cell23_3334083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_3334083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334083 prefixEnd_3334083 := by exact prefixLift 3334083
  have htrace : WordTrace (prefixWord ++ tailWord_3334083) baseStart_3334083 baseEnd_3334083 := by
    simpa [prefixWord, tailWord_3334083, baseEnd_3334083] using wordTrace_append hprefix tailTrace_3334083
  have hstable : (prefixWord ++ tailWord_3334083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334083).length < 2 ^ (prefixWord ++ tailWord_3334083).sum := by decide
  have hdescent : baseEnd_3334083 < baseStart_3334083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334090 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 1, 6]
def baseStart_3334090 : Nat := 118140960795 + 3334090 * 2 ^ 59
def prefixEnd_3334090 : Nat := 4983230072969 + 3 ^ 40 * 3334090 * 2
def baseEnd_3334090 : Nat := 570663571782988530413935

theorem tailTrace_3334090 : CollatzResearch.WordTrace tailWord_3334090 prefixEnd_3334090 570663571782988530413935 := by
  unfold tailWord_3334090
  simp only [CollatzResearch.WordTrace]
  refine ⟨30401063122792205520871931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81069501660779214722325149 30401063122792205520871931)
  ·
    refine ⟨45601594684188308281307897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30401063122792205520871931 45601594684188308281307897)
    ·
      refine ⟨34201196013141231210980923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45601594684188308281307897 34201196013141231210980923)
      ·
        refine ⟨51301794019711846816471385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34201196013141231210980923 51301794019711846816471385)
        ·
          refine ⟨38476345514783885112353539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51301794019711846816471385 38476345514783885112353539)
          ·
            refine ⟨57714518272175827668530309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38476345514783885112353539 57714518272175827668530309)
            ·
              refine ⟨10821472176032967687849433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57714518272175827668530309 10821472176032967687849433)
              ·
                refine ⟨8116104132024725765887075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10821472176032967687849433 8116104132024725765887075)
                ·
                  refine ⟨12174156198037088648830613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8116104132024725765887075 12174156198037088648830613)
                  ·
                    refine ⟨570663571782988530413935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12174156198037088648830613 570663571782988530413935)
                    ·
                      rfl

theorem cell23_3334090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_3334090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334090 prefixEnd_3334090 := by exact prefixLift 3334090
  have htrace : WordTrace (prefixWord ++ tailWord_3334090) baseStart_3334090 baseEnd_3334090 := by
    simpa [prefixWord, tailWord_3334090, baseEnd_3334090] using wordTrace_append hprefix tailTrace_3334090
  have hstable : (prefixWord ++ tailWord_3334090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334090).length < 2 ^ (prefixWord ++ tailWord_3334090).sum := by decide
  have hdescent : baseEnd_3334090 < baseStart_3334090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334103 : List Nat := [1, 1, 3, 2, 1, 1, 14]
def baseStart_3334103 : Nat := 118140960795 + 3334103 * 2 ^ 59
def prefixEnd_3334103 : Nat := 4983230072969 + 3 ^ 40 * 3334103 * 2
def baseEnd_3334103 : Nat := 21135770254289802967645

theorem tailTrace_3334103 : CollatzResearch.WordTrace tailWord_3334103 prefixEnd_3334103 21135770254289802967645 := by
  unfold tailWord_3334103
  simp only [CollatzResearch.WordTrace]
  refine ⟨121604726640121725303710963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81069817760081150202473975 121604726640121725303710963)
  ·
    refine ⟨182407089960182587955566445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121604726640121725303710963 182407089960182587955566445)
    ·
      refine ⟨68402658735068470483337417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182407089960182587955566445 68402658735068470483337417)
      ·
        refine ⟨51301994051301352862503063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68402658735068470483337417 51301994051301352862503063)
        ·
          refine ⟨76952991076952029293754595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51301994051301352862503063 76952991076952029293754595)
          ·
            refine ⟨115429486615428043940631893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76952991076952029293754595 115429486615428043940631893)
            ·
              refine ⟨21135770254289802967645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 115429486615428043940631893 21135770254289802967645)
              ·
                rfl

theorem cell23_3334103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 14].length) (baseStart_3334103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334103 prefixEnd_3334103 := by exact prefixLift 3334103
  have htrace : WordTrace (prefixWord ++ tailWord_3334103) baseStart_3334103 baseEnd_3334103 := by
    simpa [prefixWord, tailWord_3334103, baseEnd_3334103] using wordTrace_append hprefix tailTrace_3334103
  have hstable : (prefixWord ++ tailWord_3334103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334103).length < 2 ^ (prefixWord ++ tailWord_3334103).sum := by decide
  have hdescent : baseEnd_3334103 < baseStart_3334103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334137 : List Nat := [1, 2, 1, 3, 1, 6, 2, 7]
def baseStart_3334137 : Nat := 118140960795 + 3334137 * 2 ^ 59
def prefixEnd_3334137 : Nat := 4983230072969 + 3 ^ 40 * 3334137 * 2
def baseEnd_3334137 : Nat := 63407957368138033605707

theorem tailTrace_3334137 : CollatzResearch.WordTrace tailWord_3334137 prefixEnd_3334137 63407957368138033605707 := by
  unfold tailWord_3334137
  simp only [CollatzResearch.WordTrace]
  refine ⟨121605966721998549110448665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81070644481332366073632443 121605966721998549110448665)
  ·
    refine ⟨91204475041498911832836499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121605966721998549110448665 91204475041498911832836499)
    ·
      refine ⟨136806712562248367749254749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91204475041498911832836499 136806712562248367749254749)
      ·
        refine ⟨51302517210843137905970531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136806712562248367749254749 51302517210843137905970531)
        ·
          refine ⟨76953775816264706858955797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51302517210843137905970531 76953775816264706858955797)
          ·
            refine ⟨3607208241387408134013553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76953775816264706858955797 3607208241387408134013553)
            ·
              refine ⟨2705406181040556100510165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3607208241387408134013553 2705406181040556100510165)
              ·
                refine ⟨63407957368138033605707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2705406181040556100510165 63407957368138033605707)
                ·
                  rfl

theorem cell23_3334137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 7].length) (baseStart_3334137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334137 prefixEnd_3334137 := by exact prefixLift 3334137
  have htrace : WordTrace (prefixWord ++ tailWord_3334137) baseStart_3334137 baseEnd_3334137 := by
    simpa [prefixWord, tailWord_3334137, baseEnd_3334137] using wordTrace_append hprefix tailTrace_3334137
  have hstable : (prefixWord ++ tailWord_3334137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334137).length < 2 ^ (prefixWord ++ tailWord_3334137).sum := by decide
  have hdescent : baseEnd_3334137 < baseStart_3334137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334165 : List Nat := [1, 3, 2, 1, 5, 1, 3, 2, 1, 2, 2]
def baseStart_3334165 : Nat := 118140960795 + 3334165 * 2 ^ 59
def prefixEnd_3334165 : Nat := 4983230072969 + 3 ^ 40 * 3334165 * 2
def baseEnd_3334165 : Nat := 1712029226398052797803961

theorem tailTrace_3334165 : CollatzResearch.WordTrace tailWord_3334165 prefixEnd_3334165 1712029226398052797803961 := by
  unfold tailWord_3334165
  simp only [CollatzResearch.WordTrace]
  refine ⟨121606987965897109892467949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81071325310598073261645299 121606987965897109892467949)
  ·
    refine ⟨45602620487211416209675481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121606987965897109892467949 45602620487211416209675481)
    ·
      refine ⟨34201965365408562157256611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45602620487211416209675481 34201965365408562157256611)
      ·
        refine ⟨51302948048112843235884917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34201965365408562157256611 51302948048112843235884917)
        ·
          refine ⟨4809651379510579053364211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51302948048112843235884917 4809651379510579053364211)
          ·
            refine ⟨7214477069265868580046317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4809651379510579053364211 7214477069265868580046317)
            ·
              refine ⟨2705428900974700717517369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7214477069265868580046317 2705428900974700717517369)
              ·
                refine ⟨2029071675731025538138027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2705428900974700717517369 2029071675731025538138027)
                ·
                  refine ⟨3043607513596538307207041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029071675731025538138027 3043607513596538307207041)
                  ·
                    refine ⟨2282705635197403730405281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3043607513596538307207041 2282705635197403730405281)
                    ·
                      refine ⟨1712029226398052797803961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2282705635197403730405281 1712029226398052797803961)
                      ·
                        rfl

theorem cell23_3334165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_3334165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334165 prefixEnd_3334165 := by exact prefixLift 3334165
  have htrace : WordTrace (prefixWord ++ tailWord_3334165) baseStart_3334165 baseEnd_3334165 := by
    simpa [prefixWord, tailWord_3334165, baseEnd_3334165] using wordTrace_append hprefix tailTrace_3334165
  have hstable : (prefixWord ++ tailWord_3334165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334165).length < 2 ^ (prefixWord ++ tailWord_3334165).sum := by decide
  have hdescent : baseEnd_3334165 < baseStart_3334165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334181 : List Nat := [1, 3, 1, 2, 2, 3, 4, 1, 2, 1, 3]
def baseStart_3334181 : Nat := 118140960795 + 3334181 * 2 ^ 59
def prefixEnd_3334181 : Nat := 4983230072969 + 3 ^ 40 * 3334181 * 2
def baseEnd_3334181 : Nat := 1712037442088524735203887

theorem tailTrace_3334181 : CollatzResearch.WordTrace tailWord_3334181 prefixEnd_3334181 1712037442088524735203887 := by
  unfold tailWord_3334181
  simp only [CollatzResearch.WordTrace]
  refine ⟨121607571533839144625050397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81071714355892763083366931 121607571533839144625050397)
  ·
    refine ⟨45602839325189679234393899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121607571533839144625050397 45602839325189679234393899)
    ·
      refine ⟨68404258987784518851590849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45602839325189679234393899 68404258987784518851590849)
      ·
        refine ⟨51303194240838389138693137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68404258987784518851590849 51303194240838389138693137)
        ·
          refine ⟨38477395680628791854019853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51303194240838389138693137 38477395680628791854019853)
          ·
            refine ⟨14429023380235796945257445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38477395680628791854019853 14429023380235796945257445)
            ·
              refine ⟨2705441883794211927235771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14429023380235796945257445 2705441883794211927235771)
              ·
                refine ⟨4058162825691317890853657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2705441883794211927235771 4058162825691317890853657)
                ·
                  refine ⟨3043622119268488418140243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4058162825691317890853657 3043622119268488418140243)
                  ·
                    refine ⟨4565433178902732627210365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3043622119268488418140243 4565433178902732627210365)
                    ·
                      refine ⟨1712037442088524735203887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4565433178902732627210365 1712037442088524735203887)
                      ·
                        rfl

theorem cell23_3334181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_3334181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334181 prefixEnd_3334181 := by exact prefixLift 3334181
  have htrace : WordTrace (prefixWord ++ tailWord_3334181) baseStart_3334181 baseEnd_3334181 := by
    simpa [prefixWord, tailWord_3334181, baseEnd_3334181] using wordTrace_append hprefix tailTrace_3334181
  have hstable : (prefixWord ++ tailWord_3334181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334181).length < 2 ^ (prefixWord ++ tailWord_3334181).sum := by decide
  have hdescent : baseEnd_3334181 < baseStart_3334181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334204 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 1, 4, 2]
def baseStart_3334204 : Nat := 118140960795 + 3334204 * 2 ^ 59
def prefixEnd_3334204 : Nat := 4983230072969 + 3 ^ 40 * 3334204 * 2
def baseEnd_3334204 : Nat := 1712049252143578145216281

theorem tailTrace_3334204 : CollatzResearch.WordTrace tailWord_3334204 prefixEnd_3334204 1712049252143578145216281 := by
  unfold tailWord_3334204
  simp only [CollatzResearch.WordTrace]
  refine ⟨60804205206377909776568833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81072273608503879702091777 60804205206377909776568833)
  ·
    refine ⟨45603153904783432332426625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60804205206377909776568833 45603153904783432332426625)
    ·
      refine ⟨34202365428587574249319969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45603153904783432332426625 34202365428587574249319969)
      ·
        refine ⟨25651774071440680686989977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34202365428587574249319969 25651774071440680686989977)
        ·
          refine ⟨19238830553580510515242483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25651774071440680686989977 19238830553580510515242483)
          ·
            refine ⟨28858245830370765772863725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19238830553580510515242483 28858245830370765772863725)
            ·
              refine ⟨10821842186389037164823897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28858245830370765772863725 10821842186389037164823897)
              ·
                refine ⟨8116381639791777873617923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10821842186389037164823897 8116381639791777873617923)
                ·
                  refine ⟨12174572459687666810426885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8116381639791777873617923 12174572459687666810426885)
                  ·
                    refine ⟨2282732336191437526955041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12174572459687666810426885 2282732336191437526955041)
                    ·
                      refine ⟨1712049252143578145216281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2282732336191437526955041 1712049252143578145216281)
                      ·
                        rfl

theorem cell23_3334204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_3334204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334204 prefixEnd_3334204 := by exact prefixLift 3334204
  have htrace : WordTrace (prefixWord ++ tailWord_3334204) baseStart_3334204 baseEnd_3334204 := by
    simpa [prefixWord, tailWord_3334204, baseEnd_3334204] using wordTrace_append hprefix tailTrace_3334204
  have hstable : (prefixWord ++ tailWord_3334204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334204).length < 2 ^ (prefixWord ++ tailWord_3334204).sum := by decide
  have hdescent : baseEnd_3334204 < baseStart_3334204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334214 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_3334214 : Nat := 118140960795 + 3334214 * 2 ^ 59
def prefixEnd_3334214 : Nat := 4983230072969 + 3 ^ 40 * 3334214 * 2
def baseEnd_3334214 : Nat := 570684795650041035363745

theorem tailTrace_3334214 : CollatzResearch.WordTrace tailWord_3334214 prefixEnd_3334214 570684795650041035363745 := by
  unfold tailWord_3334214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3800274223209987226906303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81072516761813060840667797 3800274223209987226906303)
  ·
    refine ⟨5700411334814980840359455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3800274223209987226906303 5700411334814980840359455)
    ·
      refine ⟨8550617002222471260539183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5700411334814980840359455 8550617002222471260539183)
      ·
        refine ⟨12825925503333706890808775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8550617002222471260539183 12825925503333706890808775)
        ·
          refine ⟨19238888255000560336213163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12825925503333706890808775 19238888255000560336213163)
          ·
            refine ⟨28858332382500840504319745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19238888255000560336213163 28858332382500840504319745)
            ·
              refine ⟨21643749286875630378239809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28858332382500840504319745 21643749286875630378239809)
              ·
                refine ⟨16232811965156722783679857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21643749286875630378239809 16232811965156722783679857)
                ·
                  refine ⟨12174608973867542087759893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16232811965156722783679857 12174608973867542087759893)
                  ·
                    refine ⟨570684795650041035363745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12174608973867542087759893 570684795650041035363745)
                    ·
                      rfl

theorem cell23_3334214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_3334214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334214 prefixEnd_3334214 := by exact prefixLift 3334214
  have htrace : WordTrace (prefixWord ++ tailWord_3334214) baseStart_3334214 baseEnd_3334214 := by
    simpa [prefixWord, tailWord_3334214, baseEnd_3334214] using wordTrace_append hprefix tailTrace_3334214
  have hstable : (prefixWord ++ tailWord_3334214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334214).length < 2 ^ (prefixWord ++ tailWord_3334214).sum := by decide
  have hdescent : baseEnd_3334214 < baseStart_3334214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334220 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 1, 2, 7]
def baseStart_3334220 : Nat := 118140960795 + 3334220 * 2 ^ 59
def prefixEnd_3334220 : Nat := 4983230072969 + 3 ^ 40 * 3334220 * 2
def baseEnd_3334220 : Nat := 1712057467834050082616207

theorem tailTrace_3334220 : CollatzResearch.WordTrace tailWord_3334220 prefixEnd_3334220 1712057467834050082616207 := by
  unfold tailWord_3334220
  simp only [CollatzResearch.WordTrace]
  refine ⟨60804496990348927142860057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81072662653798569523813409 60804496990348927142860057)
  ·
    refine ⟨45603372742761695357145043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60804496990348927142860057 45603372742761695357145043)
    ·
      refine ⟨68405059114142543035717565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45603372742761695357145043 68405059114142543035717565)
      ·
        refine ⟨25651897167803453638394087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68405059114142543035717565 25651897167803453638394087)
        ·
          refine ⟨38477845751705180457591131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25651897167803453638394087 38477845751705180457591131)
          ·
            refine ⟨57716768627557770686386697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38477845751705180457591131 57716768627557770686386697)
            ·
              refine ⟨43287576470668328014790023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57716768627557770686386697 43287576470668328014790023)
              ·
                refine ⟨64931364706002492022185035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43287576470668328014790023 64931364706002492022185035)
                ·
                  refine ⟨97397047059003738033277553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64931364706002492022185035 97397047059003738033277553)
                  ·
                    refine ⟨73047785294252803524958165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97397047059003738033277553 73047785294252803524958165)
                    ·
                      refine ⟨1712057467834050082616207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73047785294252803524958165 1712057467834050082616207)
                      ·
                        rfl

theorem cell23_3334220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_3334220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334220 prefixEnd_3334220 := by exact prefixLift 3334220
  have htrace : WordTrace (prefixWord ++ tailWord_3334220) baseStart_3334220 baseEnd_3334220 := by
    simpa [prefixWord, tailWord_3334220, baseEnd_3334220] using wordTrace_append hprefix tailTrace_3334220
  have hstable : (prefixWord ++ tailWord_3334220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334220).length < 2 ^ (prefixWord ++ tailWord_3334220).sum := by decide
  have hdescent : baseEnd_3334220 < baseStart_3334220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334304 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 3, 4]
def baseStart_3334304 : Nat := 118140960795 + 3334304 * 2 ^ 59
def prefixEnd_3334304 : Nat := 4983230072969 + 3 ^ 40 * 3334304 * 2
def baseEnd_3334304 : Nat := 570700200069675917988607

theorem tailTrace_3334304 : CollatzResearch.WordTrace tailWord_3334304 prefixEnd_3334304 570700200069675917988607 := by
  unfold tailWord_3334304
  simp only [CollatzResearch.WordTrace]
  refine ⟨60806028856196768315888983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81074705141595691087851977 60806028856196768315888983)
  ·
    refine ⟨91209043284295152473833475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60806028856196768315888983 91209043284295152473833475)
    ·
      refine ⟨136813564926442728710750213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91209043284295152473833475 136813564926442728710750213)
      ·
        refine ⟨25652543423708011633265665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136813564926442728710750213 25652543423708011633265665)
        ·
          refine ⟨19239407567781008724949249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25652543423708011633265665 19239407567781008724949249)
          ·
            refine ⟨14429555675835756543711937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19239407567781008724949249 14429555675835756543711937)
            ·
              refine ⟨10822166756876817407783953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14429555675835756543711937 10822166756876817407783953)
              ·
                refine ⟨8116625067657613055837965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10822166756876817407783953 8116625067657613055837965)
                ·
                  refine ⟨3043734400371604895939237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8116625067657613055837965 3043734400371604895939237)
                  ·
                    refine ⟨570700200069675917988607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3043734400371604895939237 570700200069675917988607)
                    ·
                      rfl

theorem cell23_3334304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 3, 4].length) (baseStart_3334304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334304 prefixEnd_3334304 := by exact prefixLift 3334304
  have htrace : WordTrace (prefixWord ++ tailWord_3334304) baseStart_3334304 baseEnd_3334304 := by
    simpa [prefixWord, tailWord_3334304, baseEnd_3334304] using wordTrace_append hprefix tailTrace_3334304
  have hstable : (prefixWord ++ tailWord_3334304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334304).length < 2 ^ (prefixWord ++ tailWord_3334304).sum := by decide
  have hdescent : baseEnd_3334304 < baseStart_3334304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334347 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 3, 5]
def baseStart_3334347 : Nat := 118140960795 + 3334347 * 2 ^ 59
def prefixEnd_3334347 : Nat := 4983230072969 + 3 ^ 40 * 3334347 * 2
def baseEnd_3334347 : Nat := 570707559959057028576041

theorem tailTrace_3334347 : CollatzResearch.WordTrace tailWord_3334347 prefixEnd_3334347 570707559959057028576041 := by
  unfold tailWord_3334347
  simp only [CollatzResearch.WordTrace]
  refine ⟨121613626051237754975593295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81075750700825169983728863 121613626051237754975593295)
  ·
    refine ⟨182420439076856632463389943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121613626051237754975593295 182420439076856632463389943)
    ·
      refine ⟨273630658615284948695084915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182420439076856632463389943 273630658615284948695084915)
      ·
        refine ⟨410445987922927423042627373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273630658615284948695084915 410445987922927423042627373)
        ·
          refine ⟨153917245471097783640985265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410445987922927423042627373 153917245471097783640985265)
          ·
            refine ⟨115437934103323337730738949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153917245471097783640985265 115437934103323337730738949)
            ·
              refine ⟨21644612644373125824513553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115437934103323337730738949 21644612644373125824513553)
              ·
                refine ⟨16233459483279844368385165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21644612644373125824513553 16233459483279844368385165)
                ·
                  refine ⟨6087547306229941638144437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16233459483279844368385165 6087547306229941638144437)
                  ·
                    refine ⟨570707559959057028576041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6087547306229941638144437 570707559959057028576041)
                    ·
                      rfl

theorem cell23_3334347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 5].length) (baseStart_3334347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334347 prefixEnd_3334347 := by exact prefixLift 3334347
  have htrace : WordTrace (prefixWord ++ tailWord_3334347) baseStart_3334347 baseEnd_3334347 := by
    simpa [prefixWord, tailWord_3334347, baseEnd_3334347] using wordTrace_append hprefix tailTrace_3334347
  have hstable : (prefixWord ++ tailWord_3334347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334347).length < 2 ^ (prefixWord ++ tailWord_3334347).sum := by decide
  have hdescent : baseEnd_3334347 < baseStart_3334347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334377 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 1, 6]
def baseStart_3334377 : Nat := 118140960795 + 3334377 * 2 ^ 59
def prefixEnd_3334377 : Nat := 4983230072969 + 3 ^ 40 * 3334377 * 2
def baseEnd_3334377 : Nat := 570712694765601989450995

theorem tailTrace_3334377 : CollatzResearch.WordTrace tailWord_3334377 prefixEnd_3334377 570712694765601989450995 := by
  unfold tailWord_3334377
  simp only [CollatzResearch.WordTrace]
  refine ⟨121614720241129070099185385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81076480160752713399456923 121614720241129070099185385)
  ·
    refine ⟨91211040180846802574389039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121614720241129070099185385 91211040180846802574389039)
    ·
      refine ⟨136816560271270203861583559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91211040180846802574389039 136816560271270203861583559)
      ·
        refine ⟨205224840406905305792375339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136816560271270203861583559 205224840406905305792375339)
        ·
          refine ⟨307837260610357958688563009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205224840406905305792375339 307837260610357958688563009)
          ·
            refine ⟨230877945457768469016422257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307837260610357958688563009 230877945457768469016422257)
            ·
              refine ⟨173158459093326351762316693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230877945457768469016422257 173158459093326351762316693)
              ·
                refine ⟨8116802769999672738858595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173158459093326351762316693 8116802769999672738858595)
                ·
                  refine ⟨12175204154999509108287893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8116802769999672738858595 12175204154999509108287893)
                  ·
                    refine ⟨570712694765601989450995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12175204154999509108287893 570712694765601989450995)
                    ·
                      rfl

theorem cell23_3334377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 6].length) (baseStart_3334377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334377 prefixEnd_3334377 := by exact prefixLift 3334377
  have htrace : WordTrace (prefixWord ++ tailWord_3334377) baseStart_3334377 baseEnd_3334377 := by
    simpa [prefixWord, tailWord_3334377, baseEnd_3334377] using wordTrace_append hprefix tailTrace_3334377
  have hstable : (prefixWord ++ tailWord_3334377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334377).length < 2 ^ (prefixWord ++ tailWord_3334377).sum := by decide
  have hdescent : baseEnd_3334377 < baseStart_3334377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334378 : List Nat := [3, 1, 3, 1, 1, 2, 2, 5, 1, 1, 3]
def baseStart_3334378 : Nat := 118140960795 + 3334378 * 2 ^ 59
def prefixEnd_3334378 : Nat := 4983230072969 + 3 ^ 40 * 3334378 * 2
def baseEnd_3334378 : Nat := 1712138597777460464440481

theorem tailTrace_3334378 : CollatzResearch.WordTrace tailWord_3334378 prefixEnd_3334378 1712138597777460464440481 := by
  unfold tailWord_3334378
  simp only [CollatzResearch.WordTrace]
  refine ⟨30403689178531361817492947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81076504476083631513314525 30403689178531361817492947)
  ·
    refine ⟨45605533767797042726239421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30403689178531361817492947 45605533767797042726239421)
    ·
      refine ⟨17102075162923891022339783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45605533767797042726239421 17102075162923891022339783)
      ·
        refine ⟨25653112744385836533509675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17102075162923891022339783 25653112744385836533509675)
        ·
          refine ⟨38479669116578754800264513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25653112744385836533509675 38479669116578754800264513)
          ·
            refine ⟨28859751837434066100198385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38479669116578754800264513 28859751837434066100198385)
            ·
              refine ⟨21644813878075549575148789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28859751837434066100198385 21644813878075549575148789)
              ·
                refine ⟨2029201301069582772670199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21644813878075549575148789 2029201301069582772670199)
                ·
                  refine ⟨3043801951604374159005299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029201301069582772670199 3043801951604374159005299)
                  ·
                    refine ⟨4565702927406561238507949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3043801951604374159005299 4565702927406561238507949)
                    ·
                      refine ⟨1712138597777460464440481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4565702927406561238507949 1712138597777460464440481)
                      ·
                        rfl

theorem cell23_3334378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_3334378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334378 prefixEnd_3334378 := by exact prefixLift 3334378
  have htrace : WordTrace (prefixWord ++ tailWord_3334378) baseStart_3334378 baseEnd_3334378 := by
    simpa [prefixWord, tailWord_3334378, baseEnd_3334378] using wordTrace_append hprefix tailTrace_3334378
  have hstable : (prefixWord ++ tailWord_3334378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334378).length < 2 ^ (prefixWord ++ tailWord_3334378).sum := by decide
  have hdescent : baseEnd_3334378 < baseStart_3334378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334384 : List Nat := [2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 4]
def baseStart_3334384 : Nat := 118140960795 + 3334384 * 2 ^ 59
def prefixEnd_3334384 : Nat := 4983230072969 + 3 ^ 40 * 3334384 * 2
def baseEnd_3334384 : Nat := 1712141678661387440965453

theorem tailTrace_3334384 : CollatzResearch.WordTrace tailWord_3334384 prefixEnd_3334384 1712141678661387440965453 := by
  unfold tailWord_3334384
  simp only [CollatzResearch.WordTrace]
  refine ⟨60807487776051855147345103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81076650368069140196460137 60807487776051855147345103)
  ·
    refine ⟨91211231664077782721017655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60807487776051855147345103 91211231664077782721017655)
    ·
      refine ⟨136816847496116674081526483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91211231664077782721017655 136816847496116674081526483)
      ·
        refine ⟨205225271244175011122289725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136816847496116674081526483 205225271244175011122289725)
        ·
          refine ⟨76959476716565629170858647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205225271244175011122289725 76959476716565629170858647)
          ·
            refine ⟨115439215074848443756287971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76959476716565629170858647 115439215074848443756287971)
            ·
              refine ⟨173158822612272665634431957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115439215074848443756287971 173158822612272665634431957)
              ·
                refine ⟨4058409904975140600806999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 173158822612272665634431957 4058409904975140600806999)
                ·
                  refine ⟨6087614857462710901210499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4058409904975140600806999 6087614857462710901210499)
                  ·
                    refine ⟨9131422286194066351815749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6087614857462710901210499 9131422286194066351815749)
                    ·
                      refine ⟨1712141678661387440965453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9131422286194066351815749 1712141678661387440965453)
                      ·
                        rfl

theorem cell23_3334384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 4].length) (baseStart_3334384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334384 prefixEnd_3334384 := by exact prefixLift 3334384
  have htrace : WordTrace (prefixWord ++ tailWord_3334384) baseStart_3334384 baseEnd_3334384 := by
    simpa [prefixWord, tailWord_3334384, baseEnd_3334384] using wordTrace_append hprefix tailTrace_3334384
  have hstable : (prefixWord ++ tailWord_3334384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334384).length < 2 ^ (prefixWord ++ tailWord_3334384).sum := by decide
  have hdescent : baseEnd_3334384 < baseStart_3334384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334397 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_3334397 : Nat := 118140960795 + 3334397 * 2 ^ 59
def prefixEnd_3334397 : Nat := 4983230072969 + 3 ^ 40 * 3334397 * 2
def baseEnd_3334397 : Nat := 1712148353909895890102893

theorem tailTrace_3334397 : CollatzResearch.WordTrace tailWord_3334397 prefixEnd_3334397 1712148353909895890102893 := by
  unfold tailWord_3334397
  simp only [CollatzResearch.WordTrace]
  refine ⟨121615449701056613514913445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81076966467371075676608963 121615449701056613514913445)
  ·
    refine ⟨22802896818948115034046271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121615449701056613514913445 22802896818948115034046271)
    ·
      refine ⟨34204345228422172551069407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22802896818948115034046271 34204345228422172551069407)
      ·
        refine ⟨51306517842633258826604111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34204345228422172551069407 51306517842633258826604111)
        ·
          refine ⟨76959776763949888239906167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51306517842633258826604111 76959776763949888239906167)
          ·
            refine ⟨115439665145924832359859251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76959776763949888239906167 115439665145924832359859251)
            ·
              refine ⟨173159497718887248539788877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115439665145924832359859251 173159497718887248539788877)
              ·
                refine ⟨64934811644582718202420829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173159497718887248539788877 64934811644582718202420829)
                ·
                  refine ⟨24350554366718519325907811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64934811644582718202420829 24350554366718519325907811)
                  ·
                    refine ⟨36525831550077778988861717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24350554366718519325907811 36525831550077778988861717)
                    ·
                      refine ⟨1712148353909895890102893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36525831550077778988861717 1712148353909895890102893)
                      ·
                        rfl

theorem cell23_3334397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_3334397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334397 prefixEnd_3334397 := by exact prefixLift 3334397
  have htrace : WordTrace (prefixWord ++ tailWord_3334397) baseStart_3334397 baseEnd_3334397 := by
    simpa [prefixWord, tailWord_3334397, baseEnd_3334397] using wordTrace_append hprefix tailTrace_3334397
  have hstable : (prefixWord ++ tailWord_3334397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334397).length < 2 ^ (prefixWord ++ tailWord_3334397).sum := by decide
  have hdescent : baseEnd_3334397 < baseStart_3334397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334424 : List Nat := [2, 1, 2, 3, 1, 2, 5, 7]
def baseStart_3334424 : Nat := 118140960795 + 3334424 * 2 ^ 59
def prefixEnd_3334424 : Nat := 4983230072969 + 3 ^ 40 * 3334424 * 2
def baseEnd_3334424 : Nat := 63413415477317306832047

theorem tailTrace_3334424 : CollatzResearch.WordTrace tailWord_3334424 prefixEnd_3334424 63413415477317306832047 := by
  unfold tailWord_3334424
  simp only [CollatzResearch.WordTrace]
  refine ⟨60808217235979398563073163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81077622981305864750764217 60808217235979398563073163)
  ·
    refine ⟨91212325853969097844609745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60808217235979398563073163 91212325853969097844609745)
    ·
      refine ⟨68409244390476823383457309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91212325853969097844609745 68409244390476823383457309)
      ·
        refine ⟨25653466646428808768796491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68409244390476823383457309 25653466646428808768796491)
        ·
          refine ⟨38480199969643213153194737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25653466646428808768796491 38480199969643213153194737)
          ·
            refine ⟨28860149977232409864896053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38480199969643213153194737 28860149977232409864896053)
            ·
              refine ⟨2705639060365538424834005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28860149977232409864896053 2705639060365538424834005)
              ·
                refine ⟨63413415477317306832047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2705639060365538424834005 63413415477317306832047)
                ·
                  rfl

theorem cell23_3334424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 7].length) (baseStart_3334424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334424 prefixEnd_3334424 := by exact prefixLift 3334424
  have htrace : WordTrace (prefixWord ++ tailWord_3334424) baseStart_3334424 baseEnd_3334424 := by
    simpa [prefixWord, tailWord_3334424, baseEnd_3334424] using wordTrace_append hprefix tailTrace_3334424
  have hstable : (prefixWord ++ tailWord_3334424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334424).length < 2 ^ (prefixWord ++ tailWord_3334424).sum := by decide
  have hdescent : baseEnd_3334424 < baseStart_3334424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334435 : List Nat := [1, 1, 1, 4, 2, 2, 4, 3, 1, 2, 2]
def baseStart_3334435 : Nat := 118140960795 + 3334435 * 2 ^ 59
def prefixEnd_3334435 : Nat := 4983230072969 + 3 ^ 40 * 3334435 * 2
def baseEnd_3334435 : Nat := 1712167866174766741427719

theorem tailTrace_3334435 : CollatzResearch.WordTrace tailWord_3334435 prefixEnd_3334435 1712167866174766741427719 := by
  unfold tailWord_3334435
  simp only [CollatzResearch.WordTrace]
  refine ⟨121616835674918946004796759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81077890449945964003197839 121616835674918946004796759)
  ·
    refine ⟨182425253512378419007195139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121616835674918946004796759 182425253512378419007195139)
    ·
      refine ⟨273637880268567628510792709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182425253512378419007195139 273637880268567628510792709)
      ·
        refine ⟨51307102550356430345773633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273637880268567628510792709 51307102550356430345773633)
        ·
          refine ⟨38480326912767322759330225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51307102550356430345773633 38480326912767322759330225)
          ·
            refine ⟨28860245184575492069497669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38480326912767322759330225 28860245184575492069497669)
            ·
              refine ⟨5411295972107904763030813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28860245184575492069497669 5411295972107904763030813)
              ·
                refine ⟨2029235989540464286136555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5411295972107904763030813 2029235989540464286136555)
                ·
                  refine ⟨3043853984310696429204833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029235989540464286136555 3043853984310696429204833)
                  ·
                    refine ⟨2282890488233022321903625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3043853984310696429204833 2282890488233022321903625)
                    ·
                      refine ⟨1712167866174766741427719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2282890488233022321903625 1712167866174766741427719)
                      ·
                        rfl

theorem cell23_3334435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_3334435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334435 prefixEnd_3334435 := by exact prefixLift 3334435
  have htrace : WordTrace (prefixWord ++ tailWord_3334435) baseStart_3334435 baseEnd_3334435 := by
    simpa [prefixWord, tailWord_3334435, baseEnd_3334435] using wordTrace_append hprefix tailTrace_3334435
  have hstable : (prefixWord ++ tailWord_3334435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334435).length < 2 ^ (prefixWord ++ tailWord_3334435).sum := by decide
  have hdescent : baseEnd_3334435 < baseStart_3334435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334451 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 4, 1, 3]
def baseStart_3334451 : Nat := 118140960795 + 3334451 * 2 ^ 59
def prefixEnd_3334451 : Nat := 4983230072969 + 3 ^ 40 * 3334451 * 2
def baseEnd_3334451 : Nat := 1712176081865238678827645

theorem tailTrace_3334451 : CollatzResearch.WordTrace tailWord_3334451 prefixEnd_3334451 1712176081865238678827645 := by
  unfold tailWord_3334451
  simp only [CollatzResearch.WordTrace]
  refine ⟨121617419242860980737379207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81078279495240653824919471 121617419242860980737379207)
  ·
    refine ⟨182426128864291471106068811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121617419242860980737379207 182426128864291471106068811)
    ·
      refine ⟨273639193296437206659103217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182426128864291471106068811 273639193296437206659103217)
      ·
        refine ⟨205229394972327904994327413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273639193296437206659103217 205229394972327904994327413)
        ·
          refine ⟨19240255778655741093218195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205229394972327904994327413 19240255778655741093218195)
          ·
            refine ⟨28860383667983611639827293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19240255778655741093218195 28860383667983611639827293)
            ·
              refine ⟨10822643875493854364935235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28860383667983611639827293 10822643875493854364935235)
              ·
                refine ⟨16233965813240781547402853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10822643875493854364935235 16233965813240781547402853)
                ·
                  refine ⟨3043868589982646540138035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16233965813240781547402853 3043868589982646540138035)
                  ·
                    refine ⟨4565802884973969810207053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3043868589982646540138035 4565802884973969810207053)
                    ·
                      refine ⟨1712176081865238678827645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4565802884973969810207053 1712176081865238678827645)
                      ·
                        rfl

theorem cell23_3334451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 1, 3].length) (baseStart_3334451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334451 prefixEnd_3334451 := by exact prefixLift 3334451
  have htrace : WordTrace (prefixWord ++ tailWord_3334451) baseStart_3334451 baseEnd_3334451 := by
    simpa [prefixWord, tailWord_3334451, baseEnd_3334451] using wordTrace_append hprefix tailTrace_3334451
  have hstable : (prefixWord ++ tailWord_3334451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334451).length < 2 ^ (prefixWord ++ tailWord_3334451).sum := by decide
  have hdescent : baseEnd_3334451 < baseStart_3334451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334452 : List Nat := [2, 5, 1, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_3334452 : Nat := 118140960795 + 3334452 * 2 ^ 59
def prefixEnd_3334452 : Nat := 4983230072969 + 3 ^ 40 * 3334452 * 2
def baseEnd_3334452 : Nat := 1712176595345893174915141

theorem tailTrace_3334452 : CollatzResearch.WordTrace tailWord_3334452 prefixEnd_3334452 1712176595345893174915141 := by
  unfold tailWord_3334452
  simp only [CollatzResearch.WordTrace]
  refine ⟨60808727857928678954082805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81078303810571571938777073 60808727857928678954082805)
  ·
    refine ⟨5700818236680813651945263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60808727857928678954082805 5700818236680813651945263)
    ·
      refine ⟨8551227355021220477917895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5700818236680813651945263 8551227355021220477917895)
      ·
        refine ⟨12826841032531830716876843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8551227355021220477917895 12826841032531830716876843)
        ·
          refine ⟨19240261548797746075315265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12826841032531830716876843 19240261548797746075315265)
          ·
            refine ⟨14430196161598309556486449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19240261548797746075315265 14430196161598309556486449)
            ·
              refine ⟨10822647121198732167364837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14430196161598309556486449 10822647121198732167364837)
              ·
                refine ⟨2029246335224762281380907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10822647121198732167364837 2029246335224762281380907)
                ·
                  refine ⟨3043869502837143422071361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029246335224762281380907 3043869502837143422071361)
                  ·
                    refine ⟨2282902127127857566553521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3043869502837143422071361 2282902127127857566553521)
                    ·
                      refine ⟨1712176595345893174915141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2282902127127857566553521 1712176595345893174915141)
                      ·
                        rfl

theorem cell23_3334452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_3334452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334452 prefixEnd_3334452 := by exact prefixLift 3334452
  have htrace : WordTrace (prefixWord ++ tailWord_3334452) baseStart_3334452 baseEnd_3334452 := by
    simpa [prefixWord, tailWord_3334452, baseEnd_3334452] using wordTrace_append hprefix tailTrace_3334452
  have hstable : (prefixWord ++ tailWord_3334452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334452).length < 2 ^ (prefixWord ++ tailWord_3334452).sum := by decide
  have hdescent : baseEnd_3334452 < baseStart_3334452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334465 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_3334465 : Nat := 118140960795 + 3334465 * 2 ^ 59
def prefixEnd_3334465 : Nat := 4983230072969 + 3 ^ 40 * 3334465 * 2
def baseEnd_3334465 : Nat := 1712183270594401624052581

theorem tailTrace_3334465 : CollatzResearch.WordTrace tailWord_3334465 prefixEnd_3334465 1712183270594401624052581 := by
  unfold tailWord_3334465
  simp only [CollatzResearch.WordTrace]
  refine ⟨121617929864810261128388849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81078619909873507418925899 121617929864810261128388849)
  ·
    refine ⟨91213447398607695846291637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121617929864810261128388849 91213447398607695846291637)
    ·
      refine ⟨8551260693619471485589841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91213447398607695846291637 8551260693619471485589841)
      ·
        refine ⟨6413445520214603614192381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8551260693619471485589841 6413445520214603614192381)
        ·
          refine ⟨2405042070080476355322143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6413445520214603614192381 2405042070080476355322143)
          ·
            refine ⟨3607563105120714532983215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405042070080476355322143 3607563105120714532983215)
            ·
              refine ⟨5411344657681071799474823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3607563105120714532983215 5411344657681071799474823)
              ·
                refine ⟨8117016986521607699212235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5411344657681071799474823 8117016986521607699212235)
                ·
                  refine ⟨12175525479782411548818353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8117016986521607699212235 12175525479782411548818353)
                  ·
                    refine ⟨9131644109836808661613765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12175525479782411548818353 9131644109836808661613765)
                    ·
                      refine ⟨1712183270594401624052581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9131644109836808661613765 1712183270594401624052581)
                      ·
                        rfl

theorem cell23_3334465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_3334465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334465 prefixEnd_3334465 := by exact prefixLift 3334465
  have htrace : WordTrace (prefixWord ++ tailWord_3334465) baseStart_3334465 baseEnd_3334465 := by
    simpa [prefixWord, tailWord_3334465, baseEnd_3334465] using wordTrace_append hprefix tailTrace_3334465
  have hstable : (prefixWord ++ tailWord_3334465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334465).length < 2 ^ (prefixWord ++ tailWord_3334465).sum := by decide
  have hdescent : baseEnd_3334465 < baseStart_3334465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
